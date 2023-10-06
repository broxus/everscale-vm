use std::collections::{BTreeMap, HashMap};

use darling::util::{parse_expr, SpannedValue};
use darling::{Error, FromMeta};
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::ItemImpl;

#[derive(Debug, FromMeta)]
struct VmInstrArgs {
    code: SpannedValue<String>,
    #[darling(default)]
    range_from: Option<SpannedValue<String>>,

    #[darling(with = "parse_expr::preserve_str_literal")]
    fmt: syn::Expr,

    #[darling(default)]
    args: HashMap<String, syn::Expr>,
    #[darling(default)]
    cond: Option<syn::Expr>,
}

#[proc_macro_attribute]
pub fn vm_module(_: TokenStream, input: TokenStream) -> TokenStream {
    let mut input = syn::parse_macro_input!(input as ItemImpl);

    let opcodes_arg = quote::format_ident!("__t");

    let mut definitions = Vec::new();
    let mut errors = Vec::new();

    let mut init_function_names = Vec::new();
    let mut init_functions = Vec::new();
    let mut other_functions = Vec::new();

    let mut opcodes = Opcodes::default();

    for impl_item in input.items.drain(..) {
        let syn::ImplItem::Fn(mut fun) = impl_item else {
            other_functions.push(impl_item);
            continue;
        };

        let mut has_init = false;

        let mut instr_attrs = Vec::with_capacity(fun.attrs.len());
        let mut remaining_attr = Vec::new();
        for attr in fun.attrs.drain(..) {
            if let Some(path) = attr.meta.path().get_ident() {
                if path == "instr" {
                    instr_attrs.push(attr);
                    continue;
                } else if path == "init" {
                    has_init = true;
                    continue;
                }
            }

            remaining_attr.push(attr);
        }
        fun.attrs = remaining_attr;

        if has_init {
            fun.sig.ident = quote::format_ident!("__{}", fun.sig.ident);
            init_function_names.push(fun.sig.ident.clone());
            init_functions.push(fun);
        } else {
            for attr in instr_attrs {
                match process_instr_definition(&fun, &opcodes_arg, &attr, &mut opcodes) {
                    Ok(definition) => definitions.push(definition),
                    Err(e) => errors.push(e.with_span(&attr)),
                }
            }

            other_functions.push(syn::ImplItem::Fn(fun));
        }
    }

    if !errors.is_empty() {
        return TokenStream::from(Error::multiple(errors).write_errors());
    }

    let ty = input.self_ty;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    quote! {
        impl #impl_generics #ty #ty_generics #where_clause {
            #(#init_functions)*
        }

        #[automatically_derived]
        impl #impl_generics ::everscale_vm::instr::Module for #ty #ty_generics #where_clause {
            fn init(&self, #opcodes_arg: &mut ::everscale_vm::dispatch::Opcodes) -> ::anyhow::Result<()> {
                #(self.#init_function_names(#opcodes_arg)?;)*
                #(#definitions)*
                Ok(())
            }
        }

        #(#other_functions)*
    }
    .into()
}

fn process_instr_definition(
    function: &syn::ImplItemFn,
    opcodes_arg: &syn::Ident,
    attr: &syn::Attribute,
    opcodes: &mut Opcodes,
) -> Result<syn::Expr, Error> {
    let mut instr = VmInstrArgs::from_meta(&attr.meta)?;

    let mut opcode_bits = 0u16;
    let mut opcode_base_min = 0;
    let mut args = Vec::<(char, u16)>::new();
    for c in instr.code.chars() {
        if !c.is_ascii_alphanumeric() {
            return Err(
                Error::custom("Invalid pattern for the opcode").with_span(&instr.code.span())
            );
        }

        opcode_base_min <<= 4;

        if let Some(c) = c.to_digit(16) {
            if !args.is_empty() {
                return Err(
                    Error::custom("Invalid pattern for the opcode").with_span(&instr.code.span())
                );
            }

            opcode_bits += 4;
            opcode_base_min |= c;
        } else {
            if let Some((last, last_bits)) = args.last_mut() {
                if *last == c {
                    *last_bits += 4;
                    continue;
                }
            }

            args.push((c, 4));
        }
    }
    let arg_bits = args.iter().map(|(_, bits)| bits).sum::<u16>();

    if opcode_bits == 0 {
        return Err(Error::custom("Opcode must have a non-empty fixed prefix")
            .with_span(&instr.code.span()));
    }

    let total_bits = opcode_bits + arg_bits;
    if total_bits as usize > MAX_OPCODE_BITS {
        return Err(Error::custom(format!(
            "Too much bits for the opcode: {opcode_bits}/{MAX_OPCODE_BITS}"
        ))
        .with_span(&instr.code.span()));
    }
    let n = (total_bits / 4) as usize;

    let opcode_base_max = (opcode_base_min | ((1 << arg_bits) - 1)) + 1;

    let remaining_bits = MAX_OPCODE_BITS - total_bits as usize;

    let mut range = OpcodeRange {
        span: instr.code.span(),
        aligned_opcode_min: opcode_base_min << remaining_bits,
        aligned_opcode_max: opcode_base_max << remaining_bits,
        total_bits,
    };

    let function_name = function.sig.ident.clone();
    let fmt = match instr.fmt {
        syn::Expr::Tuple(items) => items.elems.into_token_stream(),
        fmt => fmt.into_token_stream(),
    };

    let ty = match (!args.is_empty(), instr.range_from) {
        (false, None) => {
            opcodes.add_opcode(range)?;
            OpcodeTy::Simple {
                opcode: opcode_base_min,
                bits: opcode_bits,
            }
        }
        (false, Some(range_from)) => {
            return Err(Error::custom("Unexpected `range_from` for a simple opcode")
                .with_span(&range_from.span()))
        }
        (true, None) => {
            opcodes.add_opcode(range)?;
            OpcodeTy::Fixed {
                opcode: opcode_base_min >> arg_bits,
                opcode_bits,
                arg_bits,
            }
        }
        (true, Some(range_from)) => {
            let range_from_span = &range_from.span();

            let range_from_bits = range_from.len() * 4;
            let range_from = u32::from_str_radix(&range_from, 16).map_err(|e| {
                Error::custom(format!("Invalid `range_from` value: {e}")).with_span(range_from_span)
            })?;

            if range_from_bits != total_bits as usize {
                return Err(Error::custom(format!(
                    "Invalid `range_from` size in bits. Expected {total_bits}, got {range_from_bits}",
                )).with_span(range_from_span));
            }
            if range_from <= opcode_base_min {
                return Err(Error::custom(format!(
                    "`range_from` must be greater than opcode base. \
                    Opcode base: {:0n$x}, `range_from`: {range_from:0n$x}",
                    opcode_base_min >> arg_bits
                ))
                .with_span(range_from_span));
            }
            if range_from >= opcode_base_max {
                return Err(Error::custom(format!(
                    "`range_from` must be less than opcode max value. \
                    Opcode max value: {:0n$x}, `range_from`: {range_from:0n$x}",
                    opcode_base_max >> arg_bits
                ))
                .with_span(range_from_span));
            }

            range.aligned_opcode_min = range_from << remaining_bits;
            opcodes.add_opcode(range)?;

            OpcodeTy::FixedRange {
                opcode_min: range_from,
                opcode_max: opcode_base_max,
                total_bits,
                arg_bits,
            }
        }
    };

    let wrapper_func_name = quote::format_ident!("{function_name}_wrapper");
    let wrapper_func = match &ty {
        OpcodeTy::Simple { .. } => {
            if let Some(cond) = instr.cond {
                return Err(
                    Error::custom("Unexpected condition for simple opcode").with_span(&cond)
                );
            }

            quote! {
                fn #wrapper_func_name(st: &mut ::everscale_vm::state::VmState) -> ::anyhow::Result<i32> {
                    vm_log!("execute {}", format_args!(#fmt));
                    #function_name(st)
                }
            }
        }
        OpcodeTy::Fixed { .. } | OpcodeTy::FixedRange { .. } => {
            let mut shift = arg_bits as u32;

            let function_arg_count = function.sig.inputs.len().saturating_sub(1);

            let mut errors = Vec::new();
            let mut opcode_args = args.iter().peekable();
            let mut arg_definitions = Vec::with_capacity(function_arg_count);
            let mut arg_idents = Vec::with_capacity(function_arg_count);

            #[allow(clippy::never_loop)] // fixes clippy false-positive
            for function_arg in function.sig.inputs.iter().skip(1) {
                let name = 'function_arg: {
                    if let syn::FnArg::Typed(input) = function_arg {
                        if let syn::Pat::Ident(pat) = &*input.pat {
                            break 'function_arg pat.ident.to_string();
                        }
                    }
                    return Err(
                        Error::custom("Unsupported argument binding").with_span(&function_arg)
                    );
                };

                let explicit_arg = instr.args.remove(&name);

                match opcode_args.peek() {
                    Some((opcode_arg, bits)) => {
                        if opcode_arg.to_string() != name {
                            if let Some(expr) = explicit_arg {
                                let ident = quote::format_ident!("{name}");
                                arg_definitions.push(quote! { let #ident = #expr; });
                                arg_idents.push(ident);
                                continue;
                            }

                            return Err(Error::custom(format!("Expected argument `{opcode_arg}`"))
                                .with_span(&function_arg));
                        }

                        let ident = quote::format_ident!("{name}");

                        shift -= *bits as u32;
                        arg_definitions.push(match explicit_arg {
                            None => {
                                let mask = (1u32 << *bits) - 1;
                                quote! { let #ident = (args >> #shift) & #mask; }
                            }
                            Some(expr) => {
                                quote! { let #ident = #expr; }
                            }
                        });
                        arg_idents.push(ident);

                        opcode_args.next();
                    }
                    None => match explicit_arg {
                        Some(expr) => {
                            let ident = quote::format_ident!("{name}");
                            arg_definitions.push(quote! { let #ident = #expr; });
                            arg_idents.push(ident);
                        }
                        None => {
                            errors.push(
                                Error::custom("Unexpected argument").with_span(&function_arg),
                            );
                        }
                    },
                }
            }

            for (unused_arg, _) in opcode_args {
                errors.push(
                    Error::custom(format_args!("Unused opcode arg `{unused_arg}`"))
                        .with_span(&instr.code.span()),
                )
            }
            for (unused_arg, expr) in instr.args {
                errors.push(
                    Error::custom(format_args!("Unused arg override for {unused_arg}"))
                        .with_span(&expr),
                )
            }
            if !errors.is_empty() {
                return Err(Error::multiple(errors));
            }

            let cond = instr.cond.map(|cond| {
                quote! {
                    ::anyhow::ensure!(#cond, crate::error::VmError::InvalidOpcode);
                }
            });

            quote! {
                fn #wrapper_func_name(st: &mut ::everscale_vm::state::VmState, args: u32) -> ::anyhow::Result<i32> {
                    #(#arg_definitions)*
                    #cond
                    vm_log!("execute {}", format_args!(#fmt));
                    #function_name(st, #(#arg_idents),*)
                }
            }
        }
    };

    let expr_add = match ty {
        OpcodeTy::Simple { opcode, bits } => quote! {
            #opcodes_arg.add_simple(#opcode, #bits, #wrapper_func_name)
        },
        OpcodeTy::Fixed {
            opcode,
            opcode_bits,
            arg_bits,
        } => quote! {
            #opcodes_arg.add_fixed(#opcode, #opcode_bits, #arg_bits, #wrapper_func_name)
        },
        OpcodeTy::FixedRange {
            opcode_min,
            opcode_max,
            total_bits,
            arg_bits,
        } => quote! {
            #opcodes_arg.add_fixed_range(#opcode_min, #opcode_max, #total_bits, #arg_bits, #wrapper_func_name)
        },
    };

    Ok(syn::parse_quote! {{
        #wrapper_func
        #expr_add?;
    }})
}

enum OpcodeTy {
    Simple {
        opcode: u32,
        bits: u16,
    },
    Fixed {
        opcode: u32,
        opcode_bits: u16,
        arg_bits: u16,
    },
    FixedRange {
        opcode_min: u32,
        opcode_max: u32,
        total_bits: u16,
        arg_bits: u16,
    },
}

struct OpcodeRange {
    span: proc_macro2::Span,
    aligned_opcode_min: u32,
    aligned_opcode_max: u32,
    total_bits: u16,
}

#[derive(Default)]
struct Opcodes {
    opcodes: BTreeMap<u32, OpcodeRange>,
}

impl Opcodes {
    fn add_opcode(&mut self, range: OpcodeRange) -> Result<(), Error> {
        assert!(range.aligned_opcode_min < range.aligned_opcode_max);
        assert!(range.aligned_opcode_max <= MAX_OPCODE);

        if let Some((other_min, other)) = self.opcodes.range(range.aligned_opcode_min..).next() {
            if range.aligned_opcode_max > *other_min {
                let shift = MAX_OPCODE_BITS - other.total_bits as usize;
                let other_min = other.aligned_opcode_min >> shift;
                let other_max = other.aligned_opcode_max >> shift;
                let n = other.total_bits as usize / 4;

                return Err(Error::custom(format!(
                    "Opcode overlaps with the start of the range of another opcode: \
                    {other_min:0n$x}..{other_max:0n$x}"
                ))
                .with_span(&range.span));
            }
        }

        if let Some((k, prev)) = self.opcodes.range(..=range.aligned_opcode_min).next_back() {
            debug_assert!(prev.aligned_opcode_min < prev.aligned_opcode_max);
            debug_assert!(prev.aligned_opcode_min == *k);
            if range.aligned_opcode_min < prev.aligned_opcode_max {
                let shift = MAX_OPCODE_BITS - prev.total_bits as usize;
                let prev_min = prev.aligned_opcode_min >> shift;
                let prev_max = prev.aligned_opcode_max >> shift;
                let n = prev.total_bits as usize / 4;

                return Err(Error::custom(format!(
                    "Opcode overlaps with the end of the range of another opcode: \
                    {prev_min:0n$x}..{prev_max:0n$x}"
                ))
                .with_span(&range.span));
            }
        }

        self.opcodes.insert(range.aligned_opcode_min, range);
        Ok(())
    }
}

const MAX_OPCODE_BITS: usize = 24;
const MAX_OPCODE: u32 = 1 << MAX_OPCODE_BITS;
