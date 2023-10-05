use std::collections::HashMap;

use darling::util::parse_expr;
use darling::{Error, FromMeta};
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::ItemImpl;

#[derive(Debug, FromMeta)]
struct VmInstrArgs {
    code: String,
    #[darling(default)]
    range_from: Option<String>,

    #[darling(with = "parse_expr::preserve_str_literal")]
    fmt: syn::Expr,

    #[darling(default)]
    args: Option<HashMap<String, syn::Expr>>,
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
                match process_instr_definition(&fun, &opcodes_arg, &attr) {
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
                #(#definitions?;)*
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
) -> Result<syn::Expr, Error> {
    let mut instr = VmInstrArgs::from_meta(&attr.meta)?;

    let mut opcode_bits = 0u16;
    let mut opcode_base_min = 0;
    let mut args = Vec::<(char, u16)>::new();
    for c in instr.code.chars() {
        if !c.is_ascii_alphanumeric() {
            return Err(Error::custom(format!(
                "Invalid pattern for the opcode `{}`",
                instr.code
            )));
        }

        opcode_base_min <<= 4;

        if let Some(c) = c.to_digit(16) {
            if !args.is_empty() {
                return Err(Error::custom(format!(
                    "Invalid pattern for the opcode `{}`",
                    instr.code
                )));
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
        return Err(Error::custom(format!(
            "Opcode `{}` must have a non-empty fixed prefix",
            instr.code
        )));
    }

    let total_bits = opcode_bits + arg_bits;
    if total_bits as usize > MAX_OPCODE_BITS {
        return Err(Error::custom(format!(
            "Too much bits for the opcode `{}`: {opcode_bits}",
            instr.code
        )));
    }
    let n = (total_bits / 4) as usize;

    let opcode_base_max = (opcode_base_min | ((1 << arg_bits) - 1)) + 1;

    let function_name = function.sig.ident.clone();
    let fmt = match instr.fmt {
        syn::Expr::Tuple(items) => items.elems.into_token_stream(),
        fmt => fmt.into_token_stream(),
    };

    let ty = match (!args.is_empty(), instr.range_from) {
        (false, None) => OpcodeTy::Simple {
            opcode: opcode_base_min,
            bits: opcode_bits,
        },
        (false, Some(_)) => {
            return Err(Error::custom(format!(
                "Unexpected `range_from` for a simple opcode `{}`",
                instr.code
            )))
        }
        (true, None) => OpcodeTy::Fixed {
            opcode: opcode_base_min >> opcode_bits,
            opcode_bits,
            arg_bits,
        },
        (true, Some(range_from)) => {
            let range_from_bits = range_from.len() * 4;
            let range_from = u32::from_str_radix(&range_from, 16)
                .map_err(|e| Error::custom(format!("Invalid `range_from` value: {e}")))?;

            if range_from_bits != total_bits as usize {
                return Err(Error::custom(format!(
                    "Invalid `range_from` size in bits. Expected {total_bits}, got {range_from_bits}",
                )));
            }
            if range_from <= opcode_base_min {
                return Err(Error::custom(format!(
                    "`range_from` must be greater than opcode base. \
                    Opcode base: {:0n$x}, `range_from`: {range_from:0n$x}",
                    opcode_base_min >> arg_bits
                )));
            }
            if range_from >= opcode_base_max {
                return Err(Error::custom(format!(
                    "`range_from` must be less than opcode max value. \
                    Opcode max value: {:0n$x}, `range_from`: {range_from:0n$x}",
                    opcode_base_max >> arg_bits
                )));
            }

            OpcodeTy::FixedRange {
                opcode_min: range_from >> arg_bits,
                opcode_max: opcode_base_max >> arg_bits,
                total_bits,
                arg_bits,
            }
        }
    };

    let wrapper_func_name = quote::format_ident!("{function_name}_wrapper");
    let wrapper_func = match &ty {
        OpcodeTy::Simple { .. } => {
            if instr.cond.is_some() {
                return Err(Error::custom("Unexpected condition for simple opcode"));
            }

            quote! {
                fn #wrapper_func_name(st: &mut ::everscale_vm::state::VmState) -> ::anyhow::Result<i32> {
                    vm_log!("execute {}", format_args!(#fmt));
                    #function_name(st)
                }
            }
        }
        OpcodeTy::Fixed { .. } | OpcodeTy::FixedRange { .. } => {
            let mut arg_overrides = instr.args.take().unwrap_or_default();

            let mut shift = arg_bits as u32;
            let arg_definitions = args
                .iter()
                .map(|(name, bits)| {
                    let ident = quote::format_ident!("{name}");

                    shift -= *bits as u32;
                    match arg_overrides.remove(&name.to_string()) {
                        None => {
                            let mask = (1u32 << *bits) - 1;
                            quote! { let #ident = (args >> #shift) & #mask; }
                        }
                        Some(expr) => {
                            quote! { let #ident = #expr; }
                        }
                    }
                })
                .collect::<Vec<_>>();

            let mut errors = Vec::new();
            for unused_arg in arg_overrides.into_keys() {
                errors.push(Error::custom(format_args!(
                    "Unused arg override for {unused_arg}"
                )))
            }
            if !errors.is_empty() {
                return Err(Error::multiple(errors));
            }

            let args = args.iter().map(|(name, _)| quote::format_ident!("{name}"));

            quote! {
                fn #wrapper_func_name(st: &mut ::everscale_vm::state::VmState, args: u32) -> ::anyhow::Result<i32> {
                    #(#arg_definitions)*
                    vm_log!("execute {}", format_args!(#fmt));
                    #function_name(st, #(#args),*)
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
        #expr_add
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

const MAX_OPCODE_BITS: usize = 24;
