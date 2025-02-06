use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::*;

pub fn pretty<T: ToTokens>(input: T) -> String {
    prettyplease::unparse(&parse_file(&input.to_token_stream().to_string()).unwrap())
}

pub trait Pretty {
    fn pretty(&self) -> String;
}

impl Pretty for TokenStream {
    fn pretty(&self) -> String {
        pretty(self)
    }
}

impl<T: ToTokens> Pretty for Result<T> {
    fn pretty(&self) -> String {
        match self {
            Ok(t) => pretty(t),
            Err(e) => e.to_compile_error().pretty(),
        }
    }
}

macro_rules! apply_macro {
    ($fun:expr; $($e:tt)*) => {{
        $crate::test_utils::Pretty::pretty(&$fun(::quote::quote! {$($e)*}))
    }};
}

pub(crate) use apply_macro;
