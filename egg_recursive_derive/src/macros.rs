/// Similar to [`syn::parse_macro_input!`], treats [`proc_macro2::TokenStream`] instead.
macro_rules! parse_macro_input2 {
    ($tokenstream:ident as $ty:ty) => {
        match syn::parse2::<$ty>($tokenstream) {
            ::std::result::Result::Ok(data) => data,
            ::std::result::Result::Err(err) => {
                return ::proc_macro2::TokenStream::from(err.to_compile_error());
            }
        }
    };
    ($tokenstream:ident with $parser:path) => {
        match $crate::parse::Parser::parse2($parser, $tokenstream) {
            ::std::result::Result::Ok(data) => data,
            ::std::result::Result::Err(err) => {
                return ::proc_macro2::TokenStream::from(err.to_compile_error());
            }
        }
    };
    ($tokenstream:ident) => {
        $crate::parse_macro_input!($tokenstream as _)
    };
}

pub(crate) use parse_macro_input2;
