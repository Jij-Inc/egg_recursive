use itertools::{multiunzip, Itertools};
use parse::ParseStream;
use proc_macro2::TokenStream;
use proc_macro2::*;
use quote::{quote, ToTokens};
use syn::spanned::Spanned;
use syn::*;
use token::Bracket;

use crate::macros::parse_macro_input2;

pub fn derive(input: TokenStream) -> TokenStream {
    let data = parse_macro_input2!(input as DeriveInput);
    let info = match ChildrenDeriver::try_new(data) {
        Ok(info) => info,
        Err(e) => return e.to_compile_error(),
    };
    info.derive()
}

#[derive(Debug, Clone)]
struct ChildrenDeriver {
    /// Struct visibility
    vis: Visibility,
    /// Original struct name
    orig_name: Ident,
    /// The name of the generated wrapper (array-rep) struct name
    wrapper_name: Ident,
    /// Functor impl tag for original type
    orig_impl_name: Ident,
    /// Functor impl tag for wrapper type
    wrapper_impl_name: Ident,
    fields: ChildrenFields,
    size_spec: ChildrenSize,
}

impl ChildrenDeriver {
    fn derive(self) -> TokenStream {
        let mut stream = TokenStream::default();
        stream.extend(self.to_orig_impl_tag());
        stream.extend(self.to_orig_functor());
        stream.extend(self.to_wrapper_type());
        stream.extend(self.to_wrapper_impl_tag());
        stream.extend(self.to_wrapper_functor());
        stream.extend(self.to_into_lang_children());
        stream
    }

    fn try_new(data: DeriveInput) -> Result<Self> {
        let vis = data.vis.clone();
        let orig_name = data.ident.clone();
        let orig_impl_name = Ident::new(&format!("{}Impl", orig_name), Span::mixed_site());
        let wrapper_name = Ident::new(&format!("Raw{}", data.ident), Span::mixed_site());
        let wrapper_impl_name = Ident::new(&format!("Raw{}Impl", data.ident), Span::mixed_site());
        if data.generics.params.len() != 1 {
            return Err(Error::new_spanned(
                data.generics,
                "expected exactly one generic parameter",
            ));
        }
        let Some(GenericParam::Type(para)) = data.generics.params.first() else {
            return Err(Error::new_spanned(data.generics, "expected type parameter"));
        };
        let param = &para.ident;

        let Data::Struct(strct) = data.data else {
            return Err(Error::new_spanned(data, "expected struct"));
        };

        let fields = match strct.fields {
            Fields::Unit => Ok(ChildrenFields::Unit),
            Fields::Unnamed(fs) => {
                ChildrenFieldsUnnamed::try_from_field(param, fs).map(ChildrenFields::Unnamed)
            }
            Fields::Named(fs) => {
                ChildrenFieldsNamed::try_from_field(param, fs).map(ChildrenFields::Named)
            }
        }?;
        let size_spec = ChildrenSize::try_new(fields.iter_children())?;
        Ok(Self {
            vis,
            orig_name,
            wrapper_name,
            orig_impl_name,
            wrapper_impl_name,
            fields,
            size_spec,
        })
    }

    fn to_orig_impl_tag(&self) -> TokenStream {
        let ChildrenDeriver {
            vis,
            orig_impl_name,
            orig_name,
            ..
        } = self;
        let impl_comment = format!(
            "The implementation tag of [`Functor`] for [`{}`]. Generated via `#[derive(LanguageChildren)]`",
            orig_name
        );
        quote! {
            #[doc=#impl_comment]
            #vis enum #orig_impl_name{}
        }
    }

    fn to_wrapper_impl_tag(&self) -> TokenStream {
        let ChildrenDeriver {
            vis,
            wrapper_impl_name,
            wrapper_name,
            ..
        } = self;
        let raw_impl_comment = format!(
            "The implementation tag of [`Functor`] for [`{}`]. Generated via `#[derive(LanguageChildren)]`",
            wrapper_name
        );
        quote! {
            #[doc=#raw_impl_comment]
            #vis enum #wrapper_impl_name{}
        }
    }

    fn to_orig_functor(&self) -> TokenStream {
        let orig: &Ident = &self.orig_name;
        let orig_impl: &Ident = &self.orig_impl_name;
        let (destr, assignments, constr): (Vec<_>, Vec<_>, Vec<_>) =
            multiunzip(self.fields.iter_fields().enumerate().map(|(i, (fld, ty))| {
                let (fld, destr_constr) = if let Some(fld) = fld {
                    (quote! {#fld}, quote! {#fld})
                } else {
                    let i = Index::from(i);
                    let fld = Ident::new(&format!("fld_{}", quote! {#i}), ty.span());
                    (quote! { #fld }, quote! { #i: #fld })
                };
                let assign = match ty {
                    Child::Raw(_) => quote! { let #fld = f(#fld); },
                    Child::Vec(_) => quote! { let #fld = #fld.into_iter().map(&mut f).collect(); },
                    Child::NAry(_) => quote! { let #fld = #fld.map(&mut f); },
                };
                (destr_constr.clone(), assign, destr_constr)
            }));
        quote! {
            impl<T> #orig<T> {
                pub fn map<U, F>(self, mut f: F) -> #orig<U>
                where
                    F: FnMut(T) -> U
                {
                    let Self { #(#destr),* } = self;
                    #(#assignments)*
                    #orig { #(#constr),* }
                }
            }

            impl ::egg_recursive::Functor for #orig_impl {
                type Container<T> = #orig<T>;
                fn fmap<A, B, F>(mut f: F, x: Self::Container<A>) -> Self::Container<B>
                where
                    F: FnMut(A) -> B
                {
                    x.map(f)
                }
            }
        }
    }

    fn to_wrapper_functor(&self) -> TokenStream {
        let wrapper: &Ident = &self.wrapper_name;
        let wrapper_impl: &Ident = &self.wrapper_impl_name;
        let mapper = match &self.size_spec {
            ChildrenSize::Fixed(_) => quote! { #wrapper(self.0.map(f)) },
            ChildrenSize::Variadic(_) => quote! { #wrapper(self.0.into_iter().map(f).collect()) },
        };
        quote! {
            impl<T> #wrapper<T> {
                pub fn map<U, F>(self, mut f: F) -> #wrapper<U>
                where
                    F: FnMut(T) -> U
                {
                    #mapper
                }
            }

            impl ::egg_recursive::Functor for #wrapper_impl {
                type Container<T> = #wrapper<T>;
                fn fmap<A, B, F>(mut f: F, x: Self::Container<A>) -> Self::Container<B>
                where
                    F: FnMut(A) -> B
                {
                    x.map(f)
                }
            }
        }
    }

    fn to_wrapper_type(&self) -> TokenStream {
        use ChildrenSize::*;
        let vis: &Visibility = &self.vis;
        let orig_name: &Ident = &self.orig_name;
        let name: &Ident = &self.wrapper_name;
        let comment = format!("An array-like representation of [`{}`], which is used with egg functions. Generated via `#[derive(LanguageChildren)]`", orig_name);
        match &self.size_spec {
            Fixed(n) => quote! {
                #[doc=#comment]
                #[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Hash, Clone, Debug)]
                #vis struct #name<T>(#vis [T; #n]);

                impl ::egg::LanguageChildren for #name<::egg::Id> {
                    fn len(&self) -> usize {
                        self.0.len()
                    }

                    fn can_be_length(n: usize) -> bool {
                        n == #n
                    }

                    fn from_vec(v: ::std::vec::Vec<::egg::Id>) -> Self {
                        Self(<[::egg::Id; #n]>::try_from(v.as_slice()).unwrap())
                    }

                    fn as_slice(&self) -> &[::egg::Id] {
                        self.0.as_slice()
                    }

                    fn as_mut_slice(&mut self) -> &mut [::egg::Id] {
                        self.0.as_mut_slice()
                    }
                }
            },
            Variadic(VariadicSize {
                prefix_size,
                suffix_size,
            }) => {
                let n = prefix_size + suffix_size;
                quote! {
                    #[doc=#comment]
                    #[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
                    #vis struct #name<T>(#vis ::std::vec::Vec<T>);
                    impl ::egg::LanguageChildren for #name<::egg::Id> {
                        fn len(&self) -> usize {
                            self.0.len()
                        }

                        fn can_be_length(n: usize) -> bool {
                            n >= #n
                        }

                        fn from_vec(v: Vec<::egg::Id>) -> Self {
                            Self(v)
                        }

                        fn as_slice(&self) -> &[::egg::Id] {
                            self.0.as_slice()
                        }

                        fn as_mut_slice(&mut self) -> &mut [::egg::Id] {
                            self.0.as_mut_slice()
                        }
                    }
                }
            }
        }
    }

    fn to_into_lang_children(&self) -> TokenStream {
        let spec = &self.size_spec;
        let orig: &Ident = &self.orig_name;
        let orig_impl: &Ident = &self.orig_impl_name;
        let wrapper: &Ident = &self.wrapper_name;
        let wrapper_impl: &Ident = &self.wrapper_impl_name;
        let fields: &ChildrenFields = &self.fields;
        use ChildrenSize::*;
        let (body_size, def_len) = match spec {
            Variadic(vd) => (
                vd.prefix_size + vd.suffix_size,
                quote! { let len = wrapper.0.len(); },
            ),
            Fixed(n) => (*n, quote! {}),
        };
        let packer = fields
            .iter_fields()
            .enumerate()
            .map(|(i, (fld, ty))| {
                let field = if let Some(fld) = fld {
                    quote! {orig.#fld}
                } else {
                    let i = Index::from(i);
                    quote! {orig.#i}
                };
                match ty {
                    Child::Vec(_) => quote! {vec.extend(#field);},
                    Child::Raw(_) => quote! {vec.push(#field);},
                    Child::NAry(_) => quote! {vec.extend(#field);},
                }
            })
            .collect::<Vec<_>>();

        let unpacker = fields.iter_fields().enumerate().map(|(i, (fld, ty))| {
                let fld = if let Some(fld) = fld {
                    quote! {#fld}
                } else {
                    let i = Index::from(i);
                    quote! {#i}
                };
                match ty {
                    Child::Vec(_) => {
                        quote! { #fld: iter.by_ref().take(len - #body_size).collect() }
                    }
                    Child::Raw(_) => {
                        quote! {#fld: iter.next().unwrap()}
                    }
                    Child::NAry(nary) => {
                        let size = nary.len.base10_parse::<usize>().unwrap();
                        quote! {#fld: iter.by_ref().take(#size).collect::<Vec<_>>().try_into().map_err(|_| "impossible").unwrap()}
                    }
                }
            });

        let mut toks = quote! {
            impl<T> ::std::convert::From<#orig<T>> for #wrapper<T> {
                fn from(orig: #orig<T>) -> Self {
                    let mut vec = Vec::new();
                    #(#packer)*
                    Self(vec.try_into().map_err(|_| "impossible").unwrap())
                }
            }

            impl<T> ::std::convert::From<#wrapper<T>> for #orig<T> {
                fn from(wrapper: #wrapper<T>) -> Self {
                    #def_len
                    let mut iter = wrapper.0.into_iter();
                    Self {
                        #(#unpacker),*
                    }
                }
            }
        };
        let raw_as_refs_body = match spec {
            ChildrenSize::Variadic(_) => quote! { input.iter().collect() },
            ChildrenSize::Fixed(_) => quote! { input.each_ref() },
        };

        toks.extend(quote! {
            impl<T> ::egg_recursive::IntoLanguageChildren for #orig<T> {
                type View = #orig_impl;
                type RawData = #wrapper_impl;
                type Param = T;

                fn unview<U>(input: #orig<U>) -> #wrapper<U> {
                    input.into()
                }

                fn view<U>(wrapper: #wrapper<U>) -> #orig<U> {
                    wrapper.into()
                }

                fn raw_as_refs<'a, U>(input: &'a #wrapper<U>) -> #wrapper<&'a U> {
                    let #wrapper(input) = input;
                    let input = #raw_as_refs_body;
                    #wrapper(input)
                }
            }

            impl<T> #wrapper<T> {
                pub fn view(self) -> #orig<T> {
                    self.into()
                }
            }

            impl<T> #orig<T> {
                pub fn unview(self) -> #wrapper<T> {
                    self.into()
                }
            }
        });
        toks
    }
}

#[derive(Default, Clone, Debug)]
struct ChildrenFieldsNamed(Vec<(Ident, Child)>);

impl ChildrenFieldsNamed {
    fn try_from_field(para: &Ident, fields: FieldsNamed) -> Result<Self> {
        Ok(Self(
            fields
                .named
                .into_iter()
                .map(|fld| {
                    let stream = fld.ty.to_token_stream();
                    let child = parse::Parser::parse2(
                        |a: ParseStream| Child::parse_with_ident(para, a),
                        stream,
                    )?;
                    Ok::<_, Error>((fld.ident.unwrap(), child))
                })
                .try_collect()?,
        ))
    }
}

#[derive(Default, Debug, Clone)]
struct ChildrenFieldsUnnamed(Vec<Child>);

#[derive(Debug, Clone)]
enum ChildrenSize {
    Fixed(usize),
    Variadic(VariadicSize),
}

#[derive(Debug, Clone)]
struct VariadicSize {
    prefix_size: usize,
    suffix_size: usize,
}

impl ChildrenSize {
    fn try_new<'a, I: IntoIterator<Item = &'a Child>>(chs: I) -> Result<Self> {
        use Child::*;
        use ChildrenSize::*;
        chs.into_iter().try_fold(Fixed(0), |acc, ch| match ch {
            Raw(_) => match acc {
                Fixed(u) => Ok(Fixed(u + 1)),
                Variadic(v) => Ok(Variadic(VariadicSize {
                    suffix_size: v.suffix_size + 1,
                    ..v
                })),
            },
            Vec(_) => match acc {
                Fixed(u) => Ok(Variadic(VariadicSize {
                    prefix_size: u,
                    suffix_size: 0,
                })),
                Variadic(_) => Err(Error::new_spanned(ch, "more than two variadic vec appears")),
            },
            NAry(nary) => {
                let size = nary.len.base10_parse::<usize>()?;
                match acc {
                    Fixed(u) => Ok(Fixed(u + size)),
                    Variadic(v) => Ok(Variadic(VariadicSize {
                        suffix_size: v.suffix_size + size,
                        ..v
                    })),
                }
            }
        })
    }
}

impl ChildrenFieldsUnnamed {
    fn try_from_field(para: &Ident, fields: FieldsUnnamed) -> Result<Self> {
        Ok(Self(
            fields
                .unnamed
                .into_iter()
                .map(|fld| {
                    let stream = fld.ty.to_token_stream();
                    parse::Parser::parse2(|a: ParseStream| Child::parse_with_ident(para, a), stream)
                })
                .try_collect()?,
        ))
    }
}

#[derive(Debug, Clone)]
enum ChildrenFields {
    Named(ChildrenFieldsNamed),
    Unnamed(ChildrenFieldsUnnamed),
    Unit,
}

impl ChildrenFields {
    fn iter_children(&self) -> impl Iterator<Item = &Child> {
        let boxed: Box<dyn Iterator<Item = &Child>> = match self {
            ChildrenFields::Named(named) => Box::new(named.0.iter().map(|(_, ch)| ch)),
            ChildrenFields::Unnamed(unnamed) => Box::new(unnamed.0.iter()),
            ChildrenFields::Unit => Box::new(std::iter::empty()),
        };
        boxed
    }

    fn iter_fields(&self) -> impl Iterator<Item = (Option<&Ident>, &Child)> {
        let iter: Box<dyn Iterator<Item = (Option<&Ident>, &Child)>> = match self {
            ChildrenFields::Named(named) => Box::new(named.0.iter().map(|(id, ch)| (Some(id), ch))),
            ChildrenFields::Unnamed(unnamed) => {
                Box::new(unnamed.0.iter().map(move |ch| (None, ch)))
            }
            ChildrenFields::Unit => Box::new(std::iter::empty()),
        };
        iter
    }
}

trait ParseWithIdent: Sized {
    fn parse_with_ident(ident: &Ident, input: ParseStream) -> Result<Self>;
}

#[derive(Debug, Clone)]
enum Child {
    Raw(RawChild),
    Vec(VecChild),
    NAry(NAryChild),
}

impl ParseWithIdent for Child {
    fn parse_with_ident(ident: &Ident, input: ParseStream) -> Result<Self> {
        if let Ok(nary) = NAryChild::parse_with_ident(ident, input) {
            Ok(Child::NAry(nary))
        } else if let Ok(vec) = VecChild::parse_with_ident(ident, input) {
            Ok(Child::Vec(vec))
        } else if let Ok(ch) = RawChild::parse_with_ident(ident, input) {
            Ok(Child::Raw(ch))
        } else {
            Err(Error::new_spanned(
                input.cursor().token_stream(),
                format!("expected {}, Vec<{}>, or [{}; N]", ident, ident, ident),
            ))
        }
    }
}

impl ToTokens for Child {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Child::Raw(raw) => raw.to_tokens(tokens),
            Child::Vec(vec) => vec.to_tokens(tokens),
            Child::NAry(nary) => nary.to_tokens(tokens),
        }
    }
}

#[derive(Debug, Clone)]
struct RawChild {
    ident: Ident,
}

impl ParseWithIdent for RawChild {
    fn parse_with_ident(ident: &Ident, input: ParseStream) -> Result<Self> {
        let other = input.parse::<Ident>()?;
        if &other == ident {
            Ok(RawChild { ident: other })
        } else {
            Err(Error::new_spanned(
                other,
                format!("expected type {}", ident),
            ))
        }
    }
}

impl ToTokens for RawChild {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.ident.to_tokens(tokens);
    }
}

#[derive(Debug, Clone)]
struct VecChild {
    vec_token: Ident,
    lt_token: Token![<],
    ident: Ident,
    gt_token: Token![>],
}

mod keywords {
    syn::custom_keyword!(Vec);
}

impl ParseWithIdent for VecChild {
    fn parse_with_ident(ident: &Ident, input: ParseStream) -> Result<Self> {
        if !input.peek(keywords::Vec) {
            let span = input.cursor().span();
            return Err(Error::new(span, "expected (unqualified) Vec"));
        }
        let vec_token = input.parse::<Ident>()?;
        let lt_token = input.parse::<Token![<]>()?;
        let other = input.parse::<Ident>()?;
        let gt_token = input.parse::<Token![>]>()?;
        if &other == ident {
            Ok(VecChild {
                vec_token,
                lt_token,
                ident: other,
                gt_token,
            })
        } else {
            Err(Error::new_spanned(
                other,
                format!("expected type {}", ident),
            ))
        }
    }
}

impl ToTokens for VecChild {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.vec_token.to_tokens(tokens);
        self.lt_token.to_tokens(tokens);
        self.ident.to_tokens(tokens);
        self.gt_token.to_tokens(tokens);
    }
}

#[derive(Debug, Clone)]
struct NAryChild {
    bracket_token: Bracket,
    ident: Ident,
    semi_token: Token![;],
    len: LitInt,
}

impl ParseWithIdent for NAryChild {
    fn parse_with_ident(ident: &Ident, input: ParseStream) -> Result<Self> {
        let content;
        let bracket_token = bracketed!(content in input);
        let other = content.parse::<Ident>()?;
        let semi_token = content.parse::<Token![;]>()?;
        let len = content.parse::<LitInt>()?;
        if &other == ident {
            Ok(NAryChild {
                bracket_token,
                ident: other,
                semi_token,
                len,
            })
        } else {
            Err(Error::new_spanned(
                other,
                format!("expected type {}", ident),
            ))
        }
    }
}

impl ToTokens for NAryChild {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.bracket_token.surround(tokens, |tokens| {
            self.ident.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
            self.len.to_tokens(tokens);
        });
    }
}

#[cfg(test)]
mod tests;
