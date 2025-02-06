use crate::macros::parse_macro_input2;
use itertools::Itertools;
use parse::Parser;
use proc_macro2::*;
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::parse::Parse;
use syn::spanned::Spanned;
use syn::*;
use token::Bracket;
use visit::Visit;

pub fn derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input2!(input as DeriveInput);
    let info = match LangDeriver::try_new(input) {
        Ok(info) => info,
        Err(err) => return err.to_compile_error(),
    };
    info.derive()
}

struct LangDeriver {
    vis: Visibility,
    orig_name: Ident,
    sig_name: Ident,
    egg_synonym: Ident,
    pat_synonym: Ident,
    cons_trait_name: Ident,
    raw_pat_name: TokenStream,
    variants: Vec<LangVariant>,
}

impl LangDeriver {
    fn try_new(input: DeriveInput) -> Result<Self> {
        let vis = input.vis.clone();
        if !input.generics.params.is_empty() {
            return Err(Error::new_spanned(
                input.generics,
                "generics are not supported",
            ));
        }
        let orig_name = input.ident.clone();
        let sig_name = Ident::new(&format!("{}Sig", orig_name), orig_name.span());
        let cons_trait_name = Ident::new(&format!("{}Cons", orig_name), orig_name.span());
        let egg_synonym = Ident::new(&format!("Egg{}", orig_name), Span::mixed_site());
        let pat_synonym = Ident::new(&format!("{}Pat", orig_name), Span::mixed_site());
        let Data::Enum(enm) = input.data else {
            return Err(Error::new_spanned(input, "expected enum"));
        };
        let raw_pat_name = quote! { ::egg_recursive::Pat::<#orig_name>  };
        let variants = enm
            .variants
            .into_iter()
            .map(LangVariant::try_from)
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            vis,
            orig_name,
            sig_name,
            egg_synonym,
            pat_synonym,
            raw_pat_name,
            cons_trait_name,
            variants,
        })
    }

    fn derive(self) -> TokenStream {
        let mut stream = TokenStream::default();

        // Signature type and its synonym
        stream.extend(self.to_signature_type());
        stream.extend(self.to_egg_synonym());

        // Pattern synonym, their conversion, and `Searcher` impls
        stream.extend(self.to_pat_syn_and_methods());
        stream.extend(self.to_pat_syn_converters());
        stream.extend(self.to_pat_syn_egg_impls());

        // Functor instances
        stream.extend(self.to_functor_impl());

        // Egg Language trait impl for the signature<Id>
        stream.extend(self.to_language_trait_impl());

        // Recursive impl
        stream.extend(self.to_recursive_impl());

        // Conversion b/w RecExpr
        stream.extend(self.to_expr_converters());

        // Smart constructors
        stream.extend(self.to_smart_cons_trait());
        stream.extend(self.to_smart_cons_impl_orig());
        stream.extend(self.to_smart_cons_impl_raw_pat());
        stream.extend(self.to_smart_cons_impl_newtype_pat());
        stream
    }

    fn to_signature_type(&self) -> TokenStream {
        let lang_vis = &self.vis;
        let sig_name = &self.sig_name;
        let orig_name = &self.orig_name;
        let param = Ident::new("T", Span::mixed_site());
        let sig_vars = self
            .variants
            .iter()
            .map(|v| v.to_signature_variant_without_comma(&param));
        let comment = format!(
            "The signature type corresponding to [`{}`]. Generated via `#[derive(Language)]`",
            orig_name
        );
        quote! {
            #[doc=#comment]
            #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
            #lang_vis enum #sig_name<#param> {
                #(#sig_vars),*
            }
        }
    }

    fn to_language_trait_impl(&self) -> TokenStream {
        let sig_name = &self.sig_name;
        let match_arms = self
            .variants
            .iter()
            .map(|v| v.to_lang_match_arm_without_comma());
        let children_arms = self
            .variants
            .iter()
            .map(|v| v.to_lang_children_arm_without_comma());
        let children_mut_arms = self
            .variants
            .iter()
            .map(|v| v.to_lang_children_mut_arm_without_comma());

        quote! {
            impl ::egg::Language for #sig_name<::egg::Id> {
                type Discriminant = ::std::mem::Discriminant<Self>;

                #[inline(always)]
                fn discriminant(&self) -> Self::Discriminant {
                    ::std::mem::discriminant(self)
                }

                #[inline(always)]
                fn matches(&self, other: &Self) -> bool {
                    ::std::mem::discriminant(self) == ::std::mem::discriminant(other) &&
                    match (self, other) {
                        #(#match_arms),*,
                        _ => false
                    }
                }

                fn children(&self) -> &[::egg::Id] {
                    match self {
                        #(#children_arms),*
                    }
                }

                fn children_mut(&mut self) -> &mut [::egg::Id] {
                    match self {
                        #(#children_mut_arms),*
                    }
                }
            }
        }
    }

    fn to_egg_synonym(&self) -> TokenStream {
        let Self {
            egg_synonym,
            sig_name,
            vis,
            orig_name,
            ..
        } = self;

        let egg_syn_comment = format!(
            "The egg counterpart of [`{}`]. Generated via `#[derive(Language)]`",
            orig_name
        );
        quote! {
            #[doc=#egg_syn_comment]
            #vis type #egg_synonym = #sig_name<::egg::Id>;
        }
    }

    /// Pattern synonym and its builtin method (without trait)
    fn to_pat_syn_and_methods(&self) -> TokenStream {
        let Self {
            pat_synonym,
            orig_name,
            raw_pat_name,
            vis,
            ..
        } = self;
        let pat_syn_comment = format!(
            "The pattern for [`{}`]. Generated via `#[derive(Language)]`",
            orig_name
        );
        quote! {
            #[doc=#pat_syn_comment]
            #[derive(Clone)]
            #vis struct #pat_synonym(#vis #raw_pat_name);
            impl #pat_synonym {
                /// Creates pattern variable. This DOESN'T expect to be prefixed with `?`, contrary to the egg's convention.
                pub fn pat_var<'a, S: Into<::std::borrow::Cow<'a, str>>>(v: S) -> Self {
                    Self(::egg_recursive::Pat::pat_var(v))
                }
            }
        }
    }

    fn to_pat_syn_converters(&self) -> TokenStream {
        let Self {
            pat_synonym,
            egg_synonym,
            orig_name,
            raw_pat_name,
            ..
        } = self;
        quote! {
            impl From<#pat_synonym> for #raw_pat_name {
                fn from(value: #pat_synonym) -> Self {
                    value.0
                }
            }
            impl From<#raw_pat_name> for #pat_synonym {
                fn from(value: #raw_pat_name) -> Self {
                    Self(value)
                }
            }
            impl From<#orig_name> for #pat_synonym {
                fn from(value: #orig_name) -> Self {
                    #pat_synonym(#raw_pat_name::from(value))
                }
            }
            impl From<#pat_synonym> for ::egg::Pattern<#egg_synonym> {
                fn from(value: #pat_synonym) -> Self {
                    value.0.into()
                }
            }
            impl From<#pat_synonym> for ::egg::PatternAst<#egg_synonym> {
                fn from(value: #pat_synonym) -> Self {
                    value.0.into()
                }
            }
        }
    }

    fn to_pat_syn_egg_impls(&self) -> TokenStream {
        let Self {
            pat_synonym,
            egg_synonym,
            ..
        } = self;
        quote! {
            impl<N: ::egg::Analysis<#egg_synonym>> ::egg::Searcher<#egg_synonym, N> for #pat_synonym {
                fn search_eclass_with_limit(
                    &self,
                    egraph: &::egg::EGraph<#egg_synonym, N>,
                    eclass: ::egg::Id,
                    limit: usize,
                ) -> Option<::egg::SearchMatches<#egg_synonym>> {
                    ::egg::Searcher::<#egg_synonym, N>::search_eclass_with_limit(&self.0, egraph, eclass, limit)
                }

                fn vars(&self) -> Vec<::egg::Var> {
                    ::egg::Searcher::<#egg_synonym, N>::vars(&self.0)
                }
            }
            impl<N: ::egg::Analysis<#egg_synonym>> ::egg::Applier<#egg_synonym, N> for #pat_synonym {
                fn apply_one(
                    &self,
                    egraph: &mut ::egg::EGraph<#egg_synonym, N>,
                    eclass: ::egg::Id,
                    subst: &::egg::Subst,
                    searcher_ast: Option<&::egg::PatternAst<#egg_synonym>>,
                    rule_name: ::egg::Symbol,
                ) -> Vec<::egg::Id> {
                    ::egg::Applier::<#egg_synonym, N>::apply_one(&self.0, egraph, eclass, subst, searcher_ast, rule_name)
                }
            }
        }
    }

    fn to_functor_impl(&self) -> TokenStream {
        let Self {
            orig_name,
            sig_name,
            variants,
            ..
        } = self;
        let f = Ident::new("f", Span::mixed_site());
        let map_arms = variants.iter().map(|v| v.to_map_arm_without_comma(&f));
        quote! {
            impl ::egg_recursive::Functor for #orig_name {
                type Container<T> = #sig_name<T>;

                fn fmap<A, B, F>(mut #f: F, x: Self::Container<A>) -> Self::Container<B>
                where
                    F: FnMut(A) -> B
                {
                    match x {
                        #(#map_arms),*
                    }
                }
            }
        }
    }

    fn to_recursive_impl(&self) -> TokenStream {
        let Self { orig_name, .. } = self;

        let wrap_def = self.to_recursive_impl_wrap();
        let unwrap_def = self.to_recursive_impl_unwrap();
        let sclone_def = self.to_recursive_impl_sclone();
        let sig_each_ref_def = self.to_recursive_impl_sig_each_ref();

        quote! {
            impl ::egg_recursive::Recursive for #orig_name {
                #wrap_def
                #unwrap_def
                #sclone_def
                #sig_each_ref_def
            }
        }
    }

    fn to_recursive_impl_wrap(&self) -> TokenStream {
        let Self {
            orig_name,
            sig_name,
            variants,
            ..
        } = self;
        let wrap_arms = variants
            .iter()
            .map(|v| v.to_wrap_arm_without_comma(orig_name, sig_name));
        quote! {
            fn wrap(x: Self::Container<Self>) -> Self {
                match x {
                    #(#wrap_arms),*
                }
            }
        }
    }

    fn to_recursive_impl_unwrap(&self) -> TokenStream {
        let Self {
            orig_name,
            sig_name,
            variants,
            ..
        } = self;
        let unwrap_arms = variants
            .iter()
            .map(|v| v.to_unwrap_arm_without_comma(orig_name, sig_name));
        quote! {
            fn unwrap(self) -> Self::Container<Self> {
                match self {
                    #(#unwrap_arms),*
                }
            }
        }
    }

    fn to_recursive_impl_sclone(&self) -> TokenStream {
        let Self {
            sig_name, variants, ..
        } = self;
        let t_name = &quote! { T };
        let sclone_arm = variants
            .iter()
            .map(|v| v.to_sclone_arm_without_comma(sig_name));
        quote! {
            fn sclone<#t_name: Clone>(x: &Self::Container<#t_name>) -> Self::Container<#t_name> {
                match x {
                    #(#sclone_arm),*
                }
            }
        }
    }

    fn to_recursive_impl_sig_each_ref(&self) -> TokenStream {
        let Self {
            sig_name, variants, ..
        } = self;
        let t_name = &quote! { T };
        let sig_ref_arm = variants
            .iter()
            .map(|v| v.to_sig_each_ref_arm(sig_name, t_name));
        quote! {
            fn sig_each_ref<#t_name>(sig: &::egg_recursive::Signature<Self, #t_name>) -> ::egg_recursive::Signature<Self, &#t_name> {
                match sig {
                    #(#sig_ref_arm),*
                }
            }
        }
    }

    fn to_expr_converters(&self) -> TokenStream {
        let Self {
            orig_name,
            egg_synonym,
            ..
        } = self;
        quote! {
            impl ::std::convert::From<#orig_name> for ::egg::RecExpr<#egg_synonym> {
                fn from(x: #orig_name) -> Self {
                    ::egg_recursive::Recursive::into_rec_expr(x).0
                }
            }
            impl ::std::convert::From<::egg::RecExpr<#egg_synonym>> for #orig_name {
                fn from(x: ::egg::RecExpr<#egg_synonym>) -> Self {
                    <#orig_name as ::egg_recursive::Recursive>::from_rec_expr(&x, x.root())
                }
            }
        }
    }

    fn to_smart_cons_trait(&self) -> TokenStream {
        let Self {
            orig_name,
            vis,
            cons_trait_name,
            variants,
            ..
        } = self;
        let trait_fn = variants.iter().map(|v| v.to_smart_cons_trait_fn());
        let comment = format!(
        "The smart constructor trait for [`{}`]-like types. Generated via `#[derive(Language)]`",
            orig_name
        );
        quote! {
            #[doc=#comment]
            #vis trait #cons_trait_name: Sized {
                #(#trait_fn)*
            }
        }
    }

    fn to_smart_cons_impl_orig(&self) -> TokenStream {
        let Self {
            orig_name,
            cons_trait_name,
            variants,
            ..
        } = self;
        let trait_orig_impl = variants.iter().map(|v| v.to_smart_cons_impl_orig());
        quote! {
            impl #cons_trait_name for #orig_name {
                #(#trait_orig_impl)*
            }
        }
    }

    fn to_smart_cons_impl_raw_pat(&self) -> TokenStream {
        let Self {
            cons_trait_name,
            variants,
            raw_pat_name,
            sig_name,
            ..
        } = self;
        let trait_raw_pat_impl = variants
            .iter()
            .map(|v| v.to_smart_cons_impl_raw_pat(sig_name));
        quote! {
            impl #cons_trait_name for #raw_pat_name {
                #(#trait_raw_pat_impl)*
            }
        }
    }

    fn to_smart_cons_impl_newtype_pat(&self) -> TokenStream {
        let Self {
            cons_trait_name,
            raw_pat_name,
            pat_synonym,
            ..
        } = self;
        let trait_newtype_pat_impl = self
            .variants
            .iter()
            .map(|v| v.to_smart_cons_impl_newtype_pat(raw_pat_name));
        quote! {
            impl #cons_trait_name for #pat_synonym {
                #(#trait_newtype_pat_impl)*
            }
        }
    }
}

enum LangVariant {
    Unit(Ident),
    Recursive(Ident, Option<Ident>, RecArg),
    NonRecursive(Ident, Fields),
}

impl TryFrom<Variant> for LangVariant {
    type Error = Error;

    fn try_from(variant: Variant) -> Result<Self> {
        if let Fields::Unit = variant.fields {
            return Ok(Self::Unit(variant.ident));
        };
        if variant.fields.is_empty() {
            return Ok(Self::NonRecursive(variant.ident, variant.fields));
        }
        let (selves, nonselves): (Vec<_>, Vec<_>) = variant
            .fields
            .iter()
            .map(|fld| {
                let stream = fld.ty.to_token_stream();
                if let Ok(rec) = Parser::parse2(RecArg::parse, stream.clone()) {
                    Ok(Ok((fld.ident.clone(), rec)))
                } else if let Ok(nonself) = Parser::parse2(NonSelfType::parse, stream) {
                    Ok(Err(nonself))
                } else {
                    Err(Error::new_spanned(
                        fld.ty.clone(),
                        "Recusive type should be one of the form: Box<Self>, Vec<Self>, [Box<Self>; N], or T<Box<Self>>",
                    ))
                }
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .partition_result();
        if !selves.is_empty() && !nonselves.is_empty() {
            return Err(Error::new_spanned(
                variant.fields,
                "recursive and non-recursive fields cannot be mixed",
            ));
        }
        if nonselves.is_empty() {
            if selves.len() > 1 {
                return Err(Error::new_spanned(
                    variant.fields,
                    "Recursive field must have exactly one field; consider using LanguageChildren instance (you can derive with #[derive(LanguageChildren)] whith egg_recursive)",
                ));
            }
            let (fld, rec) = selves.into_iter().next().unwrap();
            Ok(Self::Recursive(variant.ident, fld, rec))
        } else {
            Ok(Self::NonRecursive(variant.ident, variant.fields))
        }
    }
}

#[derive(Clone)]
struct NonRecSmartConsArg {
    arg_name: Ident,
    ty: Type,
    dest_field_name: Option<Ident>,
}

enum SmartConsArgs {
    Unit,
    NonRecursive(Vec<NonRecSmartConsArg>),
    /// function argument name, struct field name, and Argument Spec
    Recursive(TokenStream, Option<Ident>, RecArg),
}

impl SmartConsArgs {
    fn arg_types(&self) -> impl Iterator<Item = (TokenStream, Option<TokenStream>)> + '_ {
        let iter: Box<dyn Iterator<Item = (TokenStream, Option<TokenStream>)>> = match self {
            Self::Unit => Box::new(std::iter::empty()),
            Self::NonRecursive(fs) => Box::new(fs.iter().cloned().map(|nonrec| {
                let NonRecSmartConsArg { arg_name, ty, .. } = nonrec;
                (quote! {#arg_name}, Some(quote! { #ty }))
            })),
            Self::Recursive(fld, _, rec_arg) => Box::new(std::iter::once(match rec_arg {
                RecArg::Boxed(_) => (quote! {self}, None),
                RecArg::Variadic(_) => (quote! {#fld}, Some(quote! {::std::vec::Vec<Self>})),
                RecArg::NAry(nary) => {
                    let n: usize = nary.len.base10_parse().unwrap();
                    (quote! {#fld}, Some(quote! {[Self; #n]}))
                }
                RecArg::GenericBoxSelf(gen) => {
                    let container = &gen.container;
                    (quote! {#fld}, Some(quote! {#container<Self>}))
                }
            })),
        };
        iter
    }
}

impl LangVariant {
    fn var_name(&self) -> &Ident {
        match self {
            Self::Unit(var_name) => var_name,
            Self::Recursive(var_name, _, _) => var_name,
            Self::NonRecursive(var_name, _) => var_name,
        }
    }
    fn to_signature_variant_without_comma(&self, param: &Ident) -> TokenStream {
        match self {
            LangVariant::Unit(var_name) => quote! { #var_name },
            LangVariant::Recursive(var_name, field, rec_arg) => {
                rec_arg.to_signature_variant_without_comma(var_name, field, param)
            }
            LangVariant::NonRecursive(var_name, fields) => match fields {
                Fields::Unit => quote! { #var_name },
                Fields::Named(fs) => {
                    let field = fs.named.iter().map(|f| {
                        let ty = &f.ty;
                        let ident = f.ident.as_ref().unwrap();
                        quote! { #ident: #ty }
                    });
                    quote! { #var_name { #(#field),* } }
                }
                Fields::Unnamed(fs) => {
                    let field = fs.unnamed.iter().map(|f| {
                        let ty = &f.ty;
                        quote! { #ty }
                    });
                    quote! { #var_name (#(#field),*) }
                }
            },
        }
    }

    fn to_sig_each_ref_arm(&self, sig_name: &Ident, para: &TokenStream) -> TokenStream {
        match self {
            Self::Unit(var_name) => {
                quote! { #sig_name::#var_name => #sig_name::#var_name}
            }
            Self::NonRecursive(var_name, flds) => {
                let (flds, cloned) = match flds {
                    Fields::Unit => (quote! {}, quote! {}),
                    Fields::Named(fs) => {
                        let fs = fs
                            .named
                            .iter()
                            .map(|f| f.ident.as_ref().unwrap())
                            .collect::<Vec<_>>();
                        (
                            quote! { { #(#fs),* } },
                            quote! { { #(#fs: ::std::clone::Clone::clone(#fs)),* }},
                        )
                    }
                    Fields::Unnamed(fs) => {
                        let fs = (0..fs.unnamed.len())
                            .map(|i| Ident::new(&format!("__self_{i}"), fs.span()))
                            .collect::<Vec<_>>();
                        (
                            quote! { ( #(#fs),* ) },
                            quote! { ( #( ::std::clone::Clone::clone(#fs)),* ) },
                        )
                    }
                };
                quote! { #sig_name::#var_name #flds => #sig_name::#var_name #cloned}
            }
            Self::Recursive(var_name, fld_name, rec) => {
                let ch = rec.as_into_lang_children(para);
                let (args, refs) = if let Some(fld) = fld_name {
                    (
                        quote! { {#fld} },
                        quote! { {#fld: <#ch as ::egg_recursive::IntoLanguageChildren>::raw_as_refs(#fld)}},
                    )
                } else {
                    let x = &Ident::new("__inner", Span::mixed_site());
                    (
                        quote! { (#x) },
                        quote! { (<#ch as ::egg_recursive::IntoLanguageChildren>::raw_as_refs(#x)) },
                    )
                };
                quote! { #sig_name::#var_name #args => #sig_name::#var_name #refs }
            }
        }
    }

    fn to_map_arm_without_comma(&self, f: &Ident) -> TokenStream {
        match self {
            Self::Unit(var_name) => {
                quote! { Self::Container::#var_name => Self::Container::#var_name }
            }
            Self::NonRecursive(var_name, flds) => {
                let flds = match flds {
                    Fields::Unit => quote! {},
                    Fields::Named(fs) => {
                        let fs = fs.named.iter().map(|f| f.ident.as_ref().unwrap());
                        quote! { { #(#fs),* } }
                    }
                    Fields::Unnamed(fs) => {
                        let fs = (0..fs.unnamed.len())
                            .map(|i| Ident::new(&format!("__self_{i}"), fs.span()));
                        quote! { ( #(#fs),* ) }
                    }
                };
                quote! { Self::Container::#var_name #flds => Self::Container::#var_name #flds}
            }
            Self::Recursive(var_name, fld_name, rec_arg) => {
                let (x, args) = if let Some(fld) = fld_name {
                    (fld.clone(), quote! { {#fld} })
                } else {
                    let x = &Ident::new("__inner", Span::mixed_site());
                    (x.clone(), quote! { (#x) })
                };
                let val = rec_arg.mapped_expr(f, &x);
                let val = if let Some(name) = fld_name {
                    quote! { {#name: #val} }
                } else {
                    quote! { (#val) }
                };
                quote! { Self::Container::#var_name #args => Self::Container::#var_name #val }
            }
        }
    }

    fn to_lang_match_arm_without_comma(&self) -> TokenStream {
        match self {
            Self::Unit(var_name) => quote! { (Self::#var_name, Self::#var_name) => true },
            Self::NonRecursive(var_name, flds) => {
                let (bind_l, bind_r, eqs) = match flds {
                    Fields::Unit => (quote! {}, quote! {}, quote! {true}),
                    Fields::Named(fs) => {
                        let fs: Vec<Ident> = fs
                            .named
                            .iter()
                            .map(|f| f.ident.as_ref().cloned().unwrap())
                            .collect();
                        let names = fs
                            .iter()
                            .map(|f| {
                                (
                                    f,
                                    Ident::new(&format!("{}_l", f), f.span()),
                                    Ident::new(&format!("{}_r", f), f.span()),
                                )
                            })
                            .collect::<Vec<_>>();
                        let (bind_l, bind_r): (Vec<_>, Vec<_>) = names
                            .iter()
                            .cloned()
                            .map(|(orig, l, r)| (quote! { #orig: #l }, quote! { #orig: #r}))
                            .unzip();

                        let bind_l = quote! { { #(#bind_l),* } };
                        let bind_r = quote! { { #(#bind_r),* } };
                        let eqs = Itertools::intersperse(
                            names.into_iter().map(|(_, l, r)| quote! { #l == #r }),
                            quote! { && },
                        )
                        .collect::<TokenStream>();
                        (bind_l, bind_r, eqs)
                    }
                    Fields::Unnamed(fs) => {
                        let names = (0..fs.unnamed.len())
                            .map(|i| {
                                (
                                    Ident::new(&format!("__arg_l_{i}"), fs.span()),
                                    Ident::new(&format!("__arg_r_{i}"), fs.span()),
                                )
                            })
                            .collect::<Vec<_>>();
                        let (bind_l, bind_r): (Vec<_>, Vec<_>) = names.iter().cloned().unzip();
                        let bind_l = quote! { ( #(#bind_l),* ) };
                        let bind_r = quote! { ( #(#bind_r),* ) };
                        let eqs = Itertools::intersperse(
                            names.into_iter().map(|(l, r)| quote! { #l == #r }),
                            quote! { && },
                        )
                        .collect::<TokenStream>();

                        (bind_l, bind_r, eqs)
                    }
                };
                quote! {
                    (Self::#var_name #bind_l, Self::#var_name #bind_r) => #eqs
                }
            }
            Self::Recursive(var_name, fld, _) => {
                let (name_l, name_r, bind_l, bind_r) = if let Some(fld) = fld {
                    let name_l = Ident::new(&format!("{}_l", &fld), fld.span());
                    let name_r = Ident::new(&format!("{}_r", &fld), fld.span());
                    (
                        name_l.clone(),
                        name_r.clone(),
                        quote! { {#fld: #name_l} },
                        quote! { {#fld: #name_r} },
                    )
                } else {
                    let name_l = Ident::new("__inner_l", Span::mixed_site());
                    let name_r = Ident::new("__inner_r", Span::mixed_site());

                    (
                        name_l.clone(),
                        name_r.clone(),
                        quote! { (#name_l) },
                        quote! { (#name_r) },
                    )
                };
                let get_len = |x| quote! { ::egg::LanguageChildren::len(#x) };
                let lhs = get_len(&name_l);
                let rhs = get_len(&name_r);

                quote! {
                    (Self::#var_name #bind_l, Self::#var_name #bind_r) => #lhs == #rhs
                }
            }
        }
    }

    fn to_lang_children_arm_without_comma(&self) -> TokenStream {
        match self {
            Self::Unit(var_name) => {
                quote! { Self::#var_name => &[] }
            }
            Self::NonRecursive(var_name, flds) => {
                let wild = match flds {
                    Fields::Unit => quote! {},
                    Fields::Named(_) => quote! { {..} },
                    Fields::Unnamed(_) => quote! { (..) },
                };
                quote! { Self::#var_name #wild => &[] }
            }
            Self::Recursive(var_name, fld, _) => {
                let (binder, inner) = if let Some(name) = fld {
                    (quote! {{#name}}, name.clone())
                } else {
                    let name = Ident::new("__inner", Span::mixed_site());
                    (quote! {(#name)}, name)
                };
                quote! { Self::#var_name #binder => ::egg::LanguageChildren::as_slice(#inner)}
            }
        }
    }

    fn to_lang_children_mut_arm_without_comma(&self) -> TokenStream {
        match self {
            Self::Unit(var_name) => {
                quote! { Self::#var_name => &mut [] }
            }
            Self::NonRecursive(var_name, flds) => {
                let wild = match flds {
                    Fields::Unit => quote! {},
                    Fields::Named(_) => quote! { {..} },
                    Fields::Unnamed(_) => quote! { (..) },
                };
                quote! { Self::#var_name #wild => &mut [] }
            }
            Self::Recursive(var_name, fld, _) => {
                let (binder, inner) = if let Some(name) = fld {
                    (quote! {{#name}}, name.clone())
                } else {
                    let name = Ident::new("__inner", Span::mixed_site());
                    (quote! {(#name)}, name)
                };
                quote! { Self::#var_name #binder => ::egg::LanguageChildren::as_mut_slice(#inner)}
            }
        }
    }

    fn to_unwrap_arm_without_comma(&self, orig_name: &Ident, sig_name: &Ident) -> TokenStream {
        match self {
            LangVariant::Unit(var_name) => quote! { #orig_name::#var_name => #sig_name::#var_name },
            LangVariant::NonRecursive(var_name, flds) => match flds {
                Fields::Unit => quote! { #orig_name::#var_name => #sig_name::#var_name },
                Fields::Named(fs) => {
                    let fs = fs
                        .named
                        .iter()
                        .map(|f| {
                            let ident = f.ident.as_ref().unwrap();
                            quote! { #ident }
                        })
                        .collect::<Vec<_>>();
                    quote! { #orig_name::#var_name { #(#fs),* } => #sig_name::#var_name { #(#fs),* } }
                }
                Fields::Unnamed(fs) => {
                    let fs = (0..fs.unnamed.len())
                        .map(|i| {
                            let ident = Ident::new(&format!("__arg_{}", i), Span::mixed_site());
                            quote! { #ident }
                        })
                        .collect::<Vec<_>>();
                    quote! { #orig_name::#var_name ( #(#fs),* ) => #sig_name::#var_name ( #(#fs),* ) }
                }
            },
            LangVariant::Recursive(var_name, fld, rec_arg) => {
                let (x, args) = if let Some(fld) = fld {
                    (fld.clone(), quote! { {#fld} })
                } else {
                    let x = &Ident::new("__inner", Span::mixed_site());
                    (x.clone(), quote! { (#x) })
                };
                let val = match rec_arg {
                    RecArg::Boxed(_) => quote! { * #x },
                    RecArg::Variadic(_) => quote! { #x },
                    RecArg::NAry(_) => {
                        quote! { #x.map(|b| *b) }
                    }
                    RecArg::GenericBoxSelf(gen) => {
                        let container = &gen.container;
                        quote! {
                            <<
                                #container<::egg::Id>
                                as ::egg_recursive::IntoLanguageChildren
                            >::RawData as ::egg_recursive::Functor>::fmap(
                                |b| *b,
                                <
                                    #container<::egg::Id>
                                    as ::egg_recursive::IntoLanguageChildren
                                >::unview(#x)
                            )
                        }
                    }
                };
                let val = if let Some(name) = fld {
                    quote! { {#name: #val} }
                } else {
                    quote! { (#val) }
                };
                quote! { #orig_name::#var_name #args => #sig_name::#var_name #val }
            }
        }
    }

    fn to_wrap_arm_without_comma(&self, orig_name: &Ident, sig_name: &Ident) -> TokenStream {
        match self {
            LangVariant::Unit(var_name) => quote! { #sig_name::#var_name => #orig_name::#var_name },
            LangVariant::NonRecursive(var_name, flds) => match flds {
                Fields::Unit => quote! { #sig_name::#var_name => #orig_name::#var_name },
                Fields::Named(fs) => {
                    let fs = fs
                        .named
                        .iter()
                        .map(|f| {
                            let ident = f.ident.as_ref().unwrap();
                            quote! { #ident }
                        })
                        .collect::<Vec<_>>();
                    quote! { #sig_name::#var_name { #(#fs),* } => #orig_name::#var_name { #(#fs),* } }
                }
                Fields::Unnamed(fs) => {
                    let fs = (0..fs.unnamed.len())
                        .map(|i| {
                            let ident = Ident::new(&format!("__arg_{}", i), Span::mixed_site());
                            quote! { #ident }
                        })
                        .collect::<Vec<_>>();
                    quote! { #sig_name::#var_name ( #(#fs),* ) => #orig_name::#var_name ( #(#fs),* ) }
                }
            },
            LangVariant::Recursive(var_name, fld, rec_arg) => {
                let (x, args) = if let Some(fld) = fld {
                    (fld.clone(), quote! { {#fld} })
                } else {
                    let x = &Ident::new("__inner", Span::mixed_site());
                    (x.clone(), quote! { (#x) })
                };
                let val = match rec_arg {
                    RecArg::Boxed(_) => quote! { Box::new(#x) },
                    RecArg::Variadic(_) => quote! { #x },
                    RecArg::NAry(_) => {
                        quote! { #x.map(Box::new) }
                    }
                    RecArg::GenericBoxSelf(gen) => {
                        let container = &gen.container;
                        quote! {
                            <
                                <
                                    #container<::egg::Id>
                                    as ::egg_recursive::IntoLanguageChildren
                                >::View
                                as ::egg_recursive::Functor
                            >::fmap(
                                Box::new,
                                <#container<::egg::Id> as ::egg_recursive::IntoLanguageChildren>::view(#x)
                            )
                        }
                    }
                };
                let val = if let Some(name) = fld {
                    quote! { {#name: #val} }
                } else {
                    quote! { (#val) }
                };
                quote! { #sig_name::#var_name #args => #orig_name::#var_name #val }
            }
        }
    }

    fn to_sclone_arm_without_comma(&self, sig: &Ident) -> TokenStream {
        let var_name = self.var_name();
        let var = quote! { #sig::#var_name };
        match self {
            Self::Unit(_) => quote! { #var => #var },
            Self::NonRecursive(_, fs) => match fs {
                Fields::Unit => quote! { #var => #var },
                Fields::Named(fs) => {
                    let args = fs
                        .named
                        .iter()
                        .map(|f| {
                            let ident = f.ident.as_ref().unwrap();
                            quote! { #ident }
                        })
                        .collect::<Vec<_>>();
                    quote! { #var{#(#args),*} => #var { #(#args: #args.clone()),* } }
                }
                Fields::Unnamed(fs) => {
                    let args = (0..fs.unnamed.len())
                        .map(|i| {
                            let ident = Ident::new(&format!("__arg_{}", i), Span::mixed_site());
                            quote! { #ident }
                        })
                        .collect::<Vec<_>>();
                    quote! { #var(#(#args),*) => #var(#(#args.clone()),*) }
                }
            },
            Self::Recursive(_, sfld, _) => {
                if let Some(fld) = sfld {
                    quote! { #var{#fld} => #var{#fld: #fld.clone()}}
                } else {
                    quote! { #var(x) => #var(x.clone())}
                }
            }
        }
    }

    fn to_smart_cons_arg_spec(&self) -> SmartConsArgs {
        match self {
            Self::Unit(_) => SmartConsArgs::Unit,
            Self::NonRecursive(_, fields) => SmartConsArgs::NonRecursive(
                fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| {
                        let arg_name = f
                            .ident
                            .as_ref()
                            .cloned()
                            .unwrap_or_else(|| Ident::new(&format!("__arg_{i}"), f.span()));
                        let ty = f.ty.clone();
                        let dest_field_name = f.ident.clone();
                        NonRecSmartConsArg {
                            arg_name,
                            ty,
                            dest_field_name,
                        }
                    })
                    .collect(),
            ),
            Self::Recursive(_, field, rec_arg) => {
                let fld = field
                    .as_ref()
                    .cloned()
                    .unwrap_or_else(|| Ident::new("rec_args", Span::mixed_site()));
                let fld = match rec_arg {
                    RecArg::Boxed(_) => quote! { self },
                    _ => quote! { #fld },
                };
                SmartConsArgs::Recursive(fld, field.clone(), rec_arg.clone())
            }
        }
    }

    fn to_smart_cons_trait_fn(&self) -> TokenStream {
        let var_name = self.var_name();
        let cons = to_field_name(var_name);
        let args = self
            .to_smart_cons_arg_spec()
            .arg_types()
            .map(|(v, ty)| {
                if let Some(ty) = ty {
                    quote! {#v: #ty}
                } else {
                    v
                }
            })
            .collect::<Vec<_>>();
        quote! {
            fn #cons(#(#args),*) -> Self;
        }
    }

    fn to_smart_cons_impl_orig(&self) -> TokenStream {
        let var_name = self.var_name();
        let cons = to_field_name(var_name);
        let arg_specs = self.to_smart_cons_arg_spec();
        let args = arg_specs
            .arg_types()
            .map(|(v, ty)| {
                if let Some(ty) = ty {
                    quote! {#v: #ty}
                } else {
                    v
                }
            })
            .collect::<Vec<_>>();
        let body = match arg_specs {
            SmartConsArgs::Unit => quote! { Self::#var_name },
            SmartConsArgs::NonRecursive(bts) => {
                let cons_args = if bts.is_empty() {
                    quote! { () }
                } else {
                    let named = bts.first().unwrap().dest_field_name.is_some();
                    if named {
                        let assign = bts.into_iter().map(|b| {
                            let val = b.arg_name;
                            let fld = b.dest_field_name.unwrap();
                            quote! { #fld: #val }
                        });
                        quote! { { #(#assign),* }}
                    } else {
                        let assign = bts.into_iter().map(|b| b.arg_name);
                        quote! { ( #(#assign),* )}
                    }
                };
                quote! { Self::#var_name #cons_args }
            }
            SmartConsArgs::Recursive(x, dest, rec_arg) => {
                let val = match rec_arg {
                    RecArg::Boxed(_) => quote! { Box::new(#x) },
                    RecArg::Variadic(_) => quote! { #x },
                    RecArg::NAry(_) => quote! { #x.map(Box::new) },
                    RecArg::GenericBoxSelf(gen) => {
                        let container = &gen.container;
                        quote! {
                            <<
                                #container<::egg::Id>
                                as ::egg_recursive::IntoLanguageChildren
                            >::View as ::egg_recursive::Functor>::fmap(
                                Box::new,
                                #x
                            )
                        }
                    }
                };
                let cons_args = if let Some(fld) = dest {
                    quote! { {#fld: #val} }
                } else {
                    quote! { (#val) }
                };
                quote! { Self::#var_name #cons_args }
            }
        };
        quote! {
            fn #cons(#(#args),*) -> Self {
                #body
            }
        }
    }

    fn to_smart_cons_impl_raw_pat(&self, sig_name: &Ident) -> TokenStream {
        let var_name = self.var_name();
        let cons = to_field_name(var_name);
        let arg_specs = self.to_smart_cons_arg_spec();
        let args = arg_specs
            .arg_types()
            .map(|(v, ty)| {
                if let Some(ty) = ty {
                    quote! {#v: #ty}
                } else {
                    v
                }
            })
            .collect::<Vec<_>>();
        let body = match arg_specs {
            SmartConsArgs::Unit => quote! { Self::wrap(#sig_name::#var_name) },
            SmartConsArgs::NonRecursive(bts) => {
                let cons_args = if bts.is_empty() {
                    quote! { () }
                } else {
                    let named = bts.first().unwrap().dest_field_name.is_some();
                    if named {
                        let assign = bts.into_iter().map(|b| {
                            let val = b.arg_name;
                            let fld = b.dest_field_name.unwrap();
                            quote! { #fld: #val }
                        });
                        quote! { { #(#assign),* }}
                    } else {
                        let assign = bts.into_iter().map(|b| b.arg_name);
                        quote! { ( #(#assign),* )}
                    }
                };
                quote! { Self::wrap(#sig_name::#var_name #cons_args) }
            }
            SmartConsArgs::Recursive(x, dest, rec_arg) => {
                let val = match rec_arg {
                    RecArg::Boxed(_) => quote! { #x  },
                    RecArg::Variadic(_) => quote! { #x },
                    RecArg::NAry(_) => quote! { #x },
                    RecArg::GenericBoxSelf(gen) => {
                        let container = &gen.container;
                        quote! {
                            <
                                #container<::egg::Id>
                                as ::egg_recursive::IntoLanguageChildren
                            >::unview(#x)
                        }
                    }
                };
                let cons_args = if let Some(fld) = dest {
                    quote! { {#fld: #val} }
                } else {
                    quote! { (#val) }
                };
                quote! { Self::wrap(#sig_name::#var_name #cons_args) }
            }
        };
        quote! {
            fn #cons(#(#args),*) -> Self {
                #body
            }
        }
    }

    fn to_smart_cons_impl_newtype_pat(&self, raw_pat_name: &TokenStream) -> TokenStream {
        let var_name = self.var_name();
        let cons = to_field_name(var_name);
        let arg_specs = self.to_smart_cons_arg_spec();
        let args = arg_specs
            .arg_types()
            .map(|(v, ty)| {
                if let Some(ty) = ty {
                    quote! {#v: #ty}
                } else {
                    v
                }
            })
            .collect::<Vec<_>>();
        let body = match arg_specs {
            SmartConsArgs::Unit => quote! { Self(#raw_pat_name::#cons()) },
            SmartConsArgs::NonRecursive(bts) => {
                let assign = bts.into_iter().map(|b| b.arg_name);
                let cons_args = quote! { (#(#assign),*) };
                quote! { Self(#raw_pat_name::#cons #cons_args) }
            }
            SmartConsArgs::Recursive(x, _, rec_arg) => {
                let val = match rec_arg {
                    RecArg::Boxed(_) => quote! { #x.0 },
                    RecArg::Variadic(_) => {
                        quote! { #x.into_iter().map(|x| x.0).collect::<Vec<_>>() }
                    }
                    RecArg::NAry(_) => quote! { #x.map(|a| a.0) },
                    RecArg::GenericBoxSelf(gen) => {
                        let container = &gen.container;
                        quote! {
                            <<
                                #container<::egg::Id>
                                as ::egg_recursive::IntoLanguageChildren
                            >::View as ::egg_recursive::Functor>::fmap(|x| x.0, #x)
                        }
                    }
                };
                let cons_args = quote! { (#val) };
                quote! { Self(#raw_pat_name::#cons #cons_args) }
            }
        };
        quote! {
            fn #cons(#(#args),*) -> Self {
                #body
            }
        }
    }
}

#[derive(Debug, Clone)]
enum RecArg {
    Boxed(BoxedSelf),
    Variadic(Variadic),
    NAry(NAry),
    GenericBoxSelf(GenericBoxSelf),
}

impl ToTokens for RecArg {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            RecArg::Boxed(boxed) => boxed.to_tokens(tokens),
            RecArg::Variadic(vec) => vec.to_tokens(tokens),
            RecArg::NAry(nary) => nary.to_tokens(tokens),
            RecArg::GenericBoxSelf(gen) => gen.to_tokens(tokens),
        }
    }
}

impl Parse for RecArg {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        use RecArg::*;
        if let Ok(boxed) = input.parse() {
            Ok(Boxed(boxed))
        } else if let Ok(var) = input.parse() {
            Ok(Variadic(var))
        } else if let Ok(n_ary) = input.parse() {
            Ok(NAry(n_ary))
        } else if let Ok(generic_box_self) = input.parse() {
            Ok(GenericBoxSelf(generic_box_self))
        } else {
            Err(input.error("expected recursive argument"))
        }
    }
}

impl RecArg {
    fn to_signature_variant_without_comma(
        &self,
        var_name: &Ident,
        field: &Option<Ident>,
        param: &Ident,
    ) -> TokenStream {
        let ty = match self {
            RecArg::Boxed(_) => quote! { #param },
            RecArg::Variadic(_) => quote! { ::std::vec::Vec<#param> },
            RecArg::NAry(nary) => {
                let n: usize = nary.len.base10_parse().unwrap();
                quote! { [#param; #n] }
            }
            RecArg::GenericBoxSelf(gen) => {
                let container = &gen.container;
                quote! { ::egg_recursive::RawData<#container<#param>, #param> }
            }
        };
        if let Some(name) = field {
            quote! { #var_name{#name: #ty} }
        } else {
            quote! { #var_name(#ty) }
        }
    }

    fn mapped_expr(&self, f: &Ident, x: &Ident) -> TokenStream {
        match self {
            Self::Boxed(_) => quote! { #f(#x) },
            Self::Variadic(_) => quote! { #x.into_iter().map(&mut #f).collect() },
            Self::NAry(_) => quote! { #x.map(&mut #f) },
            Self::GenericBoxSelf(_) => quote! { #x.map(&mut #f) },
        }
    }

    fn as_into_lang_children(&self, para: &TokenStream) -> TokenStream {
        match self {
            Self::Boxed(_) => quote! { ::egg::Id },
            Self::Variadic(_) => quote! { ::std::vec::Vec::<::egg::Id> },
            Self::NAry(nary) => {
                let n: usize = nary.len.base10_parse().unwrap();
                quote! { [::egg::Id; #n] }
            }
            Self::GenericBoxSelf(gen) => {
                let container = &gen.container;
                quote! { #container::<#para> }
            }
        }
    }
}

struct NonSelfType {
    inner: Type,
}

#[derive(Debug)]
struct SelfDetector {
    present: bool,
}
impl SelfDetector {
    fn new() -> Self {
        Self { present: false }
    }
}
impl Visit<'_> for SelfDetector {
    fn visit_ident(&mut self, i: &Ident) {
        if i == "Self" {
            self.present = true;
        }
    }
}

impl Parse for NonSelfType {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let inner = input.parse()?;
        let mut detector = SelfDetector::new();
        detector.visit_type(&inner);
        if detector.present {
            return Err(Error::new_spanned(inner, "expected non-Self type"));
        }
        Ok(Self { inner })
    }
}

impl ToTokens for NonSelfType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.inner.to_tokens(tokens);
    }
}

#[derive(Debug, Clone)]
struct BoxedSelf {
    box_ident: Ident,
    lt_token: Token![<],
    self_token: Token![Self],
    gt_token: Token![>],
}

impl Parse for BoxedSelf {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        custom_keyword!(Box);
        if !input.peek(Box) {
            return Err(Error::new(input.span(), "expected `Box`"));
        }
        let box_ident = input.parse::<Ident>()?;
        let lt_token = input.parse::<Token![<]>()?;
        let self_token = input.parse::<Token![Self]>()?;
        let gt_token = input.parse::<Token![>]>()?;

        Ok(Self {
            box_ident,
            lt_token,
            self_token,
            gt_token,
        })
    }
}

impl ToTokens for BoxedSelf {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.box_ident.to_tokens(tokens);
        self.lt_token.to_tokens(tokens);
        self.self_token.to_tokens(tokens);
        self.gt_token.to_tokens(tokens);
    }
}

// TODO: support `&[Self]`
#[derive(Debug, Clone)]
struct Variadic {
    vec_ident: Ident,
    lt_token: Token![<],
    self_token: Token![Self],
    gt_token: Token![>],
}

impl Parse for Variadic {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        custom_keyword!(Vec);
        if !input.peek(Vec) {
            return Err(Error::new(input.span(), "expected `Vec`"));
        }
        let vec_ident = input.parse::<Ident>()?;
        let lt_token = input.parse::<Token![<]>()?;
        let self_token = input.parse::<Token![Self]>()?;
        let gt_token = input.parse::<Token![>]>()?;

        Ok(Self {
            vec_ident,
            lt_token,
            self_token,
            gt_token,
        })
    }
}

impl ToTokens for Variadic {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.vec_ident.to_tokens(tokens);
        self.lt_token.to_tokens(tokens);
        self.self_token.to_tokens(tokens);
        self.gt_token.to_tokens(tokens);
    }
}

#[derive(Debug, Clone)]
struct NAry {
    bracket_token: Bracket,
    boxed_token: BoxedSelf,
    semi_token: Token![;],
    len: LitInt,
}

impl Parse for NAry {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        if !input.peek(Bracket) {
            return Err(Error::new(input.span(), "expected bracket"));
        }
        let content;
        let bracket_token = bracketed!(content in input);
        let boxed_token = content.parse::<BoxedSelf>()?;
        let semi_token = content.parse::<Token![;]>()?;
        let len = content.parse::<LitInt>()?;

        Ok(Self {
            bracket_token,
            boxed_token,
            semi_token,
            len,
        })
    }
}

impl ToTokens for NAry {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.bracket_token.surround(tokens, |tokens| {
            self.boxed_token.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
            self.len.to_tokens(tokens);
        });
    }
}

// TODO: Support non-unary generics
#[derive(Debug, Clone)]
struct GenericBoxSelf {
    container: Ident,
    lt_token: Token![<],
    boxed_self: BoxedSelf,
    gt_token: Token![>],
}

impl Parse for GenericBoxSelf {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let container = input.parse::<Ident>()?;
        let lt_token = input.parse::<Token![<]>()?;
        let boxed_self = input.parse::<BoxedSelf>()?;
        let gt_token = input.parse::<Token![>]>()?;

        Ok(Self {
            container,
            lt_token,
            boxed_self,
            gt_token,
        })
    }
}

impl ToTokens for GenericBoxSelf {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.container.to_tokens(tokens);
        self.lt_token.to_tokens(tokens);
        self.boxed_self.to_tokens(tokens);
        self.gt_token.to_tokens(tokens);
    }
}

fn to_field_name(var_name: &Ident) -> Ident {
    let raw_name = ident_case::RenameRule::SnakeCase.apply_to_variant(var_name.to_string());
    let field_name = if syn::parse_str::<Ident>(&raw_name).is_ok() {
        raw_name
    } else {
        format!("{}_", raw_name)
    };
    Ident::new(&field_name, var_name.span())
}

#[cfg(test)]
mod tests;
