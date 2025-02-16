use super::*;
use crate::test_utils::*;

#[test]
fn test_to_field_name() {
    assert_eq!(
        to_field_name(&Ident::new("Foo", Span::call_site())),
        Ident::new("foo", Span::call_site())
    );
    assert_eq!(
        to_field_name(&Ident::new("If", Span::call_site())),
        Ident::new("if_", Span::call_site())
    );
}

#[test]
fn test_hoge() {
    let ty: Type = parse_quote!(Box<Self>);
    let mut detect = SelfDetector::new();
    detect.visit_type(&ty);
    assert!(detect.present);
}

#[test]
fn test_rec_arg_box() {
    let ty = quote! {Box<Self>};
    let rec_arg = Parser::parse2(RecArg::parse, ty).unwrap();
    assert!(matches!(rec_arg, RecArg::Boxed(_)));
}

#[test]
fn test_rec_nary() {
    let ty = quote! {[Box<Self>; 2]};
    let rec_arg = Parser::parse2(RecArg::parse, ty).unwrap();
    assert!(matches!(rec_arg, RecArg::NAry(_)));
}

#[test]
fn test_rec_arg_generic() {
    let ty = quote! {BinOpArgs<Box<Self>>};
    let rec_arg = Parser::parse2(RecArg::parse, ty).unwrap();
    assert!(matches!(rec_arg, RecArg::GenericBoxSelf(_)));
}

// ## Integrated Snapshots
#[test]
fn snapshot_derive_language_pub() {
    let pubs = apply_macro! {derive;
        pub enum MyLang {
            Int(i32),
            Neg(Box<Self>),
            Add { args: [Box<Self>; 2] },
            And([Box<Self>; 2]),
            Wth(usize, bool),
            Or(BinOpArgs<Box<Self>>),
            IsZero(Box<Self>),
            If(IfThenElse<Box<Self>>),
            List { elems: Vec<Self> },
            Bool { lit: bool },
            Surreal { l: Ordinal, r: Ordinal },
        }
    };
    insta::assert_snapshot!(pubs);
}

#[test]
fn snapshot_derive_language_priv() {
    let pubs = apply_macro! {derive;
        enum MyLang {
            Int(i32),
            Neg(Box<Self>),
            Add { args: [Box<Self>; 2] },
            And([Box<Self>; 2]),
            Wth(usize, bool),
            Or(BinOpArgs<Box<Self>>),
            IsZero(Box<Self>),
            If(IfThenElse<Box<Self>>),
            List { elems: Vec<Self> },
            Bool { lit: bool },
            Surreal { l: Ordinal, r: Ordinal },
            Null,
        }
    };
    insta::assert_snapshot!(pubs);
}

// ## Part-wise Snapshots

fn lang_def_for_part_snapshot() -> DeriveInput {
    parse2::<DeriveInput>(quote! {
        pub enum MyLang {
            Int(i32),
            Neg(Box<Self>),
            Add { args: [Box<Self>; 2] },
            And([Box<Self>; 2]),
            Wth(usize, bool),
            Or(BinOpArgs<Box<Self>>),
            List { elems: Vec<Self> },
            Bool { lit: bool },
            Surreal { l: Ordinal, r: Ordinal },
            If(IfThenElse<Box<Self>>),
            Null,
        }
    })
    .unwrap()
}

#[test]
fn snapshot_to_signature_type() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let lang = deriver.to_signature_type().pretty();
    insta::assert_snapshot!(lang, @r"
    ///The signature type corresponding to [`MyLang`]. Generated via `#[derive(Language)]`
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum MyLangSig<T> {
        Int(i32),
        Neg(T),
        Add { args: [T; 2usize] },
        And([T; 2usize]),
        Wth(usize, bool),
        Or(::egg_recursive::RawData<BinOpArgs<T>, T>),
        List { elems: ::std::vec::Vec<T> },
        Bool { lit: bool },
        Surreal { l: Ordinal, r: Ordinal },
        If(::egg_recursive::RawData<IfThenElse<T>, T>),
        Null,
    }
    ");
}

#[test]
fn snapshot_to_egg_synonym() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let egg = deriver.to_egg_synonym().pretty();
    insta::assert_snapshot!(egg, @r"
        ///The egg counterpart of [`MyLang`]. Generated via `#[derive(Language)]`
        pub type EggMyLang = MyLangSig<::egg::Id>;
        ");
}

#[test]
fn snapshot_to_pat_syn_and_methods() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_pat_syn_and_methods().pretty();
    insta::assert_snapshot!(pat, @r"
        ///The pattern for [`MyLang`]. Generated via `#[derive(Language)]`
        #[derive(Clone)]
        pub struct MyLangPat(pub ::egg_recursive::Pat<MyLang>);
        impl MyLangPat {
            /// Creates pattern variable. This DOESN'T expect to be prefixed with `?`, contrary to the egg's convention.
            pub fn pat_var<'a, S: Into<::std::borrow::Cow<'a, str>>>(v: S) -> Self {
                Self(::egg_recursive::Pat::pat_var(v))
            }
        }
        ");
}

#[test]
fn snapshot_to_pat_syn_converters() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_pat_syn_converters().pretty();
    insta::assert_snapshot!(pat, @r"
        impl From<MyLangPat> for ::egg_recursive::Pat<MyLang> {
            fn from(value: MyLangPat) -> Self {
                value.0
            }
        }
        impl From<::egg_recursive::Pat<MyLang>> for MyLangPat {
            fn from(value: ::egg_recursive::Pat<MyLang>) -> Self {
                Self(value)
            }
        }
        impl From<MyLang> for MyLangPat {
            fn from(value: MyLang) -> Self {
                MyLangPat(::egg_recursive::Pat::<MyLang>::from(value))
            }
        }
        impl From<MyLangPat> for ::egg::Pattern<EggMyLang> {
            fn from(value: MyLangPat) -> Self {
                value.0.into()
            }
        }
        impl From<MyLangPat> for ::egg::PatternAst<EggMyLang> {
            fn from(value: MyLangPat) -> Self {
                value.0.into()
            }
        }
        ");
}

#[test]
fn snapshot_to_pat_syn_egg_impls() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_pat_syn_egg_impls().pretty();
    insta::assert_snapshot!(pat, @r"
        impl<N: ::egg::Analysis<EggMyLang>> ::egg::Searcher<EggMyLang, N> for MyLangPat {
            fn search_eclass_with_limit(
                &self,
                egraph: &::egg::EGraph<EggMyLang, N>,
                eclass: ::egg::Id,
                limit: usize,
            ) -> Option<::egg::SearchMatches<EggMyLang>> {
                ::egg::Searcher::<
                    EggMyLang,
                    N,
                >::search_eclass_with_limit(&self.0, egraph, eclass, limit)
            }
            fn vars(&self) -> Vec<::egg::Var> {
                ::egg::Searcher::<EggMyLang, N>::vars(&self.0)
            }
        }
        impl<N: ::egg::Analysis<EggMyLang>> ::egg::Applier<EggMyLang, N> for MyLangPat {
            fn apply_one(
                &self,
                egraph: &mut ::egg::EGraph<EggMyLang, N>,
                eclass: ::egg::Id,
                subst: &::egg::Subst,
                searcher_ast: Option<&::egg::PatternAst<EggMyLang>>,
                rule_name: ::egg::Symbol,
            ) -> Vec<::egg::Id> {
                ::egg::Applier::<
                    EggMyLang,
                    N,
                >::apply_one(&self.0, egraph, eclass, subst, searcher_ast, rule_name)
            }
        }
        ");
}

#[test]
fn snapshot_to_functor_impl() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_functor_impl().pretty();
    insta::assert_snapshot!(pat, @r"
    impl ::egg_recursive::Functor for MyLang {
        type Container<T> = MyLangSig<T>;
        fn fmap<A, B, F>(mut f: F, x: Self::Container<A>) -> Self::Container<B>
        where
            F: FnMut(A) -> B,
        {
            match x {
                Self::Container::Int(__self_0) => Self::Container::Int(__self_0),
                Self::Container::Neg(__inner) => Self::Container::Neg(f(__inner)),
                Self::Container::Add { args } => {
                    Self::Container::Add {
                        args: args.map(&mut f),
                    }
                }
                Self::Container::And(__inner) => Self::Container::And(__inner.map(&mut f)),
                Self::Container::Wth(__self_0, __self_1) => {
                    Self::Container::Wth(__self_0, __self_1)
                }
                Self::Container::Or(__inner) => Self::Container::Or(__inner.map(&mut f)),
                Self::Container::List { elems } => {
                    Self::Container::List {
                        elems: elems.into_iter().map(&mut f).collect(),
                    }
                }
                Self::Container::Bool { lit } => Self::Container::Bool { lit },
                Self::Container::Surreal { l, r } => Self::Container::Surreal { l, r },
                Self::Container::If(__inner) => Self::Container::If(__inner.map(&mut f)),
                Self::Container::Null => Self::Container::Null,
            }
        }
    }
    ")
}

#[test]
fn snapshot_to_language_trait_impl() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let lang = deriver.to_language_trait_impl().pretty();
    insta::assert_snapshot!(lang, @r"
    impl ::egg::Language for MyLangSig<::egg::Id> {
        type Discriminant = ::std::mem::Discriminant<Self>;
        #[inline(always)]
        fn discriminant(&self) -> Self::Discriminant {
            ::std::mem::discriminant(self)
        }
        #[inline(always)]
        fn matches(&self, other: &Self) -> bool {
            ::std::mem::discriminant(self) == ::std::mem::discriminant(other)
                && match (self, other) {
                    (Self::Int(__arg_l_0), Self::Int(__arg_r_0)) => __arg_l_0 == __arg_r_0,
                    (Self::Neg(__inner_l), Self::Neg(__inner_r)) => {
                        ::egg::LanguageChildren::len(__inner_l)
                            == ::egg::LanguageChildren::len(__inner_r)
                    }
                    (Self::Add { args: args_l }, Self::Add { args: args_r }) => {
                        ::egg::LanguageChildren::len(args_l)
                            == ::egg::LanguageChildren::len(args_r)
                    }
                    (Self::And(__inner_l), Self::And(__inner_r)) => {
                        ::egg::LanguageChildren::len(__inner_l)
                            == ::egg::LanguageChildren::len(__inner_r)
                    }
                    (Self::Wth(__arg_l_0, __arg_l_1), Self::Wth(__arg_r_0, __arg_r_1)) => {
                        __arg_l_0 == __arg_r_0 && __arg_l_1 == __arg_r_1
                    }
                    (Self::Or(__inner_l), Self::Or(__inner_r)) => {
                        ::egg::LanguageChildren::len(__inner_l)
                            == ::egg::LanguageChildren::len(__inner_r)
                    }
                    (Self::List { elems: elems_l }, Self::List { elems: elems_r }) => {
                        ::egg::LanguageChildren::len(elems_l)
                            == ::egg::LanguageChildren::len(elems_r)
                    }
                    (Self::Bool { lit: lit_l }, Self::Bool { lit: lit_r }) => lit_l == lit_r,
                    (Self::Surreal { l: l_l, r: r_l }, Self::Surreal { l: l_r, r: r_r }) => {
                        l_l == l_r && r_l == r_r
                    }
                    (Self::If(__inner_l), Self::If(__inner_r)) => {
                        ::egg::LanguageChildren::len(__inner_l)
                            == ::egg::LanguageChildren::len(__inner_r)
                    }
                    (Self::Null, Self::Null) => true,
                    _ => false,
                }
        }
        fn children(&self) -> &[::egg::Id] {
            match self {
                Self::Int(..) => &[],
                Self::Neg(__inner) => ::egg::LanguageChildren::as_slice(__inner),
                Self::Add { args } => ::egg::LanguageChildren::as_slice(args),
                Self::And(__inner) => ::egg::LanguageChildren::as_slice(__inner),
                Self::Wth(..) => &[],
                Self::Or(__inner) => ::egg::LanguageChildren::as_slice(__inner),
                Self::List { elems } => ::egg::LanguageChildren::as_slice(elems),
                Self::Bool { .. } => &[],
                Self::Surreal { .. } => &[],
                Self::If(__inner) => ::egg::LanguageChildren::as_slice(__inner),
                Self::Null => &[],
            }
        }
        fn children_mut(&mut self) -> &mut [::egg::Id] {
            match self {
                Self::Int(..) => &mut [],
                Self::Neg(__inner) => ::egg::LanguageChildren::as_mut_slice(__inner),
                Self::Add { args } => ::egg::LanguageChildren::as_mut_slice(args),
                Self::And(__inner) => ::egg::LanguageChildren::as_mut_slice(__inner),
                Self::Wth(..) => &mut [],
                Self::Or(__inner) => ::egg::LanguageChildren::as_mut_slice(__inner),
                Self::List { elems } => ::egg::LanguageChildren::as_mut_slice(elems),
                Self::Bool { .. } => &mut [],
                Self::Surreal { .. } => &mut [],
                Self::If(__inner) => ::egg::LanguageChildren::as_mut_slice(__inner),
                Self::Null => &mut [],
            }
        }
    }
    ");
}

#[test]
fn snapshot_to_recursive_impl() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_recursive_impl().pretty();
    insta::assert_snapshot!(pat);
}

#[test]
fn snapshot_to_recursive_impl_wrap() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_recursive_impl_wrap().pretty();
    insta::assert_snapshot!(pat, @r"
    fn wrap(x: Self::Container<Self>) -> Self {
        match x {
            MyLangSig::Int(__arg_0) => MyLang::Int(__arg_0),
            MyLangSig::Neg(__inner) => MyLang::Neg(Box::new(__inner)),
            MyLangSig::Add { args } => {
                MyLang::Add {
                    args: args.map(Box::new),
                }
            }
            MyLangSig::And(__inner) => MyLang::And(__inner.map(Box::new)),
            MyLangSig::Wth(__arg_0, __arg_1) => MyLang::Wth(__arg_0, __arg_1),
            MyLangSig::Or(__inner) => {
                MyLang::Or(
                    <<BinOpArgs<
                        ::egg::Id,
                    > as ::egg_recursive::IntoLanguageChildren>::View as ::egg_recursive::Functor>::fmap(
                        Box::new,
                        <BinOpArgs<
                            ::egg::Id,
                        > as ::egg_recursive::IntoLanguageChildren>::view(__inner),
                    ),
                )
            }
            MyLangSig::List { elems } => MyLang::List { elems: elems },
            MyLangSig::Bool { lit } => MyLang::Bool { lit },
            MyLangSig::Surreal { l, r } => MyLang::Surreal { l, r },
            MyLangSig::If(__inner) => {
                MyLang::If(
                    <<IfThenElse<
                        ::egg::Id,
                    > as ::egg_recursive::IntoLanguageChildren>::View as ::egg_recursive::Functor>::fmap(
                        Box::new,
                        <IfThenElse<
                            ::egg::Id,
                        > as ::egg_recursive::IntoLanguageChildren>::view(__inner),
                    ),
                )
            }
            MyLangSig::Null => MyLang::Null,
        }
    }
    ");
}

#[test]
fn snapshot_to_recursive_impl_unwrap() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_recursive_impl_unwrap().pretty();
    insta::assert_snapshot!(pat, @r"
    fn unwrap(self) -> Self::Container<Self> {
        match self {
            MyLang::Int(__arg_0) => MyLangSig::Int(__arg_0),
            MyLang::Neg(__inner) => MyLangSig::Neg(*__inner),
            MyLang::Add { args } => {
                MyLangSig::Add {
                    args: args.map(|b| *b),
                }
            }
            MyLang::And(__inner) => MyLangSig::And(__inner.map(|b| *b)),
            MyLang::Wth(__arg_0, __arg_1) => MyLangSig::Wth(__arg_0, __arg_1),
            MyLang::Or(__inner) => {
                MyLangSig::Or(
                    <<BinOpArgs<
                        ::egg::Id,
                    > as ::egg_recursive::IntoLanguageChildren>::RawData as ::egg_recursive::Functor>::fmap(
                        |b| *b,
                        <BinOpArgs<
                            ::egg::Id,
                        > as ::egg_recursive::IntoLanguageChildren>::unview(__inner),
                    ),
                )
            }
            MyLang::List { elems } => MyLangSig::List { elems: elems },
            MyLang::Bool { lit } => MyLangSig::Bool { lit },
            MyLang::Surreal { l, r } => MyLangSig::Surreal { l, r },
            MyLang::If(__inner) => {
                MyLangSig::If(
                    <<IfThenElse<
                        ::egg::Id,
                    > as ::egg_recursive::IntoLanguageChildren>::RawData as ::egg_recursive::Functor>::fmap(
                        |b| *b,
                        <IfThenElse<
                            ::egg::Id,
                        > as ::egg_recursive::IntoLanguageChildren>::unview(__inner),
                    ),
                )
            }
            MyLang::Null => MyLangSig::Null,
        }
    }
    ");
}

#[test]
fn snapshot_to_recursive_impl_sclone() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_recursive_impl_sclone().pretty();
    insta::assert_snapshot!(pat, @r"
    fn sclone<T: Clone>(x: &Self::Container<T>) -> Self::Container<T> {
        match x {
            MyLangSig::Int(__arg_0) => MyLangSig::Int(__arg_0.clone()),
            MyLangSig::Neg(x) => MyLangSig::Neg(x.clone()),
            MyLangSig::Add { args } => {
                MyLangSig::Add {
                    args: args.clone(),
                }
            }
            MyLangSig::And(x) => MyLangSig::And(x.clone()),
            MyLangSig::Wth(__arg_0, __arg_1) => {
                MyLangSig::Wth(__arg_0.clone(), __arg_1.clone())
            }
            MyLangSig::Or(x) => MyLangSig::Or(x.clone()),
            MyLangSig::List { elems } => {
                MyLangSig::List {
                    elems: elems.clone(),
                }
            }
            MyLangSig::Bool { lit } => {
                MyLangSig::Bool {
                    lit: lit.clone(),
                }
            }
            MyLangSig::Surreal { l, r } => {
                MyLangSig::Surreal {
                    l: l.clone(),
                    r: r.clone(),
                }
            }
            MyLangSig::If(x) => MyLangSig::If(x.clone()),
            MyLangSig::Null => MyLangSig::Null,
        }
    }
    ");
}

#[test]
fn snapshot_to_recursive_impl_sig_each_ref() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_recursive_impl_sig_each_ref().pretty();
    insta::assert_snapshot!(pat, @r"
    fn sig_each_ref<T>(
        sig: &::egg_recursive::Signature<Self, T>,
    ) -> ::egg_recursive::Signature<Self, &T> {
        match sig {
            MyLangSig::Int(__self_0) => MyLangSig::Int(::std::clone::Clone::clone(__self_0)),
            MyLangSig::Neg(__inner) => {
                MyLangSig::Neg(
                    <::egg::Id as ::egg_recursive::IntoLanguageChildren>::raw_as_refs(
                        __inner,
                    ),
                )
            }
            MyLangSig::Add { args } => {
                MyLangSig::Add {
                    args: <[::egg::Id; 2usize] as ::egg_recursive::IntoLanguageChildren>::raw_as_refs(
                        args,
                    ),
                }
            }
            MyLangSig::And(__inner) => {
                MyLangSig::And(
                    <[::egg::Id; 2usize] as ::egg_recursive::IntoLanguageChildren>::raw_as_refs(
                        __inner,
                    ),
                )
            }
            MyLangSig::Wth(__self_0, __self_1) => {
                MyLangSig::Wth(
                    ::std::clone::Clone::clone(__self_0),
                    ::std::clone::Clone::clone(__self_1),
                )
            }
            MyLangSig::Or(__inner) => {
                MyLangSig::Or(
                    <BinOpArgs<
                        T,
                    > as ::egg_recursive::IntoLanguageChildren>::raw_as_refs(__inner),
                )
            }
            MyLangSig::List { elems } => {
                MyLangSig::List {
                    elems: <::std::vec::Vec<
                        ::egg::Id,
                    > as ::egg_recursive::IntoLanguageChildren>::raw_as_refs(elems),
                }
            }
            MyLangSig::Bool { lit } => {
                MyLangSig::Bool {
                    lit: ::std::clone::Clone::clone(lit),
                }
            }
            MyLangSig::Surreal { l, r } => {
                MyLangSig::Surreal {
                    l: ::std::clone::Clone::clone(l),
                    r: ::std::clone::Clone::clone(r),
                }
            }
            MyLangSig::If(__inner) => {
                MyLangSig::If(
                    <IfThenElse<
                        T,
                    > as ::egg_recursive::IntoLanguageChildren>::raw_as_refs(__inner),
                )
            }
            MyLangSig::Null => MyLangSig::Null,
        }
    }
    ");
}

#[test]
fn snapshot_to_expr_converters() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_expr_converters().pretty();
    insta::assert_snapshot!(pat, @r"
    impl ::std::convert::From<MyLang> for ::egg::RecExpr<EggMyLang> {
        fn from(x: MyLang) -> Self {
            ::egg_recursive::Recursive::into_rec_expr(x).0
        }
    }
    impl ::std::convert::From<::egg::RecExpr<EggMyLang>> for MyLang {
        fn from(x: ::egg::RecExpr<EggMyLang>) -> Self {
            <MyLang as ::egg_recursive::Recursive>::from_rec_expr(&x, x.root())
        }
    }
    ");
}

#[test]
fn snapshot_to_smart_cons_trait() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_smart_cons_trait().pretty();
    insta::assert_snapshot!(pat, @r"
    ///The smart constructor trait for [`MyLang`]-like types. Generated via `#[derive(Language)]`
    pub trait MyLangCons: Sized {
        fn int(__arg_0: i32) -> Self;
        fn neg(self) -> Self;
        fn add(args: [Self; 2usize]) -> Self;
        fn and(rec_args: [Self; 2usize]) -> Self;
        fn wth(__arg_0: usize, __arg_1: bool) -> Self;
        fn or(rec_args: BinOpArgs<Self>) -> Self;
        fn list(elems: ::std::vec::Vec<Self>) -> Self;
        fn bool(lit: bool) -> Self;
        fn surreal(l: Ordinal, r: Ordinal) -> Self;
        fn if_(rec_args: IfThenElse<Self>) -> Self;
        fn null() -> Self;
    }
    ");
}

#[test]
fn snapshot_to_smart_cons_impl_orig() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_smart_cons_impl_orig().pretty();
    insta::assert_snapshot!(pat, @r"
    impl MyLangCons for MyLang {
        fn int(__arg_0: i32) -> Self {
            Self::Int(__arg_0)
        }
        fn neg(self) -> Self {
            Self::Neg(Box::new(self))
        }
        fn add(args: [Self; 2usize]) -> Self {
            Self::Add {
                args: args.map(Box::new),
            }
        }
        fn and(rec_args: [Self; 2usize]) -> Self {
            Self::And(rec_args.map(Box::new))
        }
        fn wth(__arg_0: usize, __arg_1: bool) -> Self {
            Self::Wth(__arg_0, __arg_1)
        }
        fn or(rec_args: BinOpArgs<Self>) -> Self {
            Self::Or(
                <<BinOpArgs<
                    ::egg::Id,
                > as ::egg_recursive::IntoLanguageChildren>::View as ::egg_recursive::Functor>::fmap(
                    Box::new,
                    rec_args,
                ),
            )
        }
        fn list(elems: ::std::vec::Vec<Self>) -> Self {
            Self::List { elems: elems }
        }
        fn bool(lit: bool) -> Self {
            Self::Bool { lit: lit }
        }
        fn surreal(l: Ordinal, r: Ordinal) -> Self {
            Self::Surreal { l: l, r: r }
        }
        fn if_(rec_args: IfThenElse<Self>) -> Self {
            Self::If(
                <<IfThenElse<
                    ::egg::Id,
                > as ::egg_recursive::IntoLanguageChildren>::View as ::egg_recursive::Functor>::fmap(
                    Box::new,
                    rec_args,
                ),
            )
        }
        fn null() -> Self {
            Self::Null
        }
    }
    ");
}

#[test]
fn snapshot_to_smart_cons_impl_raw_pat() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_smart_cons_impl_raw_pat().pretty();
    insta::assert_snapshot!(pat, @r"
    impl MyLangCons for ::egg_recursive::Pat<MyLang> {
        fn int(__arg_0: i32) -> Self {
            Self::wrap(MyLangSig::Int(__arg_0))
        }
        fn neg(self) -> Self {
            Self::wrap(MyLangSig::Neg(self))
        }
        fn add(args: [Self; 2usize]) -> Self {
            Self::wrap(MyLangSig::Add { args: args })
        }
        fn and(rec_args: [Self; 2usize]) -> Self {
            Self::wrap(MyLangSig::And(rec_args))
        }
        fn wth(__arg_0: usize, __arg_1: bool) -> Self {
            Self::wrap(MyLangSig::Wth(__arg_0, __arg_1))
        }
        fn or(rec_args: BinOpArgs<Self>) -> Self {
            Self::wrap(
                MyLangSig::Or(
                    <BinOpArgs<
                        ::egg::Id,
                    > as ::egg_recursive::IntoLanguageChildren>::unview(rec_args),
                ),
            )
        }
        fn list(elems: ::std::vec::Vec<Self>) -> Self {
            Self::wrap(MyLangSig::List { elems: elems })
        }
        fn bool(lit: bool) -> Self {
            Self::wrap(MyLangSig::Bool { lit: lit })
        }
        fn surreal(l: Ordinal, r: Ordinal) -> Self {
            Self::wrap(MyLangSig::Surreal { l: l, r: r })
        }
        fn if_(rec_args: IfThenElse<Self>) -> Self {
            Self::wrap(
                MyLangSig::If(
                    <IfThenElse<
                        ::egg::Id,
                    > as ::egg_recursive::IntoLanguageChildren>::unview(rec_args),
                ),
            )
        }
        fn null() -> Self {
            Self::wrap(MyLangSig::Null)
        }
    }
    ");
}

#[test]
fn snapshot_to_smart_cons_impl_newtype_pat() {
    let input = lang_def_for_part_snapshot();
    let deriver = LangDeriver::try_new(input).unwrap();
    let pat = deriver.to_smart_cons_impl_newtype_pat().pretty();
    insta::assert_snapshot!(pat, @r"
    impl MyLangCons for MyLangPat {
        fn int(__arg_0: i32) -> Self {
            Self(::egg_recursive::Pat::<MyLang>::int(__arg_0))
        }
        fn neg(self) -> Self {
            Self(::egg_recursive::Pat::<MyLang>::neg(self.0))
        }
        fn add(args: [Self; 2usize]) -> Self {
            Self(::egg_recursive::Pat::<MyLang>::add(args.map(|a| a.0)))
        }
        fn and(rec_args: [Self; 2usize]) -> Self {
            Self(::egg_recursive::Pat::<MyLang>::and(rec_args.map(|a| a.0)))
        }
        fn wth(__arg_0: usize, __arg_1: bool) -> Self {
            Self(::egg_recursive::Pat::<MyLang>::wth(__arg_0, __arg_1))
        }
        fn or(rec_args: BinOpArgs<Self>) -> Self {
            Self(
                ::egg_recursive::Pat::<
                    MyLang,
                >::or(
                    <<BinOpArgs<
                        ::egg::Id,
                    > as ::egg_recursive::IntoLanguageChildren>::View as ::egg_recursive::Functor>::fmap(
                        |x| x.0,
                        rec_args,
                    ),
                ),
            )
        }
        fn list(elems: ::std::vec::Vec<Self>) -> Self {
            Self(
                ::egg_recursive::Pat::<
                    MyLang,
                >::list(elems.into_iter().map(|x| x.0).collect::<Vec<_>>()),
            )
        }
        fn bool(lit: bool) -> Self {
            Self(::egg_recursive::Pat::<MyLang>::bool(lit))
        }
        fn surreal(l: Ordinal, r: Ordinal) -> Self {
            Self(::egg_recursive::Pat::<MyLang>::surreal(l, r))
        }
        fn if_(rec_args: IfThenElse<Self>) -> Self {
            Self(
                ::egg_recursive::Pat::<
                    MyLang,
                >::if_(
                    <<IfThenElse<
                        ::egg::Id,
                    > as ::egg_recursive::IntoLanguageChildren>::View as ::egg_recursive::Functor>::fmap(
                        |x| x.0,
                        rec_args,
                    ),
                ),
            )
        }
        fn null() -> Self {
            Self(::egg_recursive::Pat::<MyLang>::null())
        }
    }
    ");
}
