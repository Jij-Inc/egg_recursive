//! This crate provides a recursive interface to [`egg`].
//!
//! [`egg`] alrady comes with S-expression-based interface, but it has the following drawbacks:
//!
//! - It uses [`std::str::FromStr`] and [`std::fmt::Display`] to parse/format textual representation of ASTs.
//!     + These CAN be used for other purposes and this can cause a conflict with other applications.
//! - Parser favours the first clause for terminal variants with the same parameter.
//!     + This can result in unexpected behaviour under the existence of ambiguity.
//! - ALL textual representation of ASTs fed to [`egg::rewrite`] is checked at RUNTIME.
//!     + This means we can't see syntax error until compilation;
//!     + This further complicates the debugging process.
//! - S-expressions get harder and harder to be parsed by human eyes
//!
//! This crate alleviates these problems by introducing a recursive interface to [`egg`].
//!
//! ## Abstraction over Language
//!
//! You can define a recursive language as a ordinary `Self`-referencing enum,
//! containing [`Box`]es, [`[Self; N]`], or [`Vec`]s or other terminal other types.
//! Such language AST must implement [`Recursive`] trait and have a [`Signature`] type synonym.
//! This also provides [`Pat<L>`] for pattern matching, which can be converted to/from [`Pattern<AsLanguage<L>>`].
//! We are providing a [`Language`] derive macro for automatically derive such types and impls.
//!
//! ```rust
//! use egg::*;
//! use egg_recursive::*;
//!
//! #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Language)]
//! pub enum Arith {
//!     Num(i32),
//!     Neg(Box<Self>),
//!     Add([Box<Self>; 2]),
//!     Mul([Box<Self>; 2]),
//! }
//! ```
//!
//! This generates the following entities:
//!
//! 1. `Recursive` impl for `Arith`;
//!     - You can convert from/to [`RecExpr<Signature<Arith, Id>>`] with [`From`] instances or [`Recursive::into_rec_expr`]/[`Recursive::from_rec_expr`].
//! 2. `EggArith` type alias for `Signature<Arith, Id>`, which implements [`egg::Language`];
//! 3. `ArithPat` type for recursive pattern ASTs.
//!     + It already implements [`egg::Searcher`] and [`egg::Applier`].
//!     + This is indeed a newtype wrapper of [`Pat<AsLanguage<Arith>>`].
//!         - We provide this as a newtype to allow (otherwise ophan) impls of utility traits for [`Pat`]s, (e.g. [`std::ops::Add`], [`std::ops::Mul`], etc).
//!     + This can be converted to/from [`egg::Pattern<EggArith>`] with [`From`] instances.
//! 4. `ArithCons` trait, which provides smart constructors for `Arith` and `ArithPat`s.
//!     + `ArithCons` has trait methods like `num(i64)`, `add([Self; 2])`, `mul([Self; 2])`, `neg(Self)`, etc. It has just snake_cased variant of the original enum variants. If the snake_case version is reserved keyword, suffixed with `_` (e.g. `If` becomes `if_()`).
//!
//! An `enum` passed to [`self::Language`] should satisfy the following conditions:
//!
//! 1. It MUST NOT have any generic parameters.
//! 2. Recursive variants MUST have only one field, which is one of the following (in any case, the type itself MUST be referenced by `Self`, not a enum name itself):
//!    + `Box<Self>`,
//!    + `[Box<Self>; N]`,
//!    + `Vec<Self>`,
//!    + `T<Box<Self>>` for some [`IntoLanguageChildren`] type `T` (described in the next section).
//! 3. Arguments to the non-recursive variants MUST implement at least [`Eq`], [`Ord`], [`Hash`], and [`Clone`].
//!
//! ## Helper Types for [`egg::LanguageChildren`]
//!
//! Sometimes, the more the [`LanguageChildren`] has a components, the harder to get memorise the order/semantics of components.
//! To alleviates this situation, we introduce [`IntoLanguageChildren`] trait, which abstracts over view types of [`egg::LanguageChildren`].
//!
//! You don't have to write it manually and it can generally be derived by [`self::LanguageChildren`] derive macro.
//!
//! Suppose we want to add boolean operations and if-expressions:
//!
//! ```rust
//! use egg::*;
//! use egg_recursive::*;
//!
//! #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, LanguageChildren)]
//! pub struct IfThenElse<T> {
//!     pub cond: T,
//!     pub then_branch: T,
//!     pub else_branch: T,
//! }
//!
//! #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Language)]
//! pub enum Arith {
//!     Num(i32),
//!     Bool(bool),
//!     Neg(Box<Self>),
//!     Add([Box<Self>; 2]),
//!     Mul([Box<Self>; 2]),
//!     IsZero(Box<Self>),
//!     If(IfThenElse<Box<Self>>),
//! }
//! ```
//!
//! This generates `RawIfThenElse` and [`IntoLanguageChildren`] instance to convert it to [`LanguageChildren`].
//! You can call either `IfThenElse::view` or `RawIfThenElse::unview` to convert it to/from `RawIfThenElse`.
//!
//! [`egg::LanguageChildren`] macro accepts types with the following conditions:
//!
//! 1. It MUST be a struct with exactly one generic parameter.
//! 2. Every field must be one of the following (where `T` its only parameter):
//!     + `T`,
//!     + [`[T; N]`], or
//!     + [`Vec<T>`],
//! 3. AT MOST ONE [`Vec<T>`] is allowed in its field.
//!
//! ## Writing Rewrite Rules
//!
//! `egg_recursive` provides a redefined [`rewrite!`] macro to write rewrite rules.
//! This is almost the same as the original [`egg::rewrite!`] macro, but it allows you to write conditions in a more readable way.
//! Due to the ambiguity issue, it doesn't support bidirectional rules (`<=>`) for the time being.
//!
//! The following illustrates the usage of the macro:
//!
//! ```ignore
//! pub fn make_rules() -> Vec<Rewrite<EggArith, ConstantFold>> {
//!     let v = |s: &str| ArithPat::pat_var(s);
//!     let x = || v("x");
//!     let y = || v("y");
//!     let x_var: Var = "?x".parse().unwrap();
//!     vec![
//!         rewrite!("add-comm"; x() + y() => y() + x()),
//!         rewrite!("mul-comm"; x() * y() => y() * x()),
//!         rewrite!("add-zero"; x() + ArithPat::float(0.0.into()) => x()),
//!         rewrite!("add-zero"; x() => x() + ArithPat::float(0.0.into())),
//!         rewrite!("mul-inv";
//!             x() * x().inv() => ArithPat::float(1.0.into())
//!         ;   if is_non_zero(x_var.clone())
//!         ),
//!     ]
//! }
//! ```
//!
//! In the above, `+` and `*` comes from `std::ops::Add` and `std::ops::Mul`  instances defined manually,
//! which is possible because `ArithPat` is a newtype, but not an alias.
//!
use std::borrow::Cow;

use egg::*;
pub use egg_recursive_derive::*;
pub use functo_rs::data::Functor;
use functo_rs::data::{ArrayFunctor, Identity, UndetVec};

/// A type synonym for `L::Container<T>`,
/// which corresponds to primitive terms of `L` with parameters in `T`.
pub type Signature<L, T> = <L as Functor>::Container<T>;

/// A type synonym for [`Signature<L, Id>`], which should be an egg [`Language`].
pub type AsLanguage<L> = <L as Functor>::Container<Id>;

/// A recursive language, which can be converted to and from a [`RecExpr`].
///
/// In this case, `<Self as Functor>::Container<T>` plays a role of a language signature of language `L`, that is, primitive terms with parameters `T`
/// (hence the synonym [`Signature<L, T>`]).
/// Corresponding [`Language`] in egg must be [`AsLanguage<Self>`] (e.g. [`Signature<L, Id>`]).
pub trait Recursive: Functor + Sized
where
    AsLanguage<Self>: Language,
{
    /// Unwraps a recursion by one-level.
    fn unwrap(self) -> Signature<Self, Self>;

    /// Wraps a recursion by one-level.
    fn wrap(inner: Signature<Self, Self>) -> Self;

    /// Structural clone
    fn sclone<T: Clone>(sig: &Signature<Self, T>) -> Signature<Self, T>;

    /// Converts a reference to a signature into a signature of references.
    fn sig_each_ref<T>(refs: &Signature<Self, T>) -> Signature<Self, &T>;

    /// Adds into an existing [`RecExpr`] and returns the id of the root node.
    fn add_into_rec_expr(self, expr: &mut RecExpr<Signature<Self, Id>>) -> Id
where {
        let graph = Self::fmap(|e| e.add_into_rec_expr(expr), self.unwrap());
        expr.add(graph)
    }

    /// Converts into a [`RecExpr`].
    fn into_rec_expr(self) -> (RecExpr<Signature<Self, Id>>, Id) {
        let mut expr = RecExpr::default();
        let id = self.add_into_rec_expr(&mut expr);
        (expr, id)
    }

    /// Converts from a [`RecExpr`].
    fn from_rec_expr(expr: &RecExpr<Signature<Self, Id>>, id: Id) -> Self {
        Self::wrap(Self::fmap(
            |e| Self::from_rec_expr(expr, e),
            expr[id].clone(),
        ))
    }
}

/// Recursive AST for patterns in language `L`.
/// This can be converted to/from [`Pattern<AsLanguage<L>>`].
///
/// User can also define [`From<L> for Pat<L>`] for concrete `L` with [`Self::wrap`].
///
/// [`Language`] derive macro will genrate a newtype wrapper of this type, which implements [`egg::Searcher`] and [`egg::Applier`] too, and it can have (otherwise orphan) custom instances.
pub enum Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    /// Variable in pattern.
    PatVar(Var),
    /// Recursive pattern.
    Wrap(Signature<L, Box<Pat<L>>>),
}

impl<L> Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn add_vars_to(&self, vars: &mut Vec<Var>) {
        match self {
            Self::PatVar(v) => {
                if !vars.contains(v) {
                    vars.push(*v)
                }
            }
            Self::Wrap(w) => {
                L::fmap(|e| e.add_vars_to(vars), L::sig_each_ref(w));
            }
        }
    }
}

impl<L, N> egg::Searcher<AsLanguage<L>, N> for Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
    N: Analysis<AsLanguage<L>>,
{
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<AsLanguage<L>, N>,
        eclass: Id,
        limit: usize,
    ) -> Option<::egg::SearchMatches<AsLanguage<L>>> {
        use ::egg::*;
        let pat: Pattern<AsLanguage<L>> = Pattern::from(self);
        let SearchMatches {
            eclass,
            substs,
            ast,
        } = pat.search_eclass_with_limit(egraph, eclass, limit)?;
        Some(SearchMatches {
            eclass,
            substs,
            ast: ast.map(|cow| Cow::Owned(cow.into_owned())),
        })
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = Vec::new();
        self.add_vars_to(&mut vars);
        vars
    }
}

impl<L, N> egg::Applier<AsLanguage<L>, N> for Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
    N: Analysis<AsLanguage<L>>,
{
    fn apply_one(
        &self,
        egraph: &mut EGraph<AsLanguage<L>, N>,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<AsLanguage<L>>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        Pattern::from(self).apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }
}

impl<L> Clone for Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn clone(&self) -> Self {
        match self {
            Self::PatVar(arg0) => Self::PatVar(*arg0),
            Self::Wrap(arg0) => Self::Wrap(L::sclone(arg0)),
        }
    }
}

impl<L> Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    /// Smart constructor for a variable.
    /// NOTE: this DOES NOT require `?`-prefix before the identifier.
    pub fn pat_var<'a, S: Into<Cow<'a, str>>>(v: S) -> Self {
        Self::PatVar(format!("?{}", v.into()).parse().unwrap())
    }

    /// Unwraps the pattern recursion by one layer.
    pub fn unwrap(self) -> ENodeOrVar<Signature<L, Self>> {
        match self {
            Pat::PatVar(v) => ENodeOrVar::Var(v),
            Pat::Wrap(w) => ENodeOrVar::ENode(L::fmap(|e| *e, w)),
        }
    }

    /// Wraps the pattern recursion by one layer.
    pub fn wrap(inner: Signature<L, Self>) -> Self {
        Pat::Wrap(L::fmap(Box::new, inner))
    }
}

impl<L> From<Var> for Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn from(value: Var) -> Self {
        Self::PatVar(value)
    }
}

impl<L> From<L> for Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn from(value: L) -> Self {
        Self::Wrap(L::fmap(|e| Box::new(e.into()), value.unwrap()))
    }
}

impl<L> Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    /// Convert a recursive pattern into a [`PatternAst<L>`].
    /// See also: [`Self::to_pattern_ast`].
    pub fn into_pattern_ast(self) -> PatternAst<AsLanguage<L>> {
        let mut ast = PatternAst::default();
        self.add_into_pattern_ast(&mut ast);
        ast
    }

    /// Convert a borrowed recursive pattern to a [`PatternAst<L>`].
    /// See also: [`Self::into_pattern_ast`].
    pub fn to_pattern_ast(&self) -> PatternAst<AsLanguage<L>> {
        let mut ast = PatternAst::default();
        self.add_to_pattern_ast(&mut ast);
        ast
    }

    /// Convert a [`PatternAst<L>`] into a recursive pattern.
    pub fn from_pattern_ast(ast: &PatternAst<AsLanguage<L>>, id: Id) -> Self {
        match &ast[id] {
            ENodeOrVar::Var(v) => Pat::PatVar(*v),
            ENodeOrVar::ENode(e) => Pat::Wrap(L::fmap(
                |e| Box::new(Pat::<L>::from_pattern_ast(ast, e)),
                e.clone(),
            )),
        }
    }

    /// Adds the pattern into an existing [`PatternAst`] and returns the id of the root node. See also: [`Self::into_pattern_ast`], [`Self::add_to_pattern_ast`].
    pub fn add_into_pattern_ast(self, ast: &mut PatternAst<AsLanguage<L>>) -> Id {
        match self {
            Pat::PatVar(v) => ast.add(ENodeOrVar::Var(v)),
            Pat::Wrap(w) => {
                let graph = L::fmap(|e| e.add_into_pattern_ast(ast), w);
                ast.add(ENodeOrVar::ENode(graph))
            }
        }
    }

    /// Adds the borrowed pattern into an existing [`PatternAst`] and returns the id of the root node. See also: [`Self::to_pattern_ast`], [`Self::add_into_pattern_ast`].
    pub fn add_to_pattern_ast(&self, ast: &mut PatternAst<AsLanguage<L>>) -> Id {
        match self {
            Pat::PatVar(v) => ast.add(ENodeOrVar::Var(*v)),
            Pat::Wrap(w) => {
                let graph = L::fmap(|e| e.add_to_pattern_ast(ast), L::sig_each_ref(w));
                ast.add(ENodeOrVar::ENode(graph))
            }
        }
    }
}

impl<L> From<Pat<L>> for PatternAst<AsLanguage<L>>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn from(value: Pat<L>) -> Self {
        value.into_pattern_ast()
    }
}

impl<L> From<&Pat<L>> for PatternAst<AsLanguage<L>>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn from(value: &Pat<L>) -> Self {
        value.to_pattern_ast()
    }
}

impl<L> From<&Pat<L>> for Pattern<AsLanguage<L>>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn from(value: &Pat<L>) -> Self {
        Pattern::new(value.to_pattern_ast())
    }
}

impl<L> From<PatternAst<AsLanguage<L>>> for Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn from(value: PatternAst<AsLanguage<L>>) -> Self {
        let root = value.root();
        Pat::from_pattern_ast(&value, root)
    }
}

impl<L> From<Pat<L>> for Pattern<AsLanguage<L>>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn from(value: Pat<L>) -> Self {
        Pattern::new(value.into_pattern_ast())
    }
}

impl<L> From<Pattern<AsLanguage<L>>> for Pat<L>
where
    L: Recursive,
    AsLanguage<L>: Language,
{
    fn from(value: Pattern<AsLanguage<L>>) -> Self {
        Pat::from(value.ast)
    }
}

pub type LangChildren<T> = <<T as IntoLanguageChildren>::RawData as Functor>::Container<Id>;

pub type RawData<T, U> = <<T as IntoLanguageChildren>::RawData as Functor>::Container<U>;

pub type View<T, U> = <<T as IntoLanguageChildren>::View as Functor>::Container<U>;

/// A trait for a type that can be converted from/to [`egg::LanguageChildren`].
/// [`Self::RawData`] must be a [`egg::LanguageChildren`].
///
/// This can be derived by [`self::LanguageChildren`] derive macro.
pub trait IntoLanguageChildren: Sized
where
    Self::View: Functor<Container<Self::Param> = Self>,
    Self::RawData: Functor,
    <Self::RawData as Functor>::Container<Id>: LanguageChildren,
{
    /// Parameter type (e.g. `T` for `Vec<T>`)
    type Param;
    /// View type, which has a descriptive field name.
    type View;
    /// Raw [`egg::LanguageChildren`] type, which is typiacally a fixed-length array,
    /// [`Vec`], [`egg::Id`], or their newtype-wrapper.
    type RawData;

    /// Converts [`egg::LanguageChildren`] into a view type.
    fn view<T>(children: RawData<Self, T>) -> View<Self, T>;

    /// Converts a view into [`egg::LanguageChildren`].
    fn unview<T>(children: View<Self, T>) -> RawData<Self, T>;

    /// Maps a view by a function.
    fn map<U>(self, f: impl FnMut(Self::Param) -> U) -> View<Self, U> {
        <Self::View as Functor>::fmap(f, self)
    }

    /// Converts a reference to a [`egg::LanguageChildren`] into a reference to a view.
    fn raw_as_refs<T>(refs: &RawData<Self, T>) -> RawData<Self, &T>;
}

impl<T> IntoLanguageChildren for Vec<T> {
    type View = UndetVec;
    type Param = T;
    type RawData = UndetVec;

    #[inline(always)]
    fn view<U>(children: Vec<U>) -> Vec<U> {
        children
    }

    #[inline(always)]
    fn unview<U>(children: Vec<U>) -> Vec<U> {
        children
    }

    #[inline(always)]
    fn raw_as_refs<U>(refs: &Vec<U>) -> Vec<&U> {
        refs.iter().collect()
    }
}

impl<T, const N: usize> IntoLanguageChildren for [T; N] {
    type View = ArrayFunctor<N>;
    type Param = T;
    type RawData = ArrayFunctor<N>;

    #[inline(always)]
    fn view<U>(children: [U; N]) -> [U; N] {
        children
    }

    #[inline(always)]
    fn unview<U>(children: [U; N]) -> [U; N] {
        children
    }

    #[inline(always)]
    fn raw_as_refs<U>(refs: &[U; N]) -> [&U; N] {
        refs.each_ref()
    }
}

impl IntoLanguageChildren for Id {
    type View = Identity;
    type Param = Id;
    type RawData = Identity;

    #[inline(always)]
    fn view<T>(children: T) -> T {
        children
    }

    #[inline(always)]
    fn unview<T>(children: T) -> T {
        children
    }

    #[inline(always)]
    fn raw_as_refs<T>(refs: &T) -> &T {
        refs
    }
}

#[macro_export]
macro_rules! rewrite {
    (
        $name:expr;
        $lhs:expr => $rhs:expr
    )  => {{
        let searcher = ::egg::Pattern::from($lhs);
        let applier = ::egg::Pattern::from($rhs);
        ::egg::Rewrite::new($name.to_string(), searcher, applier).unwrap()
    }};
    (
        $name:expr;
        $lhs:expr => $rhs:expr;
        $(if $cond:expr)*
    )  => {{
        let searcher = ::egg::Pattern::from($lhs);
        let core_applier = ::egg::Pattern::from($rhs);
        let applier = ::egg::__rewrite!(@applier core_applier; $($cond,)*);
        ::egg::Rewrite::new($name.to_string(), searcher, applier).unwrap()
    }};
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    #[test]
    fn test_invalid_language_derivations() {
        let t = trybuild::TestCases::new();
        let mut chs = fs::read_dir(Path::new("tests").join("invalid").join("language"))
            .unwrap()
            .flatten()
            .filter(|p| p.path().extension() == Some("rs".as_ref()))
            .collect::<Vec<_>>();
        chs.sort_by_key(|p| p.file_name());
        for entry in chs {
            t.compile_fail(entry.path());
        }
    }

    #[test]
    fn test_success() {
        let t = trybuild::TestCases::new();
        let mut chs = fs::read_dir(Path::new("tests").join("success"))
            .unwrap()
            .flatten()
            .filter(|p| p.path().extension() == Some("rs".as_ref()))
            .collect::<Vec<_>>();
        chs.sort_by_key(|p| p.file_name());
        for entry in chs {
            t.pass(entry.path());
        }
    }
}
