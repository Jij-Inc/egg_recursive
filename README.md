# egg_recursive ![badge](https://github.com/Jij-Inc/egg_recursive/actions/workflows/test.yml/badge.svg)

An S-expression-free, alternative interface for [`egg`][egg].

| crate name | crates.io | docs.rs |
| --- | --- | --- |
| [egg_recursive] | [![crate](https://img.shields.io/crates/v/egg_recursive.svg)](https://crates.io/crates/egg_recursive)  | [![docs.rs](https://docs.rs/egg_recursive/badge.svg)](https://docs.rs/egg_recursive) |
| [egg_recursive_derive] | [![crate](https://img.shields.io/crates/v/egg_recursive_derive.svg)](https://crates.io/crates/egg_recursive_derive)  | [![docs.rs](https://docs.rs/egg_recursive_derive/badge.svg)](https://docs.rs/egg_recursive_derive) |

## Overview

This crate provides a recursive interface to [`egg`][egg].

[`egg`][egg] alrady comes with S-expression-based interface, but it has the following drawbacks:

- It uses `FromStr` and `Display` to parse/format textual representation of ASTs.
  + These CAN be used for other purposes and this can cause a conflict with other applications.
- Parser favours the first clause for terminal variants with the same parameter.
  + This can result in unexpected behaviour under the existence of ambiguity.
- ALL textual representation of ASTs fed to `rewrite` is checked at RUNTIME.
  + This means we can't see syntax error until compilation;
  + This further complicates the debugging process.
- S-expressions get harder and harder to be parsed by human eyes

This crate alleviates these problems by introducing a recursive interface to [`egg`][egg].

[egg]: https://egraphs-good.github.io/

## Example Usage

See [API document](https://docs.rs/egg_recursive/latest) for details.

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, LanguageChildren)]
pub struct IfThenElse<T> {
    cond: T,
    then: T,
    else_: T,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Language)]
pub enum ArithExpr {
    Var(String),
    Int(i64),
    Bool(bool),
    Neg(Box<Self>),
    Inv(Box<Self>),
    Add([Box<Self>; 2]),
    Mul([Box<Self>; 2]),
    IsZero(Box<Self>),
    If(IfThenElse<Box<Self>>),
}

impl From<i64> for ArithExprPat {
    fn from(i: i64) -> Self {
        Self::int(i)
    }
}

impl From<bool> for ArithExprPat {
    fn from(b: bool) -> Self {
        Self::bool(b)
    }
}

impl ::std::ops::Add for ArithExprPat {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        <Self as ArithExprCons>::add([self, other])
    }
}

impl ::std::ops::Neg for ArithExprPat {
    type Output = Self;
    fn neg(self) -> Self {
        <Self as ArithExprCons>::neg(self)
    }
}

impl ::std::ops::Sub for ArithExprPat {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self + other.neg()
    }
}

impl ::std::ops::Mul for ArithExprPat {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        <Self as ArithExprCons>::mul([self, other])
    }
}

pub fn make_rules() -> Vec<Rewrite<EggArithExpr, ConstantFold>> {
    use ArithExprPat as Pat;
    let v = |s: &str| Pat::pat_var(s);
    let x = || v("x");
    let y = || v("y");
    let p = || v("p");
    let x_var = || "?x".parse::<Var>().unwrap();
    vec![
        rw!("add-comm"; x() + y() => y() + x()),
        rw!("mul-comm"; x() * y() => y() * x()),
        rw!("add-zero"; x() + Pat::float(0.into()) => x()),
        rw!("add-zero"; x() => x() + Pat::float(0.into())),
        rw!("mul-inv";
            x() * x().inv() => Pat::float(1.into())
        ;   if is_non_zero(x_var())
        ),
        rw!("is-zero-zero"; Pat::is_zero(0.into()) => true),
        rw!("if-true"; Pat::if_(IfThenElse{cond: true.into(),  then: x(), else_: v()}) => x()),
        rw!("if-false"; Pat::if_(IfThenElse{cond: false.into(),  then: x(), else_: v()}) => y()),
    ]
}
```

## License

(c) 2024- Jij Inc.

This project is licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.
