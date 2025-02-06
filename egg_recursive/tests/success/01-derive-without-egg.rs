#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, egg_recursive::LanguageChildren)]
pub struct BinOp<T> {
    lhs: T,
    rhs: T,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, egg_recursive::LanguageChildren)]
pub struct IfThenElse<T> {
    cond: T,
    then: T,
    else_: T,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, egg_recursive::Language)]
pub enum ArithExpr {
    Int(i64),
    Bool(bool),
    Neg(Box<Self>),
    Inv(Box<Self>),
    Add(BinOp<Box<Self>>),
    Mul(BinOp<Box<Self>>),
    IsZero(Box<Self>),
    If(IfThenElse<Box<Self>>),
    List(Vec<Self>),
}

fn main() {}
