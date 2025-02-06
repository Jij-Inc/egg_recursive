use egg::*;
use egg_recursive::{rewrite as rw, *};
use ordered_float::OrderedFloat;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, LanguageChildren)]
pub struct IfThenElse<T> {
    cond: T,
    then: T,
    else_: T,
}

#[test]
fn test_if_then_else() {
    let a = IfThenElse {
        cond: 1usize,
        then: 2,
        else_: 3,
    }
    .map(Id::from);
    let viewed = a.clone().unview();
    assert_eq!(&viewed, &RawIfThenElse([1, 2, 3].map(Id::from)));
    assert_eq!(viewed.view(), a);
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, LanguageChildren)]
pub struct AtLeastThree<T> {
    pub head: T,
    pub tail: Vec<T>,
    pub penultimate: T,
    pub last: T,
}

#[test]
fn test_at_least_three() {
    let a = AtLeastThree {
        head: 1usize,
        tail: vec![2, 3],
        penultimate: 4,
        last: 5,
    }
    .map(Id::from);
    let viewed = a.clone().unview();
    assert_eq!(
        &viewed,
        &RawAtLeastThree([1, 2, 3, 4, 5].into_iter().map(Id::from).collect())
    );
    assert_eq!(viewed.view(), a);
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, LanguageChildren)]
pub struct BinOpArgs<T> {
    pub left: T,
    pub right: T,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Language)]
pub enum ArithExpr {
    Var(String),
    Float(OrderedFloat<f64>),
    Bool(bool),
    Neg(Box<Self>),
    Inv(Box<Self>),
    Add([Box<Self>; 2]),
    Mul([Box<Self>; 2]),
    IsZero(Box<Self>),
    If(IfThenElse<Box<Self>>),
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

    #[allow(clippy::suspicious_arithmetic_impl)]
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

impl ::std::ops::Add for ArithExpr {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        <Self as ArithExprCons>::add([self, other])
    }
}

impl ::std::ops::Neg for ArithExpr {
    type Output = Self;
    fn neg(self) -> Self {
        <Self as ArithExprCons>::neg(self)
    }
}

impl ::std::ops::Sub for ArithExpr {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, other: Self) -> Self {
        self + other.neg()
    }
}

impl ::std::ops::Mul for ArithExpr {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        <Self as ArithExprCons>::mul([self, other])
    }
}

pub fn make_rules() -> Vec<Rewrite<EggArithExpr, ConstantFold>> {
    let v = |s: &str| ArithExprPat::pat_var(s);
    let x = || v("x");
    let y = || v("y");
    let x_var = || "?x".parse::<Var>().unwrap();
    vec![
        rw!("add-comm"; x() + y() => y() + x()),
        rw!("mul-comm"; x() * y() => y() * x()),
        rw!("add-zero"; x() + ArithExprPat::float(0.0.into()) => x()),
        rw!("add-zero"; x() => x() + ArithExprPat::float(0.0.into())),
        rw!("mul-inv";
            x() * x().inv() => ArithExprPat::float(1.0.into())
        ;   if is_non_zero(x_var())
        ),
    ]
}

#[test]
fn test() {
    let expr = ArithExpr::float(2.0.into()).inv() * ArithExpr::float(2.0.into());
    let mut runner = Runner::<EggArithExpr, _, _>::default();
    let id = runner.egraph.add_expr(&expr.into());
    let runner = runner.run(&make_rules());
    let data = runner.egraph[id].data.clone();
    assert_eq!(data, Some(Value::Float(1.0.into())));
}

#[derive(Debug, Default)]
pub struct ConstantFold {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Value {
    Float(OrderedFloat<f64>),
    Bool(bool),
}

impl Analysis<EggArithExpr> for ConstantFold {
    type Data = Option<Value>;

    fn make(egraph: &mut EGraph<EggArithExpr, Self>, enode: &EggArithExpr) -> Self::Data {
        use ArithExprSig::*;
        match enode {
            Var(_) => None,
            Float(f) => Some(Value::Float(*f)),
            Bool(b) => Some(Value::Bool(*b)),
            Neg(a) => {
                let a = egraph[*a].data.as_ref();
                match a {
                    Some(Value::Float(f)) => Some(Value::Float(-f)),
                    _ => None,
                }
            }
            Inv(a) => {
                let a = egraph[*a].data.as_ref();
                match a {
                    Some(Value::Float(f)) => Some(Value::Float(OrderedFloat::from(1.0) / f)),
                    _ => None,
                }
            }
            Add([a, b]) => {
                let a = egraph[*a].data.as_ref();
                let b = egraph[*b].data.as_ref();
                match (a, b) {
                    (Some(Value::Float(a)), Some(Value::Float(b))) => {
                        Some(Value::Float((a.into_inner() + b.into_inner()).into()))
                    }
                    _ => None,
                }
            }
            Mul([a, b]) => {
                let a = egraph[*a].data.as_ref();
                let b = egraph[*b].data.as_ref();
                match (a, b) {
                    (Some(Value::Float(a)), Some(Value::Float(b))) => {
                        Some(Value::Float((a.into_inner() * b.into_inner()).into()))
                    }
                    _ => None,
                }
            }
            IsZero(a) => {
                let a = egraph[*a].data.as_ref();
                match a {
                    Some(Value::Float(f)) => Some(Value::Bool(f.into_inner() == 0.0)),
                    _ => None,
                }
            }
            If(ifte) => {
                let IfThenElse { cond, then, else_ } = ifte.view();
                let cond = egraph[cond].data.as_ref();
                let then = egraph[then].data.as_ref();
                let else_ = egraph[else_].data.as_ref();
                match (cond, then, else_) {
                    (Some(Value::Bool(true)), Some(v), _) => Some(v.clone()),
                    (Some(Value::Bool(false)), _, Some(v)) => Some(v.clone()),
                    _ => None,
                }
            }
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        merge_option(a, b, merge_min)
    }
}

type Tester =
    Box<dyn Fn(&mut EGraph<EggArithExpr, ConstantFold>, &Subst) -> bool + Send + Sync + 'static>;
pub struct FloatTest(Tester);
impl FloatTest {
    pub fn new<F>(var: Var, f: F) -> Self
    where
        F: Fn(f64) -> bool + Send + Sync + 'static,
    {
        FloatTest(Box::new(
            move |egraph: &mut egg::EGraph<EggArithExpr, ConstantFold>, subst: &Subst| {
                matches!(
                    egraph[subst[var]].data,
                    Some(Value::Float(i)) if f(f64::from(i))
                )
            },
        ))
    }
}

impl Condition<EggArithExpr, ConstantFold> for FloatTest {
    fn check(
        &self,
        egraph: &mut egg::EGraph<EggArithExpr, ConstantFold>,
        _root: Id,
        subst: &Subst,
    ) -> bool {
        self.0(egraph, subst)
    }
}

pub fn is_non_zero(v: Var) -> FloatTest {
    FloatTest::new(v, |x| x != 0.0)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ordinal {
    Z,
    Succ(Box<Self>),
    Lim(Vec<Self>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Language)]
pub enum MyLang {
    Int(i32),
    Neg(Box<Self>),
    Add { args: [Box<Self>; 2] },
    And([Box<Self>; 2]),
    Wth(usize, bool),
    Or(BinOpArgs<Box<Self>>),
    IsZero(Box<Self>),
    IfThenElse(IfThenElse<Box<Self>>),
    List { elems: Vec<Self> },
    Bool { lit: bool },
    Surreal { l: Ordinal, r: Ordinal },
    Null,
}
