use egg_recursive::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Language)]
pub enum InvalidSelfLang {
    Int(i64),
    Add(i64, i64),
    Mul(i64, Box<Self>),
}

fn main() {
    println!("Hello, world!");
}
