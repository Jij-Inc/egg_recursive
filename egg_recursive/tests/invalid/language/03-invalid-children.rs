use egg_recursive::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, LanguageChildren)]
pub struct Bin<T> {
    l: T,
    r: T,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Language)]
pub enum InvalidSelfLang {
    Int(i64),
    Add(Box<Bin<Self>>),
}

fn main() {
    println!("Hello, world!");
}
