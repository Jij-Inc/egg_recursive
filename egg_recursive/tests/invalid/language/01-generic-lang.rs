use egg_recursive::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Language)]
pub enum GenericLang<T> {
    Int(i64),
    Param(T),
}

fn main() {
    println!("Hello, world!");
}
