use proc_macro::TokenStream as TokenStream1;

mod children;
mod language;
mod macros;

#[cfg(test)]
mod test_utils;

/// The macro to derive `Recursive` and corresponding `Language`, `Patterns`
/// and smart constructor traits for a given recursive AST.
///
/// The type passed to [`Language`] must satisfy the following conditions:
///
/// 1. It MUST NOT have any generic parameters.
/// 2. It MUST be an enum.
/// 3. Recursive variants MUST mention itself by `Self`, not the concrete name.
/// 4. Recursive variants MUST have exactly on fields with one of the following type:
///     - `Box<Self>`
///     - `[Box<Self>; N]` for constant `N`
///     - `Vec<Self>`
///     - `T<Box<Self>>` for `T: IntoLanguageChildren`.
/// 5. Non-recursive variants MUST NOT mention the type itself, and all the arguments must implement [`Eq`], [`Ord`], [`Hash`], and [`Clone`].
#[proc_macro_derive(Language)]
pub fn derive_language(input: TokenStream1) -> TokenStream1 {
    language::derive(input.into()).into()
}

/// The macro to define a view type for a `LanguageChildren` and conversion mechanisms.
///
/// The type passed to [`LanguageChildren`] must satisfy the following conditions:
///
/// 1. It MUST have exactly one generic parameter.
/// 2. It MUST be a struct.
/// 3. It MUST have at least one field with one of the following types (where `T` parameter):
///     - `T`
///     - `[T; N]`
///     - `Vec<T>`
/// 4. `Vec<T>` can appear AT MOST ONCE.
#[proc_macro_derive(LanguageChildren)]
pub fn derive_language_children(input: TokenStream1) -> TokenStream1 {
    children::derive(input.into()).into()
}
