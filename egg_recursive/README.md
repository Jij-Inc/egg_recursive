# `egg_recursive` - Recursive interface for [`egg`](https://egraphs-good.github.io/)

This crate provides a recursive interface to `egg`.
`egg` alrady comes with S-expression-based interface, but it has the following drawbacks:

- It uses [`std::str::FromStr`] and [`std::fmt::Display`] to parse/format textual representation of ASTs.
  + These CAN be used for other purposes and this can cause a conflict with other applications.
- Parser favours the first clause for terminal variants with the same parameter.
  + This can result in unexpected behaviour under the existence of ambiguity.
- ALL textual representation of ASTs fed to [`egg::rewrite`] is checked at RUNTIME.
  + This means we can't see syntax error until compilation;
  + This further complicates the debugging process.
- S-expressions get harder and harder to be parsed by human eyes

This crate alleviates these problems by introducing a recursive interface to [`egg`].
