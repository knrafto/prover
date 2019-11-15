The core language is based on univalent type theory (see HoTT book).

# Lexical structure

Whitespace are space, tab, newline, carriage return, form feed, and vertical
tab. Line comments start with `--`. Block comments are delimited with `{-` and
`-}`.

TODO: allow nested block comments.

The symbols `(`, `)`, and `,` are "punctuation", and are always treated as a
token by themselves.

Any other contiguous sequence of non-whitespace, non-punctuation Unicode
characters is a "word". The following words are reserved, and are treated
specially in the syntax:

```
_
:
:=
=
→
×
Σ
Π
λ
Type
define
assume
prove
```

# Grammar

```
module = [ statement ]*

statement =
    define name [ params ] [ : expr ] := expr
    assume name : expr
    prove name : expr

params = ( name : expr [, name : expr ]* )

expr =
    _
    name
    Type
    ( expr )
    expr ( expr [, expr]* )
    expr = expr
    expr → expr
    expr × expr
    Σ params expr
    (expr , expr [, expr]*)
    Π params expr
    λ params expr
```

TODO: operator precedence and associativity.

# Type theory

Dependent type theory. Type : Type for now.

`_` is a "hole" that will be filled in by the compiler.
