The core language is based on univalent type theory (see HoTT book).

# Lexical structure

Whitespace is one of ` ` (space), `\t`, `\r`, `\n`.
Comments start with '#'.

The symbols `(`, `)` and `,` are "punctuation", and are always treated as a
symbol by themselves. Any other contiguous sequence of non-whitespace,
non-punctuation Unicode characters is a "word". The following words are
reserved, and are treated specially in the syntax:

```
:
=
:=
→
Σ
Π
λ
```

TODO: reserve all words starting with `:`?

# File structure

At top-level, the file is broken into statements, where indented lines are
treated as a continuation of the previous command.

# Grammar

```
statement = directive | definition
directive = :prove expr  (matches any :word)
definition = name [ params ] [ : expr ] := expr
params = ( param [, param]* )
param = name [: expr]
expr =
    name
    literal
    expr ( expr [, expr]* )
    expr = expr
    expr → expr
    Σ params expr
    Π params expr
    λ params expr
    ( expr )
```
