The core language is based on univalent type theory (see HoTT book).

# Lexical structure

Whitespace are space, tab, newline, carriage return, form feed, and vertical tab.
Comments start with '#'.

The symbols `(`, `)`, `,`, and `.` are "punctuation", and are always treated as a
symbol by themselves. Any other contiguous sequence of non-whitespace,
non-punctuation Unicode characters is a "word". The following words are
reserved, and are treated specially in the syntax:

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
:assume
:prove
```

TODO: reserve all words starting with `:`?

# File structure

At top-level, the file is broken into statements, where indented lines are
treated as a continuation of the previous statement. A statement is either
a definition, or a command. 

# Grammar

```
statement = directive | definition
directive =
    :assume name : expr
    :prove name : expr
definition = name [ params ] [ : expr ] := expr
params = ( name : expr [, name : expr ]* )
expr =
    _
    name
    literal
    ( expr )
    expr ( expr [, expr]* )
    expr = expr
    expr → expr
    expr × expr
    Σ params . expr
    (expr , expr [, expr]*)
    Π params . expr
    λ params . expr
```

Here "→" is right-associative.

# Type theory

Dependent type theory. Type : Type for now.

`_` is a "hole" that will be filled in by the compiler.
