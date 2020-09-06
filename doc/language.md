The core language is based on univalent type theory (see HoTT book).

# Lexical structure

Whitespace are space, tab, newline, carriage return, form feed, and vertical
tab. Line comments start with `--`. Block comments are delimited with `{-` and
`-}`.

TODO: allow nested block comments.

The symbols `(`, `)`, `,`, and `.` are "punctuation", and are always
treated as a token by themselves.

Any other contiguous sequence of non-whitespace, non-punctuation Unicode
characters is a "word". The following words are reserved, and are treated
specially in the syntax:

```
Type
_
: ≡
= → ×
Π λ Σ
define assume prove
```

# Parentheses

Parentheses are matched in a "greedy" fashion. Unmatched left parens are
terminated at EOF; right parens are ignored (and of course these are both
errors).

# Operators

`= → ×` are operators. From tightest to least tight:
* = (non-associative)
* × (right-associative)
* → (right-associative)

These work by splitting the token stream (not looking inside of parentheses)
into parts and proceeding on those.

# Binders

`Π λ Σ` are binders, which act like prefix operators. They expect a
parenthesized group of "params", which are `name : type` pairs.

# Function application

The remaining tokens are atoms

Juxtaposition represents function application, like `f x`. If the argument
requires parentheses, we write it with no space like `f(x)`.

Multi-argument functions can be written using 
```
R : A × A → Type
R(a, b) ≡ a < b
```

# Grammar

```
module = [ statement ]*

statement =
    define name [ : expr ] ≡ expr
    assume name : expr
    prove name : expr

param = name [ : expr ]

atom =
    _
    name
    Type
    ( expr )

apps = [ apps ] atom
equals = apps [ = apps ]
times = equals [ × times ]
arrow = times [ → arrow ]
tuple = arrow [ , tuple ]
binder =
    tuple
    Π param . binder
    λ param . binder
    Σ param . binder
expr = binder
```

# Type theory

Dependent type theory. Type : Type for now.

`_` is a "hole" that will be filled in by the compiler.
