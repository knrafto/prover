The core language is based on dependent type theory (see HoTT book).

# Features

TODO: overview of define and axiom syntax.

## Rewrite rules

To quickly experiment with new types, one can define "rewrite rules" in order to
postulate new judgemental equalities. For example, the natural numbers are
postulated as:

```
axiom ℕ : Type
axiom zero : ℕ
axiom suc : ℕ → ℕ
axiom ℕ-ind : Π C : ℕ → Type. C zero → (Π n. C n → C (suc n)) → Π n. C n
rewrite ℕ-ind-zero C base step
    where ℕ-ind C base step zero ≡ base
rewrite ℕ-ind-suc C base step n
    where ℕ-ind C base step (suc n) ≡ step n (ℕ-ind C base step n)
```

The LHS in these rules must be a "pattern": either a parameter, or an axiom
applied to more patterns. The reduction algorithm will try to replace the LHS
with the RHS when it appears at the head of a term.

# Syntax

## Lexical structure

Whitespace are space, tab, newline, carriage return, form feed, and vertical
tab. Line comments start with `--`. Block comments are delimited with `{-` and
`-}`. Block comments may be nested.

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
define axiom rewrite where
```

## Pseudo-grammar

```
module = [ statement ]*

statement =
    define name param* [ : expr ] ≡ expr
    axiom name param* : expr
    rewrite name param* where expr ≡ expr

param =
    name
    ( name : expr )

expr =
    _
    name
    Type
    ( expr )
    expr expr
    expr = expr
    expr × expr
    expr → expr
    expr , expr
    Π name [ : expr ] . binder
    λ name [ : expr ] . binder
    Σ name [ : expr ] . binder
```
