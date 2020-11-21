The core language is based on dependent type theory (see HoTT book).

# Features

TODO: overview of define and axiom syntax.

## Implicit parameters

Implicit parameters are written with curly braces. Currently, implicit
parameters must come before any explicit ones, so they can be automatically
filled with holes each time the name is used.

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

The LHS in these rules must be a "pattern": either a parameter name, or an axiom
applied to more patterns. The reduction algorithm will try to replace the LHS
with the RHS when it appears at the head of a term.

The current rewrite rules are very easy to abuse. We make no attempt to verify
that the rewrite rules are confluent or terminating. If a parameter name appears
more than once in the pattern (as in the J rule) one is used arbitrarily without
checking whether the two terms are equal during reduction. For example:

```
axiom foo : Π A : Type. Π x : A. Π y : A. x = y
rewrite foo-rule A a
    where foo A a a = refl A a
```

Now `foo A a b : a = b` will be rewritten to either `refl A a : a = a` or
`refl A b : b = b`, both of which have the wrong type.

Despite these dangers, computation rules for most "nice" types can be defined
safely using rewrite rules.

## Infix operators

Infix operators can be declared using `infix`, `infixl`, and `infixr`, similar
to Haskell or Agda.

# Syntax

## Lexical structure

Whitespace are space, tab, newline, carriage return, form feed, and vertical
tab. Line comments start with `--` and end with a newline. Block comments are
delimited with `{-` and `-}`. Block comments may be nested.

The characters `(){},.` are "symbols", and are always treated as a token by
themselves.

Any other contiguous sequence of non-whitespace, non-symbol Unicode characters
is a "word". The following words are reserved, and are treated specially in the
syntax:

```
Type
_
: ≡ →
Π λ Σ
define axiom rewrite where infix infixl infixr
```

All other words are identifiers.

## Pseudo-grammar

```
module = [ decl ]*

decl =
    fixity number ident
    define ident implicit_params explicit_params [ : expr ] ≡ expr
    axiom ident implicit_params explicit_params : expr
    rewrite ident explicit_params where expr ≡ expr

implicit_params = implicit_param_group*

implicit_param_group =
    { ident }
    { ident+ : expr }

explicit_params = explicit_param_group*

explicit_param_group =
    ident
    ( ident+ : expr )

fixity =
    infix
    infixl
    infixr

expr =
    _
    ident
    Type
    ( expr )
    expr expr
    expr → expr
    expr , expr
    Π explicit_params . binder
    λ explicit_params . binder
    Σ explicit_params . binder
```
