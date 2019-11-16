The goal is to become a fully interactive proof assistant. This means we need:

* Error recovery during parsing. Every string is a valid parse.
* Positions for error message.
* Semantic highlighting.
* Info on hover.
* Automatic reformatting.
* Refactoring (e.g. make top-level definition).

# Tokenization

Tokenization should never fail. It partitions the input into distinct tokens and
labels them.

Note: nested comments.

# Indentation

Indentation behaves differently than just whitespace in front of every line. In
a sense, it's whitespace in front of a whole "block". Sections are grouped
together based on their indentation. For example, in

```
a
  b
  c
    d
  e
```

we might represent this as

a indent { b c indent { d } e}

One challenge is comments. For something like

```
a
  b
 # hello
  c
    d
  e
```

b and c are considered part of the same indented group, although the comment starts at a "negative" position.

Maybe we should just stick with context-free for now.

# Syntax

A couple points of syntax that I think will be important:

* Function call notation with parentheses, like f(x, y). More familiar to
  mathematicians and programmers.
* Dot notation for scoping.

# Parse tree

Each expression represents a span of text. Each expression is assigned an
interpretation in the core type theory. Errors become metavars, for example.
However, the core type theory itself knows nothing about positions; this must be
tracked "out of band".

# Error recovery

Every string must have a parse, possibly containing "error nodes". The parse
tree has no error nodes if and only if the string conforms to the grammar. The
grammar ends up being very "top-down" rather than "bottom-up" like Parsec.

Procedure:
* Tokenization is performed first (and never fails).
* The tokens `define`, `assume`, and `prove` always denote the start of
  another statement, no matter where in the parse tree we are. There may be
  an initial error statement.
* Parentheses are next. Parsing should proceed as if
  parentheses were matched first, where unmatched closed parentheses are
  discarded and unmatched open parentheses continue until the end of the
  statement.
* Within parenthesized groups, commas are used to break up lists before the
  innards are parsed.
* Next, infix operators are applied in order of precedence. Note these respect
  parentheses.
* Finally, we must parse atoms. What do we do with "extra stuff"? The binders
  Π, Σ, λ are straightforward. For parentheses and identifiers, we should use
  the first token/group and error on the rest.
