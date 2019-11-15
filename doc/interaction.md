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

# Parse tree

Each expression represents a span of text. Each expression is assigned an
interpretation in the core type theory. Errors become metavars, for example.
However, the core type theory itself knows nothing about positions; this must be
tracked "out of band".
