An experimental theorem prover. Everything is work in progress (including the name).

Currently, the theorem prover can perform basic type checking and type inference
(enough to prove properties about the natural numbers, say), but many
quality-of-life features are still missing. See `doc/language.md` for a
description of the syntax, and `examples/basics.pf` for some examples.

In addition, there's a VS Code extension for interactive semantic highlighting and
error messages.

# Prerequisites (macOS)

```
brew install cabal npm
npm install -g vsce
```

# Building

```
make
cabal run prover -- examples/basics.pf
```

# Building the extension

```
make install-vscode-extension
```

In VSCode, reload the window (on macOS, Shift-Cmd-P -> "Developer: Reload Window").
