An experimental theorem prover. Everything is work in progress (including the name).

Right now the theorem prover can type-check things, and even infer a few typeson
its own. In addition, there's a VS Code extension for syntax highlighting and
error messages. See `doc/language.md` for a description of the syntax, and
`examples/basics.pf` for an example.

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
