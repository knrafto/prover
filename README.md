A theorem prover.

Features:
* Good error messages and recovery, for interactive use.
* Ad-hoc overloading (ambiguous names).
* Automatically inferred propositions, with powerful proof automation.

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
