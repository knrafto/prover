hs_sources = $(shell find src/ -name '*.hs')

.PHONY: default
default: build

.PHONY: clean
clean:
	cabal clean

.PHONY: build
build: $(hs_sources)
	cabal build

extension = vscode/prover-0.0.1.vsix
json_sources = $(shell find vscode/ -name '*.json')
ts_sources = $(shell find vscode/ -name '*.ts')

$(extension): $(json_sources) $(ts_sources)
	(cd vscode && vsce package)

.PHONY: install-vscode-extension
install-vscode-extension: $(extension)
	code --install-extension $<
