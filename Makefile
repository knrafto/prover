bnfc_output = bnfc/Prover/Syntax/Concrete/Par.y
hs_sources = $(shell find src/ -name '*.hs')

.PHONY: default
default: build

.PHONY: clean
clean:
	rm -rf bnfc
	cabal clean

$(bnfc_output): src/Prover/Syntax/Concrete.bnfc
	-@mkdir -p bnfc
	(cd bnfc && bnfc -p Prover.Syntax -d ../$<)

.PHONY: build
build: $(hs_sources) $(bnfc_output)
	cabal build

extension = vscode/prover-0.0.1.vsix
json_sources = $(shell find vscode/ -name '*.json')
ts_sources = $(shell find vscode/ -name '*.ts')

$(extension): $(json_sources) $(ts_sources)
	(cd vscode && vsce package)

.PHONY: install-vscode-extension
install-vscode-extension: $(extension)
	code --install-extension $<
