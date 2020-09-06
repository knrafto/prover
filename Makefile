bnfc_output = bnfc/Prover/Syntax/Concrete/Par.y
hs_sources = $(shell find src/ -name '*.hs')

.PHONY: build
build: $(hs_sources) $(bnfc_output)
	cabal build

.PHONY: clean
	rm -rf bnfc
	cabal clean

$(bnfc_output): src/Prover/Syntax/Concrete.bnfc
	-@mkdir -p bnfc
	@(cd bnfc && bnfc -p Prover.Syntax -d ../$<)
