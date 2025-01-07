AGDA2HS = agda2hs
FLAGS =
LIBRARIES =

.PHONY: build alllib clean clean-lib clean-agdai nix-tc nix-build

build: cabal-build

alllib: lib lib/Scope.hs lib/Scope/All.hs lib/Scope/Core.hs lib/Scope/Diff.hs lib/Scope/In.hs lib/Scope/Split.hs lib/Scope/Sub.hs lib/Scope/Cut.hs

# alllib: lib lib/*.hs

lib:
	mkdir lib

lib/%.hs: src/%.agda
	$(AGDA2HS) $(FLAGS) $(LIBRARIES) $< -o lib

clean: clean-lib clean-agdai

clean-lib:
	rm -rf lib

clean-agdai:
	rm -f src/*.agdai

cabal-build: alllib
	cabal build

nix-tc:
	nix build .#scope-lib --print-build-logs

nix-build:
	nix build .#scope-hs --print-build-logs
