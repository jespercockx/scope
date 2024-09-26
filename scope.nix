# this package is produced by calling `cabal2nix .`
# and then doing the following:
# add an agda2hs argument
# add buildTools = [agda2hs];
# add preBuild = ''make alllib'';
{ mkDerivation, base, lib, agda2hs }:
mkDerivation {
  pname = "scope";
  version = "0.1.0.0";
  src = ./.;
  buildTools = [agda2hs];
  preBuild = ''make alllib'';
  libraryHaskellDepends = [ base ];
  license = lib.licenses.unlicense;
}
