{
  description = "Agda scope library";

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.mkAgdaDerivation.url = github:liesnikov/mkAgdaDerivation;
  inputs.agda2hs = {
    url = "github:liesnikov/agda2hs";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.flake-utils.follows = "flake-utils";
    inputs.mkAgdaDerivation.follows = "mkAgdaDerivation";
  };

  outputs = {self, nixpkgs, flake-utils, mkAgdaDerivation, agda2hs}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};
        agdaDerivation = pkgs.callPackage mkAgdaDerivation.lib.mkAgdaDerivation {};
        agda2hs-lib = agda2hs.packages.${system}.agda2hs-lib;
        scope-lib = agdaDerivation
          { pname = "scope";
            meta = {};
            version = "0.1.0.0";
            tcDir = "src";
            buildInputs = [
              agda2hs.packages.${system}.agda2hs-lib
            ];
            src = ./.;
          };
        helper = agda2hs.lib.${system};
        hpkgs = pkgs.haskell.packages.ghc96;
        agda2hs-ghc96 = pkgs.callPackage (helper.agda2hs-expr) {
          inherit self;
          agda2hs = hpkgs.callPackage (helper.agda2hs-pkg "--jailbreak") {};
          inherit (hpkgs) ghcWithPackages;
        };
        agda2hs-custom = agda2hs-ghc96.withPackages [agda2hs-lib];
        scope-pkg = import ./scope.nix;
        scope-hs = pkgs.haskell.packages.ghc94.callPackage scope-pkg {agda2hs = agda2hs-custom;};
      in {
        packages = {
          inherit scope-lib;
          inherit scope-hs;
          default = scope-hs;
        };
        lib = {
          inherit scope-pkg;
        };
      });
}
