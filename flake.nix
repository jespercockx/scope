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

        compiler = "ghc94";
        withCompiler = compiler:
          let haskellPackages =
                if compiler == "default"
                then pkgs.haskellPackages
                else pkgs.haskell.packages.${compiler};
              agda2hs-custom = (agda2hs.lib.${system}.withCompiler compiler).withPackages [agda2hs-lib];
          in haskellPackages.callPackage ./scope.nix {agda2hs = agda2hs-custom;};
       scope-hs = withCompiler compiler;
      in {
        packages = {
          inherit scope-lib;
          inherit scope-hs;
          default = scope-hs;
        };
        lib = {
          inherit withCompiler;
        };
      });
}
