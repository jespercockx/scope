{
  description = "Agda scope library";

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.agda2hs = {
    url = "github:agda/agda2hs";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.flake-utils.follows = "flake-utils";
  };

  outputs = {self, nixpkgs, flake-utils, agda2hs}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};
        agda2hs-lib = agda2hs.packages.${system}.agda2hs-lib;
        agda2hsWithPackages = agda2hs.lib.${system}.withPackages;
        agda2hs-custom = agda2hsWithPackages [agda2hs-lib];
        scope-lib = pkgs.agdaPackages.mkDerivation
          { pname = "scope";
            meta = {};
            version = "0.1.0.0";
            buildInputs = [
              agda2hs-lib
            ];
            preBuild = ''
              echo "module Everything where" > Everything.agda
              find src -name '*.agda' | sed -e 's/src\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
            '';
            src = ./.;
          };
        scope-pkg = import ./scope.nix;
        scope-hs = pkgs.haskellPackages.callPackage scope-pkg {agda2hs = agda2hs-custom;};
      in {
        packages = {
          inherit scope-hs scope-lib;
          default = scope-hs;
        };
        lib = {
          inherit scope-pkg;
        };

        devShells.default = pkgs.haskellPackages.shellFor {
          packages = p: with p; [scope-hs];
          buildInputs = with pkgs.haskellPackages; [
            cabal-install
            cabal2nix
            haskell-language-server
            agda2hs-custom
            (pkgs.agda.withPackages [ agda2hs-lib ])
          ];
        };
      });
}
