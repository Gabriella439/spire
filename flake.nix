{ inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/release-22.05;

    utils.url = github:numtide/flake-utils;
  };

  outputs = { nixpkgs, utils, ... }:
    utils.lib.eachDefaultSystem (system:
      let
        config = { };

        overlay = pkgsNew: pkgsOld: {
          spire =
            pkgsNew.haskell.lib.justStaticExecutables
              pkgsNew.haskellPackages.spire;

          haskellPackages = pkgsOld.haskellPackages.override (old: {
            overrides = pkgsNew.haskell.lib.packageSourceOverrides {
              spire = ./.;
            };
          });
        };

        pkgs =
          import nixpkgs { inherit config system; overlays = [ overlay ]; };

      in
        rec {
          packages.default = pkgs.haskellPackages.spire;

          apps.default = {
            type = "app";

            program = "${pkgs.spire}/bin/spire";
          };

          devShells.default = pkgs.haskellPackages.spire.env;
        }
    );
}
