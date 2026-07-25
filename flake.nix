{
  description = "Poe: dev shell with elan (for the pinned Lean toolchain) and the uplc oracle";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # Only used for its `uplc` executable (the execution oracle, see PLAN.md).
    # Not a Lean/Lake dependency of Poe itself.
    plutus.url = "github:input-output-hk/plutus";
  };

  outputs = { self, nixpkgs, flake-utils, plutus }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.elan
            plutus.packages.${system}.uplc
          ];
        };
      });

  nixConfig = {
    extra-substituters = [ "https://cache.iog.io" ];
    extra-trusted-public-keys =
      [ "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=" ];
  };
}
