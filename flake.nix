{
  description = "Poe: dev shell with elan (for the pinned Lean toolchain) and the uplc/plc oracles";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # Only used for their `uplc`/`plc` executables (the untyped and typed
    # execution/typecheck oracles, see PLAN.md). Not a Lean/Lake dependency
    # of Poe itself.
    plutus.url = "github:input-output-hk/plutus";
  };

  outputs = { self, nixpkgs, flake-utils, plutus }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # `lean4-mode` isn't packaged in nixpkgs itself (checked: absent
        # from both `emacsPackages` and `emacsPackages.melpaPackages`),
        # so it's built here directly from its upstream repo, the same
        # way nixpkgs' own MELPA packages are generated. Version/hash
        # pinned to the `1.1.2` tag for reproducibility; dependencies
        # (`compat`/`dash`/`magit-section`/`lsp-mode`) taken straight from
        # `lean4-mode.el`'s own `Package-Requires` header, not guessed.
        lean4-mode = pkgs.emacsPackages.melpaBuild {
          pname = "lean4-mode";
          version = "1.1.2";
          src = pkgs.fetchFromGitHub {
            owner = "leanprover-community";
            repo = "lean4-mode";
            rev = "1.1.2";
            hash = "sha256-DLgdxd0m3SmJ9heJ/pe5k8bZCfvWdaKAF0BDYEkwlMQ=";
          };
          packageRequires = with pkgs.emacsPackages; [
            compat
            dash
            magit-section
            lsp-mode
            # Not one of lean4-mode's own declared deps — added so
            # magit-section's bundled-`transient`-version check at load
            # time doesn't warn (Emacs 30's built-in `transient` is older
            # than magit-section wants; this MELPA build is newer).
            transient
          ];
          # `:files` overridden from MELPA's default (`*.el` only) — the
          # repo's `data/` directory (e.g. `data/abbreviations.json`,
          # loaded by `lean4-input.el` for the "Lean" input method) was
          # silently dropped without this, which broke `lean4-mode`'s
          # own setup partway through (everything after the failing
          # `require`/`set-input-method` calls in its mode body — key
          # bindings, LSP workspace creation — never ran).
          recipe = pkgs.writeText "lean4-mode-recipe" ''
            (lean4-mode :fetcher github :repo "leanprover-community/lean4-mode"
                        :files ("*.el" "data"))
          '';
        };

        # `lean4-mode` only integrates with `flycheck` optionally (via
        # `declare-function`/hooks in `lean4-mode.el`, not its
        # `Package-Requires` header) — so it has to be added explicitly,
        # or diagnostics never display at all even when the LSP server
        # is sending them correctly.
        emacsWithLean = pkgs.emacsPackages.emacsWithPackages (epkgs: [
          lean4-mode
          epkgs.melpaPackages.flycheck
        ]);
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.elan
            plutus.packages.${system}.uplc
            plutus.packages.${system}.plc
            emacsWithLean
          ];
        };
      });

  nixConfig = {
    extra-substituters = [ "https://cache.iog.io" ];
    extra-trusted-public-keys =
      [ "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=" ];
  };
}
