{
  description = "Development environment for a Rocq project built with Dune";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    opam-nix = {
      url = "github:tweag/opam-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.opam-repository.follows = "opam-repository";
    };

    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      opam-nix,
      opam-repository,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # opam-nix resolves this query as one coherent opam switch. Add the
        # opam names of project-specific Rocq libraries here as needed.
        opamScope = opam-nix.lib.${system}.queryToScope {
          repos = [ opam-repository ];
        } {
          dune = "*";
          ocaml-base-compiler = "*";
          rocq-prover = "*";
          rocq-stdlib = "*";
        };

      in
      {
        # These outputs are useful for inspecting or building individual
        # pieces of the resolved opam environment.
        packages = {
          rocq-prover = opamScope.rocq-prover;
          rocq-stdlib = opamScope.rocq-stdlib;
        };

        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.codex
            pkgs.git
            opamScope.dune
            opamScope.ocaml-base-compiler
            opamScope.rocq-prover
            opamScope.rocq-stdlib
          ];

          shellHook = ''
            echo "Rocq development shell: $(rocq --version | head -n1)"
            echo "Build with: dune build"
          '';
        };
      }
    );
}
