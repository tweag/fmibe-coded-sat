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
          cmdliner = "*";
          dolmen = "*";
          dune = "*";
          ocaml-base-compiler = "*";
          ocaml-config = "*";
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
            pkgs.just
            pkgs.perf
            opamScope.cmdliner
            opamScope.dolmen
            opamScope.dune
            opamScope.ocaml-base-compiler
            opamScope.rocq-prover
            opamScope.rocq-stdlib
          ];

          shellHook = ''
            # Both rocq-core and rocq-stdlib set ROCQLIB. Since mkShell's
            # setup-hook order leaves it pointing at rocq-core, explicitly
            # select the full standard-library installation for Dune's Rocq
            # theory discovery.
            # Quite hackish. Figure if there's a blessed way to do that, maybe
            # with an Opam file?
            export ROCQLIB="${opamScope.rocq-stdlib}/lib/ocaml/${opamScope.ocaml-base-compiler.version}/site-lib/coq"

            echo "Rocq development shell: $(rocq --version | head -n1)"
            echo "Build with: dune build"
          '';
        };
      }
    );
}
