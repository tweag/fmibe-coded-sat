# AGENTS.md

## Environment

This is a mainly Rocq-prover project. The environment is provided by a Nix shell
via the `flake.nix` file. This file provides both system dependencies and Rocq
(and possibly Ocaml) dependencies. You are running inside the Nix environment
(via direnv), so you don't need to call to Nix explicitly.

The project is built using the `dune` tool.

Useful commands
- `dune build` builds the project and check its proofs.

## Project organisation

Each logical module is split in two files, an `Impl.v` file and a `Spec.v` file.

In the `Impl.v` comes the actual program that we are writing, and in the
`Spec.v` file come corresponding specifications, theorems and proofs.

## Style

- In `Impl.v` files, we don't care too much about proving termination. So if
  termination is non-obvious, use the `#[bypass_check(guard)]` to assume
  termination.

- In proof, use bullets whenever there are generated subgoals. An alternative is
  to use braces `{`/`}` (or numbered, _e.g._ `2:{`/`}`) when a subgoal is
  principal, and the others are secondary. For instance `assert` should be
  proved within `{`/`}` and the main proof continues with the extra hypothesis.
  This avoids nesting bullets too deep and is more readable for humans. Of
  course `all:` should be used whenever relevant.

- Prefer `Is_true b` to `b = true`
