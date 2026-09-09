A fmibe-coded SAT solver
========================

This repository contains a little experiment about LLM generated code
constrained by formal proofs.

There's a current hypothesis floating around, backed by a double opportunity:
- LLM-backed coding agents are good at producing code, but it's very hard to
  check the code, making formal methods useful to constrain the generated code
  and have less to check
- LLM-backed coding agents can generate computer-verified proofs of formal
  statements, making formal proofs much cheaper to produce.
  
So what if we write specifications, let the agent generate the code and its
proof. I've [Arnaud] nicknamed this “fmibe coding”, a portmanteau for FM (Formal
Method, admittedly broader than just formal proofs) and vibe coding.

## Experimental setup

In this repository, I've [Arnaud] built a small SAT solver. I chose that for
something which has decently clear specifications (to give the project a good
chance of yielding results), is well-contained, while being non-trivial. I also
have a decently good idea of how to program a SAT solver, but it's still
something that I haven't really done before. So it's decently realistic.

For the purpose of this experiment, I'm trying to write very little code myself
but to write the important specifications myself (in practice I do let the LLM
act on specifications, but I'm quite careful about checking them).

This is all a Rocq project for simplicity. In practice, the general expectation
seems rather that the programming will be done in a programming language and the
proofs in a separate proof assistant. But there isn't really reliable such tools
available at the moment, so doing everything in a single tool seemed good enough
for the sake of an experiment (and Rocq is my proof assistant of choice). To
keep things a little bit like the expected setup, I try to split files in two:
an implementation file, using only tools available to standard programming
languages, and a specification file writing proofs.

## End product

The SAT solver is decently fast, I suppose. I haven't properly benchmarked it
against proper SAT solvers, though (probably by fear of being violently shamed).
There are a lot of optimisations I could still do if I dug deep enough, but it's
about as much as I had time for. At any rate, there are fundamental limits due
to using a pure language.

The Rocq SAT solver is packaged, with an Ocaml outer shell, as a CLI programs
which can solve DIMACS-formated problems as input. For the sake of reducing the
scope, the SAT solver computes a model when the problem is SAT, but doesn't
return UNSAT cores, just an `UNSAT` message.

The correctness of the model and of unsat are proved in Rocq, but I didn't
formally proved that the algorithm terminates.

## Usage

Run the solver on a problem in DIMACS CNF format with:

```console
$ dune exec app/solve.exe -- sat path/to/problem.cnf
```

For a satisfiable problem, `solve` prints `SAT!` followed by a model as signed
literals. For an unsatisfiable problem, it prints `UNSAT!`.

To display the available commands and options, run:

```console
$ dune exec app/solve.exe -- --help
```

Run the SATLIB benchmark corpus with the optimized benchmark profile:

```console
$ dune exec --profile benchmark app/solve.exe -- bench sat benchmarks/satlib
```

Each DIMACS file is solved once. The command prints its result, elapsed time,
and number of conflicts in a table, followed by totals. A conflict is counted
each time the solver enters its backtracking operation.

Long-running benchmarks can be bounded with `timeout`. Its usual `SIGTERM` is
handled gracefully: the active file is printed as `TIMEOUT`, partial totals are
printed, and the process exits with status 124.

```console
$ timeout 30s dune exec --profile benchmark app/solve.exe -- bench sat path/to/problem.cnf
```

The benchmark command also accepts a single DIMACS file:

```console
$ dune exec --profile benchmark app/solve.exe -- bench sat path/to/problem.cnf
```

## Acknowledgement

I'd like to thank Guillaume Bury and Simon Cruanes, whose work on [mSAT] helped
me figure out what I didn't understand well about CDCL SAT solvers, and
for answering my questions. Also, [Dolmen] giving DIMACS parsing for mostly.

[mSAT]: https://github.com/Gbury/mSAT/
[Dolmen]: https://github.com/Gbury/dolmen/
