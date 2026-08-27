# SAT benchmarks

`satlib/` contains a curated set of 98 DIMACS CNF instances from
[SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html). Files under `sat/`
are satisfiable and files under `unsat/` are unsatisfiable; the benchmark
runner checks these expected results while solving each instance once. It
prints the individual elapsed times in a table and the total time at the
bottom.

The selection contains instances from nine SATLIB archives:

- uniform random 3-SAT: `uf20-91`, `uf50-218`, and `uuf50-218`;
- flat graph colouring: `flat30-60`;
- all-interval series: `ais`;
- DIMACS collections: `AIM`, `JNH`, `DUBOIS`, and `PARITY`.

Run the full selection with the dedicated benchmark profile:

```console
$ dune exec --profile benchmark app/solve.exe -- bench sat benchmarks/satlib
```

Pass a single `.cnf` file instead of the directory to benchmark one instance.

The original archives and descriptions are available from SATLIB. The files
here retain their original contents and names.
