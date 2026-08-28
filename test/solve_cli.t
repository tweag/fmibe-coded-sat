  $ ../app/solve.exe sat sat.cnf
  SAT!
  2 1

  $ ../app/solve.exe sat unsat.cnf
  UNSAT!

  $ ../app/solve.exe sat root-unit.cnf
  SAT!
  2 1

  $ ../app/solve.exe sat backtrack.cnf
  SAT!
  2 -1

  $ ../app/solve.exe bench sat sat.cnf | sed -n '1p'
  Benchmarking 1 DIMACS instances
