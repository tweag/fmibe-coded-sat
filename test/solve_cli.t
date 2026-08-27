  $ ../app/solve.exe sat sat.cnf
  SAT!
  1 2 

  $ ../app/solve.exe sat unsat.cnf
  UNSAT!

  $ ../app/solve.exe bench sat sat.cnf | sed -n '1p'
  Benchmarking 1 DIMACS instances
