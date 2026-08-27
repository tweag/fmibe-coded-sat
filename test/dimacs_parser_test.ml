let id = Sat.Id.of_nat

let () =
  let actual =
    Dimacs_parser.parse_string
      "c a small example\np cnf 3 2\n1 -3 0\n2 3 -1 0\n"
  in
  let expected =
    [ [ Sat.Pos (id 1); Sat.Neg (id 3) ];
      [ Sat.Pos (id 2); Sat.Pos (id 3); Sat.Neg (id 1) ] ]
  in
  assert (actual = expected);
  let multiline =
    Dimacs_parser.parse_string "p cnf 2 1\n1\n-2\n0\n%\n0\n"
  in
  assert (multiline = [ [ Sat.Pos (id 1); Sat.Neg (id 2) ] ])
