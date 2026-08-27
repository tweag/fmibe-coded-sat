let () =
  let actual =
    Dimacs_parser.parse_string
      "c a small example\np cnf 3 2\n1 -3 0\n2 3 -1 0\n"
  in
  let expected =
    [ [ Sat.Pos 1; Sat.Neg 3 ]; [ Sat.Pos 2; Sat.Pos 3; Sat.Neg 1 ] ]
  in
  assert (actual = expected)
