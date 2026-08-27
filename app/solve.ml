open Cmdliner

let empty_state =
  { Sat.state_trail = [];
    state_clauses = Sat.ClauseStore.empty;
    state_learned = Sat.ClauseStore.empty;
    state_watched = Sat.ClauseMap.empty;
    state_falsified = [];
    state_pending = [] }

let rec add_clauses state = function
  | [] -> Some state
  | clause :: clauses ->
      match Sat.add_clause state clause with
      | Sat.Progress state' -> add_clauses state' clauses
      | Sat.Conflict _ -> None

let print_literal = function
  | Sat.Pos variable -> Printf.printf "%d " variable
  | Sat.Neg variable -> Printf.printf "-%d " variable

let print_model model =
  print_endline "SAT!";
  List.iter print_literal model;
  print_newline ()

let solve file =
  try
    let problem = Dimacs_parser.parse_file file in
    match add_clauses empty_state problem with
    | None ->
        print_endline "UNSAT!";
        `Ok ()
    | Some state ->
        (match Sat.sat state with
         | Sat.UNSAT -> print_endline "UNSAT!"
         | Sat.SAT model -> print_model model);
        `Ok ()
  with exn -> `Error (false, Printexc.to_string exn)

let file =
  let doc = "DIMACS CNF file to solve." in
  Arg.(required & pos 0 (some file) None & info [] ~doc ~docv:"FILE")

let sat_command =
  let doc = "solve a SAT problem in DIMACS CNF format" in
  Cmd.v (Cmd.info "sat" ~doc) Term.(ret (const solve $ file))

let command =
  let doc = "a formally verified SAT solver" in
  Cmd.group (Cmd.info "solve" ~doc) [ sat_command ]

let () = exit (Cmd.eval command)
