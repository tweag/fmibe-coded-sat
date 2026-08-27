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

let solve_problem problem =
  match add_clauses empty_state problem with
  | None -> Sat.UNSAT
  | Some state -> Sat.sat state

let solve_file file = solve_problem (Dimacs_parser.parse_file file)

let solve file =
  try
    (match solve_file file with
     | Sat.UNSAT -> print_endline "UNSAT!"
     | Sat.SAT model -> print_model model);
    `Ok ()
  with exn -> `Error (false, Printexc.to_string exn)

let has_suffix suffix string =
  let suffix_length = String.length suffix in
  let string_length = String.length string in
  string_length >= suffix_length
  && String.sub string (string_length - suffix_length) suffix_length = suffix

let rec cnf_files path =
  if Sys.is_directory path then
    Sys.readdir path
    |> Array.to_list
    |> List.sort String.compare
    |> List.concat_map (fun entry -> cnf_files (Filename.concat path entry))
  else if has_suffix ".cnf" path then [ path ]
  else []

type expected_result = Expected_sat | Expected_unsat | Unknown

let rec expected_result path =
  let parent = Filename.dirname path in
  if parent = path then Unknown
  else
    match Filename.basename parent with
    | "sat" -> Expected_sat
    | "unsat" -> Expected_unsat
    | _ -> expected_result parent

let result_name = function Sat.SAT _ -> "SAT" | Sat.UNSAT -> "UNSAT"

let result_matches expected actual =
  match expected, actual with
  | Unknown, _ | Expected_sat, Sat.SAT _ | Expected_unsat, Sat.UNSAT -> true
  | Expected_sat, Sat.UNSAT | Expected_unsat, Sat.SAT _ -> false

let solve_checked file =
  let actual = solve_file file in
  if result_matches (expected_result file) actual then actual
  else
    failwith
      (Printf.sprintf "%s: expected a different result, got %s" file
         (result_name actual))

let timed_solve file =
  let start = Unix.gettimeofday () in
  let result = solve_checked file in
  let elapsed = Unix.gettimeofday () -. start in
  result, elapsed

let benchmark_sat path =
  try
    let files = cnf_files path in
    if files = [] then `Error (false, "no .cnf files found at " ^ path)
    else begin
      Printf.printf "Benchmarking %d DIMACS instances\n%!" (List.length files);
      let file_width =
        List.fold_left
          (fun width file -> max width (String.length file))
          (String.length "FILE") files
      in
      Printf.printf "%-*s  %-6s  %10s\n" file_width "FILE" "RESULT" "SECONDS";
      Printf.printf "%s  %s  %s\n" (String.make file_width '-')
        (String.make 6 '-') (String.make 10 '-');
      let total =
        List.fold_left
          (fun total file ->
            let result, elapsed = timed_solve file in
            Printf.printf "%-*s  %-6s  %10.6f\n%!" file_width file
              (result_name result) elapsed;
            total +. elapsed)
          0. files
      in
      Printf.printf "%s  %s  %s\n" (String.make file_width '-')
        (String.make 6 '-') (String.make 10 '-');
      Printf.printf "%-*s  %-6s  %10.6f\n" file_width "TOTAL" "" total;
      `Ok ()
    end
  with exn -> `Error (false, Printexc.to_string exn)

let file =
  let doc = "DIMACS CNF file to solve." in
  Arg.(required & pos 0 (some file) None & info [] ~doc ~docv:"FILE")

let sat_command =
  let doc = "solve a SAT problem in DIMACS CNF format" in
  Cmd.v (Cmd.info "sat" ~doc) Term.(ret (const solve $ file))

let benchmark_path =
  let doc =
    "DIMACS CNF file, or a directory whose .cnf files are searched recursively."
  in
  Arg.(required & pos 0 (some string) None & info [] ~doc ~docv:"PATH")

let benchmark_sat_command =
  let doc = "benchmark SAT solving over one DIMACS file or a directory" in
  Cmd.v (Cmd.info "sat" ~doc)
    Term.(ret (const benchmark_sat $ benchmark_path))

let benchmark_command =
  let doc = "run solver benchmarks" in
  Cmd.group (Cmd.info "bench" ~doc) [ benchmark_sat_command ]

let command =
  let doc = "a formally verified SAT solver" in
  Cmd.group (Cmd.info "solve" ~doc) [ sat_command; benchmark_command ]

let () = exit (Cmd.eval command)
