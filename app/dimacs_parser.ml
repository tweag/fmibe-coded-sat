module Location = Dolmen_std.Loc

module Term = struct
  type t = Sat.literal
  type location = Location.t

  let atom ?loc:_ value =
    if value > 0 then Sat.Pos value else Sat.Neg (-value)
end

module Statement = struct
  type term = Term.t
  type location = Location.t

  type t =
    | Header of int * int
    | Clause of Sat.clause

  let p_cnf ?loc:_ variables clauses = Header (variables, clauses)
  let clause ?loc:_ literals = Clause literals
end

module Parser = Dolmen_dimacs.Make (Location) (Term) (Statement)

let problem_of_statements statements =
  List.filter_map
    (function Statement.Header _ -> None | Statement.Clause clause -> Some clause)
    statements

let parse input =
  let _file, statements = Parser.parse_all input in
  problem_of_statements (Lazy.force statements)

let words line =
  line
  |> String.map (function '\t' | '\r' -> ' ' | character -> character)
  |> String.split_on_char ' '
  |> List.filter (fun word -> word <> "")

let normalize contents =
  let output = Buffer.create (String.length contents) in
  let stopped = ref false in
  String.split_on_char '\n' contents
  |> List.iter (fun line ->
         let line = String.trim line in
         if not !stopped && line <> "" then
           match line.[0] with
           | 'c' -> ()
           | '%' -> stopped := true
           | 'p' ->
               Buffer.add_string output line;
               Buffer.add_char output '\n'
           | _ ->
               words line
               |> List.iter (fun word ->
                      Buffer.add_string output word;
                      if word = "0" then Buffer.add_char output '\n'
                      else Buffer.add_char output ' '));
  Buffer.contents output

let parse_file path =
  let contents = In_channel.with_open_bin path In_channel.input_all in
  parse (`Contents (path, normalize contents))

let parse_string ?(filename = "<string>") contents =
  parse (`Contents (filename, normalize contents))
