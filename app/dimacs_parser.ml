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

let parse_file path = parse (`File path)
let parse_string ?(filename = "<string>") contents =
  parse (`Contents (filename, contents))
