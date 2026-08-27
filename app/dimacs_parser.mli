(** Parse DIMACS CNF into the types extracted from [FMV.CDCL.Impl]. *)

val parse_file : string -> Sat.problem
(** [parse_file path] parses all clauses from the DIMACS CNF file [path]. *)

val parse_string : ?filename:string -> string -> Sat.problem
(** [parse_string contents] parses DIMACS CNF held in memory. *)
