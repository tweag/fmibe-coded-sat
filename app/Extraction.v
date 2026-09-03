Require Import FMV.CDCL.Impl.
Require Import Stdlib.extraction.Extraction.
Require Import Stdlib.extraction.ExtrOcamlBasic.
Require Import Stdlib.extraction.ExtrOcamlNatInt.

Extraction Language OCaml.
Set Extraction Output Directory ".".

(* The OCaml executable evaluates the solver eagerly.  Erase both delay
   constructors so that [Delay A] is represented by [A]. *)
Extract Inductive Delay => "" [ "" "" ].
Extract Inlined Constant delay_bind =>
  "(fun value continuation -> continuation value)".

(* Keep conflict accounting outside the verified algorithm.  In Rocq the hook
   is a no-op; the extracted program records one event per [backtrack] call. *)
Extract Constant count_conflict =>
  "(fun value -> Conflict_counter.increment (); value)".

(* The CLI uses the persistent two-watch implementation.  Unit clauses are
   queued before the first decision and backtracking leaves watches in place. *)
Extraction "sat.ml" Clause Problem empty_state add_clause sat.

(* These entry points pull in the solver state as well as [Literal], [Clause],
   and [Problem].  In particular, OCaml clients and the DIMACS frontend share
   the representation that originates in [CDCL.Impl]. *)
