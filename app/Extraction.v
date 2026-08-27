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

(* [sat] pulls in the solver state as well as [Literal], [Clause], and
   [Problem].  In particular, OCaml clients and the DIMACS frontend share the
   representation that originates in [CDCL.Impl]. *)
Extraction "sat.ml" Clause Problem sat.
