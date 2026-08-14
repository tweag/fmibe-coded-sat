(* The core loop of a CDCL-based SAT solver *)

Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import FMV.FiniteMap.
Require Import FMV.ListMap.

Definition Var := nat.
Variant Literal :=
  | Pos (l : Var)
  | Neg (l : Var)
.
Definition Clause := list Literal.

Definition Problem := list Clause.

(* A partial model. The semantics is that `Pos` literals in the list are known
   to be true, `Neg` literals are known to be false. The rest is (yet)
   undecided. *)
Definition Model := list Literal.

Definition literal_eq_dec (l r : Literal) : {l = r} + {l <> r}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition clause_eq_dec : forall l r : Clause, {l = r} + {l <> r} :=
  list_eq_dec literal_eq_dec.

Module VarKey.
  Definition t := Var.
  Definition eq_dec := Nat.eq_dec.
End VarKey.

Module ClauseElement.
  Definition t := Clause.
  Definition eq_dec := clause_eq_dec.
End ClauseElement.

Module ClauseMapBase := ListMap.Make VarKey ClauseElement.

Module ClauseMap.
  Include ClauseMapBase.

  Definition remove_clause := remove_element.

  Lemma card_of_remove_clause_eq : forall m c,
    card_of c (remove_clause c m) = 0.
  Proof. exact card_of_remove_element_eq. Qed.

  Lemma card_of_remove_clause_neq : forall m c d,
    c <> d -> card_of d (remove_clause c m) = card_of d m.
  Proof. exact card_of_remove_element_neq. Qed.

  Lemma find_remove_clause : forall m c d v,
    In d (find v (remove_clause c m)) <-> In d (find v m) /\ d <> c.
  Proof. exact find_remove_element. Qed.

  Lemma find_remove_clause_eq : forall m c v,
    find v (remove_clause c m) =
      filter (fun c' => if clause_eq_dec c c' then false else true) (find v m).
  Proof. exact find_remove_element_eq. Qed.
End ClauseMap.

Record State := {
  state_model : Model;
  (*  `state_clauses` implements two-literal watch*)
  state_clauses : ClauseMap.t;
  state_satisfied : list Clause;
  state_falsified : list Clause;
  state_pending : list Clause;
}.

Definition literal_var (l : Literal) : Var :=
  match l with
  | Pos v | Neg v => v
  end.

Definition var_is_assigned (m : Model) (v : Var) : bool :=
  existsb (fun l => Nat.eqb (literal_var l) v) m.

Definition literal_value (m : Model) (l : Literal) : option bool :=
  match find (fun l' => Nat.eqb (literal_var l') (literal_var l)) m with
  | None => None
  | Some (Pos _) =>
      match l with Pos _ => Some true | Neg _ => Some false end
  | Some (Neg _) =>
      match l with Pos _ => Some false | Neg _ => Some true end
  end.

Definition literal_is_true (m : Model) (l : Literal) : bool :=
  match literal_value m l with Some true => true | _ => false end.

Definition literal_is_undecided (m : Model) (l : Literal) : bool :=
  match literal_value m l with None => true | _ => false end.

Fixpoint scan_clause_once (m : Model) (c : Clause) : bool * list Literal :=
  match c with
  | [] => (false, [])
  | l :: c' =>
      let '(satisfied, undecided) := scan_clause_once m c' in
      (orb (literal_is_true m l) satisfied,
       if literal_is_undecided m l then l :: undecided else undecided)
  end.

Variant scan_result :=
  | propagate_literal (l : Literal)
  | clause_decided (cm : ClauseMap.t) (sat fals : list Clause)
  | clause_watched (cm : ClauseMap.t).

Fixpoint find_different_var (v : Var) (ls : list Literal) : option Literal :=
  match ls with
  | [] => None
  | l :: ls' =>
      if Nat.eqb v (literal_var l) then find_different_var v ls' else Some l
  end.

(* Is [c] satisfied? falsified? otherwise watch an additional literal *)
Definition scan_clause (m : Model) (c : Clause)
    (cm : ClauseMap.t) (sat fals : list Clause) : scan_result :=
  let '(satisfied, undecided) := scan_clause_once m c in
  if satisfied then
      clause_decided (ClauseMap.remove_clause c cm) (c :: sat) fals
  else
    match undecided with
    | [] => clause_decided (ClauseMap.remove_clause c cm) sat (c :: fals)
    | l :: undecided' =>
        match find_different_var (literal_var l) undecided' with
        | None => propagate_literal l
        | Some l' =>
            if in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm) then
              clause_watched (ClauseMap.add (literal_var l') c cm)
            else clause_watched (ClauseMap.add (literal_var l) c cm)
        end
    end.

Definition set_lit (l : Literal) (m : State) : State :=
  let watched := ClauseMap.find (literal_var l) m.(state_clauses) in
  let cm := ClauseMap.remove (literal_var l) m.(state_clauses) in
  let pending := watched ++ m.(state_pending) in
  {| state_model := l :: m.(state_model); 
     state_clauses := cm;
     state_satisfied := m.(state_satisfied);
     state_falsified := m.(state_falsified);
     state_pending := pending |}.

Definition remove_clause_from_list (c : Clause) (cs : list Clause) : list Clause :=
  filter (fun d => if clause_eq_dec c d then false else true) cs.

(* The fuel is initially larger than the number of literals in the problem.
   Every recursive call assigns a previously undecided literal. *)
Definition propagate (c : Clause) (s : State) : State :=
      match scan_clause s.(state_model) c s.(state_clauses) s.(state_satisfied) s.(state_falsified) with
      | propagate_literal l =>
          set_lit l
            {| state_model := s.(state_model);
               state_clauses := ClauseMap.remove_clause c s.(state_clauses);
               state_satisfied := c :: s.(state_satisfied);
               state_falsified := s.(state_falsified);
               state_pending :=
                 remove_clause_from_list c s.(state_pending) |}
      | clause_decided cm sat fals =>
          {| state_model := s.(state_model);
             state_clauses := cm;
             state_satisfied := sat;
             state_falsified := fals;
             state_pending := remove_clause_from_list c s.(state_pending) |}
      | clause_watched cm =>
          {| state_model := s.(state_model);
             state_clauses := cm;
             state_satisfied := s.(state_satisfied);
             state_falsified := s.(state_falsified);
             state_pending := s.(state_pending) |}
  end.

(* Game plan: to progress the state:
   - If there are pending clauses, find a new undecided literal to watch or propagate their only literal or mark the clause as satisfied or falsified.
   - Otherwise
     1. choose an undecided variable
     2. Set it to `true` in the model
     3. Wake up any clause currently watching this literal, make them all pending. *)
Definition progress (s : State) : State :=
  match s.(state_pending) with
  | c :: pending =>
      propagate c
        {| state_model := s.(state_model);
           state_clauses := s.(state_clauses);
           state_satisfied := s.(state_satisfied);
           state_falsified := s.(state_falsified);
           state_pending := pending |}
  | [] =>
      match hd_error (ClauseMap.keys s.(state_clauses)) with
      | None => s (* All the literal have been decided so no progress can be made *)
      | Some v =>
          set_lit (Pos v) s
      end
  end.

Definition is_empty {A} (l : list A) : bool :=
  match l with
  | [] => true
  | _ => false
  end.

(* TODO: Do I use *)
(* Guard structural arguments of recursive occurrences with [guard] to ensure
   normalisation when the guard condition check is bypassed. *)
Definition guard {A} (x:A) := x.
Lemma unguard : forall A (x:A), guard x = x.
Proof.
  reflexivity.
Qed.
Opaque guard.

(* Define arbitrary tail-recursive functions as co-fixpoint returning a [Delay
   A]. *)
CoInductive Delay A :=
 | Now (x:A)
 | Later (x:Delay A).
Arguments Now {A}.
Arguments Later {A}.

CoFixpoint rush (s : State) : Delay (option Model) :=
  if is_empty (s.(state_falsified)) then
    Now None
      (* TODO: add an is_empty predicate to ClauseMap directly *)
  else
    if is_empty (ClauseMap.keys s.(state_clauses)) then
      Now (Some s.(state_model))
    else
      Later (rush (progress s)).
    
