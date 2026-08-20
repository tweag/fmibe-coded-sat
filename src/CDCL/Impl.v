(* The core loop of a CDCL-based SAT solver *)

Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import FMV.FiniteMap.
Require Import FMV.ListMap.
Require Import FMV.Map.

(* General architecture:
   - Iterate until find a model or a definite contradiction:
     - Attempt to guess a model with the `rush` function
       - Rush is simply an iteration of the `progress` function which steps
         through the CDCL algorithm. Either deciding or propagating a literal at
         every iteration.
     - (TODO) Learn a conflict clause and backtrack.
 *)

Definition Var := nat.
Variant Literal :=
  | Pos (l : Var)
  | Neg (l : Var)
.
Definition neg_lit (l : Literal) : Literal :=
  match l with
  | Pos v => Neg v
  | Neg v => Pos v
  end.

Definition Clause := list Literal.
Definition ClauseId := nat.

Definition Problem := list Clause.

(* A conjunction of literal. Used to represent conflicts and such *)
Definition Conj := list Literal.

Definition neg (c : Clause) : Conj := map neg_lit c.

(* A partial model. The semantics is that `Pos` literals in the list are known
   to be true, `Neg` literals are known to be false. The rest is (yet)
   undecided. *)
Definition Model := list Literal.
Definition Pending := list (Literal * ClauseId).

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

Module ClauseIdElement.
  Definition t := ClauseId.
  Definition eq_dec := Nat.eq_dec.
End ClauseIdElement.

Module ClauseMap := ListMap.Make VarKey ClauseIdElement.

Module ClauseValue.
  Definition t := Clause.
End ClauseValue.

Module ClauseStore := Map.Make VarKey ClauseValue.

Record State := {
  state_model : Model;
  state_clauses : ClauseStore.t;
  (* `state_watched` implements two-literal watch. *)
  state_watched : ClauseMap.t;
  state_falsified : list ClauseId;
  state_pending : Pending;
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

Definition literal_is_decided (m : Model) (l : Literal) : Prop :=
  literal_is_undecided m l = false.

Fixpoint scan_clause_once (m : Model) (c : Clause) : bool * list Literal :=
  match c with
  | [] => (false, [])
  | l :: c' =>
      let '(satisfied, undecided) := scan_clause_once m c' in
      (orb (literal_is_true m l) satisfied,
       if literal_is_undecided m l then l :: undecided else undecided)
  end.

Variant scan_result :=
  | propagate_literal (l : Literal) (cm : ClauseMap.t)
  | clause_decided (cm : ClauseMap.t) (fals : list ClauseId)
  | clause_watched (cm : ClauseMap.t).

Fixpoint find_different_var (v : Var) (ls : list Literal) : option Literal :=
  match ls with
  | [] => None
  | l :: ls' =>
      if Nat.eqb v (literal_var l) then find_different_var v ls' else Some l
  end.

(* Is [c] satisfied? falsified? otherwise watch an additional literal *)
Definition scan_clause (m : Model) (ci : ClauseId) (c : Clause)
    (cm : ClauseMap.t) (fals : list ClauseId) : scan_result :=
  let '(satisfied, undecided) := scan_clause_once m c in
  if satisfied then
      clause_decided cm fals
  else
    match undecided with
    | [] => clause_decided cm (ci :: fals)
    | l :: undecided' =>
        match find_different_var (literal_var l) undecided' with
        | None =>
            if in_dec Nat.eq_dec ci (ClauseMap.find (literal_var l) cm) then
              propagate_literal l cm
            else
              propagate_literal l
                (ClauseMap.add (literal_var l) ci cm)
        | Some l' =>
            if in_dec Nat.eq_dec ci (ClauseMap.find (literal_var l) cm) then
              clause_watched (ClauseMap.add (literal_var l') ci cm)
            else clause_watched (ClauseMap.add (literal_var l) ci cm)
        end
    end.

Definition propagate (ci : ClauseId) (s : State) : State :=
  match ClauseStore.find ci s.(state_clauses) with
  | None => s
  | Some c =>
    match scan_clause s.(state_model) ci c s.(state_watched)
        s.(state_falsified) with
    | propagate_literal l cm =>
      {| state_model := s.(state_model);
         state_clauses := s.(state_clauses);
         state_watched := cm;
         state_falsified := s.(state_falsified);
         state_pending := (l, ci) :: s.(state_pending) |}
    | clause_decided cm fals =>
      {| state_model := s.(state_model); state_clauses := s.(state_clauses);
         state_watched := cm;
         state_falsified := fals;
         state_pending := s.(state_pending) |}
    | clause_watched cm =>
      {| state_model := s.(state_model); state_clauses := s.(state_clauses);
         state_watched := cm;
         state_falsified := s.(state_falsified);
         state_pending := s.(state_pending) |}
    end
  end.

Definition set_lit (l : Literal) (s : State) : State :=
  let watched := ClauseMap.find (literal_var l) s.(state_watched) in
  let cm := ClauseMap.remove (literal_var l) s.(state_watched) in
  let s' := {| state_model := l :: s.(state_model);
      state_clauses := s.(state_clauses); state_watched := cm;
      state_falsified := s.(state_falsified);
      state_pending := s.(state_pending) |} in
  fold_left (fun s c => propagate c s) watched s'.

(* Game plan: to progress the state:
   - If there is a pending propagation, assign its literal using its clause as
     the explanation.
   - Otherwise
     1. choose an undecided variable
     2. Set it to `true` in the model
     3. Wake up and process every clause currently watching this literal. *)
Definition progress_state (s : State) : State :=
  match s.(state_pending) with
  | (l, c) :: pending =>
      match literal_value s.(state_model) l with
      | Some true =>
        {| state_model := s.(state_model);
           state_clauses := s.(state_clauses);
           state_watched := s.(state_watched);
           state_falsified := s.(state_falsified);
           state_pending := pending |}
      | Some false =>
        {| state_model := s.(state_model);
           state_clauses := s.(state_clauses);
           state_watched := s.(state_watched);
           state_falsified := s.(state_falsified);
           state_pending := pending |}
      | None =>
        set_lit l
          {| state_model := s.(state_model);
             state_clauses := s.(state_clauses);
             state_watched := s.(state_watched);
             state_falsified := s.(state_falsified);
             state_pending := pending |}
      end
  | [] =>
      match hd_error (ClauseMap.keys s.(state_watched)) with
      | None => s (* All the literal have been decided so no progress can be made *)
      | Some v =>
          set_lit (Pos v) s
      end
  end.

Variant progress_result :=
  | Progress (s : State)
  | Conflict (explanation : Conj).

Definition finish_progress (s : State) : progress_result :=
  match s.(state_falsified) with
  | [] => Progress s
  | ci :: _ =>
      match ClauseStore.find ci s.(state_clauses) with
      | Some c => Conflict (neg c)
      | None => Conflict []
      end
  end.

Definition progress (s : State) : progress_result :=
  match s.(state_pending) with
  | (l, c) :: _ =>
      match literal_value s.(state_model) l with
      | Some false =>
          match ClauseStore.find c s.(state_clauses) with
          | Some clause => Conflict (neg clause)
          | None => Conflict []
          end
      | _ => finish_progress (progress_state s)
      end
  | [] => finish_progress (progress_state s)
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

(* Note: here's a termination metric, the lexicographically ordered
   `((number of watched literal - number of pending literal), number of pending literal)` *)
CoFixpoint rush (s : State) : Delay (Model + Conj) :=
  (* TODO: add an is_empty predicate to ClauseMap directly *)
  if is_empty (ClauseMap.keys s.(state_watched)) then
    Now (inl s.(state_model))
  else
    match progress s with
    | Progress s' => Later (rush s')
    | Conflict explanation => Now (inr explanation)
    end.
    
