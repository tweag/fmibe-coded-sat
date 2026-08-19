(* Specifications and proofs for the CDCL SAT solver  *)

Require Import FMV.CDCL.Impl.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.

(* A semantic model is simply a function. Because variables are decidable, we
   can always extend a finite model to a model on all possible variables. *)
Definition SModel := Var -> bool.

Definition satisfies_literal (m : SModel) (l : Literal) : bool :=
  match l with
  | Pos v => m v
  | Neg v => negb (m v)
  end.

Definition satisfies_clause (m : SModel) (c : Clause) : bool :=
  existsb (satisfies_literal m) c.

(* Sanity check *)
Lemma app_or : forall m l r,
  satisfies_clause m (l ++ r) =
  (satisfies_clause m l || satisfies_clause m r).
Proof.
  intros m l r.
  unfold satisfies_clause.
  rewrite existsb_app.
  reflexivity.
Qed.

Definition satisfies_problem (m : SModel) (p : Problem) : bool :=
  forallb (satisfies_clause m) p.

(* Sanity check *)
Lemma app_and : forall m l r,
  satisfies_problem m (l ++ r) =
  (satisfies_problem m l && satisfies_problem m r).
Proof.
  intros m l r.
  unfold satisfies_problem.
  rewrite forallb_app.
  reflexivity.
Qed.

Definition lit_is_me (v : Var) (l : Literal) : bool :=
  literal_var l =? v.

(* Sets all the variables absent from `m` to `false` *)
Definition complete_model (m : Model) : SModel :=
  fun v => match List.find (fun l => lit_is_me v l) m with
        | Some (Pos _) => true
        | Some (Neg _) => false
        | None => false
        end.

Definition InL (v : Var) (l : list Literal) : Prop :=
  In (Pos v) l \/ In (Neg v) l.

Lemma literal_InL : forall l c, In l c -> InL (literal_var l) c.
Proof.
  intros [v|v] c Hin; [left|right]; exact Hin.
Qed.

Definition pending_clauses (pending : Pending) : list Clause :=
  map snd pending.

(* A queued reason represents the second watch of its unit clause. *)
Definition card_of_watch (work : list Clause) (c : Clause) (s : State) :=
  ClauseMap.card_of c s.(state_clauses) +
    count_occ clause_eq_dec
      (work ++ pending_clauses s.(state_pending)) c.

Definition staged_invariant (work : list Clause) (s : State) : Prop :=
  (forall c, In c s.(state_satisfied) ->
     Is_true (existsb (literal_is_true s.(state_model)) c))
  /\ (forall c, In c s.(state_falsified) ->
     Is_true (negb (existsb (literal_is_true s.(state_model)) c)) /\
     filter (literal_is_undecided s.(state_model)) c = [])
  /\ (forall v c, In c (ClauseMap.find v s.(state_clauses)) ->
     ~ InL v s.(state_model) /\ InL v c)
  /\ (forall v, NoDup (ClauseMap.find v s.(state_clauses)))
  /\ NoDup (work ++ pending_clauses s.(state_pending))
  /\ (forall l c, In (l, c) s.(state_pending) ->
     In l c /\ literal_is_undecided s.(state_model) l = true)
  /\ (forall c, card_of_watch work c s = 0 \/ card_of_watch work c s = 2).

Definition state_invariant (s : State) : Prop := staged_invariant [] s.

Lemma empty_state_inv : forall m,
  state_invariant
    {| state_model := m; state_clauses := ClauseMap.empty;
       state_satisfied := []; state_falsified := []; state_pending := [] |}.
Proof.
  intros m. split.
  - intros c H. contradiction.
  - split.
    + intros c H. contradiction.
    + split.
      * intros v c H. rewrite ClauseMap.find_empty in H. contradiction.
      * split.
        -- intros v. rewrite ClauseMap.find_empty. constructor.
        -- split; [constructor|]. split.
           ++ intros l c H. contradiction.
           ++ intros c. unfold card_of_watch, pending_clauses.
              cbn [state_clauses state_pending].
              rewrite ClauseMap.card_of_empty. now left.
Qed.
