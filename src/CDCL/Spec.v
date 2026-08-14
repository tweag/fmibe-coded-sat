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

(* number of variables watched by a clause. Including the variables currently
  being set (that is occurrences in the list of pending clauses). *)
Definition card_of_watch (c : Clause) (s : State) :=
  ClauseMap.card_of c (s.(state_clauses)) + count_occ clause_eq_dec (s.(state_pending)) c.

(* This invariant is always preserved of states *)
Definition state_invariant (s : State) : Prop :=
  (* Statisfied clauses are, indeed, satisfied. *)
  (forall c, In c s.(state_satisfied)
       -> Is_true (existsb (literal_is_true s.(state_model)) c))
  (* Falsified clauses are, indeed, falsified. *)
  /\ (forall c, In c s.(state_falsified)
         -> Is_true (negb (existsb (literal_is_true s.(state_model)) c)) /\
           filter (literal_is_undecided s.(state_model)) c = [])
  (* Clauses watch undecided literal, which they feature. *)
  /\ (forall v c, In c (ClauseMap.find v s.(state_clauses))
            -> ~ InL v s.(state_model) /\ InL v c)
  (* No duplicated clause in a watch list*)
  /\ (forall v, NoDup (ClauseMap.find v s.(state_clauses)))
  (* Clauses watch two literals. *)
  /\ (forall c, card_of_watch c s = 0 \/ card_of_watch c s = 2)
.

Lemma literal_is_true_spec : forall m l,
  literal_is_true m l = true ->
  satisfies_literal (complete_model m) l = true.
Proof.
  intros m [v|v]; unfold literal_is_true, literal_value,
    satisfies_literal, complete_model, lit_is_me.
  all: cbn [literal_var].
  all: destruct (find (fun l' : Literal => literal_var l' =? v) m)
         as [[v'|v']|] eqn:Hfind; cbn [literal_var] in Hfind |-;
         try rewrite Hfind; cbn; congruence.
Qed.

Lemma literal_is_undecided_false : forall m l,
  literal_is_true m l = false ->
  literal_is_undecided m l = false ->
  satisfies_literal (complete_model m) l = false.
Proof.
  intros m [v|v]; unfold literal_is_true, literal_is_undecided,
    literal_value, satisfies_literal, complete_model, lit_is_me.
  all: cbn [literal_var].
  all: destruct (find (fun l' : Literal => literal_var l' =? v) m)
         as [[v'|v']|] eqn:Hfind; cbn [literal_var] in Hfind |-;
         try rewrite Hfind; cbn; congruence.
Qed.

Lemma clause_true_spec : forall m c,
  existsb (literal_is_true m) c = true ->
  Is_true (satisfies_clause (complete_model m) c).
Proof.
  intros m c H.
  apply Is_true_eq_left.
  apply existsb_exists in H.
  destruct H as [l [Hin Htrue]].
  apply existsb_exists. exists l. split; [exact Hin|].
  now apply literal_is_true_spec.
Qed.

Lemma clause_false_spec : forall m c,
  existsb (literal_is_true m) c = false ->
  filter (literal_is_undecided m) c = [] ->
  Is_true (negb (satisfies_clause (complete_model m) c)).
Proof.
  intros m c Htrue Hundecided.
  apply Is_true_eq_left.
  rewrite Bool.negb_true_iff.
  unfold satisfies_clause.
  destruct (existsb (satisfies_literal (complete_model m)) c)
    eqn:Hsat; [|reflexivity].
  exfalso. apply existsb_exists in Hsat.
  destruct Hsat as [l [Hin Hsat]].
  assert (literal_is_true m l = false) as Hltrue.
  { destruct (literal_is_true m l) eqn:Hl; [|reflexivity].
    assert (existsb (literal_is_true m) c = true) as Hexists.
    { apply existsb_exists. now exists l. }
    congruence. }
  assert (literal_is_undecided m l = false) as Hlundecided.
  { destruct (literal_is_undecided m l) eqn:Hlu; [|reflexivity].
    assert (In l (filter (literal_is_undecided m) c)) as Hinfilter.
    { apply filter_In. now split. }
    rewrite Hundecided in Hinfilter. contradiction. }
  pose proof (literal_is_undecided_false m l Hltrue Hlundecided) as Hfalse.
  congruence.
Qed.

Lemma literal_undecided_not_InL : forall m l,
  literal_is_undecided m l = true ->
  ~ InL (literal_var l) m.
Proof.
  intros m l Hundecided [Hpos|Hneg].
  all: unfold literal_is_undecided, literal_value in Hundecided;
       destruct (find (fun l' => literal_var l' =? literal_var l) m)
         as [[v|v]|] eqn:Hfind.
  all: try (destruct l; discriminate).
  - pose proof (find_none _ _ Hfind _ Hpos) as Hfalse.
    cbn [literal_var] in Hfalse. now rewrite Nat.eqb_refl in Hfalse.
  - pose proof (find_none _ _ Hfind _ Hneg) as Hfalse.
    cbn [literal_var] in Hfalse. now rewrite Nat.eqb_refl in Hfalse.
Qed.

Lemma not_InL_literal_undecided : forall m l,
  ~ InL (literal_var l) m -> literal_is_undecided m l = true.
Proof.
  intros m l Hnotin. unfold literal_is_undecided, literal_value.
  destruct (find (fun x => literal_var x =? literal_var l) m)
    as [x|] eqn:Hfind; [|reflexivity].
  exfalso. apply find_some in Hfind as [Hin Hvars].
  apply Nat.eqb_eq in Hvars. apply Hnotin.
  destruct x as [v|v]; cbn [literal_var] in Hvars; subst v;
    [left|right]; exact Hin.
Qed.

Lemma literal_is_true_cons_undecided : forall m l x,
  literal_is_undecided m l = true ->
  literal_is_true m x = true ->
  literal_is_true (l :: m) x = true.
Proof.
  intros m l x Hlu Hxt.
  unfold literal_is_undecided, literal_is_true, literal_value in *.
  simpl. destruct (literal_var l =? literal_var x) eqn:Hvars.
  - apply Nat.eqb_eq in Hvars. rewrite Hvars in Hlu.
    destruct (find (fun l' => literal_var l' =? literal_var x) m) eqn:Hfind.
    + destruct l, l0; discriminate Hlu.
    + discriminate Hxt.
  - exact Hxt.
Qed.

Lemma literal_is_true_cons_self : forall m l,
  literal_is_true (l :: m) l = true.
Proof.
  intros m [v|v]; unfold literal_is_true, literal_value; simpl;
    rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma decided_literal_cons_undecided : forall m l x,
  literal_is_undecided m l = true ->
  literal_is_undecided m x = false ->
  literal_is_true (l :: m) x = literal_is_true m x /\
  literal_is_undecided (l :: m) x = false.
Proof.
  intros m l x Hlu Hxu.
  unfold literal_is_undecided, literal_is_true, literal_value in *.
  simpl. destruct (literal_var l =? literal_var x) eqn:Hvars.
  - apply Nat.eqb_eq in Hvars. rewrite Hvars in Hlu.
    destruct (find (fun l' => literal_var l' =? literal_var x) m)
      as [y|] eqn:Hfind.
    + destruct l, y; discriminate Hlu.
    + discriminate Hxu.
  - split; [reflexivity|exact Hxu].
Qed.

Lemma satisfied_cons_undecided : forall m l c,
  literal_is_undecided m l = true ->
  Is_true (existsb (literal_is_true m) c) ->
  Is_true (existsb (literal_is_true (l :: m)) c).
Proof.
  intros m l c Hlu Hsat. apply Is_true_eq_true in Hsat.
  apply Is_true_eq_left.
  apply existsb_exists in Hsat as [x [Hxc Hxt]].
  apply existsb_exists. exists x. split; [exact Hxc|].
  now apply literal_is_true_cons_undecided.
Qed.

Lemma falsified_cons_undecided : forall m l c,
  literal_is_undecided m l = true ->
  Is_true (negb (existsb (literal_is_true m) c)) /\
    filter (literal_is_undecided m) c = [] ->
  Is_true (negb (existsb (literal_is_true (l :: m)) c)) /\
    filter (literal_is_undecided (l :: m)) c = [].
Proof.
  intros m l c Hlu. induction c as [|x xs IH]; intros [Hfalse Hdecided].
  - now split.
  - simpl in Hfalse, Hdecided |- *.
    destruct (literal_is_undecided m x) eqn:Hxu; [discriminate|].
    destruct (decided_literal_cons_undecided m l x Hlu Hxu)
      as [Htrue Hxu'].
    rewrite Hxu'. simpl. rewrite Htrue.
    destruct (literal_is_true m x); simpl in Hfalse |- *.
    + contradiction.
    + apply IH. now split.
Qed.

Lemma find_different_var_spec : forall v ls l,
  find_different_var v ls = Some l ->
  In l ls /\ v <> literal_var l.
Proof.
  intros v ls. induction ls as [|x xs IH]; intros l Hfind; simpl in Hfind.
  - discriminate.
  - destruct (v =? literal_var x) eqn:Heq.
    + destruct (IH l Hfind) as [Hin Hneq]. now split; [right|].
    + injection Hfind as ->. split; [now left|].
      now apply Nat.eqb_neq.
Qed.

Lemma scan_clause_once_spec : forall m c,
  scan_clause_once m c =
    (existsb (literal_is_true m) c, filter (literal_is_undecided m) c).
Proof.
  intros m c. induction c as [|l c IH]; simpl; [reflexivity|].
  now rewrite IH.
Qed.

Lemma scan_clause_inl_spec : forall m c cm sat fals l,
  scan_clause m c cm sat fals = propagate_literal l ->
  In l c /\ literal_is_undecided m l = true.
Proof.
  intros m c cm sat fals l Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c); [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|x xs]
    eqn:Hfilter; [discriminate|].
  destruct (find_different_var (literal_var x) xs).
  - destruct (in_dec clause_eq_dec c (ClauseMap.find (literal_var x) cm));
      discriminate.
  - injection Hscan as <-.
  assert (In x (filter (literal_is_undecided m) c)) as Hin.
  { rewrite Hfilter. now left. }
  now apply filter_In in Hin.
Qed.

Lemma count_occ_remove_clause_from_list_eq : forall cs c,
  count_occ clause_eq_dec (remove_clause_from_list c cs) c = 0.
Proof.
  intros cs. induction cs as [|d cs IH]; intros c; simpl.
  - reflexivity.
  - destruct (clause_eq_dec c d) as [->|Hneq]; simpl.
    + exact (IH d).
    + destruct (clause_eq_dec d c) as [Heq|_]; [congruence|]. exact (IH c).
Qed.

Lemma count_occ_remove_clause_from_list_neq : forall cs c d,
  c <> d ->
  count_occ clause_eq_dec (remove_clause_from_list c cs) d =
    count_occ clause_eq_dec cs d.
Proof.
  intros cs. induction cs as [|x xs IH]; intros c d Hneq; simpl.
  - reflexivity.
  - destruct (clause_eq_dec c x) as [->|Hcx]; simpl.
    + destruct (clause_eq_dec x d) as [Heq|_]; [congruence|].
      apply IH. exact Hneq.
    + destruct (clause_eq_dec x d); simpl; rewrite IH by exact Hneq;
        reflexivity.
Qed.

Lemma remove_clause_from_list_cons_eq : forall c cs,
  remove_clause_from_list c (c :: cs) = remove_clause_from_list c cs.
Proof.
  intros c cs. unfold remove_clause_from_list. simpl.
  destruct (clause_eq_dec c c); [reflexivity|contradiction].
Qed.

Lemma remove_pending_clause_inv : forall m cm sat fals pending c,
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := c :: pending |} ->
  state_invariant
    {| state_model := m; state_clauses := ClauseMap.remove_clause c cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := remove_clause_from_list c pending |}.
Proof.
  intros m cm sat fals pending c
    [Hsat [Hfals [Hundecided [Hnodup Hcard]]]].
  split; [exact Hsat|]. split; [exact Hfals|]. split.
  - intros v d Hin. apply ClauseMap.find_remove_clause in Hin as [Hin _].
    now apply Hundecided with (c := d).
  - split.
    + intros v. cbn [state_clauses]. rewrite ClauseMap.find_remove_clause_eq.
      apply NoDup_filter. apply Hnodup.
    + intros d. destruct (clause_eq_dec c d) as [->|Hcd].
      * unfold card_of_watch. cbn [state_clauses state_pending].
        rewrite ClauseMap.card_of_remove_clause_eq.
        rewrite count_occ_remove_clause_from_list_eq. now left.
      * unfold card_of_watch in Hcard |- *.
        cbn [state_clauses state_pending] in Hcard |- *.
        rewrite ClauseMap.card_of_remove_clause_neq by exact Hcd.
        rewrite count_occ_remove_clause_from_list_neq by exact Hcd.
        specialize (Hcard d). simpl in Hcard.
        destruct (clause_eq_dec c d); [contradiction|exact Hcard].
Qed.

Lemma add_satisfied_inv : forall m cm sat fals pending c,
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |} ->
  Is_true (existsb (literal_is_true m) c) ->
  state_invariant
    {| state_model := m; state_clauses := ClauseMap.remove_clause c cm;
       state_satisfied := c :: sat; state_falsified := fals;
       state_pending := remove_clause_from_list c pending |}.
Proof.
  intros m cm sat fals pending c
    [Hsat [Hfals [Hundecided [Hnodup Hcard]]]] Hc.
  split.
  - intros d [->|Hin]; [exact Hc|now apply Hsat].
  - split; [exact Hfals|]. split.
    + intros v d Hin. apply ClauseMap.find_remove_clause in Hin as [Hin _].
      now apply Hundecided with (c := d).
    + split.
      * intros v. cbn [state_clauses]. rewrite ClauseMap.find_remove_clause_eq.
        apply NoDup_filter. apply Hnodup.
      * intros d. destruct (clause_eq_dec c d) as [->|Hcd].
        -- unfold card_of_watch. cbn [state_clauses state_pending].
           rewrite ClauseMap.card_of_remove_clause_eq.
           rewrite count_occ_remove_clause_from_list_eq. now left.
        -- unfold card_of_watch in Hcard |- *.
           cbn [state_clauses state_pending] in Hcard |- *.
           rewrite ClauseMap.card_of_remove_clause_neq by exact Hcd.
           rewrite count_occ_remove_clause_from_list_neq by exact Hcd.
           apply Hcard.
Qed.

Lemma add_falsified_inv : forall m cm sat fals pending c,
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |} ->
  (Is_true (negb (existsb (literal_is_true m) c)) /\
    filter (literal_is_undecided m) c = []) ->
  state_invariant
    {| state_model := m; state_clauses := ClauseMap.remove_clause c cm;
       state_satisfied := sat; state_falsified := c :: fals;
       state_pending := remove_clause_from_list c pending |}.
Proof.
  intros m cm sat fals pending c Hinv Hc.
  destruct Hinv as [Hsat [Hfals [Hundecided [Hnodup Hcard]]]].
  split; [exact Hsat|]. split.
  - intros d [->|Hin]; [exact Hc|now apply Hfals].
  - split.
    + intros v d Hin. apply ClauseMap.find_remove_clause in Hin as [Hin _].
      now apply Hundecided with (c := d).
    + split.
      * intros v. cbn [state_clauses]. rewrite ClauseMap.find_remove_clause_eq.
        apply NoDup_filter. apply Hnodup.
      * intros d. destruct (clause_eq_dec c d) as [->|Hcd].
        -- unfold card_of_watch. cbn [state_clauses state_pending].
           rewrite ClauseMap.card_of_remove_clause_eq.
           rewrite count_occ_remove_clause_from_list_eq. now left.
        -- unfold card_of_watch in Hcard |- *.
           cbn [state_clauses state_pending] in Hcard |- *.
           rewrite ClauseMap.card_of_remove_clause_neq by exact Hcd.
           rewrite count_occ_remove_clause_from_list_neq by exact Hcd.
           apply Hcard.
Qed.

Lemma watch_one_fresh_inv : forall m cm sat fals pending c l,
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := c :: pending |} ->
  ~ In c (ClauseMap.find (literal_var l) cm) ->
  In l c -> literal_is_undecided m l = true ->
  state_invariant
    {| state_model := m; state_clauses := ClauseMap.add (literal_var l) c cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |}.
Proof.
  intros m cm sat fals pending c l Hinv Hfresh Hlc Hlu.
  destruct Hinv as [Hsat [Hfals [Hwatch [Hnodup Hcard]]]].
  split; [exact Hsat|]. split; [exact Hfals|]. split.
  - intros v d Hin. apply ClauseMap.find_add in Hin as [[-> ->]|Hin].
    + split; [now apply literal_undecided_not_InL|now apply literal_InL].
    + now apply Hwatch with (c := d).
  - split.
    + intros v. cbn [state_clauses]. rewrite ClauseMap.find_add_eq.
      destruct (VarKey.eq_dec (literal_var l) v) as [Heq|Hneq].
      * subst v. constructor; [exact Hfresh|apply Hnodup].
      * apply Hnodup.
    + intros d. unfold card_of_watch in Hcard |- *.
      cbn [state_clauses state_pending] in Hcard |- *.
      destruct (clause_eq_dec c d) as [->|Hcd].
      * rewrite ClauseMap.card_of_add. specialize (Hcard d). simpl in Hcard.
        destruct (clause_eq_dec d d) as [_|Habs]; [|contradiction]. lia.
      * rewrite ClauseMap.card_of_add_neq by exact Hcd.
        specialize (Hcard d). simpl in Hcard.
        destruct (clause_eq_dec c d); [contradiction|exact Hcard].
Qed.

Lemma watch_one_inv : forall m cm sat fals pending c l l' cm',
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := c :: pending |} ->
  In l c -> In l' c ->
  literal_is_undecided m l = true ->
  literal_is_undecided m l' = true ->
  literal_var l <> literal_var l' ->
  cm' = (if in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm)
    then ClauseMap.add (literal_var l') c cm
    else ClauseMap.add (literal_var l) c cm) ->
  state_invariant
    {| state_model := m;
       state_clauses := cm';
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |}.
Proof.
  intros m cm sat fals pending c l l' cm' Hinv Hlc Hl'c Hlu Hl'u Hneq
    Hcm'. subst cm'.
  destruct (in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm))
    as [Hwatched|Hfresh].
  - apply watch_one_fresh_inv; try assumption.
    intros Hwatched'.
    destruct Hinv as [_ [_ [_ [_ Hcard]]]].
    unfold card_of_watch in Hcard. cbn [state_clauses state_pending] in Hcard.
    pose proof (ClauseMap.card_of_in cm c (literal_var l) Hwatched) as Hpos.
    specialize (Hcard c). simpl in Hcard.
    destruct (clause_eq_dec c c) as [_|Habs]; [|contradiction].
    assert (ClauseMap.card_of c cm = 1) as Hone by lia.
    apply Hneq. eapply ClauseMap.card_of_unique; eauto.
  - now apply watch_one_fresh_inv.
Qed.

Lemma scan_clause_inv : forall m c cm sat fals pending cm' sat' fals',
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := c :: pending |} ->
  scan_clause m c cm sat fals = clause_decided cm' sat' fals' ->
  state_invariant
    {| state_model := m; state_clauses := cm';
       state_satisfied := sat'; state_falsified := fals';
       state_pending := remove_clause_from_list c pending |}.
Proof.
  intros m c cm sat fals pending cm' sat' fals' Hinv Hscan.
  unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c) eqn:Htrue.
  - injection Hscan as <- <- <-.
    rewrite <- remove_clause_from_list_cons_eq.
    apply add_satisfied_inv; [exact Hinv|]. now apply Is_true_eq_left.
  - destruct (filter (literal_is_undecided m) c) as [|l undecided]
      eqn:Hfilter.
    + injection Hscan as <- <- <-.
      rewrite <- remove_clause_from_list_cons_eq.
      apply add_falsified_inv; [exact Hinv|]. split.
      * apply Is_true_eq_left. now rewrite Bool.negb_true_iff.
      * exact Hfilter.
    + destruct (find_different_var (literal_var l) undecided) as [l'|].
      * destruct (in_dec clause_eq_dec c
          (ClauseMap.find (literal_var l) cm)); discriminate.
      * discriminate.
Qed.

Lemma scan_clause_watch_inv : forall m c cm sat fals pending cm',
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := c :: pending |} ->
  scan_clause m c cm sat fals = clause_watched cm' ->
  state_invariant
    {| state_model := m; state_clauses := cm';
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |}.
Proof.
  intros m c cm sat fals pending cm' Hinv Hscan.
  unfold scan_clause in Hscan. rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c); [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|l undecided]
    eqn:Hfilter; [discriminate|].
  destruct (find_different_var (literal_var l) undecided)
    as [l'|] eqn:Hdifferent; [|discriminate].
  assert (In l (filter (literal_is_undecided m) c)) as Hlfilter.
  { rewrite Hfilter. now left. }
  apply filter_In in Hlfilter as [Hlc Hlu].
  apply find_different_var_spec in Hdifferent as [Hl'undecided Hneq].
  assert (In l' (filter (literal_is_undecided m) c)) as Hl'filter.
  { rewrite Hfilter. now right. }
  apply filter_In in Hl'filter as [Hl'c Hl'u].
  destruct (in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm))
    as [Hwatched|Hfresh].
  - injection Hscan as <-. eapply watch_one_inv.
    + exact Hinv.
    + exact Hlc.
    + exact Hl'c.
    + exact Hlu.
    + exact Hl'u.
    + exact Hneq.
    +
    destruct (in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm));
      [reflexivity|contradiction].
  - injection Hscan as <-. eapply watch_one_inv.
    + exact Hinv.
    + exact Hlc.
    + exact Hl'c.
    + exact Hlu.
    + exact Hl'u.
    + exact Hneq.
    +
    destruct (in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm));
      [contradiction|reflexivity].
Qed.

Lemma empty_state_inv : forall m,
  state_invariant
    {| state_model := m; state_clauses := ClauseMap.empty;
       state_satisfied := []; state_falsified := [];
       state_pending := [] |}.
Proof.
  intros m. split.
  - intros c H. contradiction.
  - split.
    + intros c H. contradiction.
    + split.
      * intros v c H. rewrite ClauseMap.find_empty in H. contradiction.
      * split.
        -- intros v. rewrite ClauseMap.find_empty. constructor.
        -- intros c. unfold card_of_watch. cbn [state_clauses state_pending].
           rewrite ClauseMap.card_of_empty. now left.
Qed.

Lemma InL_cons_other : forall l m v,
  v <> literal_var l -> InL v (l :: m) -> InL v m.
Proof.
  intros [x|x] m v Hneq; unfold InL; simpl;
    intros [[Heq|Hin]|[Heq|Hin]].
  - injection Heq as ->. contradiction.
  - now left.
  - discriminate.
  - now right.
  - discriminate.
  - now left.
  - injection Heq as ->. contradiction.
  - now right.
Qed.

Lemma set_lit_inv : forall l s,
  literal_is_undecided s.(state_model) l = true ->
  state_invariant s -> state_invariant (set_lit l s).
Proof.
  intros l [m cm sat fals pending] Hlu Hinv.
  destruct Hinv as [Hsat [Hfals [Hundecided [Hnodup Hcard]]]].
  unfold set_lit. cbn [state_model state_clauses state_satisfied
    state_falsified state_pending].
  split.
  - intros c Hin. apply satisfied_cons_undecided; [exact Hlu|now apply Hsat].
  - split.
    + intros c Hin. apply falsified_cons_undecided; [exact Hlu|now apply Hfals].
    + split.
      * intros v c Hin.
        apply ClauseMap.find_remove in Hin as [Hin Hneq].
        destruct (Hundecided v c Hin) as [Hnotin Hinc]. split; [|exact Hinc].
        intros Hinmodel. apply Hnotin.
        eapply InL_cons_other; [exact Hneq|exact Hinmodel].
      * split.
        -- intros v. cbn [state_clauses]. rewrite ClauseMap.find_remove_eq.
           destruct (VarKey.eq_dec (literal_var l) v);
             [constructor|apply Hnodup].
        -- intros c. unfold card_of_watch in Hcard |- *.
           cbn [state_clauses state_pending] in Hcard |- *.
           rewrite count_occ_app.
           pose proof (ClauseMap.card_of_remove cm c (literal_var l))
             as Hremove.
           change (ClauseMap.card_of c (ClauseMap.remove (literal_var l) cm) +
             count_occ clause_eq_dec (ClauseMap.find (literal_var l) cm) c =
             ClauseMap.card_of c cm) in Hremove.
           destruct (Hcard c) as [Hzero|Htwo].
           { left.
             etransitivity.
             - exact (Nat.add_assoc
                 (ClauseMap.card_of c (ClauseMap.remove (literal_var l) cm))
                 (count_occ clause_eq_dec
                   (ClauseMap.find (literal_var l) cm) c)
                 (count_occ clause_eq_dec pending c)).
             - rewrite Hremove. exact Hzero. }
           { right.
             etransitivity.
             - exact (Nat.add_assoc
                 (ClauseMap.card_of c (ClauseMap.remove (literal_var l) cm))
                 (count_occ clause_eq_dec
                   (ClauseMap.find (literal_var l) cm) c)
                 (count_occ clause_eq_dec pending c)).
             - rewrite Hremove. exact Htwo. }
Qed.

Lemma propagate_inv : forall c s,
  state_invariant
    {| state_model := s.(state_model);
       state_clauses := s.(state_clauses);
       state_satisfied := s.(state_satisfied);
       state_falsified := s.(state_falsified);
       state_pending := c :: s.(state_pending) |} ->
  state_invariant (propagate c s).
Proof.
  intros c [m cm sat fals pending] Hinv.
  unfold propagate.
  cbn [state_model state_clauses state_satisfied state_falsified
    state_pending].
  destruct (scan_clause m c cm sat fals) as [l|cm' sat' fals'|cm']
    eqn:Hscan.
  - apply scan_clause_inl_spec in Hscan as [Hlc Hlu].
    pose proof (remove_pending_clause_inv m cm sat fals pending c Hinv)
      as Hclean.
    pose proof (set_lit_inv l
      {| state_model := m;
         state_clauses := ClauseMap.remove_clause c cm;
         state_satisfied := sat;
         state_falsified := fals;
         state_pending := remove_clause_from_list c pending |}
      Hlu Hclean) as Hset.
    unfold set_lit in Hset |- *.
    cbn [state_model state_clauses state_satisfied state_falsified
      state_pending] in Hset |- *.
    destruct Hset as [Hsat [Hfals [Hundecided [Hnodup Hcard]]]].
    split.
    + intros d [->|Hin].
      * apply Is_true_eq_left. apply existsb_exists. exists l.
        split; [exact Hlc|apply literal_is_true_cons_self].
      * now apply Hsat.
    + exact (conj Hfals (conj Hundecided (conj Hnodup Hcard))).
  - eapply scan_clause_inv; [exact Hinv|exact Hscan].
  - eapply scan_clause_watch_inv; [exact Hinv|exact Hscan].
Qed.

Lemma progress_inv : forall s, state_invariant s -> state_invariant (progress s).
Proof.
  intros [m cm sat fals pending] Hinv.
  unfold progress.
  cbn [state_pending state_model state_clauses state_satisfied
    state_falsified].
  destruct pending as [|c pending].
  - destruct (hd_error (ClauseMap.keys cm)) as [v|] eqn:Hhead.
    + apply set_lit_inv.
      * apply not_InL_literal_undecided.
        assert (In v (ClauseMap.keys cm)) as Hkey.
        { destruct (ClauseMap.keys cm) as [|x xs] eqn:Hkeys;
            [discriminate|].
          injection Hhead as <-. now left. }
        apply <- ClauseMap.keys_complete in Hkey.
        destruct (ClauseMap.find v cm) as [|c cs] eqn:Hfind;
          [contradiction|].
        pose proof Hinv as Hinv'.
        destruct Hinv' as [_ [_ [Hundecided _]]].
        assert (In c (ClauseMap.find v cm)) as Hin.
        { rewrite Hfind. now left. }
        exact (proj1 (Hundecided v c Hin)).
      * exact Hinv.
    + exact Hinv.
  - apply propagate_inv. exact Hinv.
Qed.
