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

Lemma literal_undecided_not_in : forall m l,
  literal_is_undecided m l = true -> ~ In l m.
Proof.
  induction m as [|x m IH]; intros l Hundecided Hin; [contradiction|].
  simpl in Hin. destruct Hin as [->|Hin].
  - unfold literal_is_undecided, literal_value in Hundecided. simpl in Hundecided.
    rewrite Nat.eqb_refl in Hundecided. destruct l; discriminate.
  - unfold literal_is_undecided, literal_value in Hundecided. simpl in Hundecided.
    destruct (literal_var x =? literal_var l) eqn:Heq;
      [destruct x, l; discriminate|].
    apply (IH l); [exact Hundecided|exact Hin].
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
  apply Is_true_eq_left. apply existsb_exists in Hsat as [x [Hxc Hxt]].
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

Lemma literal_decided_cons : forall m l x,
  literal_is_undecided m l = true ->
  literal_is_decided m x -> literal_is_decided (l :: m) x.
Proof.
  intros m l x Hlu Hdecided. unfold literal_is_decided in Hdecided |- *.
  exact (proj2 (decided_literal_cons_undecided m l x Hlu Hdecided)).
Qed.

Lemma literal_pending_cons : forall m l x,
  literal_is_undecided m l = true ->
  literal_is_undecided m x = true \/ literal_is_decided m x ->
  literal_is_undecided (l :: m) x = true \/ literal_is_decided (l :: m) x.
Proof.
  intros m l x Hlu [Hundecided|Hdecided].
  2:{ right. now apply literal_decided_cons. }
  destruct (Nat.eq_dec (literal_var l) (literal_var x)) as [Heq|Hneq].
  - right. destruct l as [v|v], x as [w|w]; cbn in Heq; subst w;
      unfold literal_is_decided, literal_is_undecided, literal_value;
      simpl; rewrite Nat.eqb_refl; reflexivity.
  - left. unfold literal_is_undecided, literal_value in Hundecided |- *.
    simpl. apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma literal_false_cons_undecided : forall m l x,
  literal_is_undecided m l = true ->
  literal_value m x = Some false ->
  literal_value (l :: m) x = Some false.
Proof.
  intros m l x Hlu Hfalse.
  unfold literal_is_undecided, literal_value in Hlu, Hfalse |- *.
  simpl. destruct (literal_var l =? literal_var x) eqn:Hvars.
  - apply Nat.eqb_eq in Hvars. rewrite Hvars in Hlu.
    destruct (find (fun l' => literal_var l' =? literal_var x) m)
      as [y|] eqn:Hfind; [|discriminate].
    destruct l, y; discriminate.
  - exact Hfalse.
Qed.

Definition watched_clause (ci : ClauseId) (s : State) : Prop :=
  exists v, In ci (ClauseMap.find v s.(state_watched)).

Definition has_opposite_literals (c : Clause) : Prop :=
  exists v, In (Pos v) c /\ In (Neg v) c.

Definition clause_needs_literal (m : Model) (l : Literal) (c : Clause) : Prop :=
  In l c /\
  forall x, In x c -> x <> l -> literal_value m x = Some false.

Lemma clause_needs_literal_cons : forall m l p c,
  literal_is_undecided m l = true ->
  clause_needs_literal m p c ->
  clause_needs_literal (l :: m) p c.
Proof.
  intros m l p c Hlu [Hpc Hneeds]. split; [exact Hpc|].
  intros x Hxc Hneq. eapply literal_false_cons_undecided; [exact Hlu|].
  now apply Hneeds.
Qed.

Definition decided_clause (ci : ClauseId) (s : State) : Prop :=
  In ci s.(state_falsified) \/
  exists c, ClauseStore.find ci s.(state_clauses) = Some c /\
    Is_true (existsb (literal_is_true s.(state_model)) c).

Definition card_of_watch (work : list ClauseId) (ci : ClauseId) (s : State) :=
  ClauseMap.card_of ci s.(state_watched).

Definition staged_invariant (work : list ClauseId) (s : State) : Prop :=
  (* Every clause which is not satisfied is covered.  [work] is the staged
     exception: its watches have just been removed and it is being scanned. *)
  (forall ci c, ClauseStore.find ci s.(state_clauses) = Some c ->
     Is_true (negb (existsb (literal_is_true s.(state_model)) c)) ->
     has_opposite_literals c \/
     In ci work \/ watched_clause ci s \/ In ci s.(state_falsified))
  /\ (* Falsified clause references exist and have the expected semantics. *)
  (forall ci, In ci s.(state_falsified) ->
     exists c, ClauseStore.find ci s.(state_clauses) = Some c /\
       Is_true (negb (existsb (literal_is_true s.(state_model)) c)) /\
       filter (literal_is_undecided s.(state_model)) c = [])
  /\ (* Every watched reference exists and watches a literal of its clause. *)
  (forall v ci, In ci (ClauseMap.find v s.(state_watched)) ->
     exists c, ClauseStore.find ci s.(state_clauses) = Some c /\
       ~ InL v (trail_model s.(state_model)) /\ InL v c /\
       ~ has_opposite_literals c)
  /\ (forall v, NoDup (ClauseMap.find v s.(state_watched)))
  /\ NoDup work
  /\ (forall ci, In ci work ->
     exists c, ClauseStore.find ci s.(state_clauses) = Some c /\
       ~ has_opposite_literals c)
  /\ (* Pending clauses genuinely need their pending literal. *)
  (forall l ci, In (l, ci) s.(state_pending) ->
     exists c, ClauseStore.find ci s.(state_clauses) = Some c /\
       clause_needs_literal s.(state_model) l c /\
       ~ has_opposite_literals c)
  /\ (forall ci, In ci work ->
     card_of_watch work ci s = 1 \/
     (card_of_watch work ci s = 0 /\
       ((exists l, In (l, ci) s.(state_pending)) \/
        decided_clause ci s)))
  /\ (forall ci,
     card_of_watch work ci s = 0 \/
     card_of_watch work ci s = 2 \/
     (card_of_watch work ci s = 1 /\
       (In ci work \/
        (exists l, In (l, ci) s.(state_pending)) \/
        decided_clause ci s))).

Definition state_invariant (s : State) : Prop := staged_invariant [] s.

Lemma staged_invariant_trail_ext : forall work t t' clauses cm fals pending,
  trail_model t = trail_model t' ->
  staged_invariant work
    {| state_model := t; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |} ->
  staged_invariant work
    {| state_model := t'; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |}.
Proof.
  intros work t t' clauses cm fals pending Hmodel Hinv.
  unfold staged_invariant, watched_clause, decided_clause,
    card_of_watch in Hinv |- *.
  cbn [state_model state_clauses state_watched state_falsified
    state_pending] in Hinv |- *.
  now rewrite <- Hmodel.
Qed.

Lemma empty_state_inv : forall m,
  state_invariant
    {| state_model := m; state_clauses := ClauseStore.empty;
       state_watched := ClauseMap.empty;
       state_falsified := []; state_pending := [] |}.
Proof.
  intros m. split.
  - intros ci c Hfind _. rewrite ClauseStore.find_empty in Hfind. discriminate.
  - split.
    + intros ci H. contradiction.
    + split.
      * intros v ci H. rewrite ClauseMap.find_empty in H. contradiction.
      * split.
        -- intros v. rewrite ClauseMap.find_empty. constructor.
        -- split; [constructor|]. split.
           ++ intros ci H. contradiction.
           ++ split.
              ** intros l ci H. contradiction.
              ** split.
                 --- intros ci H. contradiction.
                 --- intros ci. unfold card_of_watch. cbn [state_watched].
                     rewrite ClauseMap.card_of_empty. now left.
Qed.

Lemma scan_clause_once_spec : forall m c,
  scan_clause_once m c =
    (existsb (literal_is_true m) c, filter (literal_is_undecided m) c).
Proof.
  intros m c. induction c as [|l c IH]; simpl; [reflexivity|].
  now rewrite IH.
Qed.

Lemma literal_eqb_spec : forall l r,
  literal_eqb l r = true <-> l = r.
Proof.
  intros l r. unfold literal_eqb. destruct (literal_eq_dec l r) as [->|Hneq].
  - split; intros; reflexivity.
  - split; intros H; [discriminate|contradiction].
Qed.

Lemma clause_has_opposite_literals_spec : forall c,
  clause_has_opposite_literals c = true <-> has_opposite_literals c.
Proof.
  intros c. unfold clause_has_opposite_literals. rewrite existsb_exists.
  split.
  - intros [l [Hlc Hopp]]. apply existsb_exists in Hopp as [l' [Hl'c Heq]].
    apply literal_eqb_spec in Heq. subst l'. destruct l as [v|v].
    + exists v. now split.
    + exists v. now split.
  - intros [v [Hpos Hneg]]. exists (Pos v). split; [exact Hpos|].
    apply existsb_exists. exists (Neg v). split; [exact Hneg|].
    now apply literal_eqb_spec.
Qed.

Lemma fold_max_ge : forall xs x,
  In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  intros xs. induction xs as [|y ys IH]; intros x Hin; [contradiction|].
  simpl. destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
Qed.

Lemma fresh_clause_id_not_in : forall s,
  ~ In (fresh_clause_id s) (ClauseStore.keys s.(state_clauses)).
Proof.
  intros s Hin. unfold fresh_clause_id in Hin.
  pose proof (fold_max_ge _ _ Hin). lia.
Qed.

Lemma fresh_clause_id_fresh : forall s,
  ClauseStore.find (fresh_clause_id s) s.(state_clauses) = None.
Proof.
  intros s. destruct (ClauseStore.find (fresh_clause_id s)
    s.(state_clauses)) eqn:Hfind; [|reflexivity].
  exfalso. apply (fresh_clause_id_not_in s).
  apply (proj1 (ClauseStore.keys_complete _ _)). congruence.
Qed.

Lemma find_added_clause : forall s c,
  ClauseStore.find (fresh_clause_id s)
    (ClauseStore.add (fresh_clause_id s) c s.(state_clauses)) = Some c.
Proof.
  intros s c. rewrite ClauseStore.find_add_eq.
  destruct (VarKey.eq_dec (fresh_clause_id s) (fresh_clause_id s));
    [reflexivity|contradiction].
Qed.

Lemma find_old_clause_after_add : forall s c ci body,
  ClauseStore.find ci s.(state_clauses) = Some body ->
  ClauseStore.find ci
    (ClauseStore.add (fresh_clause_id s) c s.(state_clauses)) = Some body.
Proof.
  intros s c ci body Hfind. rewrite ClauseStore.find_add_eq.
  destruct (VarKey.eq_dec (fresh_clause_id s) ci) as [Heq|Hneq].
  - subst ci. rewrite fresh_clause_id_fresh in Hfind. discriminate.
  - exact Hfind.
Qed.

Lemma fresh_clause_not_watched : forall s v,
  state_invariant s ->
  ~ In (fresh_clause_id s) (ClauseMap.find v s.(state_watched)).
Proof.
  intros s v Hinv Hin. destruct Hinv as [_ [_ [Hwatch _]]].
  destruct (Hwatch v (fresh_clause_id s) Hin) as [c [Hfind _]].
  rewrite fresh_clause_id_fresh in Hfind. discriminate.
Qed.

Lemma add_resolved_clause_inv : forall s c,
  state_invariant s ->
  (Is_true (existsb (literal_is_true s.(state_model)) c) \/
   has_opposite_literals c) ->
  state_invariant
    {| state_model := s.(state_model);
       state_clauses := ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_watched := s.(state_watched);
       state_falsified := s.(state_falsified);
       state_pending := s.(state_pending) |}.
Proof.
  intros s c Hinv Hresolved. destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork Hcard]]]]]]]].
  assert (Hdecided : forall d, decided_clause d s ->
    decided_clause d
      {| state_model := s.(state_model);
         state_clauses := ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
         state_watched := s.(state_watched);
         state_falsified := s.(state_falsified);
         state_pending := s.(state_pending) |}).
  { intros d [Hd|[body [Hfind Htrue]]]; [now left|].
    right. exists body. split; [now apply find_old_clause_after_add|exact Htrue]. }
  repeat split; try assumption.
  - intros d body Hfind Hfalse. cbn [state_clauses] in Hfind.
    rewrite ClauseStore.find_add_eq in Hfind.
    destruct (VarKey.eq_dec (fresh_clause_id s) d) as [Heq|Hneq].
    + injection Hfind as <-. destruct Hresolved as [Htrue|Htrivial].
      * exfalso. exact (negb_prop_elim _ Hfalse Htrue).
      * now left.
    + now apply Hcover with (ci := d).
  - intros d Hd. destruct (Hfals d Hd) as [body [Hfind Hsem]].
    exists body. split; [now apply find_old_clause_after_add|exact Hsem].
  - intros v d Hd. destruct (Hwatch v d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_old_clause_after_add|exact Hrest].
  - intros d Hd. destruct (Hworkref d Hd) as [body [Hfind Hnoopp]].
    exists body. split; [now apply find_old_clause_after_add|exact Hnoopp].
  - intros l d Hd. destruct (Hpending l d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_old_clause_after_add|exact Hrest].
  - intros d Hd. contradiction.
  - intros d. specialize (Hcard d).
    destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
    + now left.
    + now right; left.
    + right. right. split; [exact Hone|].
      destruct Hwhy as [Habs|[Hpendingd|Hdecided']].
      * contradiction.
      * now right; left.
      * right. right. now apply Hdecided.
Qed.

Lemma add_clause_conflict_spec : forall s c s' cause,
  add_clause s c = Conflict s' cause ->
  cause = c /\
  s'.(state_model) = s.(state_model) /\
  s'.(state_clauses) =
    ClauseStore.add (fresh_clause_id s) c s.(state_clauses) /\
  ClauseStore.find (fresh_clause_id s) s'.(state_clauses) = Some c /\
  Is_true (negb (existsb (literal_is_true s'.(state_model)) c)) /\
  filter (literal_is_undecided s'.(state_model)) c = [].
Proof.
  intros [m clauses cm fals pending] c s' cause Hadd.
  unfold add_clause in Hadd. cbn [state_model state_clauses state_watched
    state_falsified state_pending] in Hadd |- *.
  rewrite scan_clause_once_spec in Hadd.
  destruct (existsb (literal_is_true m) c) eqn:Hsatisfied;
    cbn in Hadd; [discriminate|].
  destruct (clause_has_opposite_literals c) eqn:Hopposite;
    cbn in Hadd; [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|l undecided]
    eqn:Hundecided.
  - injection Hadd as <- <-. repeat split; try assumption.
    + apply find_added_clause.
    + cbn [state_model]. apply Is_true_eq_left. now rewrite Hsatisfied.
  - destruct (find_different_var (literal_var l) undecided);
      discriminate.
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

Lemma scan_clause_inl_spec : forall m ci c cm fals l,
  forall cm', scan_clause m ci c cm fals = propagate_literal l cm' ->
  existsb (literal_is_true m) c = false /\
  In l c /\ literal_is_undecided m l = true /\
  cm' = (if in_dec Nat.eq_dec ci (ClauseMap.find (literal_var l) cm)
    then cm else ClauseMap.add (literal_var l) ci cm).
Proof.
  intros m ci c cm fals l cm' Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c) eqn:Hfalse; [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|x xs]
    eqn:Hfilter; [discriminate|].
  destruct (find_different_var (literal_var x) xs).
  - destruct (in_dec Nat.eq_dec ci (ClauseMap.find (literal_var x) cm));
      discriminate.
  - destruct (in_dec Nat.eq_dec ci (ClauseMap.find (literal_var x) cm))
      as [Hinwatch|Hnotwatch].
    + injection Hscan as <- <-.
      assert (In x (filter (literal_is_undecided m) c)) as Hin
        by (rewrite Hfilter; now left).
      apply filter_In in Hin as [Hxc Hxu]. repeat split; try assumption.
      destruct (in_dec Nat.eq_dec ci
        (ClauseMap.find (literal_var x) cm)); [reflexivity|contradiction].
    + injection Hscan as <- <-.
      assert (In x (filter (literal_is_undecided m) c)) as Hin
        by (rewrite Hfilter; now left).
      apply filter_In in Hin as [Hxc Hxu]. repeat split; try assumption.
      destruct (in_dec Nat.eq_dec ci
        (ClauseMap.find (literal_var x) cm)); [contradiction|reflexivity].
Qed.

Lemma scan_clause_watched_spec : forall m ci c cm fals cm',
  scan_clause m ci c cm fals = clause_watched cm' ->
  exists l l', existsb (literal_is_true m) c = false /\
    In l c /\ In l' c /\
    literal_is_undecided m l = true /\
    literal_is_undecided m l' = true /\
    literal_var l <> literal_var l' /\
    cm' = (if in_dec Nat.eq_dec ci (ClauseMap.find (literal_var l) cm)
      then ClauseMap.add (literal_var l') ci cm
      else ClauseMap.add (literal_var l) ci cm).
Proof.
  intros m ci c cm fals cm' Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c); [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|l undecided]
    eqn:Hfilter; [discriminate|].
  destruct (find_different_var (literal_var l) undecided) as [l'|]
    eqn:Hdifferent.
  2:{ destruct (in_dec Nat.eq_dec ci
        (ClauseMap.find (literal_var l) cm)); discriminate. }
  apply find_different_var_spec in Hdifferent as [Hl'in Hneq].
  assert (In l (filter (literal_is_undecided m) c)) as Hlin
    by (rewrite Hfilter; now left).
  assert (In l' (filter (literal_is_undecided m) c)) as Hl'in'.
  { rewrite Hfilter. now right. }
  apply filter_In in Hlin as [Hlc Hlu].
  apply filter_In in Hl'in' as [Hl'c Hl'u].
  exists l, l'. repeat split; try assumption.
  destruct (in_dec Nat.eq_dec ci (ClauseMap.find (literal_var l) cm));
    now injection Hscan as <-.
Qed.

Lemma scan_clause_decided_spec : forall m ci c cm fals cm' fals',
  scan_clause m ci c cm fals = clause_decided cm' fals' ->
  (existsb (literal_is_true m) c = true /\
    cm' = cm /\ fals' = fals) \/
  (existsb (literal_is_true m) c = false /\
    filter (literal_is_undecided m) c = [] /\
    cm' = cm /\ fals' = ci :: fals).
Proof.
  intros m ci c cm fals cm' fals' Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c) eqn:Htrue.
  - injection Hscan as <- <-. now left.
  - destruct (filter (literal_is_undecided m) c) as [|l undecided]
      eqn:Hfilter.
    + injection Hscan as <- <-. right. repeat split; assumption.
    + destruct (find_different_var (literal_var l) undecided) as [l'|].
      * destruct (in_dec Nat.eq_dec ci
          (ClauseMap.find (literal_var l) cm)); discriminate.
      * destruct (in_dec Nat.eq_dec ci
          (ClauseMap.find (literal_var l) cm)); discriminate.
Qed.

Lemma find_different_var_none : forall v ls,
  find_different_var v ls = None ->
  forall l, In l ls -> literal_var l = v.
Proof.
  intros v ls. induction ls as [|x xs IH]; intros Hnone l Hin;
    [contradiction|].
  simpl in Hnone. destruct (v =? literal_var x) eqn:Heq.
  - destruct Hin as [->|Hin].
    + now apply Nat.eqb_eq in Heq.
    + now apply IH.
  - discriminate.
Qed.

Lemma unit_filter_needs : forall m c l undecided,
  ~ has_opposite_literals c ->
  existsb (literal_is_true m) c = false ->
  filter (literal_is_undecided m) c = l :: undecided ->
  find_different_var (literal_var l) undecided = None ->
  clause_needs_literal m l c.
Proof.
  intros m c l undecided Hnoopp Hfalse Hfilter Hdifferent.
  assert (Hlin : In l c /\ literal_is_undecided m l = true).
  { apply filter_In. rewrite Hfilter. now left. }
  split; [exact (proj1 Hlin)|]. intros x Hxc Hneq.
  assert (Hxtrue : literal_is_true m x = false).
  { destruct (literal_is_true m x) eqn:Hxt; [|reflexivity].
    assert (existsb (literal_is_true m) c = true).
    { apply existsb_exists. now exists x. }
    congruence. }
  assert (Hxundecided : literal_is_undecided m x = false).
  { destruct (literal_is_undecided m x) eqn:Hxu; [|reflexivity].
    assert (In x (filter (literal_is_undecided m) c)) as Hxin
      by (apply filter_In; now split).
    rewrite Hfilter in Hxin. destruct Hxin as [Heq|Hxin];
      [congruence|].
    pose proof (find_different_var_none _ _ Hdifferent _ Hxin) as Hvar.
    destruct l as [v|v], x as [w|w]; cbn in Hvar; subst w;
      try congruence.
    - exfalso. apply Hnoopp. exists v.
      split; [exact (proj1 Hlin)|exact Hxc].
    - exfalso. apply Hnoopp. exists v.
      split; [exact Hxc|exact (proj1 Hlin)]. }
  unfold literal_is_true, literal_is_undecided in Hxtrue, Hxundecided.
  unfold literal_value in *.
  destruct (find (fun l' => literal_var l' =? literal_var x) m)
    as [[v|v]|] eqn:Hvalue; destruct x; try discriminate; reflexivity.
Qed.

Lemma scan_clause_propagate_needs : forall m ci c cm fals l cm',
  ~ has_opposite_literals c ->
  scan_clause m ci c cm fals = propagate_literal l cm' ->
  clause_needs_literal m l c.
Proof.
  intros m ci c cm fals l cm' Hnoopp Hscan.
  unfold scan_clause in Hscan. rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c) eqn:Hfalse; [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|head undecided]
    eqn:Hfilter; [discriminate|].
  destruct (find_different_var (literal_var head) undecided)
    as [other|] eqn:Hdifferent.
  - destruct (in_dec Nat.eq_dec ci
      (ClauseMap.find (literal_var head) cm)); discriminate.
  - destruct (in_dec Nat.eq_dec ci
      (ClauseMap.find (literal_var head) cm)); injection Hscan as <- <-;
      eapply unit_filter_needs; eauto.
Qed.

Lemma count_occ_nodup_in : forall (xs : list ClauseId) ci,
  NoDup xs -> In ci xs -> count_occ Nat.eq_dec xs ci = 1.
Proof.
  intros xs ci Hnodup. induction Hnodup as [|x xs Hnotin Hnodup IH];
    intros Hin; [contradiction|].
  simpl in Hin |- *. destruct Hin as [->|Hin].
  - destruct (Nat.eq_dec ci ci); [|contradiction].
    rewrite (proj1 (count_occ_not_In Nat.eq_dec xs ci) Hnotin). reflexivity.
  - destruct (Nat.eq_dec x ci) as [->|Hneq]; [contradiction|].
    exact (IH Hin).
Qed.

Lemma fresh_clause_card_zero : forall s,
  state_invariant s ->
  ClauseMap.card_of (fresh_clause_id s) s.(state_watched) = 0.
Proof.
  intros s Hinv.
  destruct (ClauseMap.card_of (fresh_clause_id s) s.(state_watched))
    as [|n] eqn:Hcard; [reflexivity|].
  exfalso.
  assert (ClauseMap.card_of (fresh_clause_id s) s.(state_watched) > 0)
    as Hpositive by (rewrite Hcard; lia).
  apply ClauseMap.card_of_pos in Hpositive as [v Hin].
  exact (fresh_clause_not_watched s v Hinv Hin).
Qed.

Lemma decided_clause_after_store_add : forall s c d cm pending,
  decided_clause d s ->
  decided_clause d
    {| state_model := s.(state_model);
       state_clauses :=
         ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_watched := cm;
       state_falsified := s.(state_falsified);
       state_pending := pending |}.
Proof.
  intros s c d cm pending [Hfals|[body [Hfind Htrue]]].
  - now left.
  - right. exists body. split; [now apply find_old_clause_after_add|exact Htrue].
Qed.

Lemma add_unit_staged_inv : forall s c l,
  state_invariant s ->
  ~ has_opposite_literals c ->
  clause_needs_literal s.(state_model) l c ->
  staged_invariant [fresh_clause_id s]
    {| state_model := s.(state_model);
       state_clauses :=
         ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_watched := s.(state_watched);
       state_falsified := s.(state_falsified);
       state_pending := (l, fresh_clause_id s) :: s.(state_pending) |}.
Proof.
  intros s c l Hinv Hnoopp Hneeds.
  pose proof Hinv as Hstateinv.
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [_ [_
      [Hpending [_ Hcard]]]]]]]].
  repeat split.
  - intros d body Hfind Hfalse. cbn [state_clauses] in Hfind.
    rewrite ClauseStore.find_add_eq in Hfind.
    destruct (VarKey.eq_dec (fresh_clause_id s) d) as [->|Hneq].
    + injection Hfind as <-. right. left. now left.
    + specialize (Hcover d body Hfind Hfalse).
      destruct Hcover as [Hopp|[Hwork|[Hwatched|Hinfals]]].
      * now left.
      * contradiction.
      * now right; right; left.
      * now right; right; right.
  - intros d Hd. destruct (Hfals d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_old_clause_after_add|exact Hrest].
  - intros v d Hd. destruct (Hwatch v d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_old_clause_after_add|exact Hrest].
  - exact Hnodup.
  - constructor; [simpl; tauto|constructor].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    exists c. split; [apply find_added_clause|exact Hnoopp].
  - intros p d Hd. simpl in Hd. destruct Hd as [Heq|Hd].
    + inversion Heq; subst p d. exists c. split.
      * apply find_added_clause.
      * split; assumption.
    + destruct (Hpending p d Hd) as [body [Hfind Hrest]].
      exists body. split; [now apply find_old_clause_after_add|exact Hrest].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    right. split.
    + unfold card_of_watch. cbn [state_watched].
      now apply fresh_clause_card_zero.
    + left. exists l. now left.
  - intros d. destruct (Nat.eq_dec (fresh_clause_id s) d) as [Heq|Hneq].
    + subst d. left. unfold card_of_watch. cbn [state_watched].
      now apply fresh_clause_card_zero.
    + specialize (Hcard d).
      destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
      * now left.
      * now right; left.
      * right. right. split; [exact Hone|].
        destruct Hwhy as [Hwork|[Hpend|Hdecided]].
        -- contradiction.
        -- right. left. destruct Hpend as [p Hp]. exists p. now right.
        -- right. right.
           now apply decided_clause_after_store_add with
             (cm := s.(state_watched))
             (pending := (l, fresh_clause_id s) :: s.(state_pending)).
Qed.

Lemma add_first_watch_staged_inv : forall s c l,
  state_invariant s ->
  ~ has_opposite_literals c ->
  In l c ->
  literal_is_undecided s.(state_model) l = true ->
  staged_invariant [fresh_clause_id s]
    {| state_model := s.(state_model);
       state_clauses :=
         ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_watched :=
         ClauseMap.add (literal_var l) (fresh_clause_id s)
           s.(state_watched);
       state_falsified := s.(state_falsified);
       state_pending := s.(state_pending) |}.
Proof.
  intros s c l Hinv Hnoopp Hlc Hlu.
  pose proof Hinv as Hstateinv.
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [_ [_
      [Hpending [_ Hcard]]]]]]]].
  repeat split.
  - intros d body Hfind Hfalse. cbn [state_clauses] in Hfind.
    rewrite ClauseStore.find_add_eq in Hfind.
    destruct (VarKey.eq_dec (fresh_clause_id s) d) as [Heq|Hneq].
    + subst d. injection Hfind as <-. right. left. now left.
    + specialize (Hcover d body Hfind Hfalse).
      destruct Hcover as [Hopp|[Hwork|[Hwatched|Hinfals]]].
      * now left.
      * contradiction.
      * right. right. left. destruct Hwatched as [v Hin]. exists v.
        apply ClauseMap.find_add. now right.
      * now right; right; right.
  - intros d Hd. destruct (Hfals d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_old_clause_after_add|exact Hrest].
  - intros v d Hd. apply ClauseMap.find_add in Hd as [[Heqv Heqd]|Hd].
    + subst v d. exists c. repeat split; try assumption.
      * apply find_added_clause.
      * now apply literal_undecided_not_InL.
      * now apply literal_InL.
    + destruct (Hwatch v d Hd) as [body [Hfind Hrest]].
      exists body. split; [now apply find_old_clause_after_add|exact Hrest].
  - intros v. cbn [state_watched]. rewrite ClauseMap.find_add_eq.
    destruct (VarKey.eq_dec (literal_var l) v) as [Heq|Hneq].
    + subst v. constructor.
      * now apply fresh_clause_not_watched.
      * apply Hnodup.
    + apply Hnodup.
  - constructor; [simpl; tauto|constructor].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    exists c. split; [apply find_added_clause|exact Hnoopp].
  - intros p d Hd. destruct (Hpending p d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_old_clause_after_add|exact Hrest].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    left. unfold card_of_watch. cbn [state_watched].
    rewrite ClauseMap.card_of_add, (fresh_clause_card_zero s Hstateinv).
    reflexivity.
  - intros d. destruct (Nat.eq_dec (fresh_clause_id s) d) as [Heq|Hneq].
    + subst d. right. right. split.
      * unfold card_of_watch. cbn [state_watched].
        rewrite ClauseMap.card_of_add, (fresh_clause_card_zero s Hstateinv).
        reflexivity.
      * left. simpl. tauto.
    + specialize (Hcard d).
      unfold card_of_watch in Hcard |- *. cbn [state_watched].
      rewrite ClauseMap.card_of_add_neq by exact Hneq.
      destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
      * now left.
      * now right; left.
      * right. right. split; [exact Hone|].
        destruct Hwhy as [Hwork|[Hpend|Hdecided]].
        -- contradiction.
        -- now right; left.
        -- right. right.
           now apply decided_clause_after_store_add with
             (cm := ClauseMap.add (literal_var l) (fresh_clause_id s)
               s.(state_watched))
             (pending := s.(state_pending)).
Qed.

Lemma watch_one_fresh_inv : forall work ci c clauses m cm fals pending l,
  ClauseStore.find ci clauses = Some c ->
  ~ has_opposite_literals c ->
  staged_invariant (ci :: work)
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |} ->
  ~ In ci (ClauseMap.find (literal_var l) cm) ->
  In l c -> literal_is_undecided m l = true ->
  staged_invariant work
    {| state_model := m; state_clauses := clauses;
       state_watched := ClauseMap.add (literal_var l) ci cm;
       state_falsified := fals; state_pending := pending |}.
Proof.
  intros work ci c clauses m cm fals pending l Hfind Hnoopp Hinv
    Hfresh Hlc Hlu.
  destruct Hinv as
    [Hsat [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork Hcard]]]]]]]].
  inversion Hworknodup as [|? ? Hcinotwork Hworknodup']; subst.
  pose proof (Hwork ci (or_introl eq_refl)) as Hciwork.
  unfold card_of_watch in Hciwork. cbn -[ClauseMap.card_of] in Hciwork.
  split.
  - intros d body Hbody Hunsat.
    specialize (Hsat d body Hbody Hunsat).
    destruct Hsat as [Htrivial|[[->|Hdwork]|[Hwatched|Hinfals]]].
    + now left.
    + right. right. left. exists (literal_var l).
      apply ClauseMap.find_add. now left.
    + now right; left.
    + right. right. left. destruct Hwatched as [v Hin]. exists v.
      apply ClauseMap.find_add. now right.
    + now right; right; right.
  - split; [exact Hfals|]. split.
    + intros v d Hin. apply ClauseMap.find_add in Hin as [[-> ->]|Hin].
      * exists c. repeat split; try assumption.
        -- now apply literal_undecided_not_InL.
        -- now apply literal_InL.
      * exact (Hwatch v d Hin).
    + split.
      * intros v. cbn [state_watched]. rewrite ClauseMap.find_add_eq.
        destruct (VarKey.eq_dec (literal_var l) v) as [Heq|Hneq].
        -- subst v. constructor; [exact Hfresh|apply Hnodup].
        -- apply Hnodup.
      * split; [exact Hworknodup'|]. split.
        -- intros d Hd. exact (Hworkref d (or_intror Hd)).
        -- split; [exact Hpending|]. split.
           ++ intros d Hd. specialize (Hwork d (or_intror Hd)).
              assert (ci <> d) as Hneq by (intros ->; contradiction).
              unfold card_of_watch in Hwork |- *. cbn -[ClauseMap.card_of].
              now rewrite ClauseMap.card_of_add_neq by exact Hneq.
           ++ intros d. destruct (Nat.eq_dec ci d) as [->|Hneq].
              ** unfold card_of_watch. cbn -[ClauseMap.card_of].
                 rewrite ClauseMap.card_of_add.
                 destruct Hciwork as [Hone|[Hzero [[p Hpendingci]|Hdecided]]].
                 --- rewrite Hone. now right; left.
                 --- rewrite Hzero. right; right. split; [reflexivity|].
                     right. left. now exists p.
                 --- rewrite Hzero. right; right. split; [reflexivity|].
                     right. right. exact Hdecided.
              ** specialize (Hcard d).
                 unfold card_of_watch in Hcard |- *. cbn -[ClauseMap.card_of].
                 rewrite ClauseMap.card_of_add_neq by exact Hneq.
                 destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
                 --- now left.
                 --- now right; left.
                 --- right; right. split; [exact Hone|].
                     destruct Hwhy as [Hdwork|[Hpendingd|Hdecided]].
                     +++ simpl in Hdwork. destruct Hdwork as [Heq|Hdwork];
                           [contradiction|now left].
                     +++ right. left. exact Hpendingd.
                     +++ right. right. exact Hdecided.
Qed.

Lemma watch_one_inv : forall work ci c clauses m cm fals pending l l' cm',
  ClauseStore.find ci clauses = Some c ->
  ~ has_opposite_literals c ->
  staged_invariant (ci :: work)
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |} ->
  In l c -> In l' c ->
  literal_is_undecided m l = true ->
  literal_is_undecided m l' = true ->
  literal_var l <> literal_var l' ->
  cm' = (if in_dec Nat.eq_dec ci (ClauseMap.find (literal_var l) cm)
    then ClauseMap.add (literal_var l') ci cm
    else ClauseMap.add (literal_var l) ci cm) ->
  staged_invariant work
    {| state_model := m; state_clauses := clauses; state_watched := cm';
       state_falsified := fals; state_pending := pending |}.
Proof.
  intros work ci c clauses m cm fals pending l l' cm' Hfind Hnoopp Hinv
    Hlc Hl'c Hlu Hl'u Hneq Hcm'.
  destruct (in_dec Nat.eq_dec ci (ClauseMap.find (literal_var l) cm))
    as [Hwatched|Hfresh].
  - subst cm'. apply watch_one_fresh_inv with (c := c); try assumption.
    intros Hwatched'.
    destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [Hwork _]]]]]]]].
    specialize (Hwork ci (or_introl eq_refl)).
    unfold card_of_watch in Hwork. cbn -[ClauseMap.card_of] in Hwork.
    assert (ClauseMap.card_of ci cm = 1) as Hcone.
    { destruct Hwork as [Hone|[Hzero _]]; [exact Hone|].
      pose proof (ClauseMap.card_of_in cm ci (literal_var l) Hwatched).
      lia. }
    apply Hneq. eapply ClauseMap.card_of_unique; eauto.
  - subst cm'. now apply watch_one_fresh_inv with (c := c).
Qed.

Lemma pending_cons_inv : forall work ci c clauses (m : Trail) cm fals pending l,
  ClauseStore.find ci clauses = Some c ->
  clause_needs_literal m l c ->
  ~ has_opposite_literals c ->
  staged_invariant work
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |} ->
  staged_invariant work
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := (l, ci) :: pending |}.
Proof.
  intros work ci c clauses m cm fals pending l Hfind Hneeds Hnoopp Hinv.
  destruct Hinv as
    [Hsat [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork Hcard]]]]]]]].
  repeat split; try assumption.
  - intros p d Hpd. simpl in Hpd. destruct Hpd as [Heq|Hpd].
    + injection Heq as <- <-. exists c.
      split; [exact Hfind|]. split; [exact Hneeds|exact Hnoopp].
    + exact (Hpending p d Hpd).
  - intros d Hd. specialize (Hwork d Hd).
    destruct Hwork as [Hone|[Hzero [[p Hpd]|Hdecided]]].
    + now left.
    + right. split; [exact Hzero|]. left. exists p. now right.
    + right. split; [exact Hzero|]. right. exact Hdecided.
  - intros d. specialize (Hcard d).
    destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
    + now left.
    + now right; left.
    + right; right. split; [exact Hone|].
      destruct Hwhy as [Hdwork|[[p Hpd]|Hdecided]]; [now left| |].
      * right. left. exists p. now right.
      * right. right. exact Hdecided.
Qed.

Lemma propagate_literal_inv : forall work ci c clauses m cm fals pending l cm',
  ClauseStore.find ci clauses = Some c ->
  staged_invariant (ci :: work)
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |} ->
  scan_clause m ci c cm fals = propagate_literal l cm' ->
  staged_invariant work
    {| state_model := m; state_clauses := clauses; state_watched := cm';
       state_falsified := fals; state_pending := (l, ci) :: pending |}.
Proof.
  intros work ci c clauses m cm fals pending l cm' Hfind Hinv Hscan.
  pose proof Hinv as Hlookup.
  destruct Hlookup as [_ [_ [_ [_ [_ [Hworklookup _]]]]]].
  destruct (Hworklookup ci (or_introl eq_refl))
    as [body [Hbody Hnoopp]].
  cbn in Hbody. rewrite Hfind in Hbody. injection Hbody as <-.
  pose proof (scan_clause_propagate_needs _ _ _ _ _ _ _ Hnoopp Hscan)
    as Hneeds.
  pose proof (scan_clause_inl_spec _ _ _ _ _ _ _ Hscan) as
    [_ [Hlc [Hlu Hcm']]].
  destruct (in_dec Nat.eq_dec ci (ClauseMap.find (literal_var l) cm))
    as [Hwatched|Hfresh].
  - subst cm'.
    destruct Hinv as
      [Hcover [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
        [Hpending [Hwork Hcard]]]]]]]].
    inversion Hworknodup as [|? ? Hcinotwork Hworknodup']; subst.
    repeat split; try assumption.
    + intros d body Hbody Hunsat. specialize (Hcover d body Hbody Hunsat).
      destruct Hcover as [Htrivial|[[->|Hdwork]|[Hwatched'|Hinfals]]].
      * now left.
      * right. right. left. now exists (literal_var l).
      * now right; left.
      * now right; right; left.
      * now right; right; right.
    + intros d Hd. exact (Hworkref d (or_intror Hd)).
    + intros p d Hpd. simpl in Hpd. destruct Hpd as [Heq|Hpd].
      * injection Heq as <- <-. exists c.
        split; [exact Hfind|]. split; [exact Hneeds|exact Hnoopp].
      * exact (Hpending p d Hpd).
    + intros d Hd. specialize (Hwork d (or_intror Hd)).
      destruct Hwork as [Hone|[Hzero [[p Hpd]|Hdecided]]].
      * now left.
      * right. split; [exact Hzero|]. left. exists p. now right.
      * right. split; [exact Hzero|]. right. exact Hdecided.
    + intros d. specialize (Hcard d).
      destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
      * now left.
      * now right; left.
      * right; right. split; [exact Hone|].
        destruct Hwhy as [[->|Hdwork]|[Hpendingd|Hdecided]].
        -- right. left. exists l. simpl. now left.
        -- now left.
        -- destruct Hpendingd as [p Hpd]. right. left. exists p. now right.
        -- right. right. exact Hdecided.
  - subst cm'. apply pending_cons_inv with (c := c); try assumption.
    now apply watch_one_fresh_inv with (c := c).
Qed.

Lemma decide_active_inv : forall work ci c clauses m cm fals pending fals',
  ClauseStore.find ci clauses = Some c ->
  staged_invariant (ci :: work)
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |} ->
  (forall d, In d fals' ->
     exists body, ClauseStore.find d clauses = Some body /\
       Is_true (negb (existsb (literal_is_true m) body)) /\
       filter (literal_is_undecided m) body = []) ->
  (forall d, In d fals -> In d fals') ->
  (In ci fals' \/ Is_true (existsb (literal_is_true m) c)) ->
  staged_invariant work
    {| state_model := m; state_clauses := clauses;
       state_watched := cm;
       state_falsified := fals'; state_pending := pending |}.
Proof.
  intros work ci c clauses m cm fals pending fals' Hfind Hinv
    Hfals' Hfalspreserve Hci.
  destruct Hinv as
    [Hsat [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork Hcard]]]]]]]].
  inversion Hworknodup as [|? ? Hcinotwork Hworknodup']; subst.
  assert (Hdecided : forall d,
      decided_clause d
        {| state_model := m; state_clauses := clauses; state_watched := cm;
           state_falsified := fals; state_pending := pending |} ->
      decided_clause d
        {| state_model := m; state_clauses := clauses; state_watched := cm;
           state_falsified := fals'; state_pending := pending |}).
  { intros d [Hd|[body [Hbody Htrue]]].
    - left. now apply Hfalspreserve.
    - right. exists body. now split. }
  repeat split; try assumption.
  - intros d body Hbody Hunsat. specialize (Hsat d body Hbody Hunsat).
    destruct Hsat as [Htrivial|[[Heq|Hdwork]|[Hwatched|Hinfals]]].
    + now left.
    + subst d. cbn in Hbody. rewrite Hfind in Hbody. injection Hbody as <-.
      destruct Hci as [Hinfals'|Htrue].
      * now right; right; right.
      * exfalso. exact (negb_prop_elim _ Hunsat Htrue).
    + now right; left.
    + now right; right; left.
    + right. right. right. now apply Hfalspreserve.
  - intros d Hd. exact (Hworkref d (or_intror Hd)).
  - intros d Hd. specialize (Hwork d (or_intror Hd)).
    destruct Hwork as [Hone|[Hzero [Hpendingd|Hdecided']]].
    + now left.
    + right. split; [exact Hzero|]. now left.
    + right. split; [exact Hzero|]. right. now apply Hdecided.
  - intros d. specialize (Hcard d).
    destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
    + now left.
    + now right; left.
    + right; right. split; [exact Hone|].
      destruct Hwhy as [[Heq|Hdwork]|[Hpendingd|Hdecided']].
      * subst d. right. right. unfold decided_clause. cbn.
        destruct Hci as [Hinfals'|Htrue].
        -- now left.
        -- right. exists c. now split.
      * now left.
      * right. left. exact Hpendingd.
      * right. right. now apply Hdecided.
Qed.

Lemma propagate_decided_inv : forall work ci c clauses m cm fals pending cm' fals',
  ClauseStore.find ci clauses = Some c ->
  staged_invariant (ci :: work)
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |} ->
  scan_clause m ci c cm fals = clause_decided cm' fals' ->
  staged_invariant work
    {| state_model := m; state_clauses := clauses; state_watched := cm';
       state_falsified := fals'; state_pending := pending |}.
Proof.
  intros work ci c clauses m cm fals pending cm' fals' Hfind Hinv Hscan.
  pose proof Hinv as Hinv'.
  destruct Hinv as [_ [Hfals _]].
  pose proof (scan_clause_decided_spec _ _ _ _ _ _ _ Hscan) as Hspec.
  destruct Hspec as [[Htrue [-> ->]]|[Hfalse [Hfilter [-> ->]]]].
  - eapply decide_active_inv.
    + exact Hfind.
    + exact Hinv'.
    + exact Hfals.
    + intros d Hd. exact Hd.
    + right. now rewrite Htrue.
  - eapply decide_active_inv.
    + exact Hfind.
    + exact Hinv'.
    + intros d Hd. simpl in Hd. destruct Hd as [->|Hd].
      * exists c. repeat split; try assumption. now rewrite Hfalse.
      * exact (Hfals d Hd).
    + intros d Hd. now right.
    + left. now left.
Qed.

Lemma propagate_inv : forall ci work s,
  staged_invariant (ci :: work) s ->
  staged_invariant work (propagate ci s).
Proof.
  intros ci work [m clauses cm fals pending] Hinv.
  pose proof Hinv as Hlookup.
  destruct Hlookup as [_ [_ [_ [_ [_ [Hworkref _]]]]]].
  destruct (Hworkref ci (or_introl eq_refl)) as [c [Hfind Hnoopp]].
  cbn in Hfind.
  unfold propagate. cbn [state_model state_clauses state_watched
    state_falsified state_pending] in Hinv |- *.
  rewrite Hfind.
  destruct (scan_clause m ci c cm fals) as [l|cm' fals'|cm'] eqn:Hscan.
  - eapply propagate_literal_inv; [exact Hfind|exact Hinv|exact Hscan].
  - eapply propagate_decided_inv; [exact Hfind|exact Hinv|exact Hscan].
  - pose proof (scan_clause_watched_spec _ _ _ _ _ _ Hscan) as
    [l [l' [_ [Hlc [Hl'c [Hlu [Hl'u [Hneq Hcm']]]]]]]].
    eapply watch_one_inv.
    + exact Hfind.
    + exact Hnoopp.
    + exact Hinv.
    + exact Hlc.
    + exact Hl'c.
    + exact Hlu.
    + exact Hl'u.
    + exact Hneq.
    + exact Hcm'.
Qed.

Lemma fold_propagate_inv : forall work s,
  staged_invariant work s ->
  state_invariant (fold_left (fun s ci => propagate ci s) work s).
Proof.
  induction work as [|ci work IH]; intros s Hinv; [exact Hinv|].
  simpl. apply IH. now apply propagate_inv.
Qed.

Lemma prepare_set_lit_inv : forall l (m : Trail) clauses cm fals pending,
  literal_is_undecided m l = true ->
  state_invariant
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |} ->
  staged_invariant (ClauseMap.find (literal_var l) cm)
    {| state_model := Decision l :: m; state_clauses := clauses;
       state_watched := ClauseMap.remove (literal_var l) cm;
       state_falsified := fals; state_pending := pending |}.
Proof.
  intros l m clauses cm fals pending Hlu Hinv.
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [_ [_ [Hpending [_ Hcard]]]]]]]].
  assert (Hdecided : forall d,
      decided_clause d
        {| state_model := m; state_clauses := clauses; state_watched := cm;
           state_falsified := fals; state_pending := pending |} ->
      decided_clause d
        {| state_model := Decision l :: m; state_clauses := clauses;
           state_watched := ClauseMap.remove (literal_var l) cm;
           state_falsified := fals; state_pending := pending |}).
  { intros d [Hd|[body [Hbody Htrue]]].
    - now left.
    - right. exists body. split; [exact Hbody|].
      now apply satisfied_cons_undecided. }
  repeat split.
  - intros d body Hbody Hfalse.
    assert (Holdfalse :
      Is_true (negb (existsb (literal_is_true m) body))).
    { apply negb_prop_intro. intros Holdtrue.
      apply (negb_prop_elim _ Hfalse).
      now apply satisfied_cons_undecided. }
    specialize (Hcover d body Hbody Holdfalse).
    destruct Hcover as [Htrivial|[Habs|[[v Hin]|Hd]]].
    + now left.
    + contradiction.
    + destruct (Nat.eq_dec (literal_var l) v) as [->|Hneq].
      * now right; left.
      * right. right. left. exists v. apply ClauseMap.find_remove.
        split; [exact Hin|congruence].
    + now right; right; right.
  - intros d Hd. destruct (Hfals d Hd) as [body [Hbody Hsem]].
    exists body. split; [exact Hbody|].
    now apply falsified_cons_undecided.
  - intros v d Hin. apply ClauseMap.find_remove in Hin as [Hin Hneq].
    destruct (Hwatch v d Hin) as [body [Hbody [Hnotin [Hinc Hnoopp]]]].
    exists body. repeat split; try assumption.
    intros Hin'. apply Hnotin.
    now apply (InL_cons_other l (trail_model m) v Hneq).
  - intros v. cbn [state_watched]. rewrite ClauseMap.find_remove_eq.
    destruct (VarKey.eq_dec (literal_var l) v); [constructor|apply Hnodup].
  - apply Hnodup.
  - intros d Hd. destruct (Hwatch (literal_var l) d Hd)
      as [body [Hbody [_ [_ Hnoopp]]]].
    exists body. now split.
  - intros p d Hpd. destruct (Hpending p d Hpd)
      as [body [Hbody [Hneeds Hnoopp]]].
    exists body. split; [exact Hbody|]. split; [|exact Hnoopp].
    now apply clause_needs_literal_cons.
  - intros d Hd.
    pose proof (ClauseMap.card_of_remove cm d (literal_var l)) as Hremove.
    change (ClauseMap.card_of d (ClauseMap.remove (literal_var l) cm) +
      count_occ Nat.eq_dec (ClauseMap.find (literal_var l) cm) d =
      ClauseMap.card_of d cm) in Hremove.
    pose proof (count_occ_nodup_in _ d (Hnodup (literal_var l)) Hd) as Hcount.
    specialize (Hcard d). unfold card_of_watch in *.
    cbn -[ClauseMap.card_of] in *.
    destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
    + pose proof (ClauseMap.card_of_in cm d (literal_var l) Hd). lia.
    + left. lia.
    + right. split; [lia|].
      destruct Hwhy as [Habs|[Hpendingd|Hdecided']].
      * contradiction.
      * now left.
      * right. now apply Hdecided.
  - intros d.
    pose proof (ClauseMap.card_of_remove cm d (literal_var l)) as Hremove.
    change (ClauseMap.card_of d (ClauseMap.remove (literal_var l) cm) +
      count_occ Nat.eq_dec (ClauseMap.find (literal_var l) cm) d =
      ClauseMap.card_of d cm) in Hremove.
    specialize (Hcard d). unfold card_of_watch in *.
    cbn -[ClauseMap.card_of] in *.
    destruct (in_dec Nat.eq_dec d
      (ClauseMap.find (literal_var l) cm)) as [Hin|Hnotin].
    + pose proof (count_occ_nodup_in _ d (Hnodup (literal_var l)) Hin)
        as Hcount.
      destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
      * pose proof (ClauseMap.card_of_in cm d (literal_var l) Hin). lia.
      * right. right. split; [lia|]. now left.
      * left. lia.
    + pose proof (proj1 (count_occ_not_In Nat.eq_dec _ _) Hnotin) as Hcount.
      destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
      * left. lia.
      * right. left. lia.
      * right. right. split; [lia|].
        destruct Hwhy as [Habs|[Hpendingd|Hdecided']].
        -- contradiction.
        -- right. left. exact Hpendingd.
        -- right. right. now apply Hdecided.
Qed.

Lemma set_lit_inv : forall l s,
  literal_is_undecided s.(state_model) l = true ->
  state_invariant s -> state_invariant (set_lit l s).
Proof.
  intros l [m clauses cm fals pending] Hlu Hinv.
  unfold set_lit. cbn [state_model state_clauses state_watched
    state_falsified state_pending].
  apply fold_propagate_inv. now apply prepare_set_lit_inv.
Qed.

Lemma drop_satisfied_pending_inv : forall work l ci c pending (m : Trail)
    clauses cm fals,
  ClauseStore.find ci clauses = Some c ->
  In l c -> Is_true (existsb (literal_is_true m) c) ->
  staged_invariant work
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := (l, ci) :: pending |} ->
  staged_invariant work
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |}.
Proof.
  intros work l ci c pending m clauses cm fals Hfind Hlc Htrue Hinv.
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork Hcard]]]]]]]].
  assert (Hreason : forall d,
      (exists p, In (p, d) ((l, ci) :: pending)) ->
      (exists p, In (p, d) pending) \/
      decided_clause d
        {| state_model := m; state_clauses := clauses; state_watched := cm;
           state_falsified := fals; state_pending := pending |}).
  { intros d [p Hpd]. simpl in Hpd. destruct Hpd as [Heq|Hpd].
    - injection Heq as <- <-. right. right. exists c. now split.
    - left. now exists p. }
  repeat split; try assumption.
  - intros p d Hpd. exact (Hpending p d (or_intror Hpd)).
  - intros d Hd. specialize (Hwork d Hd).
    destruct Hwork as [Hone|[Hzero [Hpendingd|Hdecided]]].
    + now left.
    + right. split; [exact Hzero|].
      destruct (Hreason d Hpendingd); [now left|now right].
    + right. split; [exact Hzero|]. now right.
  - intros d. specialize (Hcard d).
    destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
    + now left.
    + now right; left.
    + right; right. split; [exact Hone|].
      destruct Hwhy as [Hdwork|[Hpendingd|Hdecided]].
      * now left.
      * right. destruct (Hreason d Hpendingd); [now left|now right].
      * right. right. exact Hdecided.
Qed.

Lemma set_pending_inv : forall l ci c pending (m : Trail) clauses cm fals,
  ClauseStore.find ci clauses = Some c ->
  literal_is_undecided m l = true ->
  state_invariant
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := (l, ci) :: pending |} ->
  state_invariant
    (set_propagated_lit l ci
      {| state_model := m; state_clauses := clauses; state_watched := cm;
         state_falsified := fals; state_pending := pending |}).
Proof.
  intros l ci c pending m clauses cm fals Hfind Hlu Hinv.
  pose proof Hinv as Hpendinginv.
  destruct Hpendinginv as [_ [_ [_ [_ [_ [_ [Hpending _]]]]]]].
  destruct (Hpending l ci (or_introl eq_refl))
    as [body [Hbody [Hneeds Hnoopp]]].
  cbn in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  unfold set_propagated_lit, set_trail_entry.
  cbn [trail_literal state_model state_clauses state_watched
    state_falsified state_pending].
  apply fold_propagate_inv.
  pose proof (prepare_set_lit_inv l m clauses cm fals ((l, ci) :: pending)
    Hlu Hinv) as Hprepared.
  eapply staged_invariant_trail_ext in Hprepared.
  2:{ cbn [trail_model trail_literal]. reflexivity. }
  eapply drop_satisfied_pending_inv;
    [exact Hfind|exact (proj1 Hneeds)| |exact Hprepared].
  apply Is_true_eq_left. apply existsb_exists. exists l.
  split; [exact (proj1 Hneeds)|apply literal_is_true_cons_self].
Qed.

Lemma resolve_true_pending_inv : forall l ci c pending (m : Trail)
    clauses cm fals,
  ClauseStore.find ci clauses = Some c ->
  literal_is_true m l = true ->
  state_invariant
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := (l, ci) :: pending |} ->
  state_invariant
    {| state_model := m; state_clauses := clauses; state_watched := cm;
       state_falsified := fals; state_pending := pending |}.
Proof.
  intros l ci c pending m clauses cm fals Hfind Hltrue Hinv.
  pose proof Hinv as Hpendinginv.
  destruct Hpendinginv as [_ [_ [_ [_ [_ [_ [Hpending _]]]]]]].
  destruct (Hpending l ci (or_introl eq_refl))
    as [body [Hbody [Hneeds Hnoopp]]].
  cbn in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  eapply drop_satisfied_pending_inv;
    [exact Hfind|exact (proj1 Hneeds)| |exact Hinv].
  apply Is_true_eq_left. apply existsb_exists. exists l.
  split; [exact (proj1 Hneeds)|exact Hltrue].
Qed.

Lemma finish_progress_inv : forall s s',
  state_invariant s -> finish_progress s = Progress s' -> state_invariant s'.
Proof.
  intros [m clauses cm fals pending] s' Hinv Hfinish.
  unfold finish_progress in Hfinish.
  cbn [state_falsified state_clauses] in Hfinish.
  destruct fals as [|ci fals].
  - now injection Hfinish as <-.
  - destruct (ClauseStore.find ci clauses); discriminate.
Qed.

Lemma progress_inv : forall s s',
  state_invariant s -> progress s = Progress s' -> state_invariant s'.
Proof.
  intros [m clauses cm fals pending] s' Hinv Hprogress.
  unfold progress in Hprogress.
  cbn [state_pending state_model] in Hprogress.
  destruct pending as [|[l ci] pending].
  - apply finish_progress_inv with
      (s := progress_state
        {| state_model := m; state_clauses := clauses; state_watched := cm;
           state_falsified := fals; state_pending := [] |}); [|exact Hprogress].
    unfold progress_state. cbn [state_pending state_model state_clauses
      state_watched state_falsified].
    destruct (hd_error (ClauseMap.keys cm)) as [v|] eqn:Hhead.
    + apply set_lit_inv; [|exact Hinv].
      apply not_InL_literal_undecided.
      assert (In v (ClauseMap.keys cm)) as Hkey.
      { destruct (ClauseMap.keys cm) as [|x xs] eqn:Hkeys;
          [discriminate|]. injection Hhead as <-. now left. }
      apply <- ClauseMap.keys_complete in Hkey.
      destruct (ClauseMap.find v cm) as [|d ds] eqn:Hfind;
        [contradiction|].
      destruct Hinv as [_ [_ [Hwatch _]]].
      assert (In d (ClauseMap.find v cm)) as Hin by (rewrite Hfind; now left).
      destruct (Hwatch v d Hin) as [body [_ [Hnotin _]]]. exact Hnotin.
    + exact Hinv.
  - pose proof Hinv as Hlookup.
    destruct Hlookup as [_ [_ [_ [_ [_ [_ [Hpending _]]]]]]].
    destruct (Hpending l ci (or_introl eq_refl))
      as [c [Hfind [Hlc Hstatus]]]. cbn in Hfind.
    destruct (literal_value m l) as [[|]|] eqn:Hvalue.
    + apply finish_progress_inv with
        (s := progress_state
          {| state_model := m; state_clauses := clauses; state_watched := cm;
             state_falsified := fals;
             state_pending := (l, ci) :: pending |}); [|exact Hprogress].
      unfold progress_state. cbn [state_pending state_model state_clauses
        state_watched state_falsified]. rewrite Hvalue.
      eapply resolve_true_pending_inv; [exact Hfind| |exact Hinv].
      unfold literal_is_true. now rewrite Hvalue.
    + cbn [state_clauses] in Hprogress. rewrite Hfind in Hprogress.
      discriminate.
    + apply finish_progress_inv with
        (s := progress_state
          {| state_model := m; state_clauses := clauses; state_watched := cm;
             state_falsified := fals;
             state_pending := (l, ci) :: pending |}); [|exact Hprogress].
      unfold progress_state. cbn [state_pending state_model state_clauses
        state_watched state_falsified]. rewrite Hvalue.
      eapply set_pending_inv; [exact Hfind| |exact Hinv].
      unfold literal_is_undecided. now rewrite Hvalue.
Qed.

Lemma progress_falsified_empty : forall s s',
  progress s = Progress s' -> s'.(state_falsified) = [].
Proof.
  intros s s' Hprogress. unfold progress in Hprogress.
  destruct s.(state_pending) as [|[l ci] pending].
  - unfold finish_progress in Hprogress.
    destruct (progress_state s) as [m clauses cm fals pending'].
    cbn [state_falsified state_clauses] in Hprogress.
    destruct fals as [|d fals].
    + now injection Hprogress as <-.
    + destruct (ClauseStore.find d clauses); discriminate.
  - destruct (literal_value s.(state_model) l) as [[|]|] eqn:Hvalue.
    + unfold finish_progress in Hprogress.
      destruct (progress_state s) as [m clauses cm fals pending'].
      cbn [state_falsified state_clauses] in Hprogress.
      destruct fals as [|d fals].
      * now injection Hprogress as <-.
      * destruct (ClauseStore.find d clauses); discriminate.
    + cbn [state_clauses] in Hprogress.
      destruct (ClauseStore.find ci s.(state_clauses)); discriminate.
    + unfold finish_progress in Hprogress.
      destruct (progress_state s) as [m clauses cm fals pending'].
      cbn [state_falsified state_clauses] in Hprogress.
      destruct fals as [|d fals].
      * now injection Hprogress as <-.
      * destruct (ClauseStore.find d clauses); discriminate.
Qed.

Lemma propagate_clauses : forall ci s,
  (propagate ci s).(state_clauses) = s.(state_clauses).
Proof.
  intros ci [m clauses cm fals pending]. unfold propagate. cbn.
  destruct (ClauseStore.find ci clauses) as [c|]; [|reflexivity].
  destruct (scan_clause (map trail_literal m) ci c cm fals); reflexivity.
Qed.

Lemma fold_propagate_clauses : forall work s,
  (fold_left (fun s ci => propagate ci s) work s).(state_clauses) =
  s.(state_clauses).
Proof.
  induction work as [|ci work IH]; intros s; [reflexivity|].
  simpl. rewrite IH. apply propagate_clauses.
Qed.

Lemma set_lit_clauses : forall l s,
  (set_lit l s).(state_clauses) = s.(state_clauses).
Proof.
  intros l [m clauses cm fals pending]. unfold set_lit. cbn.
  apply fold_propagate_clauses.
Qed.

Lemma set_propagated_lit_clauses : forall l cause s,
  (set_propagated_lit l cause s).(state_clauses) = s.(state_clauses).
Proof.
  intros l cause [m clauses cm fals pending].
  unfold set_propagated_lit, set_trail_entry. cbn.
  apply fold_propagate_clauses.
Qed.

Lemma progress_state_clauses : forall s,
  (progress_state s).(state_clauses) = s.(state_clauses).
Proof.
  intros [m clauses cm fals pending]. unfold progress_state. cbn.
  destruct pending as [|[l ci] pending].
  - destruct (hd_error (ClauseMap.keys cm)); [apply set_lit_clauses|reflexivity].
  - destruct (literal_value (map trail_literal m) l) as [[|]|];
      try reflexivity.
    apply set_propagated_lit_clauses.
Qed.

Lemma progress_clauses : forall s s',
  progress s = Progress s' -> s'.(state_clauses) = s.(state_clauses).
Proof.
  intros s s' Hprogress. unfold progress in Hprogress.
  destruct s.(state_pending) as [|[l ci] pending].
  - unfold finish_progress in Hprogress.
    destruct (progress_state s) as [m clauses cm fals pending'] eqn:Hstate.
    cbn [state_falsified state_clauses] in Hprogress.
    destruct fals as [|d fals].
    + injection Hprogress as <-. rewrite <- Hstate. apply progress_state_clauses.
    + destruct (ClauseStore.find d clauses); discriminate.
  - destruct (literal_value s.(state_model) l) as [[|]|] eqn:Hvalue.
    + unfold finish_progress in Hprogress.
      destruct (progress_state s) as [m clauses cm fals pending'] eqn:Hstate.
      cbn [state_falsified state_clauses] in Hprogress.
      destruct fals as [|d fals].
      * injection Hprogress as <-. rewrite <- Hstate. apply progress_state_clauses.
      * destruct (ClauseStore.find d clauses); discriminate.
    + cbn [state_clauses] in Hprogress.
      destruct (ClauseStore.find ci s.(state_clauses)); discriminate.
    + unfold finish_progress in Hprogress.
      destruct (progress_state s) as [m clauses cm fals pending'] eqn:Hstate.
      cbn [state_falsified state_clauses] in Hprogress.
      destruct fals as [|d fals].
      * injection Hprogress as <-. rewrite <- Hstate. apply progress_state_clauses.
      * destruct (ClauseStore.find d clauses); discriminate.
Qed.

Inductive delay_returns {A : Type} : Delay A -> A -> Prop :=
  | delay_returns_now (x : A) : delay_returns (Now x) x
  | delay_returns_later (d : Delay A) (x : A) :
      delay_returns d x -> delay_returns (Later d) x.

Definition satisfies_clause_store (m : SModel) (clauses : ClauseStore.t) : Prop :=
  forall ci c, ClauseStore.find ci clauses = Some c ->
    Is_true (satisfies_clause m c).

Lemma literal_is_true_complete_model : forall m l,
  literal_is_true m l = true ->
  satisfies_literal (complete_model m) l = true.
Proof.
  intros m [v|v] Htrue.
  - unfold literal_is_true, literal_value,
      satisfies_literal, complete_model, lit_is_me in *. simpl in *.
    destruct (find (fun l => literal_var l =? v) m) as [[w|w]|];
      try discriminate; reflexivity.
  - unfold literal_is_true, literal_value,
      satisfies_literal, complete_model, lit_is_me in *. simpl in *.
    destruct (find (fun l => literal_var l =? v) m) as [[w|w]|];
      try discriminate; reflexivity.
Qed.

Lemma opposite_literals_satisfied : forall m c,
  has_opposite_literals c ->
  Is_true (satisfies_clause (complete_model m) c).
Proof.
  intros m c [v [Hpos Hneg]]. apply Is_true_eq_left.
  unfold satisfies_clause. apply existsb_exists.
  destruct (complete_model m v) eqn:Hvalue.
  - exists (Pos v). split; [exact Hpos|]. cbn. exact Hvalue.
  - exists (Neg v). split; [exact Hneg|]. cbn. now rewrite Hvalue.
Qed.

Lemma terminal_state_satisfies_clauses : forall s,
  state_invariant s ->
  s.(state_falsified) = [] ->
  ClauseMap.keys s.(state_watched) = [] ->
  satisfies_clause_store (complete_model s.(state_model)) s.(state_clauses).
Proof.
  intros s Hinv Hfalsified Hkeys ci c Hfind.
  destruct Hinv as [Hcover _].
  destruct (existsb (literal_is_true s.(state_model)) c) eqn:Hknown.
  - apply Is_true_eq_left. unfold satisfies_clause.
    apply existsb_exists in Hknown as [l [Hlc Hlt]].
    apply existsb_exists. exists l. split; [exact Hlc|].
    now apply literal_is_true_complete_model.
  - assert (Hunsat : Is_true
      (negb (existsb (literal_is_true s.(state_model)) c))) by
      (apply Is_true_eq_left; now rewrite Hknown).
    specialize (Hcover ci c Hfind Hunsat).
    destruct Hcover as [Htrivial|[Hwork|[[v Hwatched]|Hfals]]].
    + now apply opposite_literals_satisfied.
    + contradiction.
    + assert (ClauseMap.find v s.(state_watched) <> []) as Hnonempty.
      { intros Hempty. rewrite Hempty in Hwatched. contradiction. }
      apply ClauseMap.keys_complete in Hnonempty. now rewrite Hkeys in Hnonempty.
    + now rewrite Hfalsified in Hfals.
Qed.

Lemma rush_unfold : forall s,
  rush s =
    if is_empty (ClauseMap.keys s.(state_watched)) then
      Now (inl s)
    else
      match progress s with
      | Progress s' => Later (rush s')
      | Conflict s' cause => Now (inr (s', cause))
      end.
Proof.
  intros s.
  transitivity
    (match rush s with Now x => Now x | Later d => Later d end).
  - destruct (rush s); reflexivity.
  - cbn [rush].
    destruct (is_empty (ClauseMap.keys s.(state_watched)));
      [reflexivity|].
    destruct (progress s); reflexivity.
Qed.

Lemma rush_result_model_sound : forall s result,
  state_invariant s ->
  s.(state_falsified) = [] ->
  delay_returns (rush s) result ->
  match result with
  | inl s' =>
      satisfies_clause_store (complete_model s'.(state_model)) s.(state_clauses)
  | inr _ => True
  end.
Proof.
  intros s result Hinv Hfalsified Hreturns.
  remember (rush s) as d eqn:Hrush.
  induction Hreturns as [x|d x Hreturns IH] in s, Hinv, Hfalsified, Hrush |- *.
  - rewrite rush_unfold in Hrush.
    destruct (ClauseMap.keys s.(state_watched)) as [|v vs] eqn:Hkeys;
      cbn [is_empty] in Hrush.
    + injection Hrush as ->. now apply terminal_state_satisfies_clauses.
    + destruct (progress s) as [s'|s' cause] eqn:Hprogress;
        [discriminate|].
      injection Hrush as ->. exact I.
  - rewrite rush_unfold in Hrush.
    destruct (ClauseMap.keys s.(state_watched)) as [|v vs] eqn:Hkeys;
      cbn [is_empty] in Hrush; [discriminate|].
    destruct (progress s) as [s'|s' cause] eqn:Hprogress;
      [|discriminate].
    injection Hrush as ->.
    assert (Hinv' : state_invariant s') by
      (now apply progress_inv with (s := s)).
    assert (Hfalsified' : s'.(state_falsified) = []) by
      (now apply progress_falsified_empty with (s := s)).
    specialize (IH s' Hinv' Hfalsified' eq_refl).
    destruct x as [final|[latest cause]]; [|exact I].
    rewrite <- (progress_clauses s s' Hprogress). exact IH.
Qed.

Theorem rush_model_sound : forall s final,
  state_invariant s ->
  s.(state_falsified) = [] ->
  delay_returns (rush s) (inl final) ->
  satisfies_clause_store
    (complete_model final.(state_model)) s.(state_clauses).
Proof.
  intros s final Hinv Hfalsified Hreturns.
  exact (rush_result_model_sound s (inl final) Hinv Hfalsified Hreturns).
Qed.

Theorem add_clause_inv : forall s c s',
  state_invariant s ->
  add_clause s c = Progress s' ->
  state_invariant s'.
Proof.
  intros s c s' Hinv Hadd.
  unfold add_clause in Hadd.
  rewrite scan_clause_once_spec in Hadd.
  destruct (existsb (literal_is_true s.(state_model)) c) eqn:Hsat.
  - cbn in Hadd. injection Hadd as <-.
    apply add_resolved_clause_inv; [exact Hinv|].
    left. apply Is_true_eq_left. exact Hsat.
  - cbn in Hadd.
    destruct (clause_has_opposite_literals c) eqn:Hopposite.
    + cbn in Hadd. injection Hadd as <-.
      apply add_resolved_clause_inv; [exact Hinv|]. right.
      now apply clause_has_opposite_literals_spec.
    + cbn in Hadd.
      assert (Hnoopp : ~ has_opposite_literals c).
      { intros Hopp. apply clause_has_opposite_literals_spec in Hopp.
        congruence. }
      destruct (filter (literal_is_undecided s.(state_model)) c)
        as [|l undecided] eqn:Hfilter; [discriminate|].
      destruct (find_different_var (literal_var l) undecided)
        as [l'|] eqn:Hdifferent.
      * injection Hadd as <-.
        apply find_different_var_spec in Hdifferent as [Hl'in Hvars].
        assert (Hlin : In l c /\
            literal_is_undecided s.(state_model) l = true).
        { apply filter_In. rewrite Hfilter. now left. }
        assert (Hl'in' : In l' c /\
            literal_is_undecided s.(state_model) l' = true).
        { apply filter_In. rewrite Hfilter. now right. }
        eapply watch_one_fresh_inv with
          (c := c)
          (cm := ClauseMap.add (literal_var l) (fresh_clause_id s)
            s.(state_watched))
          (pending := s.(state_pending)).
        -- apply find_added_clause.
        -- exact Hnoopp.
        -- now apply add_first_watch_staged_inv.
        -- intros Hin. apply ClauseMap.find_add in Hin as [[Heq _]|Hin].
           ++ exact (Hvars (eq_sym Heq)).
           ++ exact (fresh_clause_not_watched s (literal_var l') Hinv Hin).
        -- exact (proj1 Hl'in').
        -- exact (proj2 Hl'in').
      * injection Hadd as <-.
        assert (Hlin : In l c /\
            literal_is_undecided s.(state_model) l = true).
        { apply filter_In. rewrite Hfilter. now left. }
        assert (Hneeds : clause_needs_literal s.(state_model) l c).
        { eapply unit_filter_needs; eauto. }
        eapply watch_one_fresh_inv with
          (c := c)
          (cm := s.(state_watched))
          (pending := (l, fresh_clause_id s) :: s.(state_pending)).
        -- apply find_added_clause.
        -- exact Hnoopp.
        -- now apply add_unit_staged_inv.
        -- now apply fresh_clause_not_watched.
        -- exact (proj1 Hlin).
        -- exact (proj2 Hlin).
Qed.
