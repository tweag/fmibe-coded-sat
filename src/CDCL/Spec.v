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

Lemma progress_falsified_empty : forall s s',
  progress s = Progress s' -> s'.(state_falsified) = [].
Proof.
  intros s s' Hprogress. unfold progress in Hprogress.
  destruct s.(state_pending) as [|[l c] pending].
  - unfold finish_progress in Hprogress.
    destruct (progress_state s) as [m cm sat fals pending'].
    destruct fals as [|d fals]; [now injection Hprogress as <-|discriminate].
  - destruct (literal_value s.(state_model) l) as [[|]|] eqn:Hvalue;
      [|discriminate|].
    all:
      unfold finish_progress in Hprogress.
    all: destruct (progress_state s) as [m cm sat fals pending'].
    all: destruct fals as [|d fals];
      [now injection Hprogress as <-|discriminate].
Qed.

Lemma progress_conflict_spec : forall s explanation,
  progress s = Conflict explanation ->
  (exists s' c, progress_state s = s' /\
    In c s'.(state_falsified) /\ explanation = neg c) \/
  (exists l c pending, s.(state_pending) = (l, c) :: pending /\
    literal_value s.(state_model) l = Some false /\ explanation = neg c).
Proof.
  intros s explanation Hprogress. unfold progress in Hprogress.
  destruct s.(state_pending) as [|[l c] pending] eqn:Hpending.
  - left. unfold finish_progress in Hprogress.
    destruct (progress_state s) as [m cm sat fals pending'] eqn:Hstate.
    destruct fals as [|d fals]; [discriminate|]. injection Hprogress as <-.
    exists {| state_model := m; state_clauses := cm;
      state_satisfied := sat; state_falsified := d :: fals;
      state_pending := pending' |}, d. split; [reflexivity|].
    split; [now left|reflexivity].
  - destruct (literal_value s.(state_model) l) as [[|]|] eqn:Hvalue.
    + left. unfold finish_progress in Hprogress.
      destruct (progress_state s) as [m cm sat fals pending'] eqn:Hstate.
      destruct fals as [|d fals]; [discriminate|]. injection Hprogress as <-.
      exists {| state_model := m; state_clauses := cm;
        state_satisfied := sat; state_falsified := d :: fals;
        state_pending := pending' |}, d. split; [reflexivity|].
      split; [now left|reflexivity].
    + right. injection Hprogress as <-. exists l, c, pending.
      repeat split; assumption.
    + left. unfold finish_progress in Hprogress.
      destruct (progress_state s) as [m cm sat fals pending'] eqn:Hstate.
      destruct fals as [|d fals]; [discriminate|]. injection Hprogress as <-.
      exists {| state_model := m; state_clauses := cm;
        state_satisfied := sat; state_falsified := d :: fals;
        state_pending := pending' |}, d. split; [reflexivity|].
      split; [now left|reflexivity].
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

Lemma in_pending_clauses : forall pending c,
  In c (pending_clauses pending) <->
  exists l, In (l, c) pending.
Proof.
  intros pending c. unfold pending_clauses. rewrite in_map_iff. split.
  - intros [[l d] [Heq Hin]]. cbn in Heq. subst d. now exists l.
  - intros [l Hin]. exists (l, c). split; [reflexivity|exact Hin].
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

Lemma count_occ_nodup_in : forall (xs : list Clause) c,
  NoDup xs -> In c xs -> count_occ clause_eq_dec xs c = 1.
Proof.
  intros xs c Hnodup. induction Hnodup as [|x xs Hnotin Hnodup IH];
    intros Hin; [contradiction|].
  simpl in Hin |- *. destruct Hin as [->|Hin].
  - destruct (clause_eq_dec c c); [|contradiction].
    rewrite (proj1 (count_occ_not_In clause_eq_dec xs c) Hnotin). reflexivity.
  - destruct (clause_eq_dec x c) as [->|Hneq]; [contradiction|].
    exact (IH Hin).
Qed.

(* A queued reason represents the second watch of its unit clause. *)
Definition card_of_watch (work : list Clause) (c : Clause) (s : State) :=
  ClauseMap.card_of c s.(state_clauses).

Definition clause_is_decided (c : Clause) (s : State) : Prop :=
  In c s.(state_satisfied) \/ In c s.(state_falsified).

Definition staged_invariant (work : list Clause) (s : State) : Prop :=
  (forall c, In c s.(state_satisfied) ->
     Is_true (existsb (literal_is_true s.(state_model)) c))
  /\ (forall c, In c s.(state_falsified) ->
     Is_true (negb (existsb (literal_is_true s.(state_model)) c)) /\
     filter (literal_is_undecided s.(state_model)) c = [])
  /\ (forall v c, In c (ClauseMap.find v s.(state_clauses)) ->
     ~ InL v s.(state_model) /\ InL v c)
  /\ (forall v, NoDup (ClauseMap.find v s.(state_clauses)))
  /\ NoDup work
  /\ (forall l c, In (l, c) s.(state_pending) ->
     In l c /\
       (literal_is_undecided s.(state_model) l = true \/
        literal_is_decided s.(state_model) l))
  /\ (forall c, In c work ->
     card_of_watch work c s = 1 \/
     (card_of_watch work c s = 0 /\
       ((exists l, In (l, c) s.(state_pending)) \/ clause_is_decided c s)))
  /\ (forall c,
     card_of_watch work c s = 0 \/
     card_of_watch work c s = 2 \/
     (card_of_watch work c s = 1 /\
       (In c work \/ (exists l, In (l, c) s.(state_pending)) \/
         clause_is_decided c s))).

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
           ++ split.
              ** intros c H. contradiction.
              ** intros c. unfold card_of_watch, pending_clauses.
                 cbn [state_clauses state_pending].
                 rewrite ClauseMap.card_of_empty. now left.
Qed.

Lemma scan_clause_once_spec : forall m c,
  scan_clause_once m c =
    (existsb (literal_is_true m) c, filter (literal_is_undecided m) c).
Proof.
  intros m c. induction c as [|l c IH]; simpl; [reflexivity|].
  now rewrite IH.
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

Lemma scan_clause_watched_spec : forall m c cm sat fals cm',
  scan_clause m c cm sat fals = clause_watched cm' ->
  exists l l', existsb (literal_is_true m) c = false /\
    In l c /\ In l' c /\
    literal_is_undecided m l = true /\
    literal_is_undecided m l' = true /\
    literal_var l <> literal_var l' /\
    cm' = if in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm)
      then ClauseMap.add (literal_var l') c cm
      else ClauseMap.add (literal_var l) c cm.
Proof.
  intros m c cm sat fals cm' Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c); [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|l undecided]
    eqn:Hfilter; [discriminate|].
  destruct (find_different_var (literal_var l) undecided) as [l'|]
    eqn:Hdifferent; [|discriminate].
  apply find_different_var_spec in Hdifferent as [Hl'in Hneq].
  assert (In l (filter (literal_is_undecided m) c)) as Hlin
    by (rewrite Hfilter; now left).
  assert (In l' (filter (literal_is_undecided m) c)) as Hl'in'.
  { rewrite Hfilter. now right. }
  apply filter_In in Hlin as [Hlc Hlu].
  apply filter_In in Hl'in' as [Hl'c Hl'u].
  exists l, l'. repeat split; try assumption.
  destruct (in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm));
    now injection Hscan as <-.
Qed.

Lemma scan_clause_decided_spec : forall m c cm sat fals cm' sat' fals',
  scan_clause m c cm sat fals = clause_decided cm' sat' fals' ->
  (existsb (literal_is_true m) c = true /\
    cm' = cm /\ sat' = c :: sat /\ fals' = fals) \/
  (existsb (literal_is_true m) c = false /\
    filter (literal_is_undecided m) c = [] /\
    cm' = cm /\ sat' = sat /\ fals' = c :: fals).
Proof.
  intros m c cm sat fals cm' sat' fals' Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c) eqn:Htrue.
  - injection Hscan as <- <- <-. now left.
  - destruct (filter (literal_is_undecided m) c) as [|l undecided]
      eqn:Hfilter.
    + injection Hscan as <- <- <-. right. repeat split; assumption.
    + destruct (find_different_var (literal_var l) undecided) as [l'|].
      * destruct (in_dec clause_eq_dec c
          (ClauseMap.find (literal_var l) cm)); discriminate.
      * discriminate.
Qed.

Lemma watch_one_fresh_inv : forall work m cm sat fals pending c l,
  staged_invariant (c :: work)
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |} ->
  existsb (literal_is_true m) c = false ->
  ~ In c (ClauseMap.find (literal_var l) cm) ->
  In l c -> literal_is_undecided m l = true ->
  staged_invariant work
    {| state_model := m; state_clauses := ClauseMap.add (literal_var l) c cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |}.
Proof.
  intros work m cm sat fals pending c l Hinv Hfalse Hfresh Hlc Hlu.
  destruct Hinv as
    [Hsat [Hfals [Hwatch [Hnodup [Hworknodup
      [Hpending [Hwork Hcard]]]]]]].
  inversion Hworknodup as [|? ? Hcnotin Hworknodup']; subst.
  pose proof (Hwork c (or_introl eq_refl)) as Hcwork.
  unfold card_of_watch in Hcwork. cbn -[ClauseMap.card_of] in Hcwork.
  split; [exact Hsat|]. split; [exact Hfals|]. split.
  - intros v d Hin. apply ClauseMap.find_add in Hin as [[-> ->]|Hin].
    + split; [now apply literal_undecided_not_InL|now apply literal_InL].
    + now apply Hwatch with (c := d).
  - split.
    + intros v. cbn [state_clauses]. rewrite ClauseMap.find_add_eq.
      destruct (VarKey.eq_dec (literal_var l) v) as [Heq|Hneq].
      * subst v. constructor; [exact Hfresh|apply Hnodup].
      * apply Hnodup.
    + split; [exact Hworknodup'|]. split; [exact Hpending|]. split.
      * intros d Hdwork. specialize (Hwork d (or_intror Hdwork)).
        assert (c <> d) as Hcd.
        { intros ->. contradiction. }
        unfold card_of_watch in Hwork |- *.
        cbn -[ClauseMap.card_of] in Hwork |- *.
        rewrite (ClauseMap.card_of_add_neq cm c d (literal_var l) Hcd).
        exact Hwork.
      * intros d. destruct (clause_eq_dec c d) as [->|Hcd].
        -- unfold card_of_watch. cbn -[ClauseMap.card_of].
           rewrite ClauseMap.card_of_add.
           destruct Hcwork as [Hone|[Hzero Hreason]].
           ++ rewrite Hone. now right; left.
           ++ rewrite Hzero. right; right. split; [reflexivity|].
              right. exact Hreason.
        -- specialize (Hcard d).
           unfold card_of_watch in Hcard |- *.
           cbn -[ClauseMap.card_of] in Hcard |- *.
           rewrite (ClauseMap.card_of_add_neq cm c d (literal_var l) Hcd).
           destruct Hcard as [Hzero|[Htwo|[Hone Hreason]]].
           ++ now left.
           ++ now right; left.
           ++ right; right. split; [exact Hone|].
              destruct Hreason as [Hdwork|Hotherreason].
              ** simpl in Hdwork. destruct Hdwork as [Heq|Hdwork];
                   [contradiction|now left].
              ** now right.
Qed.

Lemma watch_one_inv : forall work m cm sat fals pending c l l' cm',
  staged_invariant (c :: work)
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |} ->
  existsb (literal_is_true m) c = false ->
  In l c -> In l' c ->
  literal_is_undecided m l = true ->
  literal_is_undecided m l' = true ->
  literal_var l <> literal_var l' ->
  cm' = (if in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm)
    then ClauseMap.add (literal_var l') c cm
    else ClauseMap.add (literal_var l) c cm) ->
  staged_invariant work
    {| state_model := m; state_clauses := cm';
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |}.
Proof.
  intros work m cm sat fals pending c l l' cm' Hinv Hfalse
    Hlc Hl'c Hlu Hl'u Hneq Hcm'.
  destruct (in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm))
    as [Hwatched|Hfresh].
  - subst cm'. apply watch_one_fresh_inv; try assumption.
    intros Hwatched'.
    destruct Hinv as [_ [_ [_ [_ [_ [_ [Hwork _]]]]]]].
    specialize (Hwork c (or_introl eq_refl)).
    unfold card_of_watch in Hwork. cbn -[ClauseMap.card_of] in Hwork.
    assert (ClauseMap.card_of c cm = 1) as Hcone.
    { destruct Hwork as [Hone|[Hzero _]]; [exact Hone|].
      pose proof (ClauseMap.card_of_in cm c (literal_var l) Hwatched).
      lia. }
    apply Hneq. eapply ClauseMap.card_of_unique; eauto.
  - subst cm'. now apply watch_one_fresh_inv.
Qed.

Lemma propagate_literal_inv : forall work m cm sat fals pending c l,
  staged_invariant (c :: work)
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |} ->
  scan_clause m c cm sat fals = propagate_literal l ->
  staged_invariant work
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := (l, c) :: pending |}.
Proof.
  intros work m cm sat fals pending c l Hinv Hscan.
  pose proof (scan_clause_inl_spec _ _ _ _ _ _ Hscan) as [Hlc Hlu].
  destruct Hinv as
    [Hsat [Hfals [Hwatch [Hnodup [Hworknodup
      [Hpending [Hwork Hcard]]]]]]].
  inversion Hworknodup as [|? ? Hcnotin Hworknodup']; subst.
  split; [exact Hsat|]. split; [exact Hfals|]. split; [exact Hwatch|].
  split; [exact Hnodup|]. split; [exact Hworknodup'|]. split.
  - intros p d Hpd. simpl in Hpd. destruct Hpd as [Heq|Hpd].
    + injection Heq as <- <-. split; [exact Hlc|now left].
    + exact (Hpending p d Hpd).
  - split.
    + intros d Hdwork. specialize (Hwork d (or_intror Hdwork)).
      destruct Hwork as [Hone|[Hzero Hreason]].
      * now left.
      * right. split; [exact Hzero|]. destruct Hreason as [[p Hpd]|Hdecided].
        -- left. exists p. now right.
        -- now right.
    + intros d. specialize (Hcard d).
      destruct Hcard as [Hzero|[Htwo|[Hone Hreason]]].
      * now left.
      * now right; left.
      * right; right. split; [exact Hone|].
        destruct Hreason as [Hdwork|[[p Hpd]|Hdecided]].
        -- simpl in Hdwork. destruct Hdwork as [->|Hdwork].
           ++ right. left. exists l. now left.
           ++ now left.
        -- right. left. exists p. now right.
        -- now right; right.
Qed.

Lemma decide_active_inv : forall work m cm sat fals pending c sat' fals',
  staged_invariant (c :: work)
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |} ->
  (forall d, In d sat' -> Is_true (existsb (literal_is_true m) d)) ->
  (forall d, In d fals' ->
    Is_true (negb (existsb (literal_is_true m) d)) /\
    filter (literal_is_undecided m) d = []) ->
  (In c sat' \/ In c fals') ->
  (forall d, In d sat \/ In d fals -> In d sat' \/ In d fals') ->
  staged_invariant work
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat'; state_falsified := fals';
       state_pending := pending |}.
Proof.
  intros work m cm sat fals pending c sat' fals' Hinv Hsat' Hfals'
    Hcdecided Hpreserve.
  destruct Hinv as
    [_ [_ [Hwatch [Hnodup [Hworknodup
      [Hpending [Hwork Hcard]]]]]]].
  inversion Hworknodup as [|? ? Hcnotin Hworknodup']; subst.
  split; [exact Hsat'|]. split; [exact Hfals'|]. split.
  - exact Hwatch.
  - split.
    + exact Hnodup.
    + split; [exact Hworknodup'|]. split; [exact Hpending|]. split.
      * intros d Hdwork. specialize (Hwork d (or_intror Hdwork)).
        destruct Hwork as [Hone|[Hzero [Hpendingreason|Hdecided]]].
        -- now left.
        -- right. split; [exact Hzero|now left].
        -- right. split; [exact Hzero|]. right. now apply Hpreserve.
      * intros d. specialize (Hcard d).
        destruct Hcard as [Hzero|[Htwo|[Hone Hreason]]].
        -- now left.
        -- now right; left.
        -- right; right. split; [exact Hone|].
           destruct Hreason as [Hdwork|[Hpendingreason|Hdecided]].
           ++ simpl in Hdwork. destruct Hdwork as [->|Hdwork].
              ** right; right. exact Hcdecided.
              ** now left.
           ++ now right; left.
           ++ right; right. now apply Hpreserve.
Qed.

Lemma propagate_decided_inv : forall work m cm sat fals pending c cm' sat' fals',
  staged_invariant (c :: work)
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |} ->
  scan_clause m c cm sat fals = clause_decided cm' sat' fals' ->
  staged_invariant work
    {| state_model := m; state_clauses := cm';
       state_satisfied := sat'; state_falsified := fals';
       state_pending := pending |}.
Proof.
  intros work m cm sat fals pending c cm' sat' fals' Hinv Hscan.
  pose proof (scan_clause_decided_spec _ _ _ _ _ _ _ _ Hscan) as Hspec.
  pose proof Hinv as Hinv'.
  destruct Hinv as [Hsat [Hfals Hrest]].
  destruct Hspec as [[Htrue [-> [-> ->]]]|[Hfalse [Hfilter [-> [-> ->]]]]].
  - eapply decide_active_inv.
    + exact Hinv'.
    + intros d Hd. simpl in Hd. destruct Hd as [->|Hd];
        [now rewrite Htrue|exact (Hsat d Hd)].
    + exact Hfals.
    + left. now left.
    + intros d [Hd|Hd].
      * left. now right.
      * now right.
  - eapply decide_active_inv.
    + exact Hinv'.
    + exact Hsat.
    + intros d Hd. simpl in Hd. destruct Hd as [->|Hd].
      * split; [now rewrite Hfalse|exact Hfilter].
      * exact (Hfals d Hd).
    + right. now left.
    + intros d [Hd|Hd].
      * now left.
      * right. now right.
Qed.

Lemma propagate_inv : forall c work s,
  staged_invariant (c :: work) s ->
  staged_invariant work (propagate c s).
Proof.
  intros c work [m cm sat fals pending] Hinv.
  unfold propagate. cbn [state_model state_clauses state_satisfied
    state_falsified state_pending] in Hinv |- *.
  destruct (scan_clause m c cm sat fals) as [l|cm' sat' fals'|cm']
    eqn:Hscan.
  - now eapply propagate_literal_inv.
  - eapply propagate_decided_inv.
    + exact Hinv.
    + exact Hscan.
  - pose proof (scan_clause_watched_spec _ _ _ _ _ _ Hscan) as
      [l [l' [Hfalse [Hlc [Hl'c [Hlu [Hl'u [Hneq Hcm']]]]]]]].
    eapply watch_one_inv.
    + exact Hinv.
    + exact Hfalse.
    + exact Hlc.
    + exact Hl'c.
    + exact Hlu.
    + exact Hl'u.
    + exact Hneq.
    + exact Hcm'.
Qed.

Lemma prepare_set_lit_inv : forall l m cm sat fals pending,
  literal_is_undecided m l = true ->
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |} ->
  staged_invariant (ClauseMap.find (literal_var l) cm)
    {| state_model := l :: m;
       state_clauses := ClauseMap.remove (literal_var l) cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := pending |}.
Proof.
  intros l m cm sat fals pending Hlu Hinv.
  destruct Hinv as
    [Hsat [Hfals [Hwatch [Hnodup [_ [Hpending [_ Hcard]]]]]]].
  split.
  - intros c Hin. apply satisfied_cons_undecided; [exact Hlu|exact (Hsat c Hin)].
  - split.
    + intros c Hin. apply falsified_cons_undecided; [exact Hlu|exact (Hfals c Hin)].
    + split.
      * intros v c Hin. apply ClauseMap.find_remove in Hin as [Hin Hneq].
        destruct (Hwatch v c Hin) as [Hnotin Hinc]. split; [|exact Hinc].
        intros Hinmodel. apply Hnotin.
        eapply InL_cons_other; [exact Hneq|exact Hinmodel].
      * split.
        -- intros v. cbn [state_clauses]. rewrite ClauseMap.find_remove_eq.
           destruct (VarKey.eq_dec (literal_var l) v);
             [constructor|apply Hnodup].
        -- split; [apply Hnodup|]. split.
           ++ intros p c Hpc. destruct (Hpending p c Hpc) as [Hpin Hp].
              split; [exact Hpin|now apply literal_pending_cons].
           ++ split.
              ** intros c Hcin.
                 pose proof (ClauseMap.card_of_in cm c (literal_var l) Hcin)
                   as Hpos.
                 pose proof (ClauseMap.card_of_remove cm c (literal_var l))
                   as Hremove.
                 change (ClauseMap.card_of c (ClauseMap.remove (literal_var l) cm) +
                   count_occ clause_eq_dec (ClauseMap.find (literal_var l) cm) c =
                   ClauseMap.card_of c cm) in Hremove.
                 pose proof (count_occ_nodup_in
                   (ClauseMap.find (literal_var l) cm) c
                   (Hnodup (literal_var l)) Hcin) as Hcount.
                 specialize (Hcard c).
                 unfold card_of_watch in Hcard |- *.
                 cbn -[ClauseMap.card_of] in Hcard |- *.
                 destruct Hcard as [Hzero|[Htwo|[Hone Hreason]]].
                 --- lia.
                 --- left. rewrite Hcount, Htwo in Hremove. lia.
                 --- right. split; [rewrite Hcount, Hone in Hremove; lia|].
                     destruct Hreason as [Habs|Hotherreason];
                       [contradiction|exact Hotherreason].
              ** intros c.
                 pose proof (ClauseMap.card_of_remove cm c (literal_var l))
                   as Hremove.
                 change (ClauseMap.card_of c (ClauseMap.remove (literal_var l) cm) +
                   count_occ clause_eq_dec (ClauseMap.find (literal_var l) cm) c =
                   ClauseMap.card_of c cm) in Hremove.
                 specialize (Hcard c).
                 unfold card_of_watch in Hcard |- *.
                 cbn -[ClauseMap.card_of] in Hcard |- *.
                 destruct (in_dec clause_eq_dec c
                   (ClauseMap.find (literal_var l) cm)) as [Hcin|Hnotin].
                 --- pose proof (count_occ_nodup_in
                       (ClauseMap.find (literal_var l) cm) c
                       (Hnodup (literal_var l)) Hcin) as Hcount.
                     destruct Hcard as [Hzero|[Htwo|[Hone Hreason]]].
                     +++ left. lia.
                     +++ right; right. split.
                         *** rewrite Hcount, Htwo in Hremove. lia.
                         *** now left.
                     +++ left. rewrite Hcount, Hone in Hremove. lia.
                 --- pose proof (proj1 (count_occ_not_In clause_eq_dec
                       (ClauseMap.find (literal_var l) cm) c) Hnotin) as Hcount.
                     destruct Hcard as [Hzero|[Htwo|[Hone Hreason]]].
                     +++ left. lia.
                     +++ right; left. rewrite Hcount, Htwo in Hremove. lia.
                     +++ right; right. split.
                         *** rewrite Hcount, Hone in Hremove. lia.
                         ***
                         destruct Hreason as [Habs|Hotherreason];
                           [contradiction|now right].
Qed.

Lemma fold_propagate_inv : forall work s,
  staged_invariant work s ->
  state_invariant (fold_left (fun s c => propagate c s) work s).
Proof.
  induction work as [|c work IH]; intros s Hinv; [exact Hinv|].
  simpl. apply IH. now apply propagate_inv.
Qed.

Lemma set_lit_inv : forall l s,
  literal_is_undecided s.(state_model) l = true ->
  state_invariant s -> state_invariant (set_lit l s).
Proof.
  intros l [m cm sat fals pending] Hlu Hinv.
  unfold set_lit. cbn [state_model state_clauses state_satisfied
    state_falsified state_pending].
  apply fold_propagate_inv.
  now apply prepare_set_lit_inv.
Qed.

Lemma resolve_pending_staged_inv : forall work l c pending m cm sat fals,
  staged_invariant work
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := (l, c) :: pending |} ->
  Is_true (existsb (literal_is_true m) c) ->
  staged_invariant work
    {| state_model := m; state_clauses := cm;
       state_satisfied := c :: sat; state_falsified := fals;
       state_pending := pending |}.
Proof.
  intros work l c pending m cm sat fals Hinv Hctrue.
  destruct Hinv as
    [Hsat [Hfals [Hwatch [Hnodup [Hworknodup
      [Hpending [Hwork Hcard]]]]]]].
  assert (forall d, clause_is_decided d
      {| state_model := m; state_clauses := cm;
         state_satisfied := sat; state_falsified := fals;
         state_pending := (l, c) :: pending |} ->
    clause_is_decided d
      {| state_model := m; state_clauses := cm;
         state_satisfied := c :: sat; state_falsified := fals;
         state_pending := pending |}) as Hdecided.
  { intros d [Hd|Hd]; [left; now right|now right]. }
  assert (forall d, (exists p, In (p, d) ((l, c) :: pending)) ->
    (exists p, In (p, d) pending) \/
    clause_is_decided d
      {| state_model := m; state_clauses := cm;
         state_satisfied := c :: sat; state_falsified := fals;
         state_pending := pending |}) as Hreason.
  { intros d [p Hpd]. simpl in Hpd. destruct Hpd as [Heq|Hpd].
    - injection Heq as <- <-. right. left. now left.
    - left. now exists p. }
  split.
  - intros d Hd. simpl in Hd. destruct Hd as [->|Hd]; [exact Hctrue|exact (Hsat d Hd)].
  - split; [exact Hfals|]. split; [exact Hwatch|]. split; [exact Hnodup|].
    split; [exact Hworknodup|]. split.
    + intros p d Hpd. exact (Hpending p d (or_intror Hpd)).
    + split.
      * intros d Hdwork. specialize (Hwork d Hdwork).
        destruct Hwork as [Hone|[Hzero [Hpendingreason|Holddecided]]].
        -- now left.
        -- right. split; [exact Hzero|exact (Hreason d Hpendingreason)].
        -- right. split; [exact Hzero|]. right. now apply Hdecided.
      * intros d. specialize (Hcard d).
        destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
        -- now left.
        -- now right; left.
        -- right; right. split; [exact Hone|].
           destruct Hwhy as [Hdwork|[Hpendingreason|Holddecided]].
           ++ now left.
           ++ right. exact (Hreason d Hpendingreason).
           ++ right; right. now apply Hdecided.
Qed.

Lemma set_pending_inv : forall l c pending m cm sat fals,
  literal_is_undecided m l = true ->
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := (l, c) :: pending |} ->
  state_invariant
    (set_lit l
      {| state_model := m; state_clauses := cm;
         state_satisfied := c :: sat; state_falsified := fals;
         state_pending := pending |}).
Proof.
  intros l c pending m cm sat fals Hlu Hinv.
  pose proof Hinv as Hpendinginv.
  destruct Hpendinginv as [_ [_ [_ [_ [_ [Hpending _]]]]]].
  destruct (Hpending l c (or_introl eq_refl)) as [Hlc _].
  unfold set_lit. cbn [state_model state_clauses state_satisfied
    state_falsified state_pending].
  apply fold_propagate_inv.
  pose proof (prepare_set_lit_inv l m cm sat fals ((l, c) :: pending)
    Hlu Hinv) as Hprepared.
  apply (resolve_pending_staged_inv
    (ClauseMap.find (literal_var l) cm) l c pending
    (l :: m) (ClauseMap.remove (literal_var l) cm) sat fals Hprepared).
  apply Is_true_eq_left. apply existsb_exists. exists l.
  split; [exact Hlc|apply literal_is_true_cons_self].
Qed.

Lemma resolve_true_pending_inv : forall l c pending m cm sat fals,
  literal_is_true m l = true ->
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := sat; state_falsified := fals;
       state_pending := (l, c) :: pending |} ->
  state_invariant
    {| state_model := m; state_clauses := cm;
       state_satisfied := c :: sat; state_falsified := fals;
       state_pending := pending |}.
Proof.
  intros l c pending m cm sat fals Hltrue Hinv.
  pose proof Hinv as Hpendinginv.
  destruct Hpendinginv as [_ [_ [_ [_ [_ [Hpending _]]]]]].
  destruct (Hpending l c (or_introl eq_refl)) as [Hlc _].
  apply (resolve_pending_staged_inv [] l c pending m cm sat fals Hinv).
  apply Is_true_eq_left. apply existsb_exists. now exists l.
Qed.

Lemma finish_progress_inv : forall s s',
  state_invariant s -> finish_progress s = Progress s' -> state_invariant s'.
Proof.
  intros [m cm sat fals pending] s' Hinv Hfinish.
  unfold finish_progress in Hfinish. destruct fals as [|c fals];
    [now injection Hfinish as <-|discriminate].
Qed.

Lemma progress_inv : forall s s',
  state_invariant s -> progress s = Progress s' -> state_invariant s'.
Proof.
  intros [m cm sat fals pending] s' Hinv Hprogress.
  unfold progress in Hprogress.
  cbn [state_pending state_model] in Hprogress.
  destruct pending as [|[l c] pending].
  - apply finish_progress_inv with
      (s := progress_state
        {| state_model := m; state_clauses := cm;
           state_satisfied := sat; state_falsified := fals;
           state_pending := [] |}); [|exact Hprogress].
    unfold progress_state. cbn [state_pending state_model state_clauses
      state_satisfied state_falsified].
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
      exact (proj1 (Hwatch v d Hin)).
    + exact Hinv.
  - destruct (literal_value m l) as [[|]|] eqn:Hvalue.
    + apply finish_progress_inv with
        (s := progress_state
          {| state_model := m; state_clauses := cm;
             state_satisfied := sat; state_falsified := fals;
             state_pending := (l, c) :: pending |}); [|exact Hprogress].
      unfold progress_state. cbn [state_pending state_model state_clauses
        state_satisfied state_falsified]. rewrite Hvalue.
      apply (resolve_true_pending_inv l c pending m cm sat fals);
        [|exact Hinv].
      unfold literal_is_true. now rewrite Hvalue.
    + discriminate.
    + apply finish_progress_inv with
        (s := progress_state
          {| state_model := m; state_clauses := cm;
             state_satisfied := sat; state_falsified := fals;
             state_pending := (l, c) :: pending |}); [|exact Hprogress].
      unfold progress_state. cbn [state_pending state_model state_clauses
        state_satisfied state_falsified]. rewrite Hvalue.
      apply (set_pending_inv l c pending m cm sat fals); [|exact Hinv].
      unfold literal_is_undecided. now rewrite Hvalue.
Qed.
