(* Specifications and proofs for the CDCL SAT solver  *)

Require Import FMV.CDCL.Impl.
Require Import FMV.Id.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.

Lemma count_occ_eq_one_of_nodup_in {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall (xs : list A) x,
    NoDup xs -> In x xs -> count_occ eq_dec xs x = 1.
Proof.
  intros xs x Hnodup Hin. induction Hnodup as [|a xs Hnotin Hnodup IH].
  - contradiction.
  - cbn in Hin. destruct Hin as [<-|Hin].
    + cbn. destruct (eq_dec a a) as [_|Hneq]; [|contradiction].
      assert (Hzero : count_occ eq_dec xs a = 0).
      { apply count_occ_not_In. exact Hnotin. }
      lia.
    + cbn. destruct (eq_dec a x) as [->|Hneq].
      * contradiction.
      * now apply IH.
Qed.

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

Definition satisfies_clause_store (m : SModel) (clauses : ClauseStore.t) : Prop :=
  forall ci c, ClauseStore.find ci clauses = Some c ->
    Is_true (satisfies_clause m c).

Definition clause_implied_by_store (clauses : ClauseStore.t) (c : Clause) : Prop :=
  forall m, satisfies_clause_store m clauses -> Is_true (satisfies_clause m c).

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
  Id.eqb (literal_var l) v.

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
    rewrite Id.eqb_refl in Hundecided. destruct l; discriminate.
  - unfold literal_is_undecided, literal_value in Hundecided. simpl in Hundecided.
    destruct (Id.eqb (literal_var x) (literal_var l)) eqn:Heq;
      [destruct x, l; discriminate|].
    apply (IH l); [exact Hundecided|exact Hin].
Qed.

Lemma literal_undecided_not_InL : forall m l,
  literal_is_undecided m l = true ->
  ~ InL (literal_var l) m.
Proof.
  intros m l Hundecided [Hpos|Hneg].
  all: unfold literal_is_undecided, literal_value in Hundecided;
       destruct (find (fun l' => Id.eqb (literal_var l') (literal_var l)) m)
         as [[v|v]|] eqn:Hfind.
  all: try (destruct l; discriminate).
  - pose proof (find_none _ _ Hfind _ Hpos) as Hfalse.
    cbn [literal_var] in Hfalse. now rewrite Id.eqb_refl in Hfalse.
  - pose proof (find_none _ _ Hfind _ Hneg) as Hfalse.
    cbn [literal_var] in Hfalse. now rewrite Id.eqb_refl in Hfalse.
Qed.

Lemma not_InL_literal_undecided : forall m l,
  ~ InL (literal_var l) m -> literal_is_undecided m l = true.
Proof.
  intros m l Hnotin. unfold literal_is_undecided, literal_value.
  destruct (find (fun x => Id.eqb (literal_var x) (literal_var l)) m)
    as [x|] eqn:Hfind; [|reflexivity].
  exfalso. apply find_some in Hfind as [Hin Hvars].
  apply Id.eqb_eq in Hvars. apply Hnotin.
  destruct x as [v|v]; cbn [literal_var] in Hvars; subst v;
    [left|right]; exact Hin.
Qed.

Lemma decided_literal_InL : forall m l,
  literal_is_undecided m l = false -> InL (literal_var l) m.
Proof.
  intros m l Hdecided. unfold literal_is_undecided, literal_value in Hdecided.
  destruct (find (fun x => Id.eqb (literal_var x) (literal_var l)) m)
    as [x|] eqn:Hfind; [|discriminate].
  apply find_some in Hfind as [Hin Hvar]. apply Id.eqb_eq in Hvar.
  destruct x as [v|v]; cbn in Hvar; subst v; [left|right]; exact Hin.
Qed.

Lemma InL_map_literal_var : forall m v,
  InL v m <-> In v (map literal_var m).
Proof.
  intros m v. split.
  - intros [Hpos|Hneg]; apply in_map_iff.
    + exists (Pos v). now split.
    + exists (Neg v). now split.
  - intros Hin. apply in_map_iff in Hin as [l [Hvar Hin]].
    destruct l as [w|w]; cbn in Hvar; subst w; [left|right]; exact Hin.
Qed.

Lemma literal_is_undecided_pos_neg : forall m v,
  literal_is_undecided m (Pos v) = literal_is_undecided m (Neg v).
Proof.
  intros m v. unfold literal_is_undecided, literal_value.
  cbn [literal_var].
  destruct (find (fun l => Id.eqb (literal_var l) v) m) as [[w|w]|];
    reflexivity.
Qed.

Lemma literal_is_true_cons_undecided : forall m l x,
  literal_is_undecided m l = true ->
  literal_is_true m x = true ->
  literal_is_true (l :: m) x = true.
Proof.
  intros m l x Hlu Hxt.
  unfold literal_is_undecided, literal_is_true, literal_value in *.
  simpl. destruct (Id.eqb (literal_var l) (literal_var x)) eqn:Hvars.
  - apply Id.eqb_eq in Hvars. rewrite Hvars in Hlu.
    destruct (find (fun l' => Id.eqb (literal_var l') (literal_var x)) m) eqn:Hfind.
    + destruct l, l0; discriminate Hlu.
    + discriminate Hxt.
  - exact Hxt.
Qed.

Lemma literal_is_true_cons_self : forall m l,
  literal_is_true (l :: m) l = true.
Proof.
  intros m [v|v]; unfold literal_is_true, literal_value; simpl;
    rewrite Id.eqb_refl; reflexivity.
Qed.

Lemma decided_literal_cons_undecided : forall m l x,
  literal_is_undecided m l = true ->
  literal_is_undecided m x = false ->
  literal_is_true (l :: m) x = literal_is_true m x /\
  literal_is_undecided (l :: m) x = false.
Proof.
  intros m l x Hlu Hxu.
  unfold literal_is_undecided, literal_is_true, literal_value in *.
  simpl. destruct (Id.eqb (literal_var l) (literal_var x)) eqn:Hvars.
  - apply Id.eqb_eq in Hvars. rewrite Hvars in Hlu.
    destruct (find (fun l' => Id.eqb (literal_var l') (literal_var x)) m)
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

Lemma undecided_cons_other_var : forall m l x,
  literal_var l <> literal_var x ->
  literal_is_undecided m x = true ->
  literal_is_undecided (l :: m) x = true.
Proof.
  intros m l x Hneq Hxu.
  unfold literal_is_undecided, literal_value in *. cbn.
  apply Id.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma undecided_cons_inv : forall m l x,
  literal_is_undecided (l :: m) x = true ->
  literal_var l <> literal_var x /\
  literal_is_undecided m x = true.
Proof.
  intros m l x Hxu. unfold literal_is_undecided, literal_value in Hxu |- *.
  cbn in Hxu. destruct (Id.eqb (literal_var l) (literal_var x)) eqn:Heq.
  - destruct l, x; discriminate.
  - split; [now apply Id.eqb_neq|exact Hxu].
Qed.

Lemma literal_value_cons_other_var : forall m l x,
  literal_var l <> literal_var x ->
  literal_value (l :: m) x = literal_value m x.
Proof.
  intros m l x Hneq. unfold literal_value. cbn.
  apply Id.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma unsatisfied_cons_inv : forall m l c,
  literal_is_undecided m l = true ->
  Is_true (negb (existsb (literal_is_true (l :: m)) c)) ->
  Is_true (negb (existsb (literal_is_true m) c)).
Proof.
  intros m l c Hlu Hnew. apply negb_prop_intro. intros Hold.
  apply (negb_prop_elim _ Hnew). now apply satisfied_cons_undecided.
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
  destruct (Id.eq_dec (literal_var l) (literal_var x)) as [Heq|Hneq].
  - right. destruct l as [v|v], x as [w|w]; cbn in Heq; subst w;
      unfold literal_is_decided, literal_is_undecided, literal_value;
      simpl; rewrite Id.eqb_refl; reflexivity.
  - left. unfold literal_is_undecided, literal_value in Hundecided |- *.
    simpl. apply Id.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma literal_false_cons_undecided : forall m l x,
  literal_is_undecided m l = true ->
  literal_value m x = Some false ->
  literal_value (l :: m) x = Some false.
Proof.
  intros m l x Hlu Hfalse.
  unfold literal_is_undecided, literal_value in Hlu, Hfalse |- *.
  simpl. destruct (Id.eqb (literal_var l) (literal_var x)) eqn:Hvars.
  - apply Id.eqb_eq in Hvars. rewrite Hvars in Hlu.
    destruct (find (fun l' => Id.eqb (literal_var l') (literal_var x)) m)
      as [y|] eqn:Hfind; [|discriminate].
    destruct l, y; discriminate.
  - exact Hfalse.
Qed.

Definition watched_clause (ci : ClausePointer) (s : State) : Prop :=
  exists v, In ci (ClauseMap.find v s.(state_watched)).

Definition clause_has_two_undecided (m : Model) (c : Clause) : Prop :=
  exists l l', In l c /\ In l' c /\
    literal_var l <> literal_var l' /\
    literal_is_undecided m l = true /\
    literal_is_undecided m l' = true.

Definition model_suffix (suffix model : Model) : Prop :=
  exists prefix, model = prefix ++ suffix.

Lemma model_suffix_refl : forall m, model_suffix m m.
Proof. intros m. exists []. reflexivity. Qed.

Lemma model_suffix_trans : forall m'' m' m,
  model_suffix m'' m' -> model_suffix m' m -> model_suffix m'' m.
Proof.
  intros m'' m' m [p Hp] [q Hq]. subst m' m.
  exists (q ++ p). now rewrite app_assoc.
Qed.

Lemma model_suffix_cons_cases : forall suffix l model,
  model_suffix suffix (l :: model) ->
  suffix = l :: model \/ model_suffix suffix model.
Proof.
  intros suffix l model [prefix Hprefix].
  destruct prefix as [|x prefix].
  - now left.
  - right. cbn in Hprefix. injection Hprefix as _ Hmodel.
    exists prefix. exact Hmodel.
Qed.

Lemma find_literal_with_var_some : forall v c l,
  find_literal_with_var v c = Some l -> In l c /\ literal_var l = v.
Proof.
  intros v c. induction c as [|x c IH]; intros l Hfind; cbn in Hfind.
  - discriminate.
  - destruct (Id.eq_dec v (literal_var x)) as [Heq|Hneq].
    + injection Hfind as <-. split; [now left|now symmetry].
    + destruct (IH l Hfind) as [Hin Hvar]. now split; [right|].
Qed.

Lemma find_literal_with_var_none : forall v c,
  find_literal_with_var v c = None -> ~ InL v c.
Proof.
  intros v c. induction c as [|x c IH]; intros Hnone; [now intros [H|H]|].
  cbn in Hnone. destruct (Id.eq_dec v (literal_var x)) as [Heq|Hneq];
    [discriminate|].
  intros [Hpos|Hneg]; destruct x as [w|w]; cbn in Hneq.
  - destruct Hpos as [Heq|Hin]; [injection Heq as <-; contradiction|].
    apply (IH Hnone). now left.
  - destruct Hpos as [Heq|Hin]; [discriminate|].
    apply (IH Hnone). now left.
  - destruct Hneg as [Heq|Hin]; [discriminate|].
    apply (IH Hnone). now right.
  - destruct Hneg as [Heq|Hin]; [injection Heq as <-; contradiction|].
    apply (IH Hnone). now right.
Qed.

Definition excluded_var (excluded : option Var) (v : Var) : Prop :=
  exists x, excluded = Some x /\ x = v.

Lemma excluded_var_dec : forall excluded v,
  {excluded_var excluded v} + {~ excluded_var excluded v}.
Proof.
  intros [x|] v.
  - destruct (Id.eq_dec x v) as [->|Hneq].
    + left. exists v. now split.
    + right. intros [y [Heq Hy]]. injection Heq as <-. contradiction.
  - right. intros [y [Heq _]]. discriminate.
Qed.

Lemma find_recent_clause_literal_except_some :
  forall excluded model c l,
  find_recent_clause_literal_except excluded model c = Some l ->
  exists before assigned after,
    model = before ++ assigned :: after /\
    In l c /\ literal_var assigned = literal_var l /\
    ~ excluded_var excluded (literal_var l) /\
    (forall x, In x before ->
       excluded_var excluded (literal_var x) \/ ~ InL (literal_var x) c).
Proof.
  intros excluded model. induction model as [|assigned model IH];
    intros c l Hfind; cbn in Hfind; [discriminate|].
  destruct excluded as [excluded|].
  - destruct (Id.eq_dec excluded (literal_var assigned)) as [Heq|Hneq].
    + destruct (IH c l Hfind) as
        [before [found [after [Hmodel [Hinc [Hvar [Hexcluded Hbefore]]]]]]].
      exists (assigned :: before), found, after. subst model.
      repeat split; try assumption.
      intros x [<-|Hin].
      * left. exists excluded. now split.
      * now apply Hbefore.
    + destruct (find_literal_with_var (literal_var assigned) c)
        as [found|] eqn:Hclause.
      * injection Hfind as <-. destruct (find_literal_with_var_some
          _ _ _ Hclause) as [Hinc Hvar].
        exists [], assigned, model. split; [reflexivity|].
        split; [exact Hinc|]. split; [now symmetry|]. split.
        -- intros [x [Heq Hx]]. injection Heq as <-. apply Hneq.
           rewrite <- Hvar. exact Hx.
        -- intros x H. contradiction.
      * destruct (IH c l Hfind) as
          [before [found [after [Hmodel [Hinc [Hvar [Hexcluded Hbefore]]]]]]].
        exists (assigned :: before), found, after. subst model.
        repeat split; try assumption.
        intros x [<-|Hin].
        -- right. now apply find_literal_with_var_none.
        -- now apply Hbefore.
  - destruct (find_literal_with_var (literal_var assigned) c)
      as [found|] eqn:Hclause.
    + injection Hfind as <-. destruct (find_literal_with_var_some
        _ _ _ Hclause) as [Hinc Hvar].
      exists [], assigned, model. split; [reflexivity|].
      split; [exact Hinc|]. split; [now symmetry|]. split.
      * intros [x [H _]]. discriminate.
      * intros x H. contradiction.
    + destruct (IH c l Hfind) as
        [before [found [after [Hmodel [Hinc [Hvar [Hexcluded Hbefore]]]]]]].
      exists (assigned :: before), found, after. subst model.
      repeat split; try assumption.
      intros x [<-|Hin].
      * right. now apply find_literal_with_var_none.
      * now apply Hbefore.
Qed.

Lemma find_recent_clause_literal_except_none :
  forall excluded model c,
  find_recent_clause_literal_except excluded model c = None ->
  forall assigned, In assigned model ->
    ~ excluded_var excluded (literal_var assigned) ->
    ~ InL (literal_var assigned) c.
Proof.
  intros excluded model. induction model as [|x model IH];
    intros c Hnone assigned Hin Hnotexcluded; [contradiction|].
  cbn in Hnone. destruct excluded as [v|].
  - destruct (Id.eq_dec v (literal_var x)) as [Heq|Hneq].
    + destruct Hin as [<-|Hin].
      * exfalso. apply Hnotexcluded. exists v. now split.
      * eapply IH; eauto.
    + destruct (find_literal_with_var (literal_var x) c) eqn:Hfind;
        [discriminate|].
      destruct Hin as [<-|Hin].
      * now apply find_literal_with_var_none.
      * eapply IH; eauto.
  - destruct (find_literal_with_var (literal_var x) c) eqn:Hfind;
      [discriminate|].
    destruct Hin as [<-|Hin].
    + now apply find_literal_with_var_none.
    + eapply IH; eauto.
Qed.

Lemma nodup_map_app_disjoint : forall {A B} (f : A -> B) before after x,
  NoDup (map f (before ++ after)) ->
  In x (map f before) -> ~ In x (map f after).
Proof.
  intros A B f before. induction before as [|a before IH];
    intros after x Hnodup Hin; [contradiction|].
  cbn in Hnodup, Hin. inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
  destruct Hin as [<-|Hin].
  - intros Hafter. apply Hnotin. rewrite map_app. apply in_or_app. now right.
  - eapply IH; eauto.
Qed.

Lemma prefix_before_marker : forall {A B} (f : A -> B)
    model before marker after removed suffix,
  NoDup (map f model) ->
  model = before ++ marker :: after ->
  model = removed ++ suffix ->
  In (f marker) (map f suffix) ->
  exists middle, before = removed ++ middle.
Proof.
  intros A B f model before marker after removed suffix Hnodup Hmarker Hsuffix Hin.
  subst model. pose proof Hnodup as Hnodupsplit.
  rewrite Hsuffix in Hnodupsplit. apply app_eq_app in Hsuffix as
    [middle [[Hbefore _]|[Hremoved Hrest]]].
  - now exists middle.
  - destruct middle as [|x middle].
    + rewrite app_nil_r in Hremoved. subst removed.
      exists []. now rewrite app_nil_r.
    + cbn in Hrest. injection Hrest as Hx _.
      exfalso. subst x.
      eapply nodup_map_app_disjoint; [exact Hnodupsplit| |exact Hin].
      rewrite Hremoved, map_app. apply in_or_app. right. cbn. now left.
Qed.

Lemma recent_clause_literal_undecided :
  forall excluded model c watched suffix,
  find_recent_clause_literal_except excluded model c = Some watched ->
  NoDup (map literal_var model) ->
  (forall x, In x c -> ~ excluded_var excluded (literal_var x) ->
     literal_is_undecided model x = false) ->
  model_suffix suffix model ->
  clause_has_two_undecided suffix c ->
  literal_is_undecided suffix watched = true.
Proof.
  intros excluded model c watched suffix Hrecent Hnodup Hallassigned
    [removed Hsuffix] Htwo.
  destruct (find_recent_clause_literal_except_some _ _ _ _ Hrecent) as
    [before [assigned [after [Hmodel [Hwatched [Hvar [Hexcluded Hbefore]]]]]]].
  destruct (literal_is_undecided suffix watched) eqn:Hwatchedu;
    [reflexivity|exfalso].
  assert (Hassignedsuffix : In (literal_var assigned)
      (map literal_var suffix)).
  { rewrite Hvar. apply InL_map_literal_var.
    now apply decided_literal_InL. }
  destruct (prefix_before_marker literal_var model before assigned after
      removed suffix Hnodup Hmodel Hsuffix Hassignedsuffix) as [middle Hbeforeeq].
  assert (Hundecided_excluded : forall x, In x c ->
      literal_is_undecided suffix x = true ->
      excluded_var excluded (literal_var x)).
  { intros x Hxc Hxu.
    destruct (excluded_var_dec excluded (literal_var x)) as [Hex|Hnotex];
      [exact Hex|].
    specialize (Hallassigned x Hxc Hnotex).
    pose proof (decided_literal_InL model x Hallassigned) as Hinmodel.
    assert (~ InL (literal_var x) suffix) as Hnotsuffix.
    { now apply literal_undecided_not_InL with (l := x). }
    assert (InL (literal_var x) removed) as Hinremoved.
    { rewrite Hsuffix in Hinmodel. destruct Hinmodel as [Hpos|Hneg].
      - apply in_app_or in Hpos as [Hpos|Hpos]; [now left|].
        exfalso. apply Hnotsuffix. now left.
      - apply in_app_or in Hneg as [Hneg|Hneg]; [now right|].
        exfalso. apply Hnotsuffix. now right. }
    assert (InL (literal_var x) before) as Hinbefore.
    { rewrite Hbeforeeq. destruct Hinremoved as [Hpos|Hneg].
      - left. apply in_or_app. now left.
      - right. apply in_or_app. now left. }
    destruct Hinbefore as [Hpos|Hneg].
    - specialize (Hbefore (Pos (literal_var x)) Hpos).
      destruct Hbefore as [Hex|Hnotinc]; [exact Hex|].
      exfalso. apply Hnotinc. exact (literal_InL x c Hxc).
    - specialize (Hbefore (Neg (literal_var x)) Hneg).
      destruct Hbefore as [Hex|Hnotinc]; [exact Hex|].
      exfalso. apply Hnotinc. exact (literal_InL x c Hxc). }
  destruct Htwo as [x [y [Hxc [Hyc [Hxy [Hxu Hyu]]]]]].
  destruct (Hundecided_excluded x Hxc Hxu) as [v [Hex Hx]].
  destruct (Hundecided_excluded y Hyc Hyu) as [w [Hex' Hy]].
  rewrite Hex in Hex'. injection Hex' as <-. apply Hxy. now rewrite <- Hx, <- Hy.
Qed.

Lemma undecided_model_suffix : forall model suffix l,
  model_suffix suffix model ->
  literal_is_undecided model l = true ->
  literal_is_undecided suffix l = true.
Proof.
  intros model suffix l [prefix ->] Hundecided.
  apply not_InL_literal_undecided. intros [Hpos|Hneg].
  - apply (literal_undecided_not_InL _ _ Hundecided). left.
    apply in_or_app. now right.
  - apply (literal_undecided_not_InL _ _ Hundecided). right.
    apply in_or_app. now right.
Qed.

Definition follows_two_undecided (ci : ClausePointer) (c : Clause)
    (s : State) : Prop :=
  forall m, model_suffix m (trail_model s.(state_trail)) ->
    Is_true (negb (existsb (literal_is_true m) c)) ->
    clause_has_two_undecided m c ->
    ClauseMap.card_of ci s.(state_watched) = 2 /\
    forall v, In ci (ClauseMap.find v s.(state_watched)) ->
      literal_is_undecided m (Pos v) = true.

Definition staged_watches_valid_with (detached : option Literal)
    (ci : ClausePointer) (c : Clause)
    (s : State) : Prop :=
  match detached with
  | None =>
      forall m, model_suffix m (trail_model s.(state_trail)) ->
        Is_true (negb (existsb (literal_is_true m) c)) ->
        clause_has_two_undecided m c ->
        forall v, In ci (ClauseMap.find v s.(state_watched)) ->
          literal_is_undecided m (Pos v) = true
  | Some l =>
      forall m, model_suffix m (trail_model s.(state_trail)) ->
        Is_true (negb (existsb (literal_is_true m) c)) ->
        clause_has_two_undecided m c ->
        (forall v, In ci (ClauseMap.find v s.(state_watched)) ->
           literal_is_undecided m (Pos v) = true) /\
        In l c /\
        or (m = trail_model s.(state_trail))
           (literal_is_undecided m l = true)
  end.

Definition staged_watches_valid := staged_watches_valid_with None.

Definition has_opposite_literals (c : Clause) : Prop :=
  exists v, In (Pos v) c /\ In (Neg v) c.

Definition clause_needs_literal (m : Model) (l : Literal) (c : Clause) : Prop :=
  In l c /\
  forall x, In x c -> x <> l -> literal_value m x = Some false.

Definition follows_needed_literal (ci : ClausePointer) (c : Clause)
    (s : State) : Prop :=
  forall m, model_suffix m (trail_model s.(state_trail)) ->
    forall l, literal_is_undecided m l = true ->
      clause_needs_literal m l c ->
      In ci (ClauseMap.find (literal_var l) s.(state_watched)).

Lemma clause_needs_literal_unique : forall m c l p,
  In l c ->
  literal_is_undecided m l = true ->
  clause_needs_literal m p c ->
  p = l.
Proof.
  intros m c l p Hlc Hlu [_ Hneeds].
  destruct (literal_eq_dec p l) as [Heq|Hneq]; [exact Heq|].
  specialize (Hneeds l Hlc (fun Heq => Hneq (eq_sym Heq))).
  unfold literal_is_undecided in Hlu. rewrite Hneeds in Hlu. discriminate.
Qed.

Lemma satisfied_not_needs_undecided : forall m c p,
  Is_true (existsb (literal_is_true m) c) ->
  literal_is_undecided m p = true ->
  clause_needs_literal m p c -> False.
Proof.
  intros m c p Hsatisfied Hpu [Hpc Hneeds].
  apply Is_true_eq_true in Hsatisfied.
  apply existsb_exists in Hsatisfied as [l [Hlc Hlt]].
  destruct (literal_eq_dec l p) as [->|Hneq].
  - unfold literal_is_undecided, literal_is_true in *.
    destruct (literal_value m p) as [[|]|]; discriminate.
  - specialize (Hneeds l Hlc Hneq). unfold literal_is_true in Hlt.
    rewrite Hneeds in Hlt. discriminate.
Qed.

Lemma newly_falsified_needs_opposite : forall m l c,
  literal_is_undecided m l = true ->
  Is_true (negb (existsb (literal_is_true (l :: m)) c)) ->
  filter (literal_is_undecided (l :: m)) c = [] ->
  filter (literal_is_undecided m) c <> [] ->
  clause_needs_literal m (opposite_literal l) c.
Proof.
  intros m l c Hlu Hfalse Hnewdec Holdnonempty.
  destruct (filter (literal_is_undecided m) c) as [|p ps]
    eqn:Holddec; [contradiction|].
  assert (Hpc : In p c /\ literal_is_undecided m p = true).
  { apply filter_In. rewrite Holddec. now left. }
  destruct Hpc as [Hpc Hpu].
  assert (Hvars : literal_var l = literal_var p).
  { destruct (Id.eq_dec (literal_var l) (literal_var p)) as [Heq|Hneq];
      [exact Heq|].
    assert (literal_is_undecided (l :: m) p = true) as Hpnew by
      (now apply undecided_cons_other_var).
    assert (In p (filter (literal_is_undecided (l :: m)) c)) by
      (apply filter_In; now split).
    now rewrite Hnewdec in H. }
  assert (Hpopp : p = opposite_literal l).
  { destruct l as [v|v], p as [w|w]; cbn in Hvars; subst w;
      try reflexivity.
    all: exfalso; apply (negb_prop_elim _ Hfalse);
      apply Is_true_eq_left, existsb_exists;
      eexists; split; [exact Hpc|apply literal_is_true_cons_self]. }
  subst p. split; [exact Hpc|].
  intros x Hxc Hneq.
  destruct (literal_value m x) as [[|]|] eqn:Hx; [|reflexivity|].
  - exfalso. apply (negb_prop_elim _ Hfalse).
    apply Is_true_eq_left, existsb_exists. exists x. split; [exact Hxc|].
    apply literal_is_true_cons_undecided; [exact Hlu|].
    unfold literal_is_true. now rewrite Hx.
  - assert (Hxu : literal_is_undecided m x = true).
    { unfold literal_is_undecided. now rewrite Hx. }
    assert (Hvarsx : literal_var l = literal_var x).
    { destruct (Id.eq_dec (literal_var l) (literal_var x)) as [Heq|Hdifferent];
        [exact Heq|].
      assert (literal_is_undecided (l :: m) x = true) as Hxnew by
        (now apply undecided_cons_other_var).
      assert (In x (filter (literal_is_undecided (l :: m)) c)) by
        (apply filter_In; now split).
      now rewrite Hnewdec in H. }
    destruct l as [v|v], x as [w|w]; cbn in Hvarsx; subst w.
    + exfalso. apply (negb_prop_elim _ Hfalse).
      apply Is_true_eq_left, existsb_exists. exists (Pos v).
      split; [exact Hxc|apply literal_is_true_cons_self].
    + contradiction.
    + contradiction.
    + exfalso. apply (negb_prop_elim _ Hfalse).
      apply Is_true_eq_left, existsb_exists. exists (Neg v).
      split; [exact Hxc|apply literal_is_true_cons_self].
Qed.

Lemma clause_needs_literal_cons : forall m l p c,
  literal_is_undecided m l = true ->
  clause_needs_literal m p c ->
  clause_needs_literal (l :: m) p c.
Proof.
  intros m l p c Hlu [Hpc Hneeds]. split; [exact Hpc|].
  intros x Hxc Hneq. eapply literal_false_cons_undecided; [exact Hlu|].
  now apply Hneeds.
Qed.

Definition falsified_clause (ci : ClausePointer) (s : State) : Prop :=
  exists c, find_clause ci s = Some c /\
    Is_true (negb (existsb (literal_is_true s.(state_trail)) c)) /\
      filter (literal_is_undecided s.(state_trail)) c = [].

Definition no_falsified_clauses (s : State) : Prop :=
  forall ci, ~ falsified_clause ci s.

Definition falsified_clauses_pending (s : State) : Prop :=
  forall ci, falsified_clause ci s ->
    exists l, In (l, ci) s.(state_pending).

Definition decided_clause (ci : ClausePointer) (s : State) : Prop :=
  falsified_clause ci s \/
  exists c, find_clause ci s = Some c /\
    Is_true (existsb (literal_is_true s.(state_trail)) c).

Definition clause_has_two_variables (c : Clause) : Prop :=
  exists l l', In l c /\ In l' c /\ literal_var l <> literal_var l'.

Definition staged_clause_arity (work : list ClausePointer) (s : State) : Prop :=
  forall ci c, find_clause ci s = Some c ->
    ~ In ci work ->
    ~ has_opposite_literals c ->
    (clause_has_two_variables c /\
       ClauseMap.card_of ci s.(state_watched) = 2) \/
    (~ clause_has_two_variables c /\
       ClauseMap.card_of ci s.(state_watched) = 0).

Definition card_of_watch (work : list ClausePointer) (ci : ClausePointer)
    (s : State) :=
  ClauseMap.card_of ci s.(state_watched).

Definition queued_clause (ci : ClausePointer) (s : State) : Prop :=
  falsified_clause ci s \/
  exists l, In (l, ci) s.(state_pending).

Definition trail_consistent (trail : Trail) : Prop :=
  ~ has_opposite_literals (trail_model trail).

Fixpoint trail_justified (clauses learned : ClauseStore.t) (trail : Trail) : Prop :=
  match trail with
  | [] => True
  | Decision l :: trail' =>
      literal_is_undecided (trail_model trail') l = true /\
      trail_justified clauses learned trail'
  | Propagation l cause :: trail' =>
      literal_is_undecided (trail_model trail') l = true /\
      exists c, find_clause_in clauses learned cause = Some c /\
        clause_needs_literal (trail_model trail') l c /\
        trail_justified clauses learned trail'
  end.

Definition trail_invariant (clauses learned : ClauseStore.t) (trail : Trail) : Prop :=
  trail_consistent trail /\ trail_justified clauses learned trail.

Lemma trail_justified_vars_nodup : forall clauses learned trail,
  trail_justified clauses learned trail ->
  NoDup (map literal_var (trail_model trail)).
Proof.
  intros clauses learned trail. induction trail as [|entry trail IH];
    intros Hjustified; [constructor|].
  destruct entry as [l|l cause]; cbn in Hjustified |- *.
  - destruct Hjustified as [Hlu Hjustified]. constructor.
    + intros Hin. apply (literal_undecided_not_InL _ _ Hlu).
      now apply InL_map_literal_var.
    + now apply IH.
  - destruct Hjustified as [Hlu [c [Hfind [Hneeds Hjustified]]]].
    constructor.
    + intros Hin. apply (literal_undecided_not_InL _ _ Hlu).
      now apply InL_map_literal_var.
    + now apply IH.
Qed.

Lemma trail_invariant_vars_nodup : forall clauses learned trail,
  trail_invariant clauses learned trail ->
  NoDup (map literal_var (trail_model trail)).
Proof.
  intros clauses learned trail [_ Hjustified].
  exact (trail_justified_vars_nodup clauses learned trail Hjustified).
Qed.

Lemma trail_consistent_decision : forall (trail : Trail) l,
  literal_is_undecided trail l = true ->
  trail_consistent trail ->
  trail_consistent (Decision l :: trail).
Proof.
  intros trail [w|w] Hundecided Hconsistent [v [Hpos Hneg]].
  - change (In (Pos v) (Pos w :: trail_model trail)) in Hpos.
    change (In (Neg v) (Pos w :: trail_model trail)) in Hneg.
    destruct Hpos as [Heq|Hpos].
    + injection Heq as <-. apply (literal_undecided_not_InL trail (Pos w)
        Hundecided). right. destruct Hneg as [Heq|Hneg];
        [discriminate|exact Hneg].
    + destruct Hneg as [Heq|Hneg]; [discriminate|].
      apply Hconsistent. exists v. now split.
  - change (In (Pos v) (Neg w :: trail_model trail)) in Hpos.
    change (In (Neg v) (Neg w :: trail_model trail)) in Hneg.
    destruct Hneg as [Heq|Hneg].
    + injection Heq as <-. apply (literal_undecided_not_InL trail (Neg w)
        Hundecided). left. destruct Hpos as [Heq|Hpos];
        [discriminate|exact Hpos].
    + destruct Hpos as [Heq|Hpos]; [discriminate|].
      apply Hconsistent. exists v. now split.
Qed.

Lemma consistent_model_literal_true : forall m l,
  ~ has_opposite_literals m ->
  In l m ->
  literal_value m l = Some true.
Proof.
  induction m as [|x m IH]; intros l Hconsistent Hin; [contradiction|].
  simpl in Hin. destruct Hin as [->|Hin].
  - unfold literal_value. simpl. rewrite Id.eqb_refl. destruct l; reflexivity.
  - unfold literal_value. simpl.
    destruct (Id.eqb (literal_var x) (literal_var l)) eqn:Hvar.
    + apply Id.eqb_eq in Hvar.
      destruct x as [v|v], l as [w|w]; cbn in Hvar; subst w.
      * reflexivity.
      * exfalso. apply Hconsistent. exists v. split; simpl;
          [now left|now right].
      * exfalso. apply Hconsistent. exists v. split; simpl;
          [now right|now left].
      * reflexivity.
    + fold (literal_value m l). apply IH; [|exact Hin].
      intros [v [Hpos Hneg]]. apply Hconsistent. exists v.
      split; simpl; now right.
Qed.

Definition staged_invariant (work : list ClausePointer) (s : State) : Prop :=
  (* Every clause which is not satisfied is covered.  [work] is the staged
     exception: its watches have just been removed and it is being scanned. *)
  (forall ci c, find_clause ci s = Some c ->
     Is_true (negb (existsb (literal_is_true s.(state_trail)) c)) ->
     has_opposite_literals c \/
     In ci work \/
       (watched_clause ci s /\
        filter (literal_is_undecided s.(state_trail)) c <> []) \/
       queued_clause ci s)
  /\ (* The semantic falsification predicate exposes its witnesses. *)
  (forall ci, falsified_clause ci s -> falsified_clause ci s)
  /\ (* Every watched reference exists and watches a literal of its clause. *)
  (forall v ci, In ci (ClauseMap.find v s.(state_watched)) ->
     exists c, find_clause ci s = Some c /\
       (~ In ci work ->
         follows_needed_literal ci c s /\
         (ClauseMap.card_of ci s.(state_watched) <> 1 ->
            follows_two_undecided ci c s)) /\
       InL v c /\
       ~ has_opposite_literals c /\
       (In ci (ClauseMap.find_pos v s.(state_watched)) -> In (Pos v) c) /\
       (In ci (ClauseMap.find_neg v s.(state_watched)) -> In (Neg v) c))
  /\ (forall v,
       NoDup (ClauseMap.find_pos v s.(state_watched)) /\
       NoDup (ClauseMap.find_neg v s.(state_watched)))
  /\ NoDup work
  /\ (forall ci, In ci work ->
     exists c, find_clause ci s = Some c /\
       ~ has_opposite_literals c /\ staged_watches_valid ci c s)
  /\ (* Pending clauses genuinely need their pending literal. *)
  (forall l ci, In (l, ci) s.(state_pending) ->
     exists c, find_clause ci s = Some c /\
       clause_needs_literal s.(state_trail) l c /\
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
        decided_clause ci s)))
  /\ trail_invariant s.(state_clauses) s.(state_learned) s.(state_trail).

Definition detached_work_valid (detached : Literal)
    (work : list ClausePointer) (s : State) : Prop :=
  forall ci, In ci work ->
    exists c, find_clause ci s = Some c /\ In detached c /\
      (forall m, model_suffix m (trail_model s.(state_trail)) ->
         Is_true (negb (existsb (literal_is_true m) c)) ->
         clause_has_two_undecided m c ->
         or (m = trail_model s.(state_trail))
            (literal_is_undecided m detached = true)) /\
      (forall m, model_suffix m (trail_model s.(state_trail)) ->
         forall p, literal_is_undecided m p = true ->
         clause_needs_literal m p c ->
         m = trail_model s.(state_trail) \/
         literal_var p = literal_var detached \/
         In ci (ClauseMap.find (literal_var p) s.(state_watched))).

Definition detached_clause_arity (work : list ClausePointer) (s : State) : Prop :=
  forall ci c, find_clause ci s = Some c ->
    ~ has_opposite_literals c ->
    (In ci work ->
      clause_has_two_variables c /\
      ClauseMap.card_of ci s.(state_watched) = 1) /\
    (~ In ci work ->
      (clause_has_two_variables c /\
         ClauseMap.card_of ci s.(state_watched) = 2) \/
      (~ clause_has_two_variables c /\
         ClauseMap.card_of ci s.(state_watched) = 0)).

Definition staged_invariant_with (detached : option Literal)
    (work : list ClausePointer) (s : State) : Prop :=
  staged_invariant work s /\
  match detached with
  | None => True
  | Some l => detached_work_valid l work s /\ detached_clause_arity work s
  end.

Definition learned_invariant (s : State) : Prop :=
  forall ci c, ClauseStore.find ci s.(state_learned) = Some c ->
    clause_implied_by_store s.(state_clauses) c.

(* Clauses without two distinct variables deliberately have no watches.  Once
   search has made a decision, all of them must already have been satisfied by
   propagation at level zero. *)
Definition root_unit_invariant (s : State) : Prop :=
  forall ci c, find_clause ci s = Some c ->
    ~ has_opposite_literals c ->
    ~ clause_has_two_variables c ->
    trail_has_decision s.(state_trail) = true ->
    Is_true (existsb (literal_is_true (pop_to_root s.(state_trail))) c).

Definition state_invariant (s : State) : Prop :=
  staged_invariant [] s /\
  learned_invariant s /\
  staged_clause_arity [] s.

Lemma state_invariant_learned : forall s,
  state_invariant s -> learned_invariant s.
Proof. intros s [_ [Hlearned _]]. exact Hlearned. Qed.

(* Invariant used by the persistent-watch implementation.  Watches need not
   be undecided: after a literal is set, a clause may keep watching it until a
   replacement is found.  The essential backtracking property is that as soon
   as a clause has two distinct undecided literals, both of its watches are on
   undecided literals. *)
Definition persistent_state_invariant (s : State) : Prop :=
  trail_invariant s.(state_clauses) s.(state_learned) s.(state_trail) /\
  learned_invariant s /\
  (forall v ci, In ci (ClauseMap.find v s.(state_watched)) ->
     exists c, find_clause ci s = Some c /\
       InL v c /\ ~ has_opposite_literals c /\
       (In ci (ClauseMap.find_pos v s.(state_watched)) -> In (Pos v) c) /\
       (In ci (ClauseMap.find_neg v s.(state_watched)) -> In (Neg v) c)) /\
  (forall v,
     NoDup (ClauseMap.find_pos v s.(state_watched)) /\
     NoDup (ClauseMap.find_neg v s.(state_watched))) /\
  (forall ci c, find_clause ci s = Some c ->
     ~ has_opposite_literals c ->
     clause_has_two_undecided s.(state_trail) c ->
     ClauseMap.card_of ci s.(state_watched) = 2 /\
     (forall v, In ci (ClauseMap.find_pos v s.(state_watched)) ->
        literal_is_undecided s.(state_trail) (Pos v) = true) /\
     (forall v, In ci (ClauseMap.find_neg v s.(state_watched)) ->
        literal_is_undecided s.(state_trail) (Neg v) = true)) /\
  (forall l ci, In (l, ci) s.(state_pending) ->
     exists c, find_clause ci s = Some c /\
       clause_needs_literal s.(state_trail) l c /\
       ~ has_opposite_literals c).

Lemma watched_find_nodup : forall work s v,
  staged_invariant work s -> NoDup (ClauseMap.find v s.(state_watched)).
Proof.
  intros work s v Hinv. destruct Hinv as
    [_ [_ [Hwatch [Hnodup _]]]].
  unfold ClauseMap.find. apply NoDup_app. repeat split.
  - apply Hnodup.
  - apply Hnodup.
  - intros ci Hpos Hneg.
    destruct (Hwatch v ci (in_or_app _ _ _ (or_introl Hpos))) as
      [c [_ [_ [_ [Hnoopp [Hpossem Hnegsem]]]]]].
    apply Hnoopp. exists v. split; [now apply Hpossem|now apply Hnegsem].
Qed.

Lemma unsatisfied_two_watched_card_two : forall s ci c,
  state_invariant s ->
  find_clause ci s = Some c ->
  Is_true (negb (existsb (literal_is_true s.(state_trail)) c)) ->
  clause_has_two_undecided s.(state_trail) c ->
  watched_clause ci s ->
  ClauseMap.card_of ci s.(state_watched) = 2.
Proof.
  intros s ci c [Hinv _] Hfind Hunsat Htwo [v Hwatched].
  destruct Hinv as
    [_ [Hfals [_ [_ [_ [_ [Hpending [_ [Hcard _]]]]]]]]].
  specialize (Hcard ci). unfold card_of_watch in Hcard.
  destruct Hcard as [Hzero|[Htwo'|[Hone [Hwork|[Hpendingci|Hdecided]]]]].
  - pose proof (ClauseMap.card_of_in _ _ _ Hwatched) as Hpositive. lia.
  - exact Htwo'.
  - contradiction.
  - destruct Hpendingci as [p Hp].
    destruct (Hpending p ci Hp) as [body [Hbody [Hneeds _]]].
    rewrite Hfind in Hbody. injection Hbody as <-.
    destruct Htwo as [x [y [Hxc [Hyc [Hxy [Hxu Hyu]]]]]].
    pose proof (clause_needs_literal_unique _ _ x p Hxc Hxu Hneeds) as Hpx.
    pose proof (clause_needs_literal_unique _ _ y p Hyc Hyu Hneeds) as Hpy.
    exfalso. apply Hxy.
    rewrite <- (f_equal literal_var Hpx), <- (f_equal literal_var Hpy).
    reflexivity.
  - destruct Hdecided as [Hinfals|[body [Hbody Hsat]]].
    + destruct (Hfals ci Hinfals) as [body [Hbody [_ Hnone]]].
      rewrite Hfind in Hbody. injection Hbody as <-.
      destruct Htwo as [x [y [Hxc [_ [_ [Hxu _]]]]]].
      assert (In x (filter (literal_is_undecided s.(state_trail)) c)).
      { apply filter_In. now split. }
      now rewrite Hnone in H.
    + rewrite Hfind in Hbody. injection Hbody as <-.
      apply Is_true_eq_true in Hunsat, Hsat. rewrite Hsat in Hunsat.
      discriminate.
Qed.

Lemma state_invariant_trail : forall s,
  state_invariant s ->
  trail_invariant s.(state_clauses) s.(state_learned) s.(state_trail).
Proof.
  intros s [Hstaged _]. unfold staged_invariant in Hstaged.
  tauto.
Qed.

Lemma pending_empty_small_clause_satisfied : forall s ci c,
  state_invariant s ->
  falsified_clauses_pending s ->
  s.(state_pending) = [] ->
  find_clause ci s = Some c ->
  ~ has_opposite_literals c ->
  ~ clause_has_two_variables c ->
  Is_true (existsb (literal_is_true s.(state_trail)) c).
Proof.
  intros s ci c [Hstaged [_ Harity]] Hfalsified Hempty Hfind Hnoopp Hnotwo.
  destruct (existsb (literal_is_true s.(state_trail)) c) eqn:Hsat;
    [exact I|].
  exfalso. unfold staged_invariant in Hstaged.
  destruct Hstaged as [Hcover _].
  specialize (Hcover ci c Hfind ltac:(rewrite Hsat; exact I)).
  destruct Hcover as [Hopp|Hcover].
  - contradiction.
  - destruct Hcover as [Hwork|Hcover]; [contradiction|].
    destruct Hcover as [[Hwatched _]|Hqueued].
    + destruct Hwatched as [v Hwatched].
      specialize (Harity ci c Hfind ltac:(simpl; tauto) Hnoopp).
      destruct Harity as [[Htwo Hcard]|[Hnotwo' Hcard]]; [contradiction|].
      pose proof (ClauseMap.card_of_in _ _ _ Hwatched) as Hpositive.
      lia.
    + destruct Hqueued as [Hfalse|[l Hqueued]].
      * destruct (Hfalsified ci Hfalse) as [l Hl].
        rewrite Hempty in Hl. contradiction.
      * rewrite Hempty in Hqueued. contradiction.
Qed.

Lemma staged_invariant_trail_ext : forall work t t' clauses learned cm pending,
  trail_model t = trail_model t' ->
  trail_invariant clauses learned t' ->
  staged_invariant work
    {| state_trail := t; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |} ->
  staged_invariant work
    {| state_trail := t'; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |}.
Proof.
  intros work t t' clauses learned cm pending Hmodel Htrail Hinv.
  unfold staged_invariant, watched_clause, queued_clause,
    follows_two_undecided, follows_needed_literal,
    staged_watches_valid, staged_watches_valid_with,
    clause_has_two_undecided, model_suffix, falsified_clause, decided_clause,
    card_of_watch, find_clause in Hinv |- *.
  cbn [state_trail state_clauses state_learned state_watched state_pending]
    in Hinv |- *.
  unfold falsified_clause in Hinv |- *.
  cbn [state_trail state_clauses state_learned] in Hinv |- *.
  rewrite <- Hmodel. tauto.
Qed.

Lemma empty_state_inv : forall m,
  trail_invariant ClauseStore.empty ClauseStore.empty m ->
  state_invariant
    {| state_trail := m; state_clauses := ClauseStore.empty;
       state_learned := ClauseStore.empty;
       state_watched := ClauseMap.empty;
       state_pending := [] |}.
Proof.
  intros m Htrail. unfold state_invariant. split.
  - split.
    + intros [ci|ci] c Hfind _; unfold find_clause, find_clause_in in Hfind;
        cbn [state_clauses state_learned] in Hfind;
        rewrite ClauseStore.find_empty in Hfind; discriminate.
    + split.
      * intros ci H. exact H.
      * split.
        -- intros v ci H. rewrite ClauseMap.find_empty in H. contradiction.
        -- split.
           ++ intros v. split;
                [rewrite ClauseMap.find_pos_empty|rewrite ClauseMap.find_neg_empty];
                constructor.
           ++ split; [constructor|]. split.
              ** intros ci H. contradiction.
              ** split.
                 --- intros l ci H. contradiction.
                 --- split.
                     +++ intros ci H. contradiction.
                     +++ split.
                         *** intros ci. unfold card_of_watch.
                             cbn [state_watched].
                             rewrite ClauseMap.card_of_empty. now left.
                         *** exact Htrail.
  - split.
    + intros ci c Hfind. rewrite ClauseStore.find_empty in Hfind. discriminate.
    + intros [ci|ci] c Hfind;
        unfold find_clause, find_clause_in in Hfind;
        cbn [state_clauses state_learned] in Hfind;
        rewrite ClauseStore.find_empty in Hfind; discriminate.
Qed.

Lemma empty_state_root_unit_inv : forall m,
  root_unit_invariant
    {| state_trail := m; state_clauses := ClauseStore.empty;
       state_learned := ClauseStore.empty;
       state_watched := ClauseMap.empty;
       state_pending := [] |}.
Proof.
  intros m [ci|ci] c Hfind; unfold find_clause, find_clause_in in Hfind;
    cbn [state_clauses state_learned] in Hfind;
    rewrite ClauseStore.find_empty in Hfind; discriminate.
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

Lemma negated_decisions_spec : forall trail l,
  In l (negated_decisions trail) <->
  exists decision,
    In (Decision decision) trail /\ l = opposite_literal decision.
Proof.
  intros trail. induction trail as [|entry trail IH]; intros l.
  - simpl. split; [contradiction|]. intros [decision [Hin _]]. contradiction.
  - destruct entry as [decision|propagated cause]; simpl.
    + rewrite IH. split.
      * intros [Heq|[original [Hin Heq]]].
        -- exists decision. split; [now left|exact (eq_sym Heq)].
        -- exists original. split; [now right|exact Heq].
      * intros [original [[Heq|Hin] Hl]].
        -- injection Heq as <-. now left.
        -- right. exists original. now split.
    + rewrite IH. split.
      * intros [decision [Hin Heq]]. exists decision. now split; [right|].
      * intros [decision [[Heq|Hin] Hl]].
        -- discriminate.
        -- exists decision. now split.
Qed.

Lemma negated_decisions_nil_iff : forall trail,
  negated_decisions trail = [] <->
  forall l, ~ In (Decision l) trail.
Proof.
  intros trail. split.
  - intros Hnil l Hin.
    assert (In (opposite_literal l) (negated_decisions trail)) as Hopposite.
    { apply negated_decisions_spec. exists l. now split. }
    rewrite Hnil in Hopposite. contradiction.
  - intros Hnone.
    destruct (negated_decisions trail) as [|l learned] eqn:Hdecisions;
      [reflexivity|].
    exfalso. assert (In l (negated_decisions trail)) as Hin.
    { rewrite Hdecisions. now left. }
    apply negated_decisions_spec in Hin as [decision [Hin _]].
    exact (Hnone decision Hin).
Qed.

Lemma analyze_conflict_none_iff : forall s conflict,
  analyze_conflict s conflict = None <->
  forall l, ~ In (Decision l) s.(state_trail).
Proof.
  intros s conflict. unfold analyze_conflict.
  destruct (negated_decisions s.(state_trail)) as [|l learned]
    eqn:Hdecisions.
  - split; [intros _|intros _; reflexivity].
    now apply negated_decisions_nil_iff.
  - destruct (analyze_conflict_trail s.(state_clauses) s.(state_learned)
      s.(state_trail) conflict); split; try discriminate;
      intros Hnone; exfalso;
      assert (In l (negated_decisions s.(state_trail))) as Hin.
    all: try (rewrite Hdecisions; now left).
    all: apply negated_decisions_spec in Hin as [decision [Hin _]];
      exact (Hnone decision Hin).
Qed.

Lemma analyze_conflict_some : forall s conflict learned,
  analyze_conflict s conflict = Some learned ->
  learned = analyze_conflict_trail s.(state_clauses) s.(state_learned)
      s.(state_trail) conflict \/
  analyze_conflict_trail s.(state_clauses) s.(state_learned)
      s.(state_trail) conflict = [] /\
    learned = negated_decisions s.(state_trail).
Proof.
  intros s conflict learned Hanalyze. unfold analyze_conflict in Hanalyze.
  destruct (negated_decisions s.(state_trail)) as [|l clause] eqn:Hdecisions;
    [discriminate|].
  destruct (analyze_conflict_trail s.(state_clauses) s.(state_learned)
    s.(state_trail) conflict) as [|x analyzed] eqn:Hresolved.
  - right. injection Hanalyze as <-. now split.
  - left. now injection Hanalyze as <-.
Qed.

Lemma decisions_hold : forall s l,
  state_invariant s ->
  In (Decision l) s.(state_trail) ->
  literal_value s.(state_trail) l = Some true.
Proof.
  intros s l Hinv Hin.
  pose proof (state_invariant_trail s Hinv) as [Hconsistent _].
  assert (In l (trail_model s.(state_trail))) as Hinliteral.
  { unfold trail_model. change (In (trail_literal (Decision l))
      (map trail_literal s.(state_trail))).
    now apply in_map. }
  now apply consistent_model_literal_true.
Qed.

Lemma opposite_of_true_is_false : forall m l,
  literal_value m l = Some true ->
  literal_is_true m (opposite_literal l) = false.
Proof.
  intros m [v|v] Htrue;
    unfold literal_is_true, literal_value, opposite_literal in *;
    simpl in *;
    destruct (find (fun l' => Id.eqb (literal_var l') v) m) as [[w|w]|];
    discriminate Htrue || reflexivity.
Qed.

Lemma negated_decisions_invalid : forall trail m,
  (forall l, In (Decision l) trail -> literal_value m l = Some true) ->
  existsb (literal_is_true m) (negated_decisions trail) = false.
Proof.
  intros trail. induction trail as [|entry trail IH]; intros m Hholds;
    [reflexivity|].
  destruct entry as [decision|propagated cause]; simpl.
  - rewrite opposite_of_true_is_false.
    + apply IH. intros l Hin. apply Hholds. now right.
    + apply Hholds. now left.
  - apply IH. intros l Hin. apply Hholds. now right.
Qed.

Lemma fresh_clause_id_not_in : forall s,
  ~ In (fresh_clause_id s) (ClauseStore.keys s.(state_clauses)).
Proof.
  intros s Hin. unfold fresh_clause_id in Hin.
  destruct (ClauseStore.maximum s.(state_clauses)) as [greatest|]
    eqn:Hmax.
  - apply (ClauseStore.maximum_upper s.(state_clauses) greatest
      (Id.next greatest) Hmax Hin).
    exact (Id.next_strict greatest).
  - rewrite (ClauseStore.maximum_none _ Hmax) in Hin. contradiction.
Qed.

Lemma fresh_learned_clause_id_not_in : forall s,
  ~ In (fresh_learned_clause_id s) (ClauseStore.keys s.(state_learned)).
Proof.
  intros s Hin. unfold fresh_learned_clause_id in Hin.
  destruct (ClauseStore.maximum s.(state_learned)) as [greatest|]
    eqn:Hmax.
  - apply (ClauseStore.maximum_upper s.(state_learned) greatest
      (Id.next greatest) Hmax Hin).
    exact (Id.next_strict greatest).
  - rewrite (ClauseStore.maximum_none _ Hmax) in Hin. contradiction.
Qed.

Lemma fresh_clause_id_fresh : forall s,
  ClauseStore.find (fresh_clause_id s) s.(state_clauses) = None.
Proof.
  intros s. destruct (ClauseStore.find (fresh_clause_id s)
    s.(state_clauses)) eqn:Hfind; [|reflexivity].
  exfalso. apply (fresh_clause_id_not_in s).
  apply (proj1 (ClauseStore.keys_complete _ _)). congruence.
Qed.

Lemma fresh_learned_clause_id_fresh : forall s,
  ClauseStore.find (fresh_learned_clause_id s) s.(state_learned) = None.
Proof.
  intros s. destruct (ClauseStore.find (fresh_learned_clause_id s)
    s.(state_learned)) eqn:Hfind; [|reflexivity].
  exfalso. apply (fresh_learned_clause_id_not_in s).
  apply (proj1 (ClauseStore.keys_complete _ _)). congruence.
Qed.

Lemma find_clause_fresh : forall s,
  find_clause (Source (fresh_clause_id s)) s = None.
Proof.
  intros s. unfold find_clause, find_clause_in. apply fresh_clause_id_fresh.
Qed.

Lemma find_added_clause : forall s c,
  ClauseStore.find (fresh_clause_id s)
    (ClauseStore.add (fresh_clause_id s) c s.(state_clauses)) = Some c.
Proof.
  intros s c. rewrite ClauseStore.find_add_eq.
  destruct (ClauseIdKey.eq_dec (fresh_clause_id s) (fresh_clause_id s));
    [reflexivity|contradiction].
Qed.

Lemma find_added_learned_clause : forall s c,
  ClauseStore.find (fresh_learned_clause_id s)
    (ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned)) = Some c.
Proof.
  intros s c. rewrite ClauseStore.find_add_eq.
  destruct (ClauseIdKey.eq_dec (fresh_learned_clause_id s)
    (fresh_learned_clause_id s)); [reflexivity|contradiction].
Qed.

Lemma find_old_clause_after_add : forall s c ci body,
  ClauseStore.find ci s.(state_clauses) = Some body ->
  ClauseStore.find ci
    (ClauseStore.add (fresh_clause_id s) c s.(state_clauses)) = Some body.
Proof.
  intros s c ci body Hfind. rewrite ClauseStore.find_add_eq.
  destruct (ClauseIdKey.eq_dec (fresh_clause_id s) ci) as [Heq|Hneq].
  - subst ci. rewrite fresh_clause_id_fresh in Hfind. discriminate.
  - exact Hfind.
Qed.

Lemma find_clause_after_original_add : forall s c ci body,
  find_clause ci s = Some body ->
  find_clause_in
    (ClauseStore.add (fresh_clause_id s) c s.(state_clauses))
    s.(state_learned) ci = Some body.
Proof.
  intros s c [ci|ci] body Hfind; cbn [find_clause find_clause_in] in *.
  - now apply find_old_clause_after_add.
  - exact Hfind.
Qed.

Lemma find_clause_after_learned_add : forall s c ci body,
  find_clause ci s = Some body ->
  find_clause_in s.(state_clauses)
    (ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned)) ci =
    Some body.
Proof.
  intros s c [ci|ci] body Hfind; cbn [find_clause find_clause_in] in *.
  - exact Hfind.
  - rewrite ClauseStore.find_add_eq.
    destruct (ClauseIdKey.eq_dec (fresh_learned_clause_id s) ci) as [Heq|Hneq].
    + subst ci. rewrite fresh_learned_clause_id_fresh in Hfind. discriminate.
    + exact Hfind.
Qed.

Lemma find_clause_after_original_add_state :
  forall s c trail watched pending ci body,
  find_clause ci s = Some body ->
  find_clause ci
    {| state_trail := trail;
       state_clauses := ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := watched;
       state_pending := pending |} = Some body.
Proof.
  intros s c trail watched pending ci body Hfind.
  change (find_clause_in
    (ClauseStore.add (fresh_clause_id s) c s.(state_clauses))
    s.(state_learned) ci = Some body).
  now apply find_clause_after_original_add.
Qed.

Lemma find_clause_after_learned_add_state :
  forall s c trail watched pending ci body,
  find_clause ci s = Some body ->
  find_clause ci
    {| state_trail := trail;
       state_clauses := s.(state_clauses);
       state_learned :=
         ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned);
       state_watched := watched;
       state_pending := pending |} = Some body.
Proof.
  intros s c trail watched pending ci body Hfind.
  change (find_clause_in s.(state_clauses)
    (ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned)) ci =
    Some body).
  now apply find_clause_after_learned_add.
Qed.

Lemma find_learned_add_cases : forall s c trail watched pending ci body,
  find_clause ci
    {| state_trail := trail;
       state_clauses := s.(state_clauses);
       state_learned :=
         ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned);
       state_watched := watched;
       state_pending := pending |} = Some body ->
  (ci = Learned (fresh_learned_clause_id s) /\ body = c) \/
  find_clause ci s = Some body.
Proof.
  intros s c trail watched pending [ci|ci] body Hfind.
  - right. exact Hfind.
  - cbn [find_clause find_clause_in state_clauses state_learned] in Hfind.
    rewrite ClauseStore.find_add_eq in Hfind.
    destruct (ClauseIdKey.eq_dec (fresh_learned_clause_id s) ci) as [Heq|Hneq].
    + subst ci. injection Hfind as <-. now left.
    + now right.
Qed.

Lemma trail_justified_after_learned_add : forall s c trail,
  trail_justified s.(state_clauses) s.(state_learned) trail ->
  trail_justified s.(state_clauses)
    (ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned)) trail.
Proof.
  intros s c trail. induction trail as [|entry trail IH]; intros Hjustified;
    [exact I|].
  destruct entry as [l|l cause]; cbn in Hjustified |- *.
  - destruct Hjustified as [Hundecided Hjustified].
    split; [exact Hundecided|now apply IH].
  - destruct Hjustified as [Hundecided [body [Hfind [Hneeds Hjustified]]]].
    split; [exact Hundecided|]. exists body.
    split; [now apply find_clause_after_learned_add|].
    split; [exact Hneeds|now apply IH].
Qed.

Lemma trail_invariant_after_learned_add : forall s c,
  trail_invariant s.(state_clauses) s.(state_learned) s.(state_trail) ->
  trail_invariant s.(state_clauses)
    (ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned))
    s.(state_trail).
Proof.
  intros s c [Hconsistent Hjustified]. split; [exact Hconsistent|].
  now apply trail_justified_after_learned_add.
Qed.

Lemma trail_justified_after_add : forall s c trail,
  trail_justified s.(state_clauses) s.(state_learned) trail ->
  trail_justified
    (ClauseStore.add (fresh_clause_id s) c s.(state_clauses))
    s.(state_learned) trail.
Proof.
  intros s c trail. induction trail as [|entry trail IH]; intros Hjustified;
    [exact I|].
  destruct entry as [l|l cause]; cbn in Hjustified |- *.
  - destruct Hjustified as [Hundecided Hjustified].
    split; [exact Hundecided|now apply IH].
  - destruct Hjustified as [Hundecided [body [Hfind [Hneeds Hjustified]]]].
    split; [exact Hundecided|]. exists body.
    split; [now apply find_clause_after_original_add|].
    split; [exact Hneeds|now apply IH].
Qed.

Lemma trail_invariant_after_add : forall s c,
  trail_invariant s.(state_clauses) s.(state_learned) s.(state_trail) ->
  trail_invariant
    (ClauseStore.add (fresh_clause_id s) c s.(state_clauses))
    s.(state_learned)
    s.(state_trail).
Proof.
  intros s c [Hconsistent Hjustified]. split; [exact Hconsistent|].
  now apply trail_justified_after_add.
Qed.

Lemma fresh_clause_not_watched : forall s v,
  state_invariant s ->
  ~ In (Source (fresh_clause_id s)) (ClauseMap.find v s.(state_watched)).
Proof.
  intros s v [Hinv _] Hin. destruct Hinv as [_ [_ [Hwatch _]]].
  destruct (Hwatch v (Source (fresh_clause_id s)) Hin) as [c [Hfind _]].
  rewrite find_clause_fresh in Hfind. discriminate.
Qed.

Lemma fresh_learned_clause_not_watched : forall s v,
  state_invariant s ->
  ~ In (Learned (fresh_learned_clause_id s))
      (ClauseMap.find v s.(state_watched)).
Proof.
  intros s v [Hinv _] Hin. destruct Hinv as [_ [_ [Hwatch _]]].
  destruct (Hwatch v (Learned (fresh_learned_clause_id s)) Hin)
    as [c [Hfind _]].
  cbn [find_clause find_clause_in] in Hfind.
  rewrite fresh_learned_clause_id_fresh in Hfind. discriminate.
Qed.

Lemma learned_invariant_after_add : forall s c trail watched pending,
  learned_invariant s ->
  learned_invariant
    {| state_trail := trail;
       state_clauses := ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := watched;
       state_pending := pending |}.
Proof.
  intros s c trail watched pending Hlearned ci learned Hfind m Hstore.
  apply (Hlearned ci learned Hfind m). intros d body Hbody.
  unfold satisfies_clause_store in Hstore. apply (Hstore d body).
  now apply find_old_clause_after_add.
Qed.

Lemma learned_invariant_after_learned_add :
  forall s c trail watched pending,
  learned_invariant s ->
  clause_implied_by_store s.(state_clauses) c ->
  learned_invariant
    {| state_trail := trail;
       state_clauses := s.(state_clauses);
       state_learned :=
         ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned);
       state_watched := watched;
       state_pending := pending |}.
Proof.
  intros s c trail watched pending Hlearned Himplied ci learned Hfind.
  cbn [state_learned] in Hfind. rewrite ClauseStore.find_add_eq in Hfind.
  destruct (ClauseIdKey.eq_dec (fresh_learned_clause_id s) ci) as [Heq|Hneq].
  - injection Hfind as <-. exact Himplied.
  - now apply Hlearned with (ci := ci).
Qed.

Lemma add_resolved_clause_inv : forall s c,
  state_invariant s ->
  has_opposite_literals c ->
  state_invariant
    {| state_trail := s.(state_trail);
       state_clauses := ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := s.(state_pending) |}.
Proof.
  intros s c [Hinv [Hlearned Harity]] Hresolved. destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork [Hcard Htrail]]]]]]]]].
  assert (Hdecided : forall d, decided_clause d s ->
    decided_clause d
      {| state_trail := s.(state_trail);
         state_clauses := ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
         state_learned := s.(state_learned);
         state_watched := s.(state_watched);
         state_pending := s.(state_pending) |}).
  { intros d [Hd|[body [Hfind Htrue]]].
    - left. destruct Hd as [body [Hfind [Hfalse Hnone]]].
      exists body. split;
        [now apply find_clause_after_original_add_state|].
      now split.
    - right. exists body. split;
        [now apply find_clause_after_original_add_state|exact Htrue]. }
  assert (Hqueued : forall d, queued_clause d s ->
    queued_clause d
      {| state_trail := s.(state_trail);
         state_clauses := ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
         state_learned := s.(state_learned);
         state_watched := s.(state_watched);
         state_pending := s.(state_pending) |}).
  { intros d [Hd|[l Hin]].
    - left. destruct Hd as [body [Hfind Hsem]]. exists body. split;
        [now apply find_clause_after_original_add_state|exact Hsem].
    - right. now exists l. }
  unfold state_invariant. split.
  repeat split; try assumption.
  - intros [d|d] body Hfind Hfalse.
    + cbn [find_clause find_clause_in state_clauses state_learned] in Hfind.
      rewrite ClauseStore.find_add_eq in Hfind.
      destruct (ClauseIdKey.eq_dec (fresh_clause_id s) d) as [Heq|Hneq].
      * injection Hfind as <-. now left.
      * destruct (Hcover (Source d) body Hfind Hfalse)
          as [Hopp|[Hwork'|[Hwatched|Hqueued']]].
        -- now left.
        -- now right; left.
        -- now right; right; left.
        -- now right; right; right; apply Hqueued.
    + destruct (Hcover (Learned d) body Hfind Hfalse)
        as [Hopp|[Hwork'|[Hwatched|Hqueued']]].
      * now left.
      * now right; left.
      * now right; right; left.
      * now right; right; right; apply Hqueued.
  - intros d Hd. exact Hd.
  - intros v d Hd. destruct (Hwatch v d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_clause_after_original_add_state|].
    destruct Hrest as [Hstable Hrest]. split; [|exact Hrest].
    intros Hnot. now apply Hstable.
  - apply Hnodup.
  - apply Hnodup.
  - intros d Hd. destruct (Hworkref d Hd) as [body [Hfind Hnoopp]].
    exists body. split;
      [now apply find_clause_after_original_add_state|exact Hnoopp].
  - intros l d Hd. destruct (Hpending l d Hd) as [body [Hfind Hrest]].
    exists body. split;
      [now apply find_clause_after_original_add_state|exact Hrest].
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
  - exact (proj1 Htrail).
  - exact (trail_justified_after_add s c s.(state_trail) (proj2 Htrail)).
  - split.
    + intros ci learned Hfind m Hstore.
      apply (Hlearned ci learned Hfind m). intros d body Hbody.
      unfold satisfies_clause_store in Hstore. apply (Hstore d body).
      now apply find_old_clause_after_add.
    + intros [d|d] body Hfind _ Hnoopp.
      * cbn [find_clause find_clause_in state_clauses state_learned] in Hfind.
        rewrite ClauseStore.find_add_eq in Hfind.
        destruct (ClauseIdKey.eq_dec (fresh_clause_id s) d) as [->|Hneq].
        -- injection Hfind as <-. contradiction.
        -- eapply Harity; [exact Hfind|simpl; tauto|exact Hnoopp].
      * eapply Harity; [exact Hfind|simpl; tauto|exact Hnoopp].
Qed.

Lemma add_learned_resolved_clause_inv : forall s c,
  state_invariant s ->
  clause_implied_by_store s.(state_clauses) c ->
  has_opposite_literals c ->
  state_invariant
    {| state_trail := s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := s.(state_pending) |}.
Proof.
  intros s c [Hinv [Hlearned Harity]] Himplied Hresolved. destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork [Hcard Htrail]]]]]]]]].
  assert (Hdecided : forall d, decided_clause d s ->
    decided_clause d
      {| state_trail := s.(state_trail);
         state_clauses := s.(state_clauses);
         state_learned := ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned);
         state_watched := s.(state_watched);
         state_pending := s.(state_pending) |}).
  { intros d [Hd|[body [Hfind Htrue]]].
    - left. destruct Hd as [body [Hfind [Hfalse Hnone]]].
      exists body. split;
        [now apply find_clause_after_learned_add_state|].
      now split.
    - right. exists body. split;
        [now apply find_clause_after_learned_add_state|exact Htrue]. }
  assert (Hqueued : forall d, queued_clause d s ->
    queued_clause d
      {| state_trail := s.(state_trail);
         state_clauses := s.(state_clauses);
         state_learned := ClauseStore.add (fresh_learned_clause_id s) c
           s.(state_learned);
         state_watched := s.(state_watched);
         state_pending := s.(state_pending) |}).
  { intros d [Hd|[l Hin]].
    - left. destruct Hd as [body [Hfind Hsem]]. exists body. split;
        [now apply find_clause_after_learned_add_state|exact Hsem].
    - right. now exists l. }
  unfold state_invariant. split.
  repeat split; try assumption.
  - intros d body Hfind Hfalse.
    pose proof (find_learned_add_cases s c s.(state_trail)
      s.(state_watched) s.(state_pending)
      d body Hfind) as [[-> ->]|Hold].
    + cbn. tauto.
    + destruct (Hcover d body Hold Hfalse)
        as [Hopp|[Hwork'|[Hwatched|Hqueued']]].
      * now left.
      * now right; left.
      * now right; right; left.
      * now right; right; right; apply Hqueued.
  - intros d Hd. exact Hd.
  - intros v d Hd. destruct (Hwatch v d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_clause_after_learned_add_state|].
    destruct Hrest as [Hstable Hrest]. split; [|exact Hrest].
    intros _. apply Hstable. cbn; tauto.
  - apply Hnodup.
  - apply Hnodup.
  - intros d Hd. destruct (Hworkref d Hd) as [body [Hfind Hnoopp]].
    exists body. split;
      [now apply find_clause_after_learned_add_state|exact Hnoopp].
  - intros l d Hd. destruct (Hpending l d Hd) as [body [Hfind Hrest]].
    exists body. split;
      [now apply find_clause_after_learned_add_state|exact Hrest].
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
  - exact (proj1 Htrail).
  - exact (trail_justified_after_learned_add s c s.(state_trail) (proj2 Htrail)).
  - split.
    + intros ci learned Hfind.
      cbn [state_learned] in Hfind. rewrite ClauseStore.find_add_eq in Hfind.
      destruct (ClauseIdKey.eq_dec (fresh_learned_clause_id s) ci) as [Heq|Hneq].
      * injection Hfind as <-. exact Himplied.
      * now apply Hlearned with (ci := ci).
    + intros d body Hfind _ Hnoopp.
      pose proof (find_learned_add_cases s c s.(state_trail)
        s.(state_watched) s.(state_pending)
        d body Hfind) as [[-> ->]|Hold].
      * contradiction.
      * eapply Harity; [exact Hold|simpl; tauto|exact Hnoopp].
Qed.

Lemma add_clause_conflict_spec : forall s c s' cause,
  add_clause s c = Conflict s' cause ->
  cause = c /\
  s'.(state_trail) = s.(state_trail) /\
  s'.(state_clauses) =
    ClauseStore.add (fresh_clause_id s) c s.(state_clauses) /\
  ClauseStore.find (fresh_clause_id s) s'.(state_clauses) = Some c /\
  Is_true (negb (existsb (literal_is_true s'.(state_trail)) c)) /\
  filter (literal_is_undecided s'.(state_trail)) c = [].
Proof.
  intros [m clauses learned cm pending] c s' cause Hadd.
  unfold add_clause, add_clause_to, index_clause in Hadd.
  cbn [state_trail state_clauses state_watched state_pending] in Hadd |- *.
  rewrite scan_clause_once_spec in Hadd.
  destruct (clause_has_opposite_literals c) eqn:Hopposite;
    cbn in Hadd; [discriminate|].
  destruct (existsb (literal_is_true m) c) eqn:Hsatisfied;
    cbn in Hadd; [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|l undecided]
    eqn:Hundecided.
  - injection Hadd as <- <-. repeat split; try assumption.
    + apply find_added_clause.
    + cbn [state_trail]. apply Is_true_eq_left. now rewrite Hsatisfied.
  - destruct (find_different_var (literal_var l) undecided);
      discriminate.
Qed.

Lemma find_different_var_spec : forall v ls l,
  find_different_var v ls = Some l ->
  In l ls /\ v <> literal_var l.
Proof.
  intros v ls. induction ls as [|x xs IH]; intros l Hfind; simpl in Hfind.
  - discriminate.
  - destruct (Id.eqb v (literal_var x)) eqn:Heq.
    + destruct (IH l Hfind) as [Hin Hneq]. now split; [right|].
    + injection Hfind as ->. split; [now left|].
      now apply Id.eqb_neq.
Qed.

Lemma scan_clause_inl_spec : forall m falsified ci c cm l,
  forall cm', scan_clause m falsified ci c cm = propagate_literal l cm' ->
  existsb (literal_is_true m) c = false /\
  In l c /\ literal_is_undecided m l = true /\
  cm' = (if in_dec clause_pointer_eq_dec ci (ClauseMap.find (literal_var l) cm)
    then restore_detached_watch falsified ci c cm
    else ClauseMap.add l ci cm).
Proof.
  intros m falsified ci c cm l cm' Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c) eqn:Hfalse; [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|x xs]
    eqn:Hfilter; [discriminate|].
  destruct (find_different_var (literal_var x) xs).
  - destruct (in_dec clause_pointer_eq_dec ci (ClauseMap.find (literal_var x) cm));
      discriminate.
  - destruct (in_dec clause_pointer_eq_dec ci (ClauseMap.find (literal_var x) cm))
      as [Hinwatch|Hnotwatch].
    + injection Hscan as <- <-.
      assert (In x (filter (literal_is_undecided m) c)) as Hin
        by (rewrite Hfilter; now left).
      apply filter_In in Hin as [Hxc Hxu]. repeat split; try assumption.
      destruct (in_dec clause_pointer_eq_dec ci
        (ClauseMap.find (literal_var x) cm)); [reflexivity|contradiction].
    + injection Hscan as <- <-.
      assert (In x (filter (literal_is_undecided m) c)) as Hin
        by (rewrite Hfilter; now left).
      apply filter_In in Hin as [Hxc Hxu]. repeat split; try assumption.
      destruct (in_dec clause_pointer_eq_dec ci
        (ClauseMap.find (literal_var x) cm)); [contradiction|reflexivity].
Qed.

Lemma scan_clause_watched_spec : forall m falsified ci c cm cm',
  scan_clause m falsified ci c cm = clause_watched cm' ->
  exists l l', existsb (literal_is_true m) c = false /\
    In l c /\ In l' c /\
    literal_is_undecided m l = true /\
    literal_is_undecided m l' = true /\
    literal_var l <> literal_var l' /\
    cm' = (if in_dec clause_pointer_eq_dec ci (ClauseMap.find (literal_var l) cm)
      then ClauseMap.add l' ci cm
      else ClauseMap.add l ci cm).
Proof.
  intros m falsified ci c cm cm' Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c); [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|l undecided]
    eqn:Hfilter; [discriminate|].
  destruct (find_different_var (literal_var l) undecided) as [l'|]
    eqn:Hdifferent.
  2:{ destruct (in_dec clause_pointer_eq_dec ci
        (ClauseMap.find (literal_var l) cm)); discriminate. }
  apply find_different_var_spec in Hdifferent as [Hl'in Hneq].
  assert (In l (filter (literal_is_undecided m) c)) as Hlin
    by (rewrite Hfilter; now left).
  assert (In l' (filter (literal_is_undecided m) c)) as Hl'in'.
  { rewrite Hfilter. now right. }
  apply filter_In in Hlin as [Hlc Hlu].
  apply filter_In in Hl'in' as [Hl'c Hl'u].
  exists l, l'. repeat split; try assumption.
  destruct (in_dec clause_pointer_eq_dec ci (ClauseMap.find (literal_var l) cm));
    now injection Hscan as <-.
Qed.

Lemma scan_clause_decided_spec : forall m falsified ci c cm cm',
  scan_clause m falsified ci c cm = clause_decided cm' ->
  existsb (literal_is_true m) c = true /\
  cm' = restore_detached_watch falsified ci c cm.
Proof.
  intros m falsified ci c cm cm' Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c) eqn:Htrue.
  - injection Hscan as <-. now split.
  - destruct (filter (literal_is_undecided m) c) as [|l undecided]
      eqn:Hfilter.
    + discriminate.
    + destruct (find_different_var (literal_var l) undecided) as [l'|].
      * destruct (in_dec clause_pointer_eq_dec ci
          (ClauseMap.find (literal_var l) cm)); discriminate.
      * destruct (in_dec clause_pointer_eq_dec ci
          (ClauseMap.find (literal_var l) cm)); discriminate.
Qed.

Lemma scan_clause_conflict_spec : forall m falsified ci c cm cm',
  scan_clause m falsified ci c cm = clause_conflict cm' ->
  existsb (literal_is_true m) c = false /\
  filter (literal_is_undecided m) c = [] /\
  cm' = restore_detached_watch falsified ci c cm.
Proof.
  intros m falsified ci c cm cm' Hscan. unfold scan_clause in Hscan.
  rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c) eqn:Htrue; [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|l undecided]
    eqn:Hfilter.
  - injection Hscan as <-. now repeat split.
  - destruct (find_different_var (literal_var l) undecided) as [l'|];
      destruct (in_dec clause_pointer_eq_dec ci
        (ClauseMap.find (literal_var l) cm)); discriminate.
Qed.

Lemma find_different_var_none : forall v ls,
  find_different_var v ls = None ->
  forall l, In l ls -> literal_var l = v.
Proof.
  intros v ls. induction ls as [|x xs IH]; intros Hnone l Hin;
    [contradiction|].
  simpl in Hnone. destruct (Id.eqb v (literal_var x)) eqn:Heq.
  - destruct Hin as [->|Hin].
    + now apply Id.eqb_eq in Heq.
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
  destruct (find (fun l' => Id.eqb (literal_var l') (literal_var x)) m)
    as [[v|v]|] eqn:Hvalue; destruct x; try discriminate; reflexivity.
Qed.

Lemma scan_clause_propagate_needs :
  forall m falsified ci c cm l cm',
  ~ has_opposite_literals c ->
  scan_clause m falsified ci c cm = propagate_literal l cm' ->
  clause_needs_literal m l c.
Proof.
  intros m falsified ci c cm l cm' Hnoopp Hscan.
  unfold scan_clause in Hscan. rewrite scan_clause_once_spec in Hscan.
  destruct (existsb (literal_is_true m) c) eqn:Hfalse; [discriminate|].
  destruct (filter (literal_is_undecided m) c) as [|x undecided]
    eqn:Hfilter; [discriminate|].
  destruct (find_different_var (literal_var x) undecided) eqn:Hdifferent.
  - destruct (in_dec clause_pointer_eq_dec ci
      (ClauseMap.find (literal_var x) cm)); discriminate.
  - destruct (in_dec clause_pointer_eq_dec ci
      (ClauseMap.find (literal_var x) cm)); injection Hscan as <- <-;
      eapply unit_filter_needs; eauto.
Qed.

Lemma fresh_clause_card_zero : forall s,
  state_invariant s ->
  ClauseMap.card_of (Source (fresh_clause_id s)) s.(state_watched) = 0.
Proof.
  intros s Hinv.
  destruct (ClauseMap.card_of (Source (fresh_clause_id s)) s.(state_watched))
    as [|n] eqn:Hcard; [reflexivity|].
  exfalso.
  assert (ClauseMap.card_of (Source (fresh_clause_id s)) s.(state_watched) > 0)
    as Hpositive by (rewrite Hcard; lia).
  apply ClauseMap.card_of_pos in Hpositive as [v Hin].
  exact (fresh_clause_not_watched s v Hinv Hin).
Qed.

Lemma fresh_learned_clause_card_zero : forall s,
  state_invariant s ->
  ClauseMap.card_of (Learned (fresh_learned_clause_id s))
    s.(state_watched) = 0.
Proof.
  intros s Hinv.
  destruct (ClauseMap.card_of (Learned (fresh_learned_clause_id s))
    s.(state_watched)) as [|n] eqn:Hcard; [reflexivity|].
  exfalso.
  assert (ClauseMap.card_of (Learned (fresh_learned_clause_id s))
      s.(state_watched) > 0) as Hpositive by (rewrite Hcard; lia).
  apply ClauseMap.card_of_pos in Hpositive as [v Hin].
  exact (fresh_learned_clause_not_watched s v Hinv Hin).
Qed.

Lemma decided_clause_after_store_add : forall s c d cm pending,
  decided_clause d s ->
  decided_clause d
    {| state_trail := s.(state_trail);
       state_clauses :=
         ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := cm;
       state_pending := pending |}.
Proof.
  intros s c d cm pending [Hfals|[body [Hfind Htrue]]].
  - left. destruct Hfals as [body [Hfind Hsem]]. exists body. split;
      [now apply find_clause_after_original_add_state|exact Hsem].
  - right. exists body. split;
      [now apply find_clause_after_original_add_state|exact Htrue].
Qed.

Lemma decided_clause_after_learned_store_add : forall s c d cm pending,
  decided_clause d s ->
  decided_clause d
    {| state_trail := s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned :=
         ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned);
       state_watched := cm;
       state_pending := pending |}.
Proof.
  intros s c d cm pending [Hfals|[body [Hfind Htrue]]].
  - left. destruct Hfals as [body [Hfind Hsem]]. exists body. split;
      [now apply find_clause_after_learned_add_state|exact Hsem].
  - right. exists body. split;
      [now apply find_clause_after_learned_add_state|exact Htrue].
Qed.

Lemma add_unit_staged_inv : forall s c l,
  state_invariant s ->
  ~ has_opposite_literals c ->
  clause_needs_literal s.(state_trail) l c ->
  staged_invariant [Source (fresh_clause_id s)]
    {| state_trail := s.(state_trail);
       state_clauses :=
         ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := (l, Source (fresh_clause_id s)) :: s.(state_pending) |}.
Proof.
  intros s c l Hinv Hnoopp Hneeds.
  pose proof Hinv as Hstateinv.
  destruct Hinv as [Hinv _].
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [_ [_
      [Hpending [_ [Hcard Htrail]]]]]]]]].
  repeat split.
  - intros [d|d] body Hfind Hfalse.
    + cbn [find_clause find_clause_in state_clauses state_learned] in Hfind.
      rewrite ClauseStore.find_add_eq in Hfind.
      destruct (ClauseIdKey.eq_dec (fresh_clause_id s) d) as [->|Hneq].
      * injection Hfind as <-. right. left. now left.
      * specialize (Hcover (Source d) body Hfind Hfalse).
        destruct Hcover as [Hopp|[Hwork|[Hwatched|Hinfals]]].
        -- now left.
        -- contradiction.
        -- now right; right; left.
        -- right; right; right.
           unfold queued_clause in Hinfals |- *. cbn.
           destruct Hinfals as [Hin|[p Hin]].
           ++ left. destruct Hin as [old [Hfindold Hsem]]. exists old. split;
                [now apply find_clause_after_original_add_state|exact Hsem].
           ++ right. exists p. now right.
    + specialize (Hcover (Learned d) body Hfind Hfalse).
      destruct Hcover as [Hopp|[Hwork|[Hwatched|Hinfals]]].
      * cbn. tauto.
      * contradiction.
      * now right; right; left.
      * right; right; right.
        unfold queued_clause in Hinfals |- *. cbn.
        destruct Hinfals as [Hin|[p Hin]].
        -- left. destruct Hin as [old [Hfindold Hsem]]. exists old. split;
             [now apply find_clause_after_original_add_state|exact Hsem].
        -- right. exists p. now right.
  - intros d Hd. exact Hd.
  - intros v d Hd. destruct (Hwatch v d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_clause_after_original_add_state|].
    destruct Hrest as [Hstable Hrest]. split; [|exact Hrest].
    intros _. apply Hstable. cbn; tauto.
  - apply Hnodup.
  - apply Hnodup.
  - constructor; [simpl; tauto|constructor].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    exists c. split; [apply find_added_clause|]. split; [exact Hnoopp|].
    unfold staged_watches_valid, staged_watches_valid_with.
    cbn [state_trail state_watched].
    intros model Hsuffix Hunsat Htwo v Hin.
    pose proof (ClauseMap.card_of_in _ _ _ Hin) as Hpositive.
    rewrite (fresh_clause_card_zero s Hstateinv) in Hpositive. lia.
  - intros p d Hd. simpl in Hd. destruct Hd as [Heq|Hd].
    + inversion Heq; subst p d. exists c. split.
      * apply find_added_clause.
      * split; assumption.
    + destruct (Hpending p d Hd) as [body [Hfind Hrest]].
      exists body. split;
        [now apply find_clause_after_original_add_state|exact Hrest].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    right. split.
    + unfold card_of_watch. cbn [state_watched].
      now apply fresh_clause_card_zero.
    + left. exists l. now left.
  - intros d. destruct (clause_pointer_eq_dec (Source (fresh_clause_id s)) d)
      as [Heq|Hneq].
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
             (pending := (l, Source (fresh_clause_id s)) :: s.(state_pending)).
  - exact (proj1 Htrail).
  - exact (trail_justified_after_add s c s.(state_trail) (proj2 Htrail)).
Qed.

Lemma add_learned_unit_staged_inv : forall s c l,
  state_invariant s ->
  ~ has_opposite_literals c ->
  clause_needs_literal s.(state_trail) l c ->
  staged_invariant [Learned (fresh_learned_clause_id s)]
    {| state_trail := s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned :=
         ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := (l, Learned (fresh_learned_clause_id s)) :: s.(state_pending) |}.
Proof.
  intros s c l Hinv Hnoopp Hneeds.
  pose proof Hinv as Hstateinv.
  destruct Hinv as [Hinv _].
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [_ [_
      [Hpending [_ [Hcard Htrail]]]]]]]]].
  repeat split.
  - intros d body Hfind Hfalse.
    pose proof (find_learned_add_cases s c s.(state_trail)
      s.(state_watched)
      ((l, Learned (fresh_learned_clause_id s)) :: s.(state_pending))
      d body Hfind) as [[-> ->]|Hold].
    + right. left. now left.
    + specialize (Hcover d body Hold Hfalse).
      destruct Hcover as [Hopp|[Hwork|[Hwatched|Hinfals]]].
      * now left.
      * contradiction.
      * now right; right; left.
      * right; right; right. unfold queued_clause in Hinfals |- *. cbn.
        destruct Hinfals as [Hin|[p Hin]].
        -- left. destruct Hin as [old [Hfindold Hsem]]. exists old. split;
             [now apply find_clause_after_learned_add_state|exact Hsem].
        -- right. exists p. now right.
  - intros d Hd. exact Hd.
  - intros v d Hd. destruct (Hwatch v d Hd) as [body [Hfind Hrest]].
    exists body. split; [now apply find_clause_after_learned_add_state|].
    destruct Hrest as [Hstable Hrest]. split; [|exact Hrest].
    intros _. apply Hstable. cbn; tauto.
  - apply Hnodup.
  - apply Hnodup.
  - constructor; [simpl; tauto|constructor].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    exists c. split; [apply find_added_learned_clause|]. split; [exact Hnoopp|].
    unfold staged_watches_valid, staged_watches_valid_with.
    cbn [state_trail state_watched].
    intros model Hsuffix Hunsat Htwo v Hin.
    pose proof (ClauseMap.card_of_in _ _ _ Hin) as Hpositive.
    rewrite (fresh_learned_clause_card_zero s Hstateinv) in Hpositive. lia.
  - intros p d Hd. simpl in Hd. destruct Hd as [Heq|Hd].
    + inversion Heq; subst p d. exists c. split.
      * apply find_added_learned_clause.
      * split; assumption.
    + destruct (Hpending p d Hd) as [body [Hfind Hrest]].
      exists body. split;
        [now apply find_clause_after_learned_add_state|exact Hrest].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    right. split.
    + unfold card_of_watch. cbn [state_watched].
      now apply fresh_learned_clause_card_zero.
    + left. exists l. now left.
  - intros d. destruct (clause_pointer_eq_dec (Learned (fresh_learned_clause_id s)) d)
      as [Heq|Hneq].
    + subst d. left. unfold card_of_watch. cbn [state_watched].
      now apply fresh_learned_clause_card_zero.
    + specialize (Hcard d).
      destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
      * now left.
      * now right; left.
      * right. right. split; [exact Hone|].
        destruct Hwhy as [Hwork|[Hpend|Hdecided]].
        -- contradiction.
        -- right. left. destruct Hpend as [p Hp]. exists p. now right.
        -- right. right.
           now apply decided_clause_after_learned_store_add with
             (cm := s.(state_watched))
             (pending := (l, Learned (fresh_learned_clause_id s)) :: s.(state_pending)).
  - exact (proj1 Htrail).
  - exact (trail_justified_after_learned_add s c s.(state_trail) (proj2 Htrail)).
Qed.

Lemma add_first_watch_staged_inv : forall s c l,
  state_invariant s ->
  ~ has_opposite_literals c ->
  In l c ->
  literal_is_undecided s.(state_trail) l = true ->
  staged_invariant [Source (fresh_clause_id s)]
    {| state_trail := s.(state_trail);
       state_clauses :=
         ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched :=
         ClauseMap.add l (Source (fresh_clause_id s))
           s.(state_watched);
       state_pending := s.(state_pending) |}.
Proof.
  intros s c l Hinv Hnoopp Hlc Hlu.
  pose proof Hinv as Hstateinv.
  destruct Hinv as [Hinv _].
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [_ [_
      [Hpending [_ [Hcard Htrail]]]]]]]]].
  repeat split.
  - intros [d|d] body Hfind Hfalse.
    + cbn [find_clause find_clause_in state_clauses state_learned] in Hfind.
      rewrite ClauseStore.find_add_eq in Hfind.
      destruct (ClauseIdKey.eq_dec (fresh_clause_id s) d) as [Heq|Hneq].
      * subst d. injection Hfind as <-. right. left. now left.
      * specialize (Hcover (Source d) body Hfind Hfalse).
        destruct Hcover as [Hopp|[Hwork|[Hwatched|Hinfals]]].
        -- now left.
        -- contradiction.
        -- right. right. left. destruct Hwatched as [[v Hin] Hnonempty]. split.
           ++ exists v. apply ClauseMap.find_add. now right.
           ++ exact Hnonempty.
        -- right; right; right. destruct Hinfals as [Hfalse'|[p Hp]].
           ++ left. destruct Hfalse' as [old [Hfindold Hsem]]. exists old.
              split; [now apply find_clause_after_original_add_state|exact Hsem].
           ++ right. now exists p.
    + specialize (Hcover (Learned d) body Hfind Hfalse).
      destruct Hcover as [Hopp|[Hwork|[Hwatched|Hinfals]]].
      * now left.
      * contradiction.
      * right. right. left. destruct Hwatched as [[v Hin] Hnonempty]. split.
        -- exists v. apply ClauseMap.find_add. now right.
        -- exact Hnonempty.
      * right; right; right. destruct Hinfals as [Hfalse'|[p Hp]].
        -- left. destruct Hfalse' as [old [Hfindold Hsem]]. exists old.
           split; [now apply find_clause_after_original_add_state|exact Hsem].
        -- right. now exists p.
  - intros d Hd. exact Hd.
  - intros v d Hd. apply ClauseMap.find_add in Hd as [[Heqv Heqd]|Hd].
    + subst v d. exists c. split; [apply find_added_clause|].
      split.
      * intros Hnot. exfalso. apply Hnot. now left.
      * repeat split; try assumption.
        -- now apply literal_InL.
        -- destruct l as [w|w]; cbn; intros Hbucket.
           ++ exact Hlc.
           ++ exfalso. eapply fresh_clause_not_watched with (v := w);
             [exact Hstateinv|].
           unfold ClauseMap.find. apply in_or_app. left.
           change (In (Source (fresh_clause_id s))
             (ClauseMap.find_pos w
               (ClauseMap.add (Neg w) (Source (fresh_clause_id s))
                 s.(state_watched)))) in Hbucket.
           now rewrite ClauseMap.find_pos_add_neg in Hbucket.
        -- destruct l as [w|w]; cbn; intros Hbucket.
           ++ exfalso. eapply fresh_clause_not_watched with (v := w);
             [exact Hstateinv|].
           unfold ClauseMap.find. apply in_or_app. right.
           change (In (Source (fresh_clause_id s))
             (ClauseMap.find_neg w
               (ClauseMap.add (Pos w) (Source (fresh_clause_id s))
                 s.(state_watched)))) in Hbucket.
           now rewrite ClauseMap.find_neg_add_pos in Hbucket.
           ++ exact Hlc.
    + destruct (Hwatch v d Hd) as
        [body [Hfind [Hstable [Hinc [Hnoopp' Hpolarity]]]]].
      exists body. split; [now apply find_clause_after_original_add_state|].
      split.
      * intros _. destruct (Hstable ltac:(cbn; tauto)) as [Hfollow Htwo].
        split.
        -- intros p Hsuffix x Hxu Hneeds. apply ClauseMap.find_add. right.
           eapply Hfollow; eauto.
        -- intros Hcardout.
        assert (d <> Source (fresh_clause_id s)) as Hneq.
        { intros ->. eapply fresh_clause_not_watched with (v := v);
            [exact Hstateinv|exact Hd]. }
        assert (ClauseMap.card_of d s.(state_watched) <> 1) as Hcardold.
        { rewrite <- (ClauseMap.card_of_add_neq s.(state_watched)
            (Source (fresh_clause_id s)) d l (not_eq_sym Hneq)).
          exact Hcardout. }
        specialize (Htwo Hcardold).
        unfold follows_two_undecided in *.
           intros model Hsuffix Hunsat Htwoundecided.
           destruct (Htwo model Hsuffix Hunsat Htwoundecided)
             as [Hwatchcard Hall].
           split.
           ++ cbn [state_watched].
              rewrite ClauseMap.card_of_add_neq by exact (not_eq_sym Hneq).
              exact Hwatchcard.
           ++ intros w Hw. apply Hall.
              apply ClauseMap.find_add in Hw.
              destruct Hw as [[_ Heq]|Hw]; [congruence|exact Hw].
      * repeat split; try assumption.
        -- destruct Hpolarity as [Hpossem _]. intros Hbucket. apply Hpossem.
        eapply ClauseMap.find_pos_add_old; [|exact Hbucket]. intros Heq.
        eapply fresh_clause_not_watched with (v := v); [exact Hstateinv|].
        now rewrite <- Heq.
        -- destruct Hpolarity as [_ Hnegsem]. intros Hbucket. apply Hnegsem.
        eapply ClauseMap.find_neg_add_old; [|exact Hbucket]. intros Heq.
        eapply fresh_clause_not_watched with (v := v); [exact Hstateinv|].
        now rewrite <- Heq.
  - apply ClauseMap.find_pos_add_nodup; [apply Hnodup|].
    now apply fresh_clause_not_watched.
  - apply ClauseMap.find_neg_add_nodup; [apply Hnodup|].
    now apply fresh_clause_not_watched.
  - constructor; [simpl; tauto|constructor].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    exists c. split; [apply find_added_clause|]. split; [exact Hnoopp|].
    unfold staged_watches_valid, staged_watches_valid_with.
    cbn [state_trail state_watched].
    intros model Hsuffix Hunsat Htwo v Hin. apply ClauseMap.find_add in Hin.
    destruct Hin as [[Hv _]|Hold].
    + subst v.
      pose proof (undecided_model_suffix _ _ l Hsuffix Hlu) as Hlumodel.
      destruct l; cbn; [exact Hlumodel|].
      rewrite literal_is_undecided_pos_neg. exact Hlumodel.
    + exfalso. eapply fresh_clause_not_watched; [exact Hstateinv|exact Hold].
  - intros p d Hd. destruct (Hpending p d Hd) as [body [Hfind Hrest]].
    exists body. split;
      [now apply find_clause_after_original_add_state|exact Hrest].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    left. unfold card_of_watch. cbn [state_watched].
    rewrite ClauseMap.card_of_add, (fresh_clause_card_zero s Hstateinv).
    reflexivity.
  - intros d. destruct (clause_pointer_eq_dec (Source (fresh_clause_id s)) d)
      as [Heq|Hneq].
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
             (cm := ClauseMap.add l (Source (fresh_clause_id s))
               s.(state_watched))
             (pending := s.(state_pending)).
  - exact (proj1 Htrail).
  - exact (trail_justified_after_add s c s.(state_trail) (proj2 Htrail)).
Qed.

Lemma add_learned_first_watch_staged_inv : forall s c l,
  state_invariant s ->
  ~ has_opposite_literals c ->
  In l c ->
  literal_is_undecided s.(state_trail) l = true ->
  staged_invariant [Learned (fresh_learned_clause_id s)]
    {| state_trail := s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned :=
         ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned);
       state_watched :=
         ClauseMap.add l (Learned (fresh_learned_clause_id s))
           s.(state_watched);
       state_pending := s.(state_pending) |}.
Proof.
  intros s c l Hinv Hnoopp Hlc Hlu.
  pose proof Hinv as Hstateinv.
  destruct Hinv as [Hinv _].
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [_ [_
      [Hpending [_ [Hcard Htrail]]]]]]]]].
  repeat split.
  - intros d body Hfind Hfalse.
    pose proof (find_learned_add_cases s c s.(state_trail)
      (ClauseMap.add l (Learned (fresh_learned_clause_id s))
        s.(state_watched))
      s.(state_pending) d body Hfind)
      as [[-> ->]|Hold].
    + right. left. now left.
    + specialize (Hcover d body Hold Hfalse).
      destruct Hcover as [Hopp|[Hwork|[Hwatched|Hinfals]]].
      * now left.
      * contradiction.
      * right. right. left. destruct Hwatched as [[v Hin] Hnonempty]. split.
        -- exists v. apply ClauseMap.find_add. now right.
        -- exact Hnonempty.
      * right; right; right. destruct Hinfals as [Hfalse'|[p Hp]].
        -- left. destruct Hfalse' as [old [Hfindold Hsem]]. exists old.
           split; [now apply find_clause_after_learned_add_state|exact Hsem].
        -- right. now exists p.
  - intros d Hd. exact Hd.
  - intros v d Hd. apply ClauseMap.find_add in Hd as [[Heqv Heqd]|Hd].
    + subst v d. exists c. split; [apply find_added_learned_clause|].
      split.
      * intros Hnot. exfalso. apply Hnot. now left.
      * repeat split; try assumption.
        -- now apply literal_InL.
        -- destruct l as [w|w]; cbn; intros Hbucket.
           ++ exact Hlc.
           ++ exfalso. eapply fresh_learned_clause_not_watched with (v := w);
             [exact Hstateinv|].
           unfold ClauseMap.find. apply in_or_app. left.
           change (In (Learned (fresh_learned_clause_id s))
             (ClauseMap.find_pos w
               (ClauseMap.add (Neg w) (Learned (fresh_learned_clause_id s))
                 s.(state_watched)))) in Hbucket.
           now rewrite ClauseMap.find_pos_add_neg in Hbucket.
        -- destruct l as [w|w]; cbn; intros Hbucket.
           ++ exfalso. eapply fresh_learned_clause_not_watched with (v := w);
             [exact Hstateinv|].
           unfold ClauseMap.find. apply in_or_app. right.
           change (In (Learned (fresh_learned_clause_id s))
             (ClauseMap.find_neg w
               (ClauseMap.add (Pos w) (Learned (fresh_learned_clause_id s))
                 s.(state_watched)))) in Hbucket.
           now rewrite ClauseMap.find_neg_add_pos in Hbucket.
           ++ exact Hlc.
    + destruct (Hwatch v d Hd) as
        [body [Hfind [Hstable [Hinc [Hnoopp' Hpolarity]]]]].
      exists body. split; [now apply find_clause_after_learned_add_state|].
      split.
      * intros _. destruct (Hstable ltac:(cbn; tauto)) as [Hfollow Htwo].
        split.
        -- intros p Hsuffix x Hxu Hneeds. apply ClauseMap.find_add. right.
           eapply Hfollow; eauto.
        -- intros Hcardout.
        assert (d <> Learned (fresh_learned_clause_id s)) as Hneq.
        { intros ->. eapply fresh_learned_clause_not_watched with (v := v);
            [exact Hstateinv|exact Hd]. }
        assert (ClauseMap.card_of d s.(state_watched) <> 1) as Hcardold.
        { rewrite <- (ClauseMap.card_of_add_neq s.(state_watched)
            (Learned (fresh_learned_clause_id s)) d l (not_eq_sym Hneq)).
          exact Hcardout. }
        specialize (Htwo Hcardold).
        unfold follows_two_undecided in *.
           intros model Hsuffix Hunsat Htwoundecided.
           destruct (Htwo model Hsuffix Hunsat Htwoundecided)
             as [Hwatchcard Hall].
           split.
           ++ cbn [state_watched].
              rewrite ClauseMap.card_of_add_neq by exact (not_eq_sym Hneq).
              exact Hwatchcard.
           ++ intros w Hw. apply Hall.
              apply ClauseMap.find_add in Hw.
              destruct Hw as [[_ Heq]|Hw]; [congruence|exact Hw].
      * repeat split; try assumption.
        -- destruct Hpolarity as [Hpossem _]. intros Hbucket. apply Hpossem.
        eapply ClauseMap.find_pos_add_old; [|exact Hbucket]. intros Heq.
        eapply fresh_learned_clause_not_watched with (v := v);
          [exact Hstateinv|]. now rewrite <- Heq.
        -- destruct Hpolarity as [_ Hnegsem]. intros Hbucket. apply Hnegsem.
        eapply ClauseMap.find_neg_add_old; [|exact Hbucket]. intros Heq.
        eapply fresh_learned_clause_not_watched with (v := v);
          [exact Hstateinv|]. now rewrite <- Heq.
  - apply ClauseMap.find_pos_add_nodup; [apply Hnodup|].
    now apply fresh_learned_clause_not_watched.
  - apply ClauseMap.find_neg_add_nodup; [apply Hnodup|].
    now apply fresh_learned_clause_not_watched.
  - constructor; [simpl; tauto|constructor].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    exists c. split; [apply find_added_learned_clause|]. split; [exact Hnoopp|].
    unfold staged_watches_valid, staged_watches_valid_with.
    cbn [state_trail state_watched].
    intros model Hsuffix Hunsat Htwo v Hin. apply ClauseMap.find_add in Hin.
    destruct Hin as [[Hv _]|Hold].
    + subst v.
      pose proof (undecided_model_suffix _ _ l Hsuffix Hlu) as Hlumodel.
      destruct l; cbn; [exact Hlumodel|].
      rewrite literal_is_undecided_pos_neg. exact Hlumodel.
    + exfalso. eapply fresh_learned_clause_not_watched;
        [exact Hstateinv|exact Hold].
  - intros p d Hd. destruct (Hpending p d Hd) as [body [Hfind Hrest]].
    exists body. split;
      [now apply find_clause_after_learned_add_state|exact Hrest].
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|Hd]; [subst d|contradiction].
    left. unfold card_of_watch. cbn [state_watched].
    rewrite ClauseMap.card_of_add, (fresh_learned_clause_card_zero s Hstateinv).
    reflexivity.
  - intros d. destruct (clause_pointer_eq_dec (Learned (fresh_learned_clause_id s)) d)
      as [Heq|Hneq].
    + subst d. right. right. split.
      * unfold card_of_watch. cbn [state_watched].
        rewrite ClauseMap.card_of_add, (fresh_learned_clause_card_zero s Hstateinv).
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
           now apply decided_clause_after_learned_store_add with
             (cm := ClauseMap.add l (Learned (fresh_learned_clause_id s))
               s.(state_watched))
             (pending := s.(state_pending)).
  - exact (proj1 Htrail).
  - exact (trail_justified_after_learned_add s c s.(state_trail) (proj2 Htrail)).
Qed.

Lemma watched_undecided_follows_needed :
  forall ci c clauses learned (m : Trail) cm pending l,
  In l c ->
  literal_is_undecided m l = true ->
  In ci (ClauseMap.find (literal_var l) cm) ->
  follows_needed_literal ci c
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |}.
Proof.
  intros ci c clauses learned m cm pending l Hlc Hlu Hwatched.
  intros model Hsuffix p Hpu Hneeds.
  pose proof (undecided_model_suffix m model l Hsuffix Hlu) as Hlumodel.
  pose proof (clause_needs_literal_unique model c l p Hlc Hlumodel Hneeds)
    as ->.
  exact Hwatched.
Qed.

Lemma watch_one_fresh_inv : forall work ci c clauses learned m cm pending l,
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  staged_invariant (ci :: work)
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |} ->
  ~ In ci (ClauseMap.find (literal_var l) cm) ->
  In l c ->
  (follows_needed_literal ci c
      {| state_trail := m; state_clauses := clauses; state_learned := learned;
         state_watched := ClauseMap.add l ci cm;
         state_pending := pending |} /\
    (ClauseMap.card_of ci (ClauseMap.add l ci cm) <> 1 ->
      follows_two_undecided ci c
      {| state_trail := m; state_clauses := clauses; state_learned := learned;
         state_watched := ClauseMap.add l ci cm;
         state_pending := pending |})) ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := ClauseMap.add l ci cm;
       state_pending := pending |}.
Proof.
  intros work ci c clauses learned m cm pending l Hfind Hnoopp Hinv
    Hfresh Hlc Hstableout.
  destruct Hinv as
    [Hsat [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork [Hcard Htrail]]]]]]]]].
  inversion Hworknodup as [|? ? Hcinotwork Hworknodup']; subst.
  pose proof (Hwork ci (or_introl eq_refl)) as Hciwork.
  unfold card_of_watch in Hciwork. cbn -[ClauseMap.card_of] in Hciwork.
  split.
  - intros d body Hbody Hunsat.
    specialize (Hsat d body Hbody Hunsat).
    destruct Hsat as [Htrivial|[[->|Hdwork]|[Hwatched|Hinfals]]].
    + now left.
    + change (find_clause_in clauses learned d = Some body) in Hbody.
      rewrite Hfind in Hbody. injection Hbody as <-.
      destruct (filter (literal_is_undecided m) c) as [|p ps]
        eqn:Hundecided.
      * right; right; right; left. exists c. repeat split; assumption.
      * right. right. left. split.
        -- exists (literal_var l). apply ClauseMap.find_add. now left.
        -- cbn [state_trail]. rewrite Hundecided. discriminate.
    + now right; left.
    + right. right. left. destruct Hwatched as [[v Hin] Hundecided]. split.
      * exists v. apply ClauseMap.find_add. now right.
      * exact Hundecided.
    + right; right; right. exact Hinfals.
  - split; [exact Hfals|]. split.
    + intros v d Hin. apply ClauseMap.find_add in Hin as [[-> ->]|Hin].
      * exists c. split; [exact Hfind|]. split.
        -- intros _. exact Hstableout.
        -- repeat split; try assumption.
           ++ now apply literal_InL.
           ++ destruct l as [w|w]; cbn; intros Hbucket.
              ** exact Hlc.
              ** exfalso. apply Hfresh. unfold ClauseMap.find.
              apply in_or_app. left. now rewrite ClauseMap.find_pos_add_neg in Hbucket.
           ++ destruct l as [w|w]; cbn; intros Hbucket.
              ** exfalso. apply Hfresh. unfold ClauseMap.find.
              apply in_or_app. right. now rewrite ClauseMap.find_neg_add_pos in Hbucket.
              ** exact Hlc.
      * destruct (Hwatch v d Hin) as
          [body [Hbody [Hstable [Hinc [Hnoopp' Hpolarity]]]]].
        exists body. split; [exact Hbody|]. split.
        -- intros Hdnot.
           destruct (clause_pointer_eq_dec d ci) as [->|Hneq].
           ++ change (find_clause_in clauses learned ci = Some body) in Hbody.
              rewrite Hfind in Hbody. injection Hbody as <-.
              exact Hstableout.
           ++ assert (~ In d (ci :: work)) as Hdnot'.
              { cbn. intros [Heq|Hinwork]; [congruence|now apply Hdnot]. }
              destruct (Hstable Hdnot') as [Hfollow Htwo'].
              split.
              ** intros p Hsuffix x Hxu Hneeds. apply ClauseMap.find_add. right.
                 eapply Hfollow; eauto.
              ** intros Hcardout.
              assert (ClauseMap.card_of d cm <> 1) as Hcardold.
              { rewrite <- (ClauseMap.card_of_add_neq cm ci d l
                    (not_eq_sym Hneq)).
                exact Hcardout. }
              specialize (Htwo' Hcardold).
              unfold follows_two_undecided in *.
                 intros model Hsuffix Hunsat Htwoundecided.
                 destruct (Htwo' model Hsuffix Hunsat Htwoundecided)
                   as [Hwatchcard Hall].
                 split.
                 --- cbn [state_watched].
                     rewrite ClauseMap.card_of_add_neq by exact (not_eq_sym Hneq).
                     exact Hwatchcard.
                 --- intros w Hw. apply Hall.
                     apply ClauseMap.find_add in Hw.
                     destruct Hw as [[_ Heq]|Hw]; [congruence|exact Hw].
        -- repeat split; try assumption.
           ++ destruct Hpolarity as [Hpossem _]. intros Hbucket. apply Hpossem.
              eapply ClauseMap.find_pos_add_existing; eauto.
           ++ destruct Hpolarity as [_ Hnegsem]. intros Hbucket. apply Hnegsem.
              eapply ClauseMap.find_neg_add_existing; eauto.
    + split.
      * intros v. split.
        -- apply ClauseMap.find_pos_add_nodup; [apply Hnodup|exact Hfresh].
        -- apply ClauseMap.find_neg_add_nodup; [apply Hnodup|exact Hfresh].
      * split; [exact Hworknodup'|]. split.
        -- intros d Hd.
           destruct (Hworkref d (or_intror Hd)) as
             [body [Hbody [Hnoopp' Hvalid]]].
           exists body. split; [exact Hbody|]. split; [exact Hnoopp'|].
           unfold staged_watches_valid, staged_watches_valid_with in Hvalid |- *.
           cbn [state_trail state_watched] in Hvalid |- *.
           intros model Hsuffix Hunsat Htwo v Hin.
           apply ClauseMap.find_add in Hin.
           destruct Hin as [[_ Heq]|Hin].
           ++ subst d. contradiction.
           ++ now apply Hvalid.
        -- split; [exact Hpending|]. split.
           ++ intros d Hd. specialize (Hwork d (or_intror Hd)).
              assert (ci <> d) as Hneq by (intros ->; contradiction).
              unfold card_of_watch in Hwork |- *. cbn -[ClauseMap.card_of].
              now rewrite ClauseMap.card_of_add_neq by exact Hneq.
           ++ split.
              ** intros d. destruct (clause_pointer_eq_dec ci d) as [->|Hneq].
                 --- unfold card_of_watch. cbn -[ClauseMap.card_of].
                 rewrite ClauseMap.card_of_add.
                 destruct Hciwork as [Hone|[Hzero [[p Hpendingci]|Hdecided]]].
                     +++ rewrite Hone. now right; left.
                     +++ rewrite Hzero. right; right. split; [reflexivity|].
                     right. left. now exists p.
                     +++ rewrite Hzero. right; right. split; [reflexivity|].
                     right. right. exact Hdecided.
                 --- specialize (Hcard d).
                 unfold card_of_watch in Hcard |- *. cbn -[ClauseMap.card_of].
                 rewrite ClauseMap.card_of_add_neq by exact Hneq.
                 destruct Hcard as [Hzero|[Hcardtwo|[Hone Hwhy]]].
                     +++ now left.
                     +++ now right; left.
                     +++ right; right. split; [exact Hone|].
                     destruct Hwhy as [Hdwork|[Hpendingd|Hdecided]].
                         *** simpl in Hdwork. destruct Hdwork as [Heq|Hdwork];
                           [contradiction|now left].
                         *** right. left. exact Hpendingd.
                         *** right. right. exact Hdecided.
              ** exact Htrail.
Qed.

Lemma restage_one_watch_inv : forall work ci c clauses learned m cm pending,
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  ClauseMap.card_of ci cm = 1 ->
  ~ In ci work ->
  staged_watches_valid ci c
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  staged_invariant (ci :: work)
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |}.
Proof.
  intros work ci c clauses learned m cm pending Hfind Hnoopp Hone
    Hfresh Hvalid Hinv.
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork [Hcard Htrail]]]]]]]]].
  split.
  - intros d body Hbody Hfalse. specialize (Hcover d body Hbody Hfalse).
    destruct Hcover as [Hopp|[Hdwork|[Hwatched|Hinfals]]].
    + now left.
    + right. left. now right.
    + now right; right; left.
    + right; right; right. exact Hinfals.
  - split; [exact Hfals|].
    split.
    + intros v d Hd. destruct (Hwatch v d Hd) as [body [Hbody [Hstable Hrest]]].
      exists body. split; [exact Hbody|]. split; [|exact Hrest].
      intros Hnotnew. apply Hstable.
      intros Hinold. apply Hnotnew. now right.
    + split; [exact Hnodup|].
      split.
      * constructor; [exact Hfresh|exact Hworknodup].
      * split.
        -- intros d Hd. cbn in Hd. destruct Hd as [->|Hd].
           ++ exists c. now repeat split.
           ++ exact (Hworkref d Hd).
        -- split; [exact Hpending|]. split.
           ++ intros d Hd. cbn in Hd. destruct Hd as [->|Hd].
              ** left. exact Hone.
              ** exact (Hwork d Hd).
           ++ split.
              ** intros d. destruct (clause_pointer_eq_dec ci d) as [->|Hneq].
                 --- right. right. split.
                     +++ unfold card_of_watch. cbn. exact Hone.
                     +++ cbn. tauto.
                 --- specialize (Hcard d).
                     destruct Hcard as [Hzero|[Htwo|[Hone' Hwhy]]].
                     +++ now left.
                     +++ now right; left.
                     +++ right. right. split; [exact Hone'|].
                         destruct Hwhy as [Hdwork|[Hpendingd|Hdecided]].
                         *** left. now right.
                         *** now right; left.
                         *** now right; right.
              ** exact Htrail.
Qed.

Lemma stage_zero_decided_inv : forall ci c clauses learned m cm pending,
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  ClauseMap.card_of ci cm = 0 ->
  ((exists p, In (p, ci) pending) \/
   decided_clause ci
     {| state_trail := m; state_clauses := clauses; state_learned := learned;
        state_watched := cm; state_pending := pending |}) ->
  state_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  staged_invariant [ci]
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |}.
Proof.
  intros ci c clauses learned m cm pending Hfind Hnoopp Hzero Hdecided
    [Hinv _].
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [_ [_
      [Hpending [_ [Hcard Htrail]]]]]]]]].
  split.
  - intros d body Hbody Hfalse. specialize (Hcover d body Hbody Hfalse).
    destruct Hcover as [Hopp|[Habs|[Hwatched|Hinfals]]].
    + now left.
    + contradiction.
    + now right; right; left.
    + now right; right; right.
  - split; [exact Hfals|].
    split.
    + intros v d Hd. destruct (Hwatch v d Hd) as [body [Hbody [Hstable Hrest]]].
      exists body. split; [exact Hbody|]. split; [|exact Hrest].
      intros Hnotnew. apply Hstable. cbn; tauto.
    + split; [exact Hnodup|].
      split.
      * constructor; [simpl; tauto|constructor].
      * split.
        -- intros d Hd. cbn in Hd. destruct Hd as [->|Hd];
             [|contradiction].
           exists c. split; [exact Hfind|]. split; [exact Hnoopp|].
           unfold staged_watches_valid, staged_watches_valid_with.
           cbn [state_trail state_watched].
    intros model Hsuffix Hunsat Htwo v Hin.
           pose proof (ClauseMap.card_of_in _ _ _ Hin) as Hpositive.
           rewrite Hzero in Hpositive. lia.
        -- split; [exact Hpending|]. split.
           ++ intros d Hd. cbn in Hd. destruct Hd as [->|Hd]; [|contradiction].
              right. split; [exact Hzero|]. exact Hdecided.
           ++ split.
              ** intros d. destruct (clause_pointer_eq_dec ci d) as [->|Hneq].
                 --- left. exact Hzero.
                 --- specialize (Hcard d). destruct Hcard as [Hz|[Ht|[Ho Hwhy]]].
                     +++ now left.
                     +++ now right; left.
                     +++ right. right. split; [exact Ho|].
                         destruct Hwhy as [Habs|[Hp|Hd]];
                           [contradiction|now right; left|now right; right].
              ** exact Htrail.
Qed.

Lemma two_added_watches_undecided : forall ci cm m l l',
  ClauseMap.card_of ci cm = 0 ->
  literal_is_undecided m l = true ->
  literal_is_undecided m l' = true ->
  (forall v, In ci (ClauseMap.find_pos v
      (ClauseMap.add l' ci (ClauseMap.add l ci cm))) ->
     literal_is_undecided m (Pos v) = true) /\
  (forall v, In ci (ClauseMap.find_neg v
      (ClauseMap.add l' ci (ClauseMap.add l ci cm))) ->
     literal_is_undecided m (Neg v) = true).
Proof.
  intros ci cm m [x|x] [y|y] Hzero Hlu Hl'u; split; intros v Hin.
  all: repeat first
    [ rewrite ClauseMap.find_pos_add_pos in Hin
    | rewrite ClauseMap.find_pos_add_neg in Hin
    | rewrite ClauseMap.find_neg_add_pos in Hin
    | rewrite ClauseMap.find_neg_add_neg in Hin ].
  all: repeat match goal with
    | H : context [if VarKey.eq_dec ?x ?v then _ else _] |- _ =>
        destruct (VarKey.eq_dec x v) as [->|?]; cbn in H
    end.
  all: repeat match goal with
    | H : _ = _ \/ _ |- _ => destruct H as [<-|H]
    end; try assumption.
  all: exfalso;
    match type of Hin with
    | In _ (ClauseMap.find_pos _ _) =>
        pose proof (ClauseMap.card_of_in cm ci v
          (in_or_app _ _ _ (or_introl Hin)))
    | In _ (ClauseMap.find_neg _ _) =>
        pose proof (ClauseMap.card_of_in cm ci v
          (in_or_app _ _ _ (or_intror Hin)))
    end; lia.
Qed.

Lemma watch_two_fresh_inv : forall ci c clauses learned (m : Trail) cm
    pending l l',
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  In l c -> In l' c ->
  literal_is_undecided m l = true ->
  (forall model, model_suffix model m ->
    Is_true (negb (existsb (literal_is_true model) c)) ->
    clause_has_two_undecided model c ->
    literal_is_undecided model l = true /\
    literal_is_undecided model l' = true) ->
  literal_var l <> literal_var l' ->
  ~ In ci (ClauseMap.find (literal_var l) cm) ->
  ~ In ci (ClauseMap.find (literal_var l') cm) ->
  ClauseMap.card_of ci cm = 0 ->
  staged_invariant [ci]
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  staged_invariant []
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := ClauseMap.add l' ci (ClauseMap.add l ci cm);
       state_pending := pending |}.
Proof.
  intros ci c clauses learned m cm pending l l' Hfind Hnoopp Hlin Hl'in
    Hlu Hrecent Hvars Hfresh Hfresh' Hzero Hstage.
  assert (Hone : ClauseMap.card_of ci (ClauseMap.add l ci cm) = 1).
  { rewrite ClauseMap.card_of_add, Hzero. reflexivity. }
  assert (Hstablefirst :
      follows_needed_literal ci c
        {| state_trail := m; state_clauses := clauses; state_learned := learned;
           state_watched := ClauseMap.add l ci cm;
           state_pending := pending |} /\
      (ClauseMap.card_of ci (ClauseMap.add l ci cm) <> 1 ->
       follows_two_undecided ci c
        {| state_trail := m; state_clauses := clauses; state_learned := learned;
           state_watched := ClauseMap.add l ci cm;
           state_pending := pending |})).
  { split.
    - eapply watched_undecided_follows_needed with (l := l); eauto.
      apply ClauseMap.find_add. now left.
    - intros Hneq. exfalso. now apply Hneq. }
  pose proof (watch_one_fresh_inv [] ci c clauses learned m cm pending l
    Hfind Hnoopp Hstage Hfresh Hlin Hstablefirst) as Hfirst.
  assert (Hvalidfirst : staged_watches_valid ci c
      {| state_trail := m; state_clauses := clauses; state_learned := learned;
         state_watched := ClauseMap.add l ci cm;
         state_pending := pending |}).
  { unfold staged_watches_valid, staged_watches_valid_with.
    cbn [state_trail state_watched].
    intros model Hsuffix Hunsat Htwo v Hin. apply ClauseMap.find_add in Hin.
    destruct Hin as [[Hv _]|Hin].
    - subst v.
      pose proof (proj1 (Hrecent model Hsuffix Hunsat Htwo)) as Hlumodel.
      destruct l; cbn; [exact Hlumodel|].
      rewrite literal_is_undecided_pos_neg. exact Hlumodel.
    - exfalso. pose proof (ClauseMap.card_of_in _ _ _ Hin) as Hpositive.
      rewrite Hzero in Hpositive. lia. }
  pose proof (restage_one_watch_inv [] ci c clauses learned m
    (ClauseMap.add l ci cm) pending Hfind Hnoopp Hone (fun H => H)
    Hvalidfirst Hfirst) as Hrestaged.
  apply (watch_one_fresh_inv [] ci c clauses learned m
    (ClauseMap.add l ci cm) pending l'); try assumption.
  - intros Hin. apply ClauseMap.find_add in Hin as [[Heq _]|Hin].
    + now apply Hvars.
    + now apply Hfresh'.
  - split.
    + eapply watched_undecided_follows_needed with (l := l); eauto.
      apply ClauseMap.find_add. right. apply ClauseMap.find_add. now left.
    + intros _. unfold follows_two_undecided.
      intros model Hsuffix Hunsat Htwo.
      split.
      * cbn [state_watched]. rewrite !ClauseMap.card_of_add, Hzero. reflexivity.
      * destruct (Hrecent model Hsuffix Hunsat Htwo)
          as [Hlumodel Hl'umodel].
        destruct (two_added_watches_undecided ci cm model l l'
          Hzero Hlumodel Hl'umodel)
          as [Hpos Hneg].
        intros v Hin. unfold ClauseMap.find in Hin.
        apply in_app_or in Hin as [Hin|Hin].
        -- now apply Hpos.
        -- rewrite literal_is_undecided_pos_neg. now apply Hneg.
Qed.

Lemma mark_falsified_inv : forall work ci c clauses learned (m : Trail) cm
    pending,
  find_clause_in clauses learned ci = Some c ->
  Is_true (negb (existsb (literal_is_true m) c)) ->
  filter (literal_is_undecided m) c = [] ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |} ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |}.
Proof.
  intros work ci c clauses learned m cm pending Hfind Hfalse Hfilter Hinv.
  exact Hinv.
Qed.

Lemma watch_one_inv : forall work ci c clauses learned m cm
    pending l l' cm',
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  staged_invariant (ci :: work)
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |} ->
  In l c -> In l' c ->
  literal_is_undecided m l = true ->
  literal_is_undecided m l' = true ->
  literal_var l <> literal_var l' ->
  Is_true (negb (existsb (literal_is_true m) c)) ->
  cm' = (if in_dec clause_pointer_eq_dec ci (ClauseMap.find (literal_var l) cm)
      then ClauseMap.add l' ci cm
      else ClauseMap.add l ci cm) ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm';
       state_pending := pending |}.
Proof.
  intros work ci c clauses learned m cm pending l l' cm' Hfind Hnoopp Hinv
    Hlc Hl'c Hlu Hl'u Hneq Hunsat Hcm'.
  assert (Htwo : clause_has_two_undecided m c).
  { exists l, l'. repeat split; assumption. }
  pose proof Hinv as Hfacts.
  destruct Hfacts as
    [_ [Hfals [_ [_ [_ [Hworkref [Hpending [Hwork _]]]]]]]].
  destruct (Hworkref ci (or_introl eq_refl)) as
    [body [Hbody [_ Hstagedvalid]]].
  change (find_clause_in clauses learned ci = Some body) in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  assert (Holdwatchundec : forall v, In ci (ClauseMap.find v cm) ->
      literal_is_undecided m (Pos v) = true).
  { now apply (Hstagedvalid (trail_model m) (model_suffix_refl _) Hunsat Htwo). }
  assert (Hcardold : ClauseMap.card_of ci cm = 1).
  { specialize (Hwork ci (or_introl eq_refl)).
    unfold card_of_watch in Hwork. cbn -[ClauseMap.card_of] in Hwork.
    destruct Hwork as [Hone|[Hzero [[p Hp]|Hdecided]]]; [exact Hone| |].
    - destruct (Hpending p ci Hp) as [body [Hbody [Hneeds _]]].
      change (find_clause_in clauses learned ci = Some body) in Hbody.
      rewrite Hfind in Hbody. injection Hbody as <-.
      pose proof (clause_needs_literal_unique m c l p Hlc Hlu Hneeds) as Hp_l.
      pose proof (clause_needs_literal_unique m c l' p Hl'c Hl'u Hneeds) as Hp_l'.
      exfalso. apply Hneq.
      rewrite <- (f_equal literal_var Hp_l), <- (f_equal literal_var Hp_l').
      reflexivity.
    - destruct Hdecided as [Hinfals|[body [Hbody Hsatisfied]]].
      + destruct (Hfals ci Hinfals) as [body [Hbody [_ Hnone]]].
        change (find_clause_in clauses learned ci = Some body) in Hbody.
        rewrite Hfind in Hbody. injection Hbody as <-.
        cbn [state_trail] in Hnone.
        assert (In l (filter (literal_is_undecided m) c)) as Hinfilter.
        { apply filter_In. now split. }
        now rewrite Hnone in Hinfilter.
      + change (find_clause_in clauses learned ci = Some body) in Hbody.
        rewrite Hfind in Hbody. injection Hbody as <-.
        cbn [state_trail] in Hsatisfied.
        apply Is_true_eq_true in Hsatisfied.
        apply Is_true_eq_true in Hunsat. rewrite Hsatisfied in Hunsat.
        discriminate. }
  destruct (in_dec clause_pointer_eq_dec ci (ClauseMap.find (literal_var l) cm))
    as [Hwatched|Hfresh].
  - subst cm'. apply watch_one_fresh_inv with (c := c); try assumption.
    + intros Hwatched'.
      apply Hneq. eapply ClauseMap.card_of_unique; eauto.
    + split.
      * eapply watched_undecided_follows_needed with (l := l'); eauto.
        apply ClauseMap.find_add. now left.
      * intros _. unfold follows_two_undecided.
        intros model Hsuffix Hunsat' Htwo'.
        cbn [state_watched state_trail].
        split.
        -- rewrite ClauseMap.card_of_add, Hcardold. reflexivity.
        -- intros v Hin. apply ClauseMap.find_add in Hin as [[Hv _]|Hin].
           ++ subst v.
              pose proof (undecided_model_suffix _ _ l' Hsuffix Hl'u) as Hu.
              destruct l'; cbn; [exact Hu|].
              rewrite literal_is_undecided_pos_neg. exact Hu.
           ++ now apply (Hstagedvalid model Hsuffix Hunsat' Htwo').
  - subst cm'. apply watch_one_fresh_inv with (c := c); try assumption.
    + split.
      * eapply watched_undecided_follows_needed with (l := l); eauto.
        apply ClauseMap.find_add. now left.
      * intros _. unfold follows_two_undecided.
        intros model Hsuffix Hunsat' Htwo'.
        cbn [state_watched state_trail].
        split.
        -- rewrite ClauseMap.card_of_add, Hcardold. reflexivity.
        -- intros v Hin. apply ClauseMap.find_add in Hin as [[Hv _]|Hin].
           ++ subst v.
              pose proof (undecided_model_suffix _ _ l Hsuffix Hlu) as Hu.
              destruct l; cbn; [exact Hu|].
              rewrite literal_is_undecided_pos_neg. exact Hu.
           ++ now apply (Hstagedvalid model Hsuffix Hunsat' Htwo').
Qed.

Lemma pending_cons_inv : forall work ci c clauses learned (m : Trail) cm
    pending l,
  find_clause_in clauses learned ci = Some c ->
  clause_needs_literal m l c ->
  ~ has_opposite_literals c ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |} ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := (l, ci) :: pending |}.
Proof.
  intros work ci c clauses learned m cm pending l Hfind Hneeds Hnoopp Hinv.
  destruct Hinv as
    [Hsat [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork [Hcard Htrail]]]]]]]]].
  repeat split; try assumption.
  - intros d body Hbody Hunsat.
    destruct (Hsat d body Hbody Hunsat) as
      [Hopp|[Hdwork|[Hwatched|Hqueued]]].
    + now left.
    + now right; left.
    + now right; right; left.
    + right; right; right. unfold queued_clause in Hqueued |- *. cbn.
      destruct Hqueued as [Hin|[p Hin]]; [now left|].
      right. exists p. now right.
  - apply Hnodup.
  - apply Hnodup.
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
  - exact (proj1 Htrail).
  - exact (proj2 Htrail).
Qed.

Lemma detached_clause_arity_add :
  forall work ci c clauses learned m cm pending l,
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  ~ In ci work ->
  detached_clause_arity (ci :: work)
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  detached_clause_arity work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := ClauseMap.add l ci cm; state_pending := pending |}.
Proof.
  intros work ci c clauses learned m cm pending l Hfind Hnoopp
    Hnotin Harity d body Hbody Hbody_noopp.
  assert (Hsamefind : find_clause_in clauses learned d = Some body) by
    exact Hbody.
  split.
  - intros Hdwork. assert (d <> ci) as Hneq.
    { intros ->. contradiction. }
    destruct (proj1 (Harity d body Hsamefind Hbody_noopp)
      (or_intror Hdwork)) as [Htwo Hone].
    split; [exact Htwo|]. cbn [state_watched].
    now rewrite ClauseMap.card_of_add_neq by exact (not_eq_sym Hneq).
  - intros Hdnotwork. destruct (clause_pointer_eq_dec d ci) as [->|Hneq].
    + change (find_clause_in clauses learned ci = Some body) in Hsamefind.
      rewrite Hfind in Hsamefind. injection Hsamefind as <-.
      destruct (proj1 (Harity ci c Hfind Hnoopp) (or_introl eq_refl))
        as [Htwo Hone]. left. split; [exact Htwo|].
      cbn [state_watched] in Hone |- *.
      now rewrite ClauseMap.card_of_add, Hone.
    + specialize (proj2 (Harity d body Hsamefind Hbody_noopp)) as Hold.
      assert (~ In d (ci :: work)) as Hdnotall.
      { intros [Heq|Hin]; [congruence|contradiction]. }
      specialize (Hold Hdnotall). cbn [state_watched] in Hold |- *.
      rewrite ClauseMap.card_of_add_neq by exact (not_eq_sym Hneq).
      exact Hold.
Qed.

Lemma propagate_literal_inv :
  forall work falsified ci c clauses learned m cm pending l cm',
  find_clause_in clauses learned ci = Some c ->
  In falsified c ->
  ~ In ci (ClauseMap.find (literal_var falsified) cm) ->
  staged_invariant_with (Some falsified) (ci :: work)
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |} ->
  scan_clause m falsified ci c cm = propagate_literal l cm' ->
  staged_invariant_with (Some falsified) work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm';
       state_pending := (l, ci) :: pending |}.
Proof.
  intros work falsified ci c clauses learned m cm pending l cm'
    Hfind Hfalsified Hfreshf [Hinv [Hdetached Harity]] Hscan.
  pose proof Hinv as Hlookup.
  destruct Hlookup as [_ [_ [_ [_ [_ [Hworklookup _]]]]]].
  destruct (Hworklookup ci (or_introl eq_refl))
    as [body [Hbody [Hnoopp Hstagedvalid]]].
  change (find_clause_in clauses learned ci = Some body) in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  destruct (Hdetached ci (or_introl eq_refl)) as
    [detached_body [Hdetached_body
      [Hdetached_in [Hdetached_valid Hdetached_needed]]]].
  change (find_clause_in clauses learned ci = Some detached_body)
    in Hdetached_body.
  rewrite Hfind in Hdetached_body. injection Hdetached_body as <-.
  pose proof Hinv as Hworkfacts.
  destruct Hworkfacts as [_ [_ [_ [_ [_ [_ [_ [Hworkcard _]]]]]]]].
  assert (Hnotin : ~ In ci work).
  { unfold staged_invariant in Hinv.
    destruct Hinv as [_ [_ [_ [_ [Hnodup _]]]]].
    now inversion Hnodup. }
  specialize (Hworkcard ci (or_introl eq_refl)).
  unfold card_of_watch in Hworkcard.
  cbn [state_watched] in Hworkcard.
  pose proof (scan_clause_propagate_needs m falsified ci c cm l cm' Hnoopp Hscan)
    as Hneeds.
  pose proof (scan_clause_inl_spec m falsified ci c cm l cm' Hscan) as
    [_ [Hlc [Hlu Hcm']]].
  assert (Hlive : filter (literal_is_undecided m) c <> []).
  { intros Hempty.
    assert (In l (filter (literal_is_undecided m) c)).
    { apply filter_In. now split. }
    now rewrite Hempty in H. }
  destruct (in_dec clause_pointer_eq_dec ci
      (ClauseMap.find (literal_var l) cm)) as [Hwatched|Hfresh].
  - assert (Hrestore : restore_detached_watch falsified ci c cm =
        ClauseMap.add falsified ci cm).
    { unfold restore_detached_watch.
      destruct (find_different_var (literal_var falsified) c) eqn:Hdifferent;
        [reflexivity|].
      exfalso. apply Hfreshf. rewrite <- (find_different_var_none
        (literal_var falsified) c Hdifferent l Hlc). exact Hwatched. }
    subst cm'. rewrite Hrestore. split.
    { eapply pending_cons_inv;
      [exact Hfind|exact Hneeds|exact Hnoopp|].
    eapply watch_one_fresh_inv;
      [exact Hfind|exact Hnoopp|exact Hinv|exact Hfreshf|exact Hfalsified|].
    split.
    + eapply watched_undecided_follows_needed with (l := l); eauto.
      apply ClauseMap.find_add. now right.
    + intros _. unfold follows_two_undecided.
      intros model Hsuffix Hunsat Htwo.
      destruct (list_eq_dec literal_eq_dec model (trail_model m))
        as [Heq|Hneqmodel].
      * subst model. destruct Htwo as
          [x [y [Hxc [Hyc [Hxy [Hxu Hyu]]]]]].
        pose proof (clause_needs_literal_unique m c x l Hxc Hxu Hneeds) as Hlx.
        pose proof (clause_needs_literal_unique m c y l Hyc Hyu Hneeds) as Hly.
        exfalso. apply Hxy.
        rewrite <- (f_equal literal_var Hlx), <- (f_equal literal_var Hly).
        reflexivity.
      * assert (Hcardold : ClauseMap.card_of ci cm = 1).
        { destruct Hworkcard as [Hone|[Hzero _]]; [exact Hone|].
          pose proof (ClauseMap.card_of_in _ _ _ Hwatched) as Hpositive. lia. }
        split.
        -- cbn [state_watched]. rewrite ClauseMap.card_of_add, Hcardold.
           reflexivity.
        -- intros v Hin. apply ClauseMap.find_add in Hin as [[Hv _]|Hin].
           ++ subst v.
              destruct (Hdetached_valid model Hsuffix Hunsat Htwo)
                as [Heq|Hu]; [contradiction|].
              destruct falsified; cbn; [exact Hu|].
              rewrite literal_is_undecided_pos_neg. exact Hu.
           ++ now apply (Hstagedvalid model Hsuffix Hunsat Htwo). }
    split.
    + intros d Hd. destruct (Hdetached d (or_intror Hd)) as
      [body [Hbody [Hdetachedin Hvalid]]].
      exists body. cbn [find_clause state_trail].
      split; [exact Hbody|]. split; [exact Hdetachedin|].
      destruct Hvalid as [Htwo Hneeded]. split; [exact Htwo|].
      intros model Hsuffix p Hpu Hneedsp.
      destruct (Hneeded model Hsuffix p Hpu Hneedsp)
        as [Heq|[Hvar|Hwatched']]; [now left|now right; left|].
      right. right. apply ClauseMap.find_add. now right.
    + eapply detached_clause_arity_add; eauto.
  - subst cm'. split.
    { eapply pending_cons_inv;
      [exact Hfind|exact Hneeds|exact Hnoopp|].
    eapply watch_one_fresh_inv;
      [exact Hfind|exact Hnoopp|exact Hinv|exact Hfresh|exact Hlc|].
    split.
    + eapply watched_undecided_follows_needed with (l := l); eauto.
      apply ClauseMap.find_add. now left.
    + intros Hcardout. unfold follows_two_undecided.
      intros model Hsuffix Hunsat Htwo.
      assert (Hcardold : ClauseMap.card_of ci cm = 1).
      { destruct Hworkcard as [Hone|[Hzero _]]; [exact Hone|].
        exfalso. apply Hcardout. rewrite ClauseMap.card_of_add, Hzero.
        reflexivity. }
      split.
      * cbn [state_watched]. rewrite ClauseMap.card_of_add, Hcardold.
        reflexivity.
      * intros v Hin. apply ClauseMap.find_add in Hin as [[Hv _]|Hin].
        -- subst v.
           pose proof (undecided_model_suffix _ _ l Hsuffix Hlu) as Hu.
           destruct l; cbn; [exact Hu|].
           rewrite literal_is_undecided_pos_neg. exact Hu.
        -- now apply (Hstagedvalid model Hsuffix Hunsat Htwo). }
    split.
    + intros d Hd. destruct (Hdetached d (or_intror Hd)) as
      [body [Hbody [Hdetachedin Hvalid]]].
      exists body. cbn [find_clause state_trail].
      split; [exact Hbody|]. split; [exact Hdetachedin|].
      destruct Hvalid as [Htwo Hneeded]. split; [exact Htwo|].
      intros model Hsuffix p Hpu Hneedsp.
      destruct (Hneeded model Hsuffix p Hpu Hneedsp)
        as [Heq|[Hvar|Hwatched']]; [now left|now right; left|].
      right. right. apply ClauseMap.find_add. now right.
    + eapply detached_clause_arity_add; eauto.
Qed.

Lemma detached_unit_card_zero : forall work falsified ci c clauses learned m cm
    pending,
  find_clause_in clauses learned ci = Some c ->
  In falsified c ->
  find_different_var (literal_var falsified) c = None ->
  ~ In ci (ClauseMap.find (literal_var falsified) cm) ->
  staged_invariant (ci :: work)
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  ClauseMap.card_of ci cm = 0.
Proof.
  intros work falsified ci c clauses learned m cm pending Hfind Hin
    Hunit Hfresh Hinv.
  destruct (ClauseMap.card_of ci cm) eqn:Hcard; [reflexivity|].
  exfalso. assert (ClauseMap.card_of ci cm > 0) as Hpos by lia.
  apply ClauseMap.card_of_pos in Hpos as [v Hwatched].
  destruct Hinv as [_ [_ [Hwatch _]]].
  destruct (Hwatch v ci Hwatched) as [body [Hbody [_ [HinL _]]]].
  change (find_clause_in clauses learned ci = Some body) in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  assert (v = literal_var falsified) as ->.
  { destruct HinL as [Hposlit|Hneglit].
    - exact (find_different_var_none (literal_var falsified) c
        Hunit (Pos v) Hposlit).
    - exact (find_different_var_none (literal_var falsified) c
        Hunit (Neg v) Hneglit). }
  now apply Hfresh.
Qed.

Lemma drop_decided_zero_inv : forall work ci c clauses learned m cm pending,
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  ClauseMap.card_of ci cm = 0 ->
  ((exists p, In (p, ci) pending) \/
   decided_clause ci
     {| state_trail := m; state_clauses := clauses; state_learned := learned;
        state_watched := cm; state_pending := pending |}) ->
  staged_invariant (ci :: work)
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |}.
Proof.
  intros work ci c clauses learned m cm pending Hfind Hnoopp Hzero
    Hdecided Hinv.
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork [Hcard Htrail]]]]]]]]].
  inversion Hworknodup as [|? ? Hfresh Hworknodup']; subst.
  split.
  - intros d body Hbody Hfalse. specialize (Hcover d body Hbody Hfalse).
    destruct Hcover as [Hopp|[[Heq|Hdwork]|[Hwatched|Hinfals]]].
    + now left.
    + subst d. change (find_clause_in clauses learned ci = Some body) in Hbody.
      rewrite Hfind in Hbody. injection Hbody as <-.
      destruct Hdecided as [[p Hp]|[Hinfals'|[body' [Hbody' Htrue]]]].
      * right; right; right. right. now exists p.
      * right; right; right. left. exact Hinfals'.
      * change (find_clause_in clauses learned ci = Some body') in Hbody'.
        rewrite Hfind in Hbody'. injection Hbody' as <-.
        exfalso. exact (negb_prop_elim _ Hfalse Htrue).
    + right. left. exact Hdwork.
    + now right; right; left.
    + right; right; right. exact Hinfals.
  - split; [exact Hfals|]. split.
    + intros v d Hin.
      destruct (Hwatch v d Hin) as [body [Hbody [Hstable Hrest]]].
      exists body. split; [exact Hbody|]. split; [|exact Hrest].
      intros Hdnot. apply Hstable.
      cbn. intros [Heq|Hdwork].
      * subst d. pose proof (ClauseMap.card_of_in _ _ _ Hin) as Hpositive.
        cbn [state_watched] in Hpositive.
        rewrite Hzero in Hpositive. lia.
      * now apply Hdnot.
    + split; [exact Hnodup|].
      split; [exact Hworknodup'|]. split.
      * intros d Hd. exact (Hworkref d (or_intror Hd)).
      * split; [exact Hpending|]. split.
        { intros d Hd. exact (Hwork d (or_intror Hd)). }
        split.
        { intros d. destruct (clause_pointer_eq_dec ci d) as [->|Hneq].
          - left. exact Hzero.
          - specialize (Hcard d). destruct Hcard as [Hz|[Ht|[Ho Hwhy]]].
            + now left.
            + now right; left.
            + right. right. split; [exact Ho|].
              destruct Hwhy as [[Heq|Hdwork]|[Hp|Hd]].
              * contradiction.
              * now left.
              * now right; left.
              * now right; right. }
        exact Htrail.
Qed.

Lemma two_variables_find_different : forall falsified c,
  In falsified c ->
  clause_has_two_variables c ->
  exists l, find_different_var (literal_var falsified) c = Some l.
Proof.
  intros falsified c Hfc [x [y [Hxc [Hyc Hxy]]]].
  destruct (find_different_var (literal_var falsified) c) as [l|]
    eqn:Hfind; [now exists l|].
  exfalso. apply Hxy.
  rewrite (find_different_var_none _ _ Hfind x Hxc),
    (find_different_var_none _ _ Hfind y Hyc). reflexivity.
Qed.

Lemma propagate_decided_inv :
  forall work falsified ci c clauses learned m cm pending cm',
  find_clause_in clauses learned ci = Some c ->
  In falsified c ->
  ~ In ci (ClauseMap.find (literal_var falsified) cm) ->
  staged_invariant_with (Some falsified) (ci :: work)
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |} ->
  scan_clause m falsified ci c cm = clause_decided cm' ->
  staged_invariant_with (Some falsified) work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm';
       state_pending := pending |}.
Proof.
  intros work falsified ci c clauses learned m cm pending cm'
    Hfind Hfalsified Hfresh [Hinv [Hdetached Harity]] Hscan.
  pose proof Hinv as Hlookup.
  destruct Hlookup as [_ [_ [_ [_ [_ [Hworklookup _]]]]]].
  destruct (Hworklookup ci (or_introl eq_refl))
    as [body [Hbody [Hnoopp Hstagedvalid]]].
  change (find_clause_in clauses learned ci = Some body) in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  destruct (Hdetached ci (or_introl eq_refl)) as
    [detached_body [Hdetached_body
      [Hdetached_in [Hdetached_valid Hdetached_needed]]]].
  change (find_clause_in clauses learned ci = Some detached_body)
    in Hdetached_body.
  rewrite Hfind in Hdetached_body. injection Hdetached_body as <-.
  pose proof Hinv as Hworkfacts.
  destruct Hworkfacts as [_ [_ [_ [_ [_ [_ [_ [Hworkcard _]]]]]]]].
  specialize (Hworkcard ci (or_introl eq_refl)).
  unfold card_of_watch in Hworkcard.
  cbn [state_watched] in Hworkcard.
  assert (Hnotin : ~ In ci work).
  { unfold staged_invariant in Hinv.
    destruct Hinv as [_ [_ [_ [_ [Hnodup _]]]]].
    now inversion Hnodup. }
  destruct (proj1 (Harity ci c Hfind Hnoopp) (or_introl eq_refl))
    as [Htwo_variables Hdetached_card].
  destruct (two_variables_find_different falsified c Hfalsified Htwo_variables)
    as [other Hdifferent_exists].
  assert (Hrestore : restore_detached_watch falsified ci c cm =
      ClauseMap.add falsified ci cm).
  { unfold restore_detached_watch. now rewrite Hdifferent_exists. }
  destruct (scan_clause_decided_spec m falsified ci c cm cm' Hscan)
    as [Htrue Hcm'].
  split.
  {
  rewrite Hcm'. unfold restore_detached_watch.
    destruct (find_different_var (literal_var falsified) c) eqn:Hdifferent.
    + eapply watch_one_fresh_inv; try eassumption.
      * split.
        -- intros model Hsuffix p Hpu Hneeds.
           destruct (Hdetached_needed model Hsuffix p Hpu Hneeds)
             as [Heq|[Hvar|Hwatched]].
           ++ subst model. exfalso. eapply satisfied_not_needs_undecided;
                [apply Is_true_eq_left; exact Htrue|exact Hpu|exact Hneeds].
           ++ apply ClauseMap.find_add. now left.
           ++ apply ClauseMap.find_add. now right.
        -- intros Hcardout. unfold follows_two_undecided.
           intros model Hsuffix Hunsat Htwo.
           destruct (list_eq_dec literal_eq_dec model (trail_model m))
             as [Heq|Hneqmodel].
           ++ subst model. exfalso. apply Is_true_eq_true in Hunsat.
              rewrite Htrue in Hunsat. discriminate.
           ++ assert (Hcardold : ClauseMap.card_of ci cm = 1).
              { destruct Hworkcard as [Hone|[Hzero _]]; [exact Hone|].
                exfalso. apply Hcardout.
                rewrite ClauseMap.card_of_add, Hzero. reflexivity. }
              split.
              ** cbn [state_watched]. rewrite ClauseMap.card_of_add, Hcardold.
                 reflexivity.
              ** intros v Hin. apply ClauseMap.find_add in Hin as [[Hv _]|Hin].
                 --- subst v.
                     destruct (Hdetached_valid model Hsuffix Hunsat Htwo)
                       as [Heq|Hu]; [contradiction|].
                     destruct falsified; cbn; [exact Hu|].
                     rewrite literal_is_undecided_pos_neg. exact Hu.
                 --- now apply (Hstagedvalid model Hsuffix Hunsat Htwo).
    + eapply drop_decided_zero_inv; [exact Hfind|exact Hnoopp| | |exact Hinv].
      * eapply detached_unit_card_zero; eauto.
      * right. right. exists c. split; [exact Hfind|].
        apply Is_true_eq_left. exact Htrue.
  }
  rewrite Hrestore in Hcm'. subst cm'. split.
  - intros d Hd. destruct (Hdetached d (or_intror Hd)) as
      [body [Hbody [Hdetachedin Hvalid]]].
    exists body. cbn [find_clause state_trail].
    split; [exact Hbody|]. split; [exact Hdetachedin|].
    destruct Hvalid as [Htwo Hneeded]. split; [exact Htwo|].
    intros model Hsuffix p Hpu Hneeds.
    destruct (Hneeded model Hsuffix p Hpu Hneeds)
      as [Heq|[Hvar|Hwatched']]; [now left|now right; left|].
    right. right. apply ClauseMap.find_add. now right.
  - eapply detached_clause_arity_add; eauto.
Qed.

Lemma propagate_conflict_scan_inv :
  forall work falsified ci c clauses learned m cm pending cm',
  find_clause_in clauses learned ci = Some c ->
  In falsified c ->
  ~ In ci (ClauseMap.find (literal_var falsified) cm) ->
  staged_invariant_with (Some falsified) (ci :: work)
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  scan_clause m falsified ci c cm = clause_conflict cm' ->
  staged_invariant_with (Some falsified) work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm'; state_pending := pending |}.
Proof.
  intros work falsified ci c clauses learned m cm pending cm'
    Hfind Hfalsified Hfresh [Hinv [Hdetached Harity]] Hscan.
  pose proof Hinv as Hlookup.
  destruct Hlookup as [_ [_ [_ [_ [_ [Hworklookup _]]]]]].
  destruct (Hworklookup ci (or_introl eq_refl))
    as [body [Hbody [Hnoopp Hstagedvalid]]].
  change (find_clause_in clauses learned ci = Some body) in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  destruct (Hdetached ci (or_introl eq_refl)) as
    [detached_body [Hdetached_body
      [Hdetached_in [Hdetached_valid Hdetached_needed]]]].
  change (find_clause_in clauses learned ci = Some detached_body)
    in Hdetached_body.
  rewrite Hfind in Hdetached_body. injection Hdetached_body as <-.
  pose proof Hinv as Hworkfacts.
  destruct Hworkfacts as [_ [_ [_ [_ [_ [_ [_ [Hworkcard _]]]]]]]].
  specialize (Hworkcard ci (or_introl eq_refl)).
  unfold card_of_watch in Hworkcard. cbn [state_watched] in Hworkcard.
  assert (Hnotin : ~ In ci work).
  { unfold staged_invariant in Hinv.
    destruct Hinv as [_ [_ [_ [_ [Hnodup _]]]]].
    now inversion Hnodup. }
  destruct (proj1 (Harity ci c Hfind Hnoopp) (or_introl eq_refl))
    as [Htwo_variables Hdetached_card].
  destruct (two_variables_find_different falsified c Hfalsified Htwo_variables)
    as [other Hdifferent_exists].
  assert (Hrestore : restore_detached_watch falsified ci c cm =
      ClauseMap.add falsified ci cm).
  { unfold restore_detached_watch. now rewrite Hdifferent_exists. }
  destruct (scan_clause_conflict_spec m falsified ci c cm cm' Hscan)
    as [Hfalse [Hdecided Hcm']].
  split.
  {
  rewrite Hcm'. unfold restore_detached_watch.
    destruct (find_different_var (literal_var falsified) c) eqn:Hdifferent.
    + eapply watch_one_fresh_inv; try eassumption.
      split.
      * intros model Hsuffix p Hpu Hneeds.
        destruct (Hdetached_needed model Hsuffix p Hpu Hneeds)
          as [Heq|[Hvar|Hwatched]].
        -- subst model. exfalso.
           destruct Hneeds as [Hpc _].
           assert (In p (filter (literal_is_undecided (trail_model m)) c)).
           { apply filter_In. now split. }
           rewrite Hdecided in H. contradiction.
        -- apply ClauseMap.find_add. now left.
        -- apply ClauseMap.find_add. now right.
      * intros Hcardout. unfold follows_two_undecided.
        intros model Hsuffix Hunsat Htwo.
        destruct (list_eq_dec literal_eq_dec model (trail_model m))
          as [Heq|Hneqmodel].
        -- subst model. exfalso.
           destruct Htwo as [x [y [Hxc [Hyc [Hxy [Hxu Hyu]]]]]].
           assert (In x (filter (literal_is_undecided (trail_model m)) c)).
           { apply filter_In. now split. }
           rewrite Hdecided in H. contradiction.
        -- assert (Hcardold : ClauseMap.card_of ci cm = 1).
           { destruct Hworkcard as [Hone|[Hzero _]]; [exact Hone|].
             exfalso. apply Hcardout.
             rewrite ClauseMap.card_of_add, Hzero. reflexivity. }
           split.
           ++ cbn [state_watched]. rewrite ClauseMap.card_of_add, Hcardold.
              reflexivity.
           ++ intros v Hin. apply ClauseMap.find_add in Hin as [[Hv _]|Hin].
              ** subst v.
                 destruct (Hdetached_valid model Hsuffix Hunsat Htwo)
                   as [Heq|Hu]; [contradiction|].
                 destruct falsified; cbn; [exact Hu|].
                 rewrite literal_is_undecided_pos_neg. exact Hu.
              ** now apply (Hstagedvalid model Hsuffix Hunsat Htwo).
    + eapply drop_decided_zero_inv; [exact Hfind|exact Hnoopp| | |exact Hinv].
      * eapply detached_unit_card_zero; eauto.
      * right. left. exists c. split; [exact Hfind|]. split.
        -- apply Is_true_eq_left. now apply Bool.negb_true_iff.
        -- exact Hdecided.
  }
  rewrite Hrestore in Hcm'. subst cm'. split.
  - intros d Hd. destruct (Hdetached d (or_intror Hd)) as
      [body [Hbody [Hdetachedin Hvalid]]].
    exists body. cbn [find_clause state_trail].
    split; [exact Hbody|]. split; [exact Hdetachedin|].
    destruct Hvalid as [Htwo Hneeded]. split; [exact Htwo|].
    intros model Hsuffix p Hpu Hneeds.
    destruct (Hneeded model Hsuffix p Hpu Hneeds)
      as [Heq|[Hvar|Hwatched']]; [now left|now right; left|].
    right. right. apply ClauseMap.find_add. now right.
  - eapply detached_clause_arity_add; eauto.
Qed.

Lemma propagate_progress_inv : forall falsified ci work s s',
  (exists c, find_clause ci s = Some c /\ In falsified c) ->
  ~ In ci (ClauseMap.find (literal_var falsified) s.(state_watched)) ->
  staged_invariant_with (Some falsified) (ci :: work) s ->
  propagate falsified ci s = Progress s' ->
  staged_invariant_with (Some falsified) work s'.
Proof.
  intros falsified ci work [m clauses learned cm pending] s'
    [watched [Hwatchedfind Hfalsified]] Hfresh Hinv Hpropagate.
  pose proof Hinv as Hlookup.
  destruct Hlookup as [Hlookup _].
  destruct Hlookup as [_ [_ [_ [_ [_ [Hworkref _]]]]]].
  destruct (Hworkref ci (or_introl eq_refl)) as [c [Hfind [Hnoopp _]]].
  change (find_clause_in clauses learned ci = Some c) in Hfind.
  change (find_clause_in clauses learned ci = Some watched) in Hwatchedfind.
  rewrite Hfind in Hwatchedfind. injection Hwatchedfind as <-.
  unfold propagate, find_clause in Hpropagate.
  cbn -[find_clause_in] in Hinv, Hpropagate |- *.
  rewrite Hfind in Hpropagate.
  destruct (scan_clause (map trail_literal m) falsified ci c cm)
    as [l cm'|cm'|cm'|cm'] eqn:Hscan.
  - injection Hpropagate as <-. eapply propagate_literal_inv;
      [exact Hfind|exact Hfalsified|exact Hfresh|exact Hinv|exact Hscan].
  - discriminate.
  - injection Hpropagate as <-. eapply propagate_decided_inv;
      [exact Hfind|exact Hfalsified|exact Hfresh|exact Hinv|exact Hscan].
  - injection Hpropagate as <-.
    pose proof (scan_clause_watched_spec _ _ _ _ _ _ Hscan) as
    [l [l' [Hunsat [Hlc [Hl'c [Hlu [Hl'u [Hneq Hcm']]]]]]]].
    split.
    + eapply watch_one_inv.
      * exact Hfind.
      * exact Hnoopp.
      * exact (proj1 Hinv).
      * exact Hlc.
      * exact Hl'c.
      * exact Hlu.
      * exact Hl'u.
      * exact Hneq.
      * apply Is_true_eq_left. apply Bool.negb_true_iff. exact Hunsat.
      * exact Hcm'.
    + destruct (proj2 Hinv) as [Hdetached Harity]. split.
      * intros d Hd. destruct (Hdetached d (or_intror Hd)) as
          [body [Hbody [Hdetachedin Hvalid]]].
        exists body. cbn [find_clause state_trail].
        split; [exact Hbody|]. split; [exact Hdetachedin|].
        destruct Hvalid as [Htwo Hneeded]. split; [exact Htwo|].
        intros model Hsuffix p Hpu Hneeds.
        destruct (Hneeded model Hsuffix p Hpu Hneeds)
          as [Heq|[Hvar|Hwatched']]; [now left|now right; left|].
        right. right. rewrite Hcm'.
        destruct (in_dec clause_pointer_eq_dec ci
          (ClauseMap.find (literal_var l) cm));
          apply ClauseMap.find_add; now right.
      * assert (Hnotin : ~ In ci work).
        { pose proof (proj1 Hinv) as Hstaged.
          unfold staged_invariant in Hstaged.
          destruct Hstaged as [_ [_ [_ [_ [Hnodup _]]]]].
          now inversion Hnodup. }
        rewrite Hcm'. destruct (in_dec clause_pointer_eq_dec ci
          (ClauseMap.find (literal_var l) cm));
          eapply detached_clause_arity_add; eauto.
Qed.

Lemma propagate_conflict_staged_inv : forall falsified ci work s s' cause,
  (exists c, find_clause ci s = Some c /\ In falsified c) ->
  ~ In ci (ClauseMap.find (literal_var falsified) s.(state_watched)) ->
  staged_invariant_with (Some falsified) (ci :: work) s ->
  propagate falsified ci s = Conflict s' cause ->
  staged_invariant_with (Some falsified) work s'.
Proof.
  intros falsified ci work [m clauses learned cm pending] s' cause
    [watched [Hwatchedfind Hfalsified]] Hfresh Hinv Hpropagate.
  pose proof Hinv as Hlookup. destruct Hlookup as [Hlookup _].
  destruct Hlookup as [_ [_ [_ [_ [_ [Hworkref _]]]]]].
  destruct (Hworkref ci (or_introl eq_refl)) as [c [Hfind [Hnoopp _]]].
  change (find_clause_in clauses learned ci = Some c) in Hfind.
  change (find_clause_in clauses learned ci = Some watched) in Hwatchedfind.
  rewrite Hfind in Hwatchedfind. injection Hwatchedfind as <-.
  unfold propagate, find_clause in Hpropagate.
  cbn -[find_clause_in] in Hinv, Hpropagate |- *.
  rewrite Hfind in Hpropagate.
  destruct (scan_clause (map trail_literal m) falsified ci c cm)
    as [l cm'|cm'|cm'|cm'] eqn:Hscan; try discriminate.
  injection Hpropagate as <- <-.
  eapply propagate_conflict_scan_inv; eauto.
Qed.

Lemma propagate_learned_inv : forall falsified ci s s',
  learned_invariant s ->
  propagate falsified ci s = Progress s' ->
  learned_invariant s'.
Proof.
  intros falsified ci [m clauses learned cm pending] s' Hlearned Hpropagate.
  unfold propagate, find_clause in Hpropagate. cbn -[find_clause_in] in Hpropagate.
  destruct (find_clause_in clauses learned ci) as [c|].
  - destruct (scan_clause (map trail_literal m) falsified ci c cm);
      try discriminate; injection Hpropagate as <-; exact Hlearned.
  - injection Hpropagate as <-. exact Hlearned.
Qed.

Lemma propagate_conflict_learned_inv : forall falsified ci s s' cause,
  learned_invariant s ->
  propagate falsified ci s = Conflict s' cause ->
  learned_invariant s'.
Proof.
  intros falsified ci [m clauses learned cm pending] s' cause
    Hlearned Hpropagate.
  unfold propagate, find_clause in Hpropagate. cbn -[find_clause_in] in Hpropagate.
  destruct (find_clause_in clauses learned ci) as [c|]; [|discriminate].
  destruct (scan_clause (map trail_literal m) falsified ci c cm);
    try discriminate; injection Hpropagate as <- <-; exact Hlearned.
Qed.

Lemma find_add_other_pointer : forall cm l ci d v,
  d <> ci ->
  In d (ClauseMap.find v (ClauseMap.add l ci cm)) <->
  In d (ClauseMap.find v cm).
Proof.
  intros cm l ci d v Hneq. rewrite ClauseMap.find_add.
  split; intros H.
  - destruct H as [[_ Heq]|H]; [congruence|exact H].
  - now right.
Qed.

Lemma propagate_other_watch : forall falsified ci d s s' v,
  d <> ci ->
  propagate falsified ci s = Progress s' ->
  In d (ClauseMap.find v s'.(state_watched)) <->
  In d (ClauseMap.find v s.(state_watched)).
Proof.
  intros falsified ci d [m clauses learned cm pending] s' v Hneq Hpropagate.
  unfold propagate, find_clause in Hpropagate. cbn -[find_clause_in] in Hpropagate.
  destruct (find_clause_in clauses learned ci) as [c|].
  2:{ injection Hpropagate as <-. reflexivity. }
  unfold scan_clause in Hpropagate.
  destruct (scan_clause_once (map trail_literal m) c)
    as [satisfied undecided].
  destruct satisfied.
  - unfold restore_detached_watch in Hpropagate.
    destruct (find_different_var (literal_var falsified) c);
      injection Hpropagate as <-;
      cbn [state_watched];
      [apply find_add_other_pointer; exact Hneq|reflexivity].
  - destruct undecided as [|l undecided].
    + discriminate.
    + destruct (find_different_var (literal_var l) undecided).
      * destruct (in_dec clause_pointer_eq_dec ci
          (ClauseMap.find (literal_var l) cm)); injection Hpropagate as <-;
          cbn [state_watched];
          apply find_add_other_pointer; exact Hneq.
      * destruct (in_dec clause_pointer_eq_dec ci
          (ClauseMap.find (literal_var l) cm)).
        -- unfold restore_detached_watch in Hpropagate.
           destruct (find_different_var (literal_var falsified) c);
             injection Hpropagate as <-;
             cbn [state_watched];
             [apply find_add_other_pointer; exact Hneq|reflexivity].
        -- injection Hpropagate as <-. cbn [state_watched].
           apply find_add_other_pointer. exact Hneq.
Qed.

Lemma propagate_conflict_other_watch : forall falsified ci d s s' cause v,
  d <> ci ->
  propagate falsified ci s = Conflict s' cause ->
  In d (ClauseMap.find v s'.(state_watched)) <->
  In d (ClauseMap.find v s.(state_watched)).
Proof.
  intros falsified ci d [m clauses learned cm pending] s' cause v
    Hneq Hpropagate.
  unfold propagate, find_clause in Hpropagate. cbn -[find_clause_in] in Hpropagate.
  destruct (find_clause_in clauses learned ci) as [c|]; [|discriminate].
  destruct (scan_clause (map trail_literal m) falsified ci c cm)
    as [l cm'|cm'|cm'|cm'] eqn:Hscan; try discriminate.
  injection Hpropagate as <- <-. cbn [state_watched].
  pose proof (scan_clause_conflict_spec _ _ _ _ _ _ Hscan)
    as [_ [_ ->]].
  unfold restore_detached_watch.
  destruct (find_different_var (literal_var falsified) c);
    [apply find_add_other_pointer; exact Hneq|reflexivity].
Qed.

Lemma propagate_find_clause : forall falsified ci s s' d,
  propagate falsified ci s = Progress s' ->
  find_clause d s' = find_clause d s.
Proof.
  intros falsified ci [m clauses learned cm pending] s' d Hpropagate.
  unfold propagate, find_clause in Hpropagate |- *. cbn -[find_clause_in] in *.
  destruct (find_clause_in clauses learned ci) as [c|].
  - destruct (scan_clause (map trail_literal m) falsified ci c cm);
      try discriminate; now injection Hpropagate as <-.
  - now injection Hpropagate as <-.
Qed.

Lemma propagate_conflict_find_clause : forall falsified ci s s' cause d,
  propagate falsified ci s = Conflict s' cause ->
  find_clause d s' = find_clause d s.
Proof.
  intros falsified ci [m clauses learned cm pending] s' cause d Hpropagate.
  unfold propagate, find_clause in Hpropagate |- *. cbn -[find_clause_in] in *.
  destruct (find_clause_in clauses learned ci) as [c|]; [|discriminate].
  destruct (scan_clause (map trail_literal m) falsified ci c cm);
    try discriminate; now injection Hpropagate as <- <-.
Qed.

Lemma propagate_clauses_inv : forall falsified work s s',
  NoDup work ->
  (forall ci, In ci work ->
    exists c, find_clause ci s = Some c /\ In falsified c) ->
  (forall ci, In ci work ->
    ~ In ci (ClauseMap.find (literal_var falsified) s.(state_watched))) ->
  staged_invariant_with (Some falsified) work s ->
  learned_invariant s ->
  propagate_clauses falsified work s = Progress s' ->
  state_invariant s'.
Proof.
  intros falsified work. induction work as [|ci work IH];
    intros s s' Hnodup Hcontains Hfresh Hinv Hlearned Hpropagates.
  - injection Hpropagates as <-. destruct Hinv as [Hstaged [_ Harity]].
    split; [exact Hstaged|]. split; [exact Hlearned|].
    intros d c Hfind _ Hnoopp.
    exact (proj2 (Harity d c Hfind Hnoopp) ltac:(simpl; tauto)).
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    cbn [propagate_clauses] in Hpropagates.
    destruct (propagate falsified ci s) as [next|conflict cause]
      eqn:Hpropagate.
    2:{ destruct (propagate_clauses falsified work conflict); discriminate. }
    eapply IH with (s := next).
    + exact Hnodup'.
    + intros d Hd. destruct (Hcontains d (or_intror Hd)) as [c [Hfind Hin]].
      exists c. split; [|exact Hin].
      now rewrite (propagate_find_clause falsified ci s next d Hpropagate).
    + intros d Hd Hin.
      apply (Hfresh d (or_intror Hd)).
      assert (d <> ci) as Hneq by (intros ->; contradiction).
      apply (proj1 (propagate_other_watch falsified ci d s next
        (literal_var falsified) Hneq Hpropagate)).
      exact Hin.
    + eapply propagate_progress_inv.
      * exact (Hcontains ci (or_introl eq_refl)).
      * exact (Hfresh ci (or_introl eq_refl)).
      * exact Hinv.
      * exact Hpropagate.
    + eapply propagate_learned_inv; [exact Hlearned|exact Hpropagate].
    + exact Hpropagates.
Qed.

Lemma propagate_clauses_conflict_inv : forall falsified work s s' cause,
  NoDup work ->
  (forall ci, In ci work ->
    exists c, find_clause ci s = Some c /\ In falsified c) ->
  (forall ci, In ci work ->
    ~ In ci (ClauseMap.find (literal_var falsified) s.(state_watched))) ->
  staged_invariant_with (Some falsified) work s ->
  learned_invariant s ->
  propagate_clauses falsified work s = Conflict s' cause ->
  state_invariant s'.
Proof.
  intros falsified work. induction work as [|ci work IH];
    intros s s' cause Hnodup Hcontains Hfresh Hinv Hlearned Hpropagates.
  - discriminate.
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    cbn [propagate_clauses] in Hpropagates.
    destruct (propagate falsified ci s) as [next|conflict firstcause]
      eqn:Hpropagate.
    + eapply IH with (s := next).
      * exact Hnodup'.
      * intros d Hd. destruct (Hcontains d (or_intror Hd)) as [c [Hfind Hin]].
        exists c. split; [|exact Hin].
        now rewrite (propagate_find_clause falsified ci s next d Hpropagate).
      * intros d Hd Hin.
        apply (Hfresh d (or_intror Hd)).
        assert (d <> ci) as Hneq by (intros ->; contradiction).
        apply (proj1 (propagate_other_watch falsified ci d s next
          (literal_var falsified) Hneq Hpropagate)). exact Hin.
      * eapply propagate_progress_inv.
        -- exact (Hcontains ci (or_introl eq_refl)).
        -- exact (Hfresh ci (or_introl eq_refl)).
        -- exact Hinv.
        -- exact Hpropagate.
      * eapply propagate_learned_inv; [exact Hlearned|exact Hpropagate].
      * exact Hpropagates.
    + assert (Hconflictinv : staged_invariant_with (Some falsified) work conflict).
      { eapply propagate_conflict_staged_inv.
        - exact (Hcontains ci (or_introl eq_refl)).
        - exact (Hfresh ci (or_introl eq_refl)).
        - exact Hinv.
        - exact Hpropagate. }
      assert (Hconflictlearned : learned_invariant conflict).
      { eapply propagate_conflict_learned_inv; [exact Hlearned|exact Hpropagate]. }
      assert (Hconflictcontains : forall d, In d work ->
          exists c, find_clause d conflict = Some c /\ In falsified c).
      { intros d Hd. destruct (Hcontains d (or_intror Hd)) as [c [Hfind Hin]].
        exists c. split; [|exact Hin].
        now rewrite (propagate_conflict_find_clause falsified ci s conflict
          firstcause d Hpropagate). }
      assert (Hconflictfresh : forall d, In d work ->
          ~ In d (ClauseMap.find (literal_var falsified)
            conflict.(state_watched))).
      { intros d Hd Hin. apply (Hfresh d (or_intror Hd)).
        assert (d <> ci) as Hneq by (intros ->; contradiction).
        apply (proj1 (propagate_conflict_other_watch falsified ci d s conflict
          firstcause (literal_var falsified) Hneq Hpropagate)). exact Hin. }
      destruct (propagate_clauses falsified work conflict)
        as [final|final latercause] eqn:Hrest.
      * injection Hpropagates as <- <-.
        eapply propagate_clauses_inv; eauto.
      * injection Hpropagates as <- <-.
        eapply IH; eauto.
Qed.

Lemma prepare_set_lit_inv : forall l (m : Trail) clauses learned cm pending,
  literal_is_undecided m l = true ->
  state_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |} ->
  let work := ClauseMap.find_falsified l cm in
  let falsified := opposite_literal l in
  staged_invariant_with (Some falsified) work
    {| state_trail := Decision l :: m; state_clauses := clauses;
       state_learned := learned;
       state_watched := ClauseMap.clear_falsified l cm;
       state_pending := pending |} /\
  (forall ci, In ci work ->
     exists c, find_clause_in clauses learned ci = Some c /\
       In falsified c) /\
  (forall ci, In ci work ->
     ~ In ci (ClauseMap.find (literal_var falsified)
       (ClauseMap.clear_falsified l cm))).
Proof.
  intros l m clauses learned cm pending Hlu Hstateinv.
  pose proof Hstateinv as Hfullinv.
  destruct Hstateinv as [Hinv [Hlearned Harity]].
  cbn zeta.
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [_ [_ [Hpending [_ [Hcard Htrail]]]]]]]]].
  assert (Hworknodup : NoDup (ClauseMap.find_falsified l cm)).
  { destruct l; apply Hnodup. }
  assert (Hworkref : forall d, In d (ClauseMap.find_falsified l cm) ->
      exists body, find_clause_in clauses learned d = Some body /\
        ~ has_opposite_literals body /\ In (opposite_literal l) body).
  { intros d Hd. pose proof (ClauseMap.find_falsified_in l cm d Hd) as Hall.
    destruct (Hwatch (literal_var l) d Hall) as
      [body [Hbody [_ [Hinc [Hnoopp [Hpos Hneg]]]]]].
    exists body. split; [exact Hbody|]. split; [exact Hnoopp|].
    destruct l as [v|v]; [now apply Hneg|now apply Hpos]. }
  assert (Hfresh : forall d, In d (ClauseMap.find_falsified l cm) ->
      ~ In d (ClauseMap.find (literal_var (opposite_literal l))
        (ClauseMap.clear_falsified l cm))).
  { intros d Hd Hremaining.
    destruct (Hworkref d Hd) as [body [Hbody [Hnoopp Hfalsewatch]]].
    destruct l as [v|v].
    - change (In d (ClauseMap.find v
        (ClauseMap.clear_literal (Neg v) cm))) in Hremaining.
      unfold ClauseMap.find in Hremaining.
      rewrite ClauseMap.find_pos_clear_neg,
        ClauseMap.find_neg_clear_neg in Hremaining.
      destruct (VarKey.eq_dec v v) as [_|Habs]; [|contradiction].
      rewrite app_nil_r in Hremaining.
      destruct (Hwatch v d (in_or_app _ _ _ (or_introl Hremaining)))
        as [body' [Hbody' [_ [_ [_ [Hpos _]]]]]].
      change (find_clause_in clauses learned d = Some body') in Hbody'.
      rewrite Hbody in Hbody'. injection Hbody' as <-.
      apply Hnoopp. exists v. split; [now apply Hpos|exact Hfalsewatch].
    - change (In d (ClauseMap.find v
        (ClauseMap.clear_literal (Pos v) cm))) in Hremaining.
      unfold ClauseMap.find in Hremaining.
      rewrite ClauseMap.find_pos_clear_pos,
        ClauseMap.find_neg_clear_pos in Hremaining.
      destruct (VarKey.eq_dec v v) as [_|Habs]; [|contradiction].
      cbn in Hremaining.
      destruct (Hwatch v d (in_or_app _ _ _ (or_intror Hremaining)))
        as [body' [Hbody' [_ [_ [_ [_ Hneg]]]]]].
      change (find_clause_in clauses learned d = Some body') in Hbody'.
      rewrite Hbody in Hbody'. injection Hbody' as <-.
      apply Hnoopp. exists v. split; [exact Hfalsewatch|now apply Hneg]. }
  split.
  - split.
    { repeat split.
    + intros d body Hbody Hfalse.
      change (find_clause_in clauses learned d = Some body) in Hbody.
      assert (Holdfalse :
        Is_true (negb (existsb (literal_is_true m) body))).
      { apply negb_prop_intro. intros Holdtrue.
        apply (negb_prop_elim _ Hfalse).
        now apply satisfied_cons_undecided. }
      specialize (Hcover d body Hbody Holdfalse).
      destruct Hcover as [Hopp|[Habs|[[[v Hin] Hnonempty]|Hd]]].
      * now left.
      * contradiction.
      * destruct (Id.eq_dec (literal_var l) v) as [Heq|Hneq].
        -- subst v. destruct (Hwatch (literal_var l) d Hin) as
             [body' [Hbody' [_ [_ [_ [Hpos Hneg]]]]]].
           change (find_clause_in clauses learned d = Some body) in Hbody.
           change (find_clause_in clauses learned d = Some body') in Hbody'.
           rewrite Hbody in Hbody'. injection Hbody' as <-.
           destruct l as [w|w]; unfold ClauseMap.find in Hin;
             apply in_app_or in Hin as [Htrue|Hfalsebucket].
           ++ exfalso. apply (negb_prop_elim _ Hfalse).
              apply Is_true_eq_left, existsb_exists. exists (Pos w).
              split; [now apply Hpos|apply literal_is_true_cons_self].
           ++ now right; left.
           ++ now right; left.
           ++ exfalso. apply (negb_prop_elim _ Hfalse).
              apply Is_true_eq_left, existsb_exists. exists (Neg w).
              split; [now apply Hneg|apply literal_is_true_cons_self].
        -- destruct (filter
             (literal_is_undecided (trail_model (Decision l :: m))) body)
             as [|p ps] eqn:Hnewdec.
           ++ right; left.
              destruct (Hwatch v d Hin) as
                [body' [Hbody' [Hfollow [_ [Hnoopp [Hpos Hneg]]]]]].
              change (find_clause_in clauses learned d = Some body) in Hbody.
              change (find_clause_in clauses learned d = Some body') in Hbody'.
              rewrite Hbody in Hbody'. injection Hbody' as <-.
              assert (Hneeds : clause_needs_literal m (opposite_literal l) body).
              { eapply newly_falsified_needs_opposite; eauto. }
              assert (Hoppu : literal_is_undecided m (opposite_literal l) = true).
              { destruct l as [w|w]; cbn.
                - rewrite <- literal_is_undecided_pos_neg. exact Hlu.
                - rewrite literal_is_undecided_pos_neg. exact Hlu. }
              destruct (Hfollow (fun H => H)) as [Hfollow' _].
              specialize (Hfollow' m (model_suffix_refl m)
                (opposite_literal l) Hoppu Hneeds).
              destruct Hneeds as [Hoppin _].
              destruct l as [w|w]; unfold ClauseMap.find in Hfollow';
                apply in_app_or in Hfollow' as [Hpositive|Hnegative].
              ** assert (Hposin : In (Pos w) body).
                 { destruct (Hwatch w d (in_or_app _ _ _ (or_introl Hpositive)))
                     as [body' [Hbody' [_ [_ [_ [Hpos' _]]]]]].
                   change (find_clause_in clauses learned d = Some body') in Hbody'.
                   rewrite Hbody in Hbody'. injection Hbody' as <-.
                   now apply Hpos'. }
                 exfalso. apply Hnoopp. exists w. now split.
              ** exact Hnegative.
              ** exact Hpositive.
              ** assert (Hnegin : In (Neg w) body).
                 { destruct (Hwatch w d (in_or_app _ _ _ (or_intror Hnegative)))
                     as [body' [Hbody' [_ [_ [_ [_ Hneg']]]]]].
                   change (find_clause_in clauses learned d = Some body') in Hbody'.
                   rewrite Hbody in Hbody'. injection Hbody' as <-.
                   now apply Hneg'. }
                 exfalso. apply Hnoopp. exists w. now split.
           ++ right; right; left. split.
              ** exists v.
                 change (In d (ClauseMap.find v
                   (ClauseMap.clear_literal (opposite_literal l) cm))).
                 rewrite ClauseMap.find_clear_literal_other.
                 --- exact Hin.
                 --- destruct l; exact Hneq.
              ** cbn [state_trail]. rewrite Hnewdec. discriminate.
      * right; right; right. destruct Hd as [Hdfalse|Hdpending].
        -- left. destruct Hdfalse as [body' [Hbody' Holdsem]].
           change (find_clause_in clauses learned d = Some body') in Hbody'.
           rewrite Hbody in Hbody'. injection Hbody' as <-.
           exists body. split; [exact Hbody|]. split; [exact Hfalse|].
           exact (proj2 (falsified_cons_undecided m l body Hlu Holdsem)).
        -- now right.
    + intros d Hd. exact Hd.
    + intros v d Hin.
      pose proof (ClauseMap.find_clear_literal_in cm (opposite_literal l)
        v d Hin) as Hold.
      destruct (Hwatch v d Hold) as
        [body [Hbody [Hstable [Hinc [Hnoopp [Hpos Hneg]]]]]].
      change (find_clause_in clauses learned d = Some body) in Hbody.
      exists body. split; [exact Hbody|]. split.
      * intros Hdnotwork.
        destruct (Hstable (fun H => H)) as [Hunit Holdtwo].
        assert (Hcountzero : count_occ clause_pointer_eq_dec
            (ClauseMap.find_literal (opposite_literal l) cm) d = 0).
        { apply count_occ_not_In. destruct l; exact Hdnotwork. }
        assert (Hcardeq : ClauseMap.card_of d
            (ClauseMap.clear_falsified l cm) = ClauseMap.card_of d cm).
        { pose proof (ClauseMap.card_of_clear_literal cm d
              (opposite_literal l)) as Hclear.
          change (ClauseMap.card_of d (ClauseMap.clear_falsified l cm) +
            count_occ clause_pointer_eq_dec
              (ClauseMap.find_literal (opposite_literal l) cm) d =
            ClauseMap.card_of d cm) in Hclear.
          lia. }
        split.
        -- intros suffix Hsuffix p Hpu Hneeds.
           destruct (model_suffix_cons_cases suffix l (trail_model m) Hsuffix)
             as [Heqmodel|Holdsuffix].
           2:{ pose proof (Hunit suffix Holdsuffix p Hpu Hneeds) as Holdp.
              change (In d (ClauseMap.find (literal_var p)
                (ClauseMap.clear_literal (opposite_literal l) cm))).
              destruct (Id.eq_dec (literal_var (opposite_literal l))
                (literal_var p)) as [Heq|Hneq].
              - destruct l as [w|w].
                + cbn in Heq. change (In d (ClauseMap.find (literal_var p)
                    (ClauseMap.clear_literal (Neg w) cm))).
                  rewrite <- Heq, ClauseMap.find_clear_neg_eq.
                  rewrite <- Heq in Holdp.
                  unfold ClauseMap.find in Holdp.
                  apply in_app_or in Holdp as [Hposp|Hnegp];
                    [exact Hposp|contradiction].
                + cbn in Heq. change (In d (ClauseMap.find (literal_var p)
                    (ClauseMap.clear_literal (Pos w) cm))).
                  rewrite <- Heq, ClauseMap.find_clear_pos_eq.
                  rewrite <- Heq in Holdp.
                  unfold ClauseMap.find in Holdp.
                  apply in_app_or in Holdp as [Hposp|Hnegp];
                    [contradiction|exact Hnegp].
              - rewrite ClauseMap.find_clear_literal_other; [exact Holdp|].
                now intros Heq; apply Hneq. }
           subst suffix.
           assert (Hnewunsat : Is_true (negb (existsb
               (literal_is_true (trail_model (Decision l :: m))) body))).
           { apply negb_prop_intro. intros Hsat.
             eapply satisfied_not_needs_undecided;
               [exact Hsat|exact Hpu|exact Hneeds]. }
           assert (Hpneq : literal_var l <> literal_var p).
           { now apply undecided_cons_inv in Hpu as [Hpneq _]. }
           destruct (in_dec literal_eq_dec (opposite_literal l) body)
             as [Hopin|Hopnotin].
           ++ assert (Holdu : literal_is_undecided (trail_model m) p = true).
              { exact (proj2 (undecided_cons_inv _ _ _ Hpu)). }
              assert (Hopu : literal_is_undecided (trail_model m)
                  (opposite_literal l) = true).
              { destruct l as [w|w]; cbn.
                - now rewrite <- literal_is_undecided_pos_neg.
                - now rewrite literal_is_undecided_pos_neg. }
              assert (Htwoold : clause_has_two_undecided
                  (trail_model m) body).
              { exists p, (opposite_literal l). repeat split.
                - exact (proj1 Hneeds).
                - exact Hopin.
                - intros Heq. apply Hpneq. destruct l; cbn in Heq |- *;
                    symmetry; exact Heq.
                - exact Holdu.
                - exact Hopu. }
              assert (Holdunsat : Is_true (negb
                  (existsb (literal_is_true (trail_model m)) body))).
              { eapply unsatisfied_cons_inv; [exact Hlu|exact Hnewunsat]. }
              assert (Holdcard : ClauseMap.card_of d cm = 2).
              { pose proof (unsatisfied_two_watched_card_two
                    {| state_trail := m; state_clauses := clauses;
                       state_learned := learned; state_watched := cm;
                       state_pending := pending |}
                    d body Hfullinv Hbody Holdunsat Htwoold
                    (ex_intro _ v Hold)) as Hcardtwo.
                exact Hcardtwo. }
              assert (Holdcardneq : ClauseMap.card_of d cm <> 1) by lia.
              destruct (Holdtwo Holdcardneq (trail_model m)
                  (model_suffix_refl _) Holdunsat Htwoold)
                as [_ Hallold].
              assert (Hpositive : ClauseMap.card_of d cm > 0) by lia.
              destruct (ClauseMap.card_of_pos cm d Hpositive) as [q Hq].
              assert (Hql : literal_var l <> q).
              { intros Heq. rewrite <- Heq in Hq. destruct l as [w|w];
                  unfold ClauseMap.find in Hq; apply in_app_or in Hq as [Hqp|Hqn].
                - destruct (Hwatch w d (in_or_app _ _ _ (or_introl Hqp))) as
                    [body' [Hbody' [_ [_ [_ [Hpos' _]]]]]].
                  change (find_clause_in clauses learned d = Some body') in Hbody'.
                  rewrite Hbody in Hbody'. injection Hbody' as <-.
                  apply (negb_prop_elim _ Hnewunsat).
                  apply Is_true_eq_left, existsb_exists. exists (Pos w).
                  split; [now apply Hpos'|apply literal_is_true_cons_self].
                - apply Hdnotwork. exact Hqn.
                - apply Hdnotwork. exact Hqp.
                - destruct (Hwatch w d (in_or_app _ _ _ (or_intror Hqn))) as
                    [body' [Hbody' [_ [_ [_ [_ Hneg']]]]]].
                  change (find_clause_in clauses learned d = Some body') in Hbody'.
                  rewrite Hbody in Hbody'. injection Hbody' as <-.
                  apply (negb_prop_elim _ Hnewunsat).
                  apply Is_true_eq_left, existsb_exists. exists (Neg w).
                  split; [now apply Hneg'|apply literal_is_true_cons_self]. }
              destruct (Hwatch q d Hq) as
                [body' [Hbody' [_ [Hinq _]]]].
              change (find_clause_in clauses learned d = Some body') in Hbody'.
              rewrite Hbody in Hbody'. injection Hbody' as <-.
              destruct Hinq as [Hinq|Hinq].
              ** assert (Hqu : literal_is_undecided
                    (trail_model (Decision l :: m)) (Pos q) = true).
                 { apply undecided_cons_other_var; [exact Hql|].
                   exact (Hallold q Hq). }
                 pose proof (clause_needs_literal_unique _ _ (Pos q) p
                   Hinq Hqu Hneeds) as Heq.
                 pose proof (f_equal literal_var Heq) as Hqeq. cbn in Hqeq.
                 
                 subst q. change (In d (ClauseMap.find (literal_var p)
                   (ClauseMap.clear_literal (opposite_literal l) cm))).
                 rewrite ClauseMap.find_clear_literal_other.
                 --- exact Hq.
                 --- destruct l; exact Hpneq.
              ** assert (Hqu : literal_is_undecided
                    (trail_model (Decision l :: m)) (Neg q) = true).
                 { rewrite <- literal_is_undecided_pos_neg.
                   apply undecided_cons_other_var; [exact Hql|].
                   exact (Hallold q Hq). }
                 pose proof (clause_needs_literal_unique _ _ (Neg q) p
                   Hinq Hqu Hneeds) as Heq.
                 pose proof (f_equal literal_var Heq) as Hqeq. cbn in Hqeq.
                 subst q. change (In d (ClauseMap.find (literal_var p)
                   (ClauseMap.clear_literal (opposite_literal l) cm))).
                 rewrite ClauseMap.find_clear_literal_other.
                 --- exact Hq.
                 --- destruct l; exact Hpneq.
           ++ assert (Holdneeds : clause_needs_literal (trail_model m) p body).
              { destruct Hneeds as [Hpin Hneeds]. split; [exact Hpin|].
                intros x Hxin Hxp.
                assert (Hxl : literal_var l <> literal_var x).
                { intros Heq. destruct l as [w|w], x as [q|q];
                    cbn in Heq; subst q.
                  - specialize (Hneeds (Pos w) Hxin Hxp).
                    unfold literal_value in Hneeds. cbn in Hneeds.
                    rewrite Id.eqb_refl in Hneeds. discriminate.
                  - apply Hopnotin. exact Hxin.
                  - apply Hopnotin. exact Hxin.
                  - specialize (Hneeds (Neg w) Hxin Hxp).
                    unfold literal_value in Hneeds. cbn in Hneeds.
                    rewrite Id.eqb_refl in Hneeds. discriminate. }
                rewrite <- (literal_value_cons_other_var _ _ _ Hxl).
                now apply Hneeds. }
              pose proof (Hunit (trail_model m) (model_suffix_refl _) p
                (proj2 (undecided_cons_inv _ _ _ Hpu)) Holdneeds) as Holdp.
              change (In d (ClauseMap.find (literal_var p)
                (ClauseMap.clear_literal (opposite_literal l) cm))).
              rewrite ClauseMap.find_clear_literal_other.
              ** exact Holdp.
              ** destruct l; exact Hpneq.
        -- intros Hcardout.
           change (ClauseMap.card_of d (ClauseMap.clear_falsified l cm) <> 1)
             in Hcardout.
           unfold follows_two_undecided.
           intros suffix Hsuffix Hunsat Htwo.
           assert (Holdcardneq : ClauseMap.card_of d cm <> 1).
           { intros Holdone. apply Hcardout. rewrite Hcardeq. exact Holdone. }
           destruct (model_suffix_cons_cases suffix l (trail_model m) Hsuffix)
             as [Heq|Holdsuffix].
           ++ subst suffix.
              assert (Holdunsat : Is_true (negb
                  (existsb (literal_is_true (trail_model m)) body))).
              { eapply unsatisfied_cons_inv; [exact Hlu|exact Hunsat]. }
              destruct Htwo as [x [y [Hxin [Hyin [Hxy [Hxu Hyu]]]]]].
              apply undecided_cons_inv in Hxu as [_ Hxu].
              apply undecided_cons_inv in Hyu as [_ Hyu].
              assert (Htwoold : clause_has_two_undecided
                  (trail_model m) body).
              { exists x, y. now repeat split. }
              destruct (Holdtwo Holdcardneq (trail_model m)
                  (model_suffix_refl _) Holdunsat Htwoold)
                as [Holdcard Hallold].
              split.
              ** change (ClauseMap.card_of d
                   (ClauseMap.clear_falsified l cm) = 2).
                 rewrite Hcardeq. exact Holdcard.
              ** intros q Hq.
              pose proof (ClauseMap.find_clear_literal_in cm
                (opposite_literal l) q d Hq) as Hqold.
              destruct (Hwatch q d Hqold) as
                [body' [Hbody' [_ [_ [_ [Hposq Hnegq]]]]]].
              change (find_clause_in clauses learned d = Some body') in Hbody'.
              rewrite Hbody in Hbody'. injection Hbody' as <-.
              assert (Hql : literal_var l <> q).
              { intros Heq. subst q. destruct l as [w|w];
                  unfold ClauseMap.find in Hq; apply in_app_or in Hq as [Hqp|Hqn].
                - change (In d (ClauseMap.find_pos w
                    (ClauseMap.clear_literal (Neg w) cm))) in Hqp.
                  rewrite ClauseMap.find_pos_clear_neg in Hqp.
                  apply (negb_prop_elim _ Hunsat).
                  apply Is_true_eq_left, existsb_exists. exists (Pos w).
                  split; [now apply Hposq|apply literal_is_true_cons_self].
                - change (In d (ClauseMap.find_neg w
                    (ClauseMap.clear_literal (Neg w) cm))) in Hqn.
                  rewrite ClauseMap.find_neg_clear_neg in Hqn.
                  destruct (VarKey.eq_dec w w); contradiction.
                - change (In d (ClauseMap.find_pos w
                    (ClauseMap.clear_literal (Pos w) cm))) in Hqp.
                  rewrite ClauseMap.find_pos_clear_pos in Hqp.
                  destruct (VarKey.eq_dec w w); contradiction.
                - change (In d (ClauseMap.find_neg w
                    (ClauseMap.clear_literal (Pos w) cm))) in Hqn.
                  rewrite ClauseMap.find_neg_clear_pos in Hqn.
                  apply (negb_prop_elim _ Hunsat).
                  apply Is_true_eq_left, existsb_exists. exists (Neg w).
                  split; [now apply Hnegq|apply literal_is_true_cons_self]. }
              apply undecided_cons_other_var; [exact Hql|].
              exact (Hallold q Hqold).
           ++ destruct (Holdtwo Holdcardneq suffix Holdsuffix Hunsat Htwo)
                as [Holdcard Hallold].
              split.
              ** change (ClauseMap.card_of d
                   (ClauseMap.clear_falsified l cm) = 2).
                 rewrite Hcardeq. exact Holdcard.
              ** intros q Hq.
                 apply Hallold.
                 exact (ClauseMap.find_clear_literal_in cm
                   (opposite_literal l) q d Hq).
      * split; [exact Hinc|]. split; [exact Hnoopp|]. split.
        { destruct l as [w|w].
          - intros Hbucket. apply Hpos.
            change (In d (ClauseMap.find_pos v
              (ClauseMap.clear_literal (Neg w) cm))) in Hbucket.
            rewrite ClauseMap.find_pos_clear_neg in Hbucket. exact Hbucket.
          - intros Hbucket. apply Hpos.
            change (In d (ClauseMap.find_pos v
              (ClauseMap.clear_literal (Pos w) cm))) in Hbucket.
            rewrite ClauseMap.find_pos_clear_pos in Hbucket.
            destruct (VarKey.eq_dec w v);
              [subst v; contradiction|exact Hbucket]. }
        { destruct l as [w|w].
          - intros Hbucket. apply Hneg.
            change (In d (ClauseMap.find_neg v
              (ClauseMap.clear_literal (Neg w) cm))) in Hbucket.
            rewrite ClauseMap.find_neg_clear_neg in Hbucket.
            destruct (VarKey.eq_dec w v);
              [subst v; contradiction|exact Hbucket].
          - intros Hbucket. apply Hneg.
            change (In d (ClauseMap.find_neg v
              (ClauseMap.clear_literal (Pos w) cm))) in Hbucket.
            rewrite ClauseMap.find_neg_clear_pos in Hbucket. exact Hbucket. }
    + destruct l as [w|w].
      * change (NoDup (ClauseMap.find_pos v
          (ClauseMap.clear_literal (Neg w) cm))).
        rewrite ClauseMap.find_pos_clear_neg. apply Hnodup.
      * change (NoDup (ClauseMap.find_pos v
          (ClauseMap.clear_literal (Pos w) cm))).
        rewrite ClauseMap.find_pos_clear_pos.
        destruct (VarKey.eq_dec w v); [constructor|apply Hnodup].
    + destruct l as [w|w].
      * change (NoDup (ClauseMap.find_neg v
          (ClauseMap.clear_literal (Neg w) cm))).
        rewrite ClauseMap.find_neg_clear_neg.
        destruct (VarKey.eq_dec w v); [constructor|apply Hnodup].
      * change (NoDup (ClauseMap.find_neg v
          (ClauseMap.clear_literal (Pos w) cm))).
        rewrite ClauseMap.find_neg_clear_pos. apply Hnodup.
    + exact Hworknodup.
    + intros d Hd. destruct (Hworkref d Hd) as
        [body [Hbody [Hnoopp Hdetachedin]]].
      exists body. split; [exact Hbody|]. split; [exact Hnoopp|].
      unfold staged_watches_valid, staged_watches_valid_with.
      intros suffix Hsuffix Hunsat Htwo q Hq.
      pose proof (ClauseMap.find_clear_literal_in cm (opposite_literal l)
        q d Hq) as Hqold.
      pose proof (ClauseMap.find_falsified_in l cm d Hd) as Hdetachedwatch.
      destruct (Hwatch (literal_var l) d Hdetachedwatch) as
        [body' [Hbody' [Hstable _]]].
      change (find_clause_in clauses learned d = Some body') in Hbody'.
      rewrite Hbody in Hbody'. injection Hbody' as <-.
      destruct (Hstable (fun H => H)) as [_ Holdtwo].
      assert (Hcount : count_occ clause_pointer_eq_dec
          (ClauseMap.find_literal (opposite_literal l) cm) d = 1).
      { destruct l.
        - apply count_occ_eq_one_of_nodup_in; [apply Hnodup|exact Hd].
        - apply count_occ_eq_one_of_nodup_in; [apply Hnodup|exact Hd]. }
      pose proof (ClauseMap.card_of_clear_literal cm d (opposite_literal l))
        as Hclear.
      assert (Houtpositive : ClauseMap.card_of d
          (ClauseMap.clear_falsified l cm) > 0).
      { exact (ClauseMap.card_of_in _ _ _ Hq). }
      assert (Holdcardneq : ClauseMap.card_of d cm <> 1).
      { change (ClauseMap.card_of d (ClauseMap.clear_falsified l cm) +
          count_occ clause_pointer_eq_dec
            (ClauseMap.find_literal (opposite_literal l) cm) d =
          ClauseMap.card_of d cm) in Hclear. lia. }
      destruct (model_suffix_cons_cases suffix l (trail_model m) Hsuffix)
        as [->|Holdsuffix].
      * assert (Holdunsat : Is_true (negb
            (existsb (literal_is_true (trail_model m)) body))).
        { eapply unsatisfied_cons_inv; [exact Hlu|exact Hunsat]. }
        destruct Htwo as [x [y [Hxin [Hyin [Hxy [Hxu Hyu]]]]]].
        apply undecided_cons_inv in Hxu as [_ Hxu].
        apply undecided_cons_inv in Hyu as [_ Hyu].
        assert (Htwoold : clause_has_two_undecided (trail_model m) body).
        { exists x, y. now repeat split. }
        destruct (Holdtwo Holdcardneq (trail_model m) (model_suffix_refl _)
          Holdunsat Htwoold) as [_ Hallold].
        assert (Hql : literal_var l <> q).
        { intros Heq. subst q. destruct l as [w|w];
            unfold ClauseMap.find in Hq; apply in_app_or in Hq as [Hqp|Hqn].
          - change (In d (ClauseMap.find_pos w
              (ClauseMap.clear_literal (Neg w) cm))) in Hqp.
            rewrite ClauseMap.find_pos_clear_neg in Hqp.
            destruct (Hwatch w d (in_or_app _ _ _ (or_introl Hqp))) as
              [c' [Hc' [_ [_ [_ [Hpos' _]]]]]].
            change (find_clause_in clauses learned d = Some c') in Hc'.
            rewrite Hbody in Hc'. injection Hc' as <-.
            apply (negb_prop_elim _ Hunsat), Is_true_eq_left, existsb_exists.
            exists (Pos w). split; [now apply Hpos'|apply literal_is_true_cons_self].
          - change (In d (ClauseMap.find_neg w
              (ClauseMap.clear_literal (Neg w) cm))) in Hqn.
            rewrite ClauseMap.find_neg_clear_neg in Hqn.
            destruct (VarKey.eq_dec w w); contradiction.
          - change (In d (ClauseMap.find_pos w
              (ClauseMap.clear_literal (Pos w) cm))) in Hqp.
            rewrite ClauseMap.find_pos_clear_pos in Hqp.
            destruct (VarKey.eq_dec w w); contradiction.
          - change (In d (ClauseMap.find_neg w
              (ClauseMap.clear_literal (Pos w) cm))) in Hqn.
            rewrite ClauseMap.find_neg_clear_pos in Hqn.
            destruct (Hwatch w d (in_or_app _ _ _ (or_intror Hqn))) as
              [c' [Hc' [_ [_ [_ [_ Hneg']]]]]].
            change (find_clause_in clauses learned d = Some c') in Hc'.
            rewrite Hbody in Hc'. injection Hc' as <-.
            apply (negb_prop_elim _ Hunsat), Is_true_eq_left, existsb_exists.
            exists (Neg w). split; [now apply Hneg'|apply literal_is_true_cons_self]. }
        apply undecided_cons_other_var; [exact Hql|]. exact (Hallold q Hqold).
      * destruct (Holdtwo Holdcardneq suffix Holdsuffix Hunsat Htwo)
          as [_ Hallold]. exact (Hallold q Hqold).
    + intros p d Hpd. destruct (Hpending p d Hpd)
        as [body [Hbody [Hneeds Hnoopp]]].
      exists body. split; [exact Hbody|]. split; [|exact Hnoopp].
      now apply clause_needs_literal_cons.
    + intros d Hd.
      destruct (Hworkref d Hd) as [body [Hbody [Hnoopp Hfalsewatch]]].
      assert (Hcount : count_occ clause_pointer_eq_dec
          (ClauseMap.find_literal (opposite_literal l) cm) d = 1).
      { destruct l.
        - apply count_occ_eq_one_of_nodup_in; [apply Hnodup|exact Hd].
        - apply count_occ_eq_one_of_nodup_in; [apply Hnodup|exact Hd]. }
      pose proof (ClauseMap.card_of_clear_literal cm d (opposite_literal l))
        as Hclear.
      change (ClauseMap.card_of d (ClauseMap.clear_falsified l cm) +
        count_occ clause_pointer_eq_dec
          (ClauseMap.find_literal (opposite_literal l) cm) d =
        ClauseMap.card_of d cm) in Hclear.
      specialize (Hcard d). unfold card_of_watch in *.
      cbn -[ClauseMap.card_of] in *.
      destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
      * lia.
      * left. lia.
      * right. split; [lia|].
        destruct Hwhy as [Habs|[Hpendingd|Hdecided]].
        -- contradiction.
        -- now left.
        -- right. destruct Hdecided as [Hdfals|[b [Hb Htrue]]].
           ++ left. destruct Hdfals as [b [Hb Hsem]]. exists b.
              split; [exact Hb|]. now apply falsified_cons_undecided.
           ++ right. exists b. split; [exact Hb|].
              now apply satisfied_cons_undecided.
    + intros d.
      destruct (in_dec clause_pointer_eq_dec d
        (ClauseMap.find_falsified l cm)) as [Hin|Hnotin].
      * assert (Hcount : count_occ clause_pointer_eq_dec
          (ClauseMap.find_literal (opposite_literal l) cm) d = 1).
        { destruct l.
          - apply count_occ_eq_one_of_nodup_in; [apply Hnodup|exact Hin].
          - apply count_occ_eq_one_of_nodup_in; [apply Hnodup|exact Hin]. }
        pose proof (ClauseMap.card_of_clear_literal cm d (opposite_literal l))
          as Hclear.
        change (ClauseMap.card_of d (ClauseMap.clear_falsified l cm) +
          count_occ clause_pointer_eq_dec
            (ClauseMap.find_literal (opposite_literal l) cm) d =
          ClauseMap.card_of d cm) in Hclear.
        specialize (Hcard d). unfold card_of_watch in *.
        cbn -[ClauseMap.card_of] in *.
        destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
        -- lia.
        -- right; right. split; [lia|now left].
        -- left. lia.
      * assert (Hcount : count_occ clause_pointer_eq_dec
            (ClauseMap.find_literal (opposite_literal l) cm) d = 0).
        { destruct l; apply count_occ_not_In; exact Hnotin. }
        pose proof (ClauseMap.card_of_clear_literal cm d (opposite_literal l))
          as Hclear.
        change (ClauseMap.card_of d (ClauseMap.clear_falsified l cm) +
          count_occ clause_pointer_eq_dec
            (ClauseMap.find_literal (opposite_literal l) cm) d =
          ClauseMap.card_of d cm) in Hclear.
        specialize (Hcard d). unfold card_of_watch in *.
        cbn -[ClauseMap.card_of] in *.
        destruct Hcard as [Hzero|[Htwo|[Hone Hwhy]]].
        -- left. lia.
        -- right; left. lia.
        -- right; right. split; [lia|].
           destruct Hwhy as [Habs|[Hpendingd|Hdecided]].
           ++ contradiction.
           ++ now right; left.
           ++ right; right. destruct Hdecided as [Hdfals|[b [Hb Htrue]]].
              ** left. destruct Hdfals as [b [Hb Hsem]]. exists b.
                 split; [exact Hb|]. now apply falsified_cons_undecided.
              ** right. exists b. split; [exact Hb|].
                 now apply satisfied_cons_undecided.
    + exact (trail_consistent_decision m l Hlu (proj1 Htrail)).
    + change (literal_is_undecided (trail_model m) l = true). exact Hlu.
    + exact (proj2 Htrail). }
    { split.
    { unfold detached_work_valid.
      intros d Hd. destruct (Hworkref d Hd) as
        [body [Hbody [_ Hdetachedin]]].
      exists body. split; [exact Hbody|]. split; [exact Hdetachedin|].
      split.
      - intros suffix Hsuffix Hunsat Htwo.
        destruct (model_suffix_cons_cases suffix l (trail_model m) Hsuffix)
          as [Heq|Holdsuffix].
        + now left.
        + right.
          assert (Hopu : literal_is_undecided (trail_model m)
              (opposite_literal l) = true).
          { destruct l as [w|w]; cbn.
            - now rewrite <- literal_is_undecided_pos_neg.
            - now rewrite literal_is_undecided_pos_neg. }
          exact (undecided_model_suffix _ _ _ Holdsuffix Hopu).
      - intros suffix Hsuffix p Hpu Hneeds.
        destruct (model_suffix_cons_cases suffix l (trail_model m) Hsuffix)
          as [Heq|Holdsuffix]; [now left|].
        pose proof (ClauseMap.find_falsified_in l cm d Hd) as Hdetachedwatch.
        destruct (Hwatch (literal_var l) d Hdetachedwatch) as
          [body' [Hbody' [Hstable _]]].
        change (find_clause_in clauses learned d = Some body') in Hbody'.
        rewrite Hbody in Hbody'. injection Hbody' as <-.
        destruct (Hstable (fun H => H)) as [Hunit _].
        pose proof (Hunit suffix Holdsuffix p Hpu Hneeds) as Hwatched.
        right. destruct (Id.eq_dec (literal_var p)
          (literal_var (opposite_literal l))) as [Hvar|Hvar].
        + now left.
        + right. change (In d (ClauseMap.find (literal_var p)
            (ClauseMap.clear_literal (opposite_literal l) cm))).
          rewrite ClauseMap.find_clear_literal_other; [exact Hwatched|].
          now intros Heq; apply Hvar; symmetry. }
    { unfold detached_clause_arity.
      intros d body Hbody Hnoopp.
      cbn [find_clause state_trail state_clauses state_learned state_watched]
        in Hbody |- *.
      split.
      - intros Hd.
        specialize (Harity d body Hbody ltac:(simpl; tauto) Hnoopp).
        assert (Hcount : count_occ clause_pointer_eq_dec
            (ClauseMap.find_literal (opposite_literal l) cm) d = 1).
        { destruct l.
          - apply count_occ_eq_one_of_nodup_in; [apply Hnodup|exact Hd].
          - apply count_occ_eq_one_of_nodup_in; [apply Hnodup|exact Hd]. }
        pose proof (ClauseMap.card_of_clear_literal cm d (opposite_literal l))
          as Hclear.
        change (ClauseMap.card_of d (ClauseMap.clear_falsified l cm) +
          count_occ clause_pointer_eq_dec
            (ClauseMap.find_literal (opposite_literal l) cm) d =
          ClauseMap.card_of d cm) in Hclear.
        cbn [state_watched] in Harity.
        destruct Harity as [[Htwo Hcardtwo]|[Hnotwo Hcardzero]].
        + split; [exact Htwo|lia].
        + pose proof (ClauseMap.card_of_in _ _ _
            (ClauseMap.find_falsified_in l cm d Hd)) as Hpositive.
          lia.
      - intros Hd.
        specialize (Harity d body Hbody ltac:(simpl; tauto) Hnoopp).
        assert (Hcount : count_occ clause_pointer_eq_dec
            (ClauseMap.find_literal (opposite_literal l) cm) d = 0).
        { destruct l; apply count_occ_not_In; exact Hd. }
        pose proof (ClauseMap.card_of_clear_literal cm d (opposite_literal l))
          as Hclear.
        change (ClauseMap.card_of d (ClauseMap.clear_falsified l cm) +
          count_occ clause_pointer_eq_dec
            (ClauseMap.find_literal (opposite_literal l) cm) d =
          ClauseMap.card_of d cm) in Hclear.
        cbn [state_watched] in Harity.
        destruct Harity as [[Htwo Hcardtwo]|[Hnotwo Hcardzero]].
        + left. split; [exact Htwo|lia].
        + right. split; [exact Hnotwo|lia]. } }
  - split.
    + intros d Hd. destruct (Hworkref d Hd) as [body [Hbody [_ Hin]]].
      now exists body.
    + exact Hfresh.
Qed.
Lemma set_lit_inv : forall l s s',
  literal_is_undecided s.(state_trail) l = true ->
  state_invariant s ->
  set_lit l s = Progress s' ->
  state_invariant s'.
Proof.
  intros l [m clauses learned cm pending] s' Hlu Hinv Hset.
  pose proof (proj1 (proj2 Hinv)) as Hlearned.
  unfold set_lit, set_trail_entry in Hset.
  cbn [state_trail state_clauses state_learned state_watched state_pending]
    in Hset.
  cbn [trail_literal] in Hset.
  pose proof (prepare_set_lit_inv l m clauses learned cm pending Hlu Hinv)
    as [Hstaged [Hcontains Hfresh]].
  eapply (propagate_clauses_inv (opposite_literal l)
    (ClauseMap.find_falsified l cm)
    {| state_trail := Decision l :: m;
       state_clauses := clauses; state_learned := learned;
       state_watched := ClauseMap.clear_falsified l cm;
       state_pending := pending |} s').
  - destruct Hstaged as [Hstage _].
    unfold staged_invariant in Hstage.
    destruct Hstage as [_ [_ [_ [_ [Hnodup _]]]]]. exact Hnodup.
  - exact Hcontains.
  - exact Hfresh.
  - exact Hstaged.
  - exact Hlearned.
  - exact Hset.
Qed.

Lemma set_lit_conflict_inv : forall l s s' cause,
  literal_is_undecided s.(state_trail) l = true ->
  state_invariant s ->
  set_lit l s = Conflict s' cause ->
  state_invariant s'.
Proof.
  intros l [m clauses learned cm pending] s' cause Hlu Hinv Hset.
  pose proof (proj1 (proj2 Hinv)) as Hlearned.
  unfold set_lit, set_trail_entry in Hset.
  cbn [state_trail state_clauses state_learned state_watched state_pending]
    in Hset. cbn [trail_literal] in Hset.
  pose proof (prepare_set_lit_inv l m clauses learned cm pending Hlu Hinv)
    as [Hstaged [Hcontains Hfresh]].
  eapply (propagate_clauses_conflict_inv (opposite_literal l)
    (ClauseMap.find_falsified l cm)
    {| state_trail := Decision l :: m;
       state_clauses := clauses; state_learned := learned;
       state_watched := ClauseMap.clear_falsified l cm;
       state_pending := pending |} s' cause).
  - destruct Hstaged as [Hstage _]. unfold staged_invariant in Hstage.
    destruct Hstage as [_ [_ [_ [_ [Hnodup _]]]]]. exact Hnodup.
  - exact Hcontains.
  - exact Hfresh.
  - exact Hstaged.
  - exact Hlearned.
  - exact Hset.
Qed.

Lemma drop_satisfied_pending_inv : forall work l ci c pending (m : Trail)
    clauses learned cm,
  find_clause_in clauses learned ci = Some c ->
  In l c -> Is_true (existsb (literal_is_true m) c) ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := (l, ci) :: pending |} ->
  staged_invariant work
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |}.
Proof.
  intros work l ci c pending m clauses learned cm Hfind Hlc Htrue Hinv.
  destruct Hinv as
    [Hcover [Hfals [Hwatch [Hnodup [Hworknodup [Hworkref
      [Hpending [Hwork [Hcard Htrail]]]]]]]]].
  assert (Hreason : forall d,
      (exists p, In (p, d) ((l, ci) :: pending)) ->
      (exists p, In (p, d) pending) \/
      decided_clause d
        {| state_trail := m; state_clauses := clauses; state_learned := learned;
           state_watched := cm;
           state_pending := pending |}).
  { intros d [p Hpd]. simpl in Hpd. destruct Hpd as [Heq|Hpd].
    - injection Heq as <- <-. right. right. exists c. now split.
    - left. now exists p. }
  repeat split; try assumption.
  - intros d body Hbody Hunsat.
    destruct (Hcover d body Hbody Hunsat) as
      [Hopp|[Hdwork|[Hwatched|Hqueued]]].
    + now left.
    + now right; left.
    + now right; right; left.
    + right; right; right. unfold queued_clause in Hqueued |- *. cbn in Hqueued |- *.
      destruct Hqueued as [Hin|[p [Heq|Hin]]].
      * now left.
      * injection Heq as <- <-.
        change (find_clause_in clauses learned ci = Some body) in Hbody.
        rewrite Hfind in Hbody. injection Hbody as <-.
        exfalso. exact (negb_prop_elim _ Hunsat Htrue).
      * right. now exists p.
  - apply Hnodup.
  - apply Hnodup.
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
  - exact (proj1 Htrail).
  - exact (proj2 Htrail).
Qed.

Lemma set_pending_inv : forall l ci c pending (m : Trail) clauses learned cm s',
  find_clause_in clauses learned ci = Some c ->
  literal_is_undecided m l = true ->
  state_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := (l, ci) :: pending |} ->
  set_propagated_lit l ci
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} = Progress s' ->
  state_invariant s'.
Proof.
  intros l ci c pending m clauses learned cm s' Hfind Hlu Hinv Hset.
  pose proof Hinv as Hpendinginv.
  pose proof Hinv as Htrailinv.
  destruct Htrailinv as [Htrailinv _].
  destruct Htrailinv as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ Htrail]]]]]]]]].
  destruct Hpendinginv as [Hpendinginv _].
  destruct Hpendinginv as [_ [_ [_ [_ [_ [_ [Hpending _]]]]]]].
  destruct (Hpending l ci (or_introl eq_refl))
    as [body [Hbody [Hneeds Hnoopp]]].
  change (find_clause_in clauses learned ci = Some body) in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  unfold set_propagated_lit, set_trail_entry in Hset.
  cbn [trail_literal state_trail state_clauses state_learned state_watched
    state_pending] in Hset.
  pose proof (prepare_set_lit_inv l m clauses learned cm
      ((l, ci) :: pending)
    Hlu Hinv) as [Hprepared [Hcontains Hfresh]].
  assert (Hpropagation : trail_invariant clauses learned
      (Propagation l ci :: m)).
  { split.
    - exact (trail_consistent_decision m l Hlu (proj1 Htrail)).
    - cbn. split; [exact Hlu|]. exists c. split; [exact Hfind|].
      split; [exact Hneeds|exact (proj2 Htrail)]. }
  destruct Hprepared as [Hprepared [Hdetached Harity]].
  eapply staged_invariant_trail_ext with
    (t' := Propagation l ci :: m) in Hprepared;
    [|reflexivity|exact Hpropagation].
  assert (Hdetached' : detached_work_valid (opposite_literal l)
      (ClauseMap.find_falsified l cm)
      {| state_trail := Propagation l ci :: m;
         state_clauses := clauses; state_learned := learned;
         state_watched := ClauseMap.clear_falsified l cm;
         state_pending := (l, ci) :: pending |}).
  { unfold detached_work_valid in Hdetached |- *.
    cbn [trail_model trail_literal find_clause state_trail state_clauses
      state_learned] in Hdetached |- *. exact Hdetached. }
  assert (Harity' : detached_clause_arity
      (ClauseMap.find_falsified l cm)
      {| state_trail := Propagation l ci :: m;
         state_clauses := clauses; state_learned := learned;
         state_watched := ClauseMap.clear_falsified l cm;
         state_pending := pending |}).
  { unfold detached_clause_arity in Harity |- *.
    cbn [find_clause state_trail state_clauses state_learned state_watched]
      in Harity |- *. exact Harity. }
  assert (Hsatisfied : Is_true
      (existsb (literal_is_true (trail_model (Propagation l ci :: m))) c)).
  { apply Is_true_eq_left. apply existsb_exists. exists l.
    split; [exact (proj1 Hneeds)|apply literal_is_true_cons_self]. }
  pose proof (drop_satisfied_pending_inv
    (ClauseMap.find_falsified l cm) l ci c pending
    (Propagation l ci :: m) clauses learned
    (ClauseMap.clear_falsified l cm) Hfind (proj1 Hneeds) Hsatisfied
    Hprepared) as Hstagedbase.
  assert (Hstaged : staged_invariant_with (Some (opposite_literal l))
      (ClauseMap.find_falsified l cm)
      {| state_trail := Propagation l ci :: m;
         state_clauses := clauses; state_learned := learned;
         state_watched := ClauseMap.clear_falsified l cm;
         state_pending := pending |}).
  { split; [exact Hstagedbase|]. split.
    - unfold detached_work_valid in Hdetached' |- *.
      cbn [find_clause state_pending] in Hdetached' |- *. exact Hdetached'.
    - exact Harity'. }
  eapply (propagate_clauses_inv (opposite_literal l)
    (ClauseMap.find_falsified l cm)
    {| state_trail := Propagation l ci :: m;
       state_clauses := clauses; state_learned := learned;
       state_watched := ClauseMap.clear_falsified l cm;
       state_pending := pending |} s').
  - destruct Hstaged as [Hstage _]. unfold staged_invariant in Hstage.
    destruct Hstage as [_ [_ [_ [_ [Hnodup _]]]]]. exact Hnodup.
  - exact Hcontains.
  - exact Hfresh.
  - exact Hstaged.
  - exact (proj1 (proj2 Hinv)).
  - exact Hset.
Qed.

Lemma set_pending_conflict_inv :
  forall l ci c pending (m : Trail) clauses learned cm s' cause,
  find_clause_in clauses learned ci = Some c ->
  literal_is_undecided m l = true ->
  state_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := (l, ci) :: pending |} ->
  set_propagated_lit l ci
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} = Conflict s' cause ->
  state_invariant s'.
Proof.
  intros l ci c pending m clauses learned cm s' cause Hfind Hlu Hinv Hset.
  pose proof Hinv as Hpendinginv. pose proof Hinv as Htrailinv.
  destruct Htrailinv as [Htrailinv _].
  destruct Htrailinv as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ Htrail]]]]]]]]].
  destruct Hpendinginv as [Hpendinginv _].
  destruct Hpendinginv as [_ [_ [_ [_ [_ [_ [Hpending _]]]]]]].
  destruct (Hpending l ci (or_introl eq_refl))
    as [body [Hbody [Hneeds Hnoopp]]].
  change (find_clause_in clauses learned ci = Some body) in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  unfold set_propagated_lit, set_trail_entry in Hset.
  cbn [trail_literal state_trail state_clauses state_learned state_watched
    state_pending] in Hset.
  pose proof (prepare_set_lit_inv l m clauses learned cm
      ((l, ci) :: pending) Hlu Hinv) as [Hprepared [Hcontains Hfresh]].
  assert (Hpropagation : trail_invariant clauses learned
      (Propagation l ci :: m)).
  { split.
    - exact (trail_consistent_decision m l Hlu (proj1 Htrail)).
    - cbn. split; [exact Hlu|]. exists c. split; [exact Hfind|].
      split; [exact Hneeds|exact (proj2 Htrail)]. }
  destruct Hprepared as [Hprepared [Hdetached Harity]].
  eapply staged_invariant_trail_ext with
    (t' := Propagation l ci :: m) in Hprepared;
    [|reflexivity|exact Hpropagation].
  assert (Hdetached' : detached_work_valid (opposite_literal l)
      (ClauseMap.find_falsified l cm)
      {| state_trail := Propagation l ci :: m;
         state_clauses := clauses; state_learned := learned;
         state_watched := ClauseMap.clear_falsified l cm;
         state_pending := (l, ci) :: pending |}).
  { unfold detached_work_valid in Hdetached |- *.
    cbn [trail_model trail_literal find_clause state_trail state_clauses
      state_learned] in Hdetached |- *. exact Hdetached. }
  assert (Harity' : detached_clause_arity
      (ClauseMap.find_falsified l cm)
      {| state_trail := Propagation l ci :: m;
         state_clauses := clauses; state_learned := learned;
         state_watched := ClauseMap.clear_falsified l cm;
         state_pending := pending |}).
  { unfold detached_clause_arity in Harity |- *.
    cbn [find_clause state_trail state_clauses state_learned state_watched]
      in Harity |- *. exact Harity. }
  assert (Hsatisfied : Is_true
      (existsb (literal_is_true (trail_model (Propagation l ci :: m))) c)).
  { apply Is_true_eq_left. apply existsb_exists. exists l.
    split; [exact (proj1 Hneeds)|apply literal_is_true_cons_self]. }
  pose proof (drop_satisfied_pending_inv
    (ClauseMap.find_falsified l cm) l ci c pending
    (Propagation l ci :: m) clauses learned
    (ClauseMap.clear_falsified l cm) Hfind (proj1 Hneeds) Hsatisfied
    Hprepared) as Hstagedbase.
  assert (Hstaged : staged_invariant_with (Some (opposite_literal l))
      (ClauseMap.find_falsified l cm)
      {| state_trail := Propagation l ci :: m;
         state_clauses := clauses; state_learned := learned;
         state_watched := ClauseMap.clear_falsified l cm;
         state_pending := pending |}).
  { split; [exact Hstagedbase|]. split.
    - unfold detached_work_valid in Hdetached' |- *.
      cbn [find_clause state_pending] in Hdetached' |- *. exact Hdetached'.
    - exact Harity'. }
  eapply (propagate_clauses_conflict_inv (opposite_literal l)
    (ClauseMap.find_falsified l cm)
    {| state_trail := Propagation l ci :: m;
       state_clauses := clauses; state_learned := learned;
       state_watched := ClauseMap.clear_falsified l cm;
       state_pending := pending |} s' cause).
  - destruct Hstaged as [Hstage _]. unfold staged_invariant in Hstage.
    destruct Hstage as [_ [_ [_ [_ [Hnodup _]]]]]. exact Hnodup.
  - exact Hcontains.
  - exact Hfresh.
  - exact Hstaged.
  - exact (proj1 (proj2 Hinv)).
  - exact Hset.
Qed.

Lemma resolve_true_pending_inv : forall l ci c pending (m : Trail)
    clauses learned cm,
  find_clause_in clauses learned ci = Some c ->
  literal_is_true m l = true ->
  state_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := (l, ci) :: pending |} ->
  state_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm;
       state_pending := pending |}.
Proof.
  intros l ci c pending m clauses learned cm Hfind Hltrue Hinv.
  pose proof Hinv as Hpendinginv.
  destruct Hpendinginv as [Hpendinginv Hlearned].
  destruct Hpendinginv as [_ [_ [_ [_ [_ [_ [Hpending _]]]]]]].
  destruct (Hpending l ci (or_introl eq_refl))
    as [body [Hbody [Hneeds Hnoopp]]].
  change (find_clause_in clauses learned ci = Some body) in Hbody.
  rewrite Hfind in Hbody. injection Hbody as <-.
  unfold state_invariant. split.
  - eapply drop_satisfied_pending_inv;
      [exact Hfind|exact (proj1 Hneeds)| |exact (proj1 Hinv)].
    apply Is_true_eq_left. apply existsb_exists. exists l.
    split; [exact (proj1 Hneeds)|exact Hltrue].
  - exact Hlearned.
Qed.

Lemma find_undecided_var_unassigned : forall m vs v,
  find_undecided_var m vs = Some v -> var_is_assigned m v = false.
Proof.
  intros m vs. induction vs as [|w vs IH]; intros v Hfind; [discriminate|].
  cbn in Hfind. destruct (var_is_assigned m w) eqn:Hassigned.
  - now apply IH.
  - injection Hfind as <-. exact Hassigned.
Qed.

Lemma var_unassigned_pos_undecided : forall m v,
  var_is_assigned m v = false -> literal_is_undecided m (Pos v) = true.
Proof.
  intros m v Hunassigned. apply not_InL_literal_undecided.
  intros [Hpos|Hneg].
  - assert (var_is_assigned m v = true) as Hassigned.
    { unfold var_is_assigned. apply existsb_exists. exists (Pos v).
      split; [exact Hpos|]. cbn. apply Id.eqb_refl. }
    congruence.
  - assert (var_is_assigned m v = true) as Hassigned.
    { unfold var_is_assigned. apply existsb_exists. exists (Neg v).
      split; [exact Hneg|]. cbn. apply Id.eqb_refl. }
    congruence.
Qed.

Lemma progress_inv : forall s s',
  state_invariant s -> progress s = Progress s' -> state_invariant s'.
Proof.
  intros [m clauses learned cm pending] s' Hinv Hprogress.
  unfold progress in Hprogress.
  cbn [state_pending state_trail] in Hprogress.
  destruct pending as [|[l ci] pending].
  - unfold progress_state, problem_vars in Hprogress.
    cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
    destruct (find_undecided_var m (clause_store_vars clauses))
      as [v|] eqn:Hfindvar.
    + eapply set_lit_inv; [|exact Hinv|exact Hprogress].
      apply var_unassigned_pos_undecided.
      now apply (find_undecided_var_unassigned m (clause_store_vars clauses) v).
    + now injection Hprogress as <-.
  - pose proof Hinv as Hlookup.
    destruct Hlookup as [Hlookup _].
    destruct Hlookup as [_ [_ [_ [_ [_ [_ [Hpending _]]]]]]].
    destruct (Hpending l ci (or_introl eq_refl))
      as [c [Hfind [Hlc Hstatus]]].
    change (find_clause_in clauses learned ci = Some c) in Hfind.
    destruct (literal_value m l) as [[|]|] eqn:Hvalue.
    + unfold progress_state in Hprogress.
      cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
      rewrite Hvalue in Hprogress. injection Hprogress as <-.
      eapply resolve_true_pending_inv; [exact Hfind| |exact Hinv].
      unfold literal_is_true. now rewrite Hvalue.
    + unfold find_clause in Hprogress. cbn -[find_clause_in] in Hprogress.
      rewrite Hfind in Hprogress.
      discriminate.
    + unfold progress_state in Hprogress.
      cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
      rewrite Hvalue in Hprogress.
      eapply set_pending_inv; [exact Hfind| |exact Hinv|exact Hprogress].
      unfold literal_is_undecided. now rewrite Hvalue.
Qed.

Definition progress_result_state (result : progress_result) : State :=
  match result with
  | Progress s => s
  | Conflict s _ => s
  end.

Lemma propagate_result_clauses : forall falsified ci s,
  (progress_result_state (propagate falsified ci s)).(state_clauses) =
  s.(state_clauses).
Proof.
  intros falsified ci [m clauses learned cm pending].
  unfold progress_result_state, propagate, find_clause. cbn -[find_clause_in].
  destruct (find_clause_in clauses learned ci) as [c|]; [|reflexivity].
  destruct (scan_clause (map trail_literal m) falsified ci c cm);
    reflexivity.
Qed.

Lemma propagate_clauses_result_clauses : forall falsified work s,
  (progress_result_state (propagate_clauses falsified work s)).(state_clauses) =
  s.(state_clauses).
Proof.
  intros falsified work. induction work as [|ci work IH]; intros s;
    [reflexivity|].
  cbn [propagate_clauses].
  destruct (propagate falsified ci s) as [next|conflict cause] eqn:Hpropagate.
  - rewrite IH. pose proof (propagate_result_clauses falsified ci s) as H.
    now rewrite Hpropagate in H.
  - pose proof (propagate_result_clauses falsified ci s) as H.
    pose proof (IH conflict) as Hrest.
    destruct (propagate_clauses falsified work conflict); cbn in Hrest |- *;
      rewrite Hrest; now rewrite Hpropagate in H.
Qed.

Lemma propagate_result_trail : forall falsified ci s,
  (progress_result_state (propagate falsified ci s)).(state_trail) =
  s.(state_trail).
Proof.
  intros falsified ci [m clauses learned cm pending].
  unfold progress_result_state, propagate, find_clause. cbn -[find_clause_in].
  destruct (find_clause_in clauses learned ci) as [c|]; [|reflexivity].
  destruct (scan_clause (map trail_literal m) falsified ci c cm); reflexivity.
Qed.

Lemma propagate_clauses_result_trail : forall falsified work s,
  (progress_result_state (propagate_clauses falsified work s)).(state_trail) =
  s.(state_trail).
Proof.
  intros falsified work. induction work as [|ci work IH]; intros s;
    [reflexivity|].
  cbn [propagate_clauses].
  destruct (propagate falsified ci s) as [next|conflict cause] eqn:Hpropagate.
  - rewrite IH. pose proof (propagate_result_trail falsified ci s) as H.
    now rewrite Hpropagate in H.
  - pose proof (propagate_result_trail falsified ci s) as H.
    pose proof (IH conflict) as Hrest.
    destruct (propagate_clauses falsified work conflict); cbn in Hrest |- *;
      rewrite Hrest; now rewrite Hpropagate in H.
Qed.

Lemma propagate_result_learned : forall falsified ci s,
  (progress_result_state (propagate falsified ci s)).(state_learned) =
  s.(state_learned).
Proof.
  intros falsified ci [m clauses learned cm pending].
  unfold progress_result_state, propagate, find_clause. cbn -[find_clause_in].
  destruct (find_clause_in clauses learned ci) as [c|]; [|reflexivity].
  destruct (scan_clause (map trail_literal m) falsified ci c cm); reflexivity.
Qed.

Lemma propagate_clauses_result_learned : forall falsified work s,
  (progress_result_state (propagate_clauses falsified work s)).(state_learned) =
  s.(state_learned).
Proof.
  intros falsified work. induction work as [|ci work IH]; intros s;
    [reflexivity|].
  cbn [propagate_clauses].
  destruct (propagate falsified ci s) as [next|conflict cause] eqn:Hpropagate.
  - rewrite IH. pose proof (propagate_result_learned falsified ci s) as H.
    now rewrite Hpropagate in H.
  - pose proof (propagate_result_learned falsified ci s) as H.
    pose proof (IH conflict) as Hrest.
    destruct (propagate_clauses falsified work conflict); cbn in Hrest |- *;
      rewrite Hrest; now rewrite Hpropagate in H.
Qed.

Lemma set_trail_entry_result_trail : forall entry s,
  (progress_result_state (set_trail_entry entry s)).(state_trail) =
  entry :: s.(state_trail).
Proof.
  intros entry [m clauses learned cm pending]. unfold set_trail_entry. cbn.
  apply propagate_clauses_result_trail.
Qed.

Lemma set_trail_entry_result_learned : forall entry s,
  (progress_result_state (set_trail_entry entry s)).(state_learned) =
  s.(state_learned).
Proof.
  intros entry [m clauses learned cm pending]. unfold set_trail_entry. cbn.
  apply propagate_clauses_result_learned.
Qed.

Lemma set_trail_entry_result_clauses : forall entry s,
  (progress_result_state (set_trail_entry entry s)).(state_clauses) =
  s.(state_clauses).
Proof.
  intros entry [m clauses learned cm pending].
  unfold set_trail_entry. cbn.
  apply propagate_clauses_result_clauses.
Qed.

Lemma progress_state_result_clauses : forall s,
  (progress_result_state (progress_state s)).(state_clauses) =
  s.(state_clauses).
Proof.
  intros [m clauses learned cm pending].
  unfold progress_state, problem_vars. cbn.
  destruct pending as [|[l ci] pending].
  - destruct (find_undecided_var (map trail_literal m)
      (clause_store_vars clauses));
      [apply propagate_clauses_result_clauses|reflexivity].
  - destruct (literal_value (map trail_literal m) l) as [[|]|];
      try reflexivity.
    apply propagate_clauses_result_clauses.
Qed.

Lemma progress_result_clauses : forall s,
  (progress_result_state (progress s)).(state_clauses) = s.(state_clauses).
Proof.
  intros s. unfold progress.
  destruct s.(state_pending) as [|[l ci] pending].
  - apply progress_state_result_clauses.
  - destruct (literal_value s.(state_trail) l) as [[|]|].
    + apply progress_state_result_clauses.
    + destruct (find_clause ci s); reflexivity.
    + apply progress_state_result_clauses.
Qed.

Lemma progress_state_result_learned : forall s,
  (progress_result_state (progress_state s)).(state_learned) =
  s.(state_learned).
Proof.
  intros [m clauses learned cm pending].
  unfold progress_state, problem_vars. cbn.
  destruct pending as [|[l ci] pending].
  - destruct (find_undecided_var (map trail_literal m)
      (clause_store_vars clauses));
      [apply propagate_clauses_result_learned|reflexivity].
  - destruct (literal_value (map trail_literal m) l) as [[|]|];
      try reflexivity.
    apply propagate_clauses_result_learned.
Qed.

Lemma progress_result_learned : forall s,
  (progress_result_state (progress s)).(state_learned) = s.(state_learned).
Proof.
  intros s. unfold progress.
  destruct s.(state_pending) as [|[l ci] pending].
  - apply progress_state_result_learned.
  - destruct (literal_value s.(state_trail) l) as [[|]|].
    + apply progress_state_result_learned.
    + destruct (find_clause ci s); reflexivity.
    + apply progress_state_result_learned.
Qed.

Lemma progress_clauses : forall s s',
  progress s = Progress s' -> s'.(state_clauses) = s.(state_clauses).
Proof.
  intros s s' Hprogress.
  pose proof (progress_result_clauses s) as Hclauses.
  now rewrite Hprogress in Hclauses.
Qed.

Lemma progress_conflict_clauses : forall s s' cause,
  progress s = Conflict s' cause ->
  s'.(state_clauses) = s.(state_clauses).
Proof.
  intros s s' cause Hprogress.
  pose proof (progress_result_clauses s) as Hclauses.
  now rewrite Hprogress in Hclauses.
Qed.

Inductive delay_returns {A : Type} : Delay A -> A -> Prop :=
  | delay_returns_now (x : A) : delay_returns (Now x) x
  | delay_returns_later (d : Delay A) (x : A) :
      delay_returns d x -> delay_returns (Later d) x.

Definition clause_falsified_by_model (m : Model) (c : Clause) : Prop :=
  forall l, In l c -> literal_value m l = Some false.

Fixpoint below_current_level (trail : Trail) : Trail :=
  match trail with
  | [] => []
  | Decision _ :: trail' => trail'
  | Propagation _ _ :: trail' => below_current_level trail'
  end.

Definition current_level_falsified_invariant (s : State) : Prop :=
  trail_has_decision s.(state_trail) = true ->
  forall ci c, find_clause ci s = Some c ->
    clause_falsified_by_model s.(state_trail) c ->
    ~ clause_falsified_by_model (below_current_level s.(state_trail)) c.

Lemma empty_state_current_level_inv : forall m,
  current_level_falsified_invariant
    {| state_trail := m; state_clauses := ClauseStore.empty;
       state_learned := ClauseStore.empty;
       state_watched := ClauseMap.empty;
       state_pending := [] |}.
Proof.
  intros m _ [ci|ci] c Hfind;
    unfold find_clause, find_clause_in in Hfind;
    cbn [state_clauses state_learned] in Hfind;
    rewrite ClauseStore.find_empty in Hfind; discriminate.
Qed.

Definition backtrack_invariant (s : State) : Prop :=
  state_invariant s /\
  root_unit_invariant s /\
  current_level_falsified_invariant s.

Lemma state_invariant_backtrack : forall s,
  state_invariant s ->
  root_unit_invariant s ->
  current_level_falsified_invariant s ->
  backtrack_invariant s.
Proof.
  intros s Hinv Hroot Hcurrent. exact (conj Hinv (conj Hroot Hcurrent)).
Qed.

Lemma found_clause_implied : forall s pointer c,
  state_invariant s ->
  find_clause pointer s = Some c ->
  clause_implied_by_store s.(state_clauses) c.
Proof.
  intros s [ci|ci] c Hinv Hfind.
  - intros m Hstore. apply (Hstore ci c). exact Hfind.
  - exact (proj1 (proj2 Hinv) ci c Hfind).
Qed.

Lemma falsified_clause_spec : forall m c,
  Is_true (negb (existsb (literal_is_true m) c)) ->
  filter (literal_is_undecided m) c = [] ->
  clause_falsified_by_model m c.
Proof.
  intros m c Hfalse Hdecided l Hin.
  assert (literal_is_true m l = false) as Hnottrue.
  { destruct (literal_is_true m l) eqn:Htrue; [|reflexivity].
    exfalso. apply Is_true_eq_true in Hfalse.
    apply Bool.negb_true_iff in Hfalse.
    assert (existsb (literal_is_true m) c = true).
    { apply existsb_exists. now exists l. }
    congruence. }
  assert (literal_is_undecided m l = false) as Hnotundecided.
  { destruct (literal_is_undecided m l) eqn:Hundecided; [|reflexivity].
    assert (In l (filter (literal_is_undecided m) c)).
    { apply filter_In. now split. }
    rewrite Hdecided in H. contradiction. }
  unfold literal_is_true, literal_is_undecided in Hnottrue, Hnotundecided.
  destruct (literal_value m l) as [[|]|]; try discriminate; reflexivity.
Qed.

Lemma falsified_scan_clause_once : forall m c,
  clause_falsified_by_model m c -> scan_clause_once m c = (false, []).
Proof.
  intros m c Hfalse.
  induction c as [|l c IH]; [reflexivity|].
  pose proof (Hfalse l (or_introl eq_refl)) as Hhead.
  assert (Htail : clause_falsified_by_model m c).
  { intros x Hx. apply Hfalse. now right. }
  specialize (IH Htail). cbn [scan_clause_once]. rewrite IH.
  unfold literal_is_true, literal_is_undecided. rewrite Hhead. reflexivity.
Qed.

Lemma found_clause_implied_from_learned : forall clauses learned pointer c,
  (forall ci body, ClauseStore.find ci learned = Some body ->
    clause_implied_by_store clauses body) ->
  find_clause_in clauses learned pointer = Some c ->
  clause_implied_by_store clauses c.
Proof.
  intros clauses learned [ci|ci] c Hlearned Hfind.
  - intros model Hstore. now apply (Hstore ci c).
  - now apply (Hlearned ci c).
Qed.

Lemma propagate_conflict_sound : forall falsified ci s s' cause,
  learned_invariant s ->
  propagate falsified ci s = Conflict s' cause ->
  clause_implied_by_store s.(state_clauses) cause /\
  clause_falsified_by_model s'.(state_trail) cause.
Proof.
  intros falsified ci [m clauses learned cm pending] s' cause
    Hlearned Hpropagate.
  unfold propagate, find_clause in Hpropagate. cbn -[find_clause_in] in *.
  destruct (find_clause_in clauses learned ci) as [c|] eqn:Hfind;
    [|discriminate].
  destruct (scan_clause (map trail_literal m) falsified ci c cm)
    as [l cm'|cm'|cm'|cm'] eqn:Hscan; try discriminate.
  injection Hpropagate as <- <-. split.
  - eapply found_clause_implied_from_learned; eauto.
  - destruct (scan_clause_conflict_spec _ _ _ _ _ _ Hscan)
      as [Hfalse [Hdecided _]].
    cbn [state_trail]. apply falsified_clause_spec; [|exact Hdecided].
    apply Is_true_eq_left. now apply Bool.negb_true_iff.
Qed.

Lemma propagate_clauses_conflict_sound : forall falsified work s s' cause,
  learned_invariant s ->
  propagate_clauses falsified work s = Conflict s' cause ->
  clause_implied_by_store s.(state_clauses) cause /\
  clause_falsified_by_model s'.(state_trail) cause.
Proof.
  intros falsified work. induction work as [|ci work IH];
    intros s s' cause Hlearned Hpropagates; [discriminate|].
  cbn [propagate_clauses] in Hpropagates.
  destruct (propagate falsified ci s) as [next|conflict firstcause]
    eqn:Hpropagate.
  - destruct (IH next s' cause) as [Himplied Hfalse].
    + eapply propagate_learned_inv; eauto.
    + exact Hpropagates.
    + split; [|exact Hfalse].
      pose proof (propagate_result_clauses falsified ci s) as Hclauses.
      rewrite Hpropagate in Hclauses. cbn in Hclauses.
      now rewrite Hclauses in Himplied.
  - destruct (propagate_conflict_sound falsified ci s conflict firstcause
      Hlearned Hpropagate) as [Himplied Hfalse].
    destruct (propagate_clauses falsified work conflict)
      as [final|final latercause] eqn:Hrest.
    + injection Hpropagates as <- <-. split; [exact Himplied|].
      pose proof (propagate_clauses_result_trail falsified work conflict)
        as Htrail. rewrite Hrest in Htrail. cbn in Htrail. now rewrite Htrail.
    + injection Hpropagates as <- <-. split; [exact Himplied|].
      pose proof (propagate_clauses_result_trail falsified work conflict)
        as Htrail. rewrite Hrest in Htrail. cbn in Htrail. now rewrite Htrail.
Qed.

Lemma set_trail_entry_conflict_sound : forall entry s s' cause,
  learned_invariant s ->
  set_trail_entry entry s = Conflict s' cause ->
  clause_implied_by_store s.(state_clauses) cause /\
  clause_falsified_by_model s'.(state_trail) cause.
Proof.
  intros entry [m clauses learned cm pending] s' cause Hlearned Hset.
  unfold set_trail_entry in Hset. cbn in Hset.
  eapply propagate_clauses_conflict_sound with
    (s := {| state_trail := entry :: m; state_clauses := clauses;
      state_learned := learned;
      state_watched := ClauseMap.clear_falsified (trail_literal entry) cm;
      state_pending := pending |}); [exact Hlearned|exact Hset].
Qed.

Lemma progress_conflict : forall s s' c,
  state_invariant s ->
  progress s = Conflict s' c ->
  clause_implied_by_store s.(state_clauses) c /\
  clause_falsified_by_model s'.(state_trail) c.
Proof.
  intros [m clauses learned cm pending] s' c Hinv Hprogress.
  unfold progress in Hprogress. cbn [state_pending state_trail] in Hprogress.
  destruct pending as [|[l pointer] pending].
  - unfold progress_state, problem_vars in Hprogress.
    cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
    destruct (find_undecided_var m (clause_store_vars clauses));
      [|discriminate].
    unfold set_lit in Hprogress.
    eapply set_trail_entry_conflict_sound; [exact (proj1 (proj2 Hinv))|].
    exact Hprogress.
  - pose proof (proj1 Hinv) as Hlookup.
    destruct Hlookup as [_ [_ [_ [_ [_ [_ [Hpendinginv _]]]]]]].
    destruct (Hpendinginv l pointer (or_introl eq_refl))
      as [body [Hfind [Hneeds Hnoopp]]].
    change (find_clause_in clauses learned pointer = Some body) in Hfind.
    destruct (literal_value m l) as [[|]|] eqn:Hvalue.
    + unfold progress_state in Hprogress.
      cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
      rewrite Hvalue in Hprogress. discriminate.
    + unfold find_clause in Hprogress. cbn -[find_clause_in] in Hprogress.
      rewrite Hfind in Hprogress. injection Hprogress as <- <-. split.
      * now apply found_clause_implied with
          (s := {| state_trail := m; state_clauses := clauses;
             state_learned := learned; state_watched := cm;
             state_pending := (l, pointer) :: pending |})
          (pointer := pointer).
      * intros x Hxc. destruct (literal_eq_dec x l) as [->|Hneq].
        -- exact Hvalue.
        -- exact (proj2 Hneeds x Hxc Hneq).
    + unfold progress_state in Hprogress.
      cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
      rewrite Hvalue in Hprogress.
      unfold set_propagated_lit in Hprogress.
      eapply set_trail_entry_conflict_sound with
        (s := {| state_trail := m; state_clauses := clauses;
          state_learned := learned; state_watched := cm;
          state_pending := pending |}); [exact (proj1 (proj2 Hinv))|].
      exact Hprogress.
Qed.

Lemma progress_conflict_inv : forall s s' c,
  state_invariant s ->
  progress s = Conflict s' c ->
  state_invariant s' /\ s'.(state_clauses) = s.(state_clauses).
Proof.
  intros [m clauses learned cm pending] s' c Hinv Hprogress.
  pose proof Hprogress as Hprogress_clauses.
  unfold progress in Hprogress. cbn [state_pending state_trail] in Hprogress.
  split; [|now apply progress_conflict_clauses in Hprogress_clauses].
  destruct pending as [|[l pointer] pending].
  - unfold progress_state, problem_vars in Hprogress.
    cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
    destruct (find_undecided_var m (clause_store_vars clauses))
      as [v|] eqn:Hfindvar; [|discriminate].
    eapply set_lit_conflict_inv; [|exact Hinv|exact Hprogress].
    apply var_unassigned_pos_undecided.
    now apply (find_undecided_var_unassigned m (clause_store_vars clauses) v).
  - pose proof (proj1 Hinv) as Hlookup.
    destruct Hlookup as [_ [_ [_ [_ [_ [_ [Hpendinginv _]]]]]]].
    destruct (Hpendinginv l pointer (or_introl eq_refl))
      as [body [Hfind [Hneeds Hnoopp]]].
    change (find_clause_in clauses learned pointer = Some body) in Hfind.
    destruct (literal_value m l) as [[|]|] eqn:Hvalue.
    + unfold progress_state in Hprogress.
      cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
      rewrite Hvalue in Hprogress. discriminate.
    + unfold find_clause in Hprogress. cbn -[find_clause_in] in Hprogress.
      rewrite Hfind in Hprogress. now injection Hprogress as <- <-.
    + unfold progress_state in Hprogress.
      cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
      rewrite Hvalue in Hprogress.
      eapply set_pending_conflict_inv; [exact Hfind| |exact Hinv|exact Hprogress].
      unfold literal_is_undecided. now rewrite Hvalue.
Qed.

Lemma trail_consistent_tail : forall entry trail,
  trail_consistent (entry :: trail) -> trail_consistent trail.
Proof.
  intros entry trail Hconsistent [v [Hpos Hneg]]. apply Hconsistent.
  exists v. split.
  - change (In (Pos v) (trail_literal entry :: trail_model trail)). now right.
  - change (In (Neg v) (trail_literal entry :: trail_model trail)). now right.
Qed.

Lemma trail_invariant_tail : forall clauses learned entry trail,
  trail_invariant clauses learned (entry :: trail) ->
  trail_invariant clauses learned trail.
Proof.
  intros clauses learned entry trail [Hconsistent Hjustified]. split.
  - now apply trail_consistent_tail with (entry := entry).
  - destruct entry as [decision|propagated cause]; cbn in Hjustified.
    + exact (proj2 Hjustified).
    + destruct Hjustified as [_ [c [Hfind [Hneeds Hjustified]]]].
      exact Hjustified.
Qed.

Lemma pop_to_decision_after_trail_invariant :
  forall clauses learned clause after trail,
  trail_invariant clauses learned trail ->
  trail_invariant clauses learned
    (pop_to_decision_after clause after trail).
Proof.
  intros clauses learned clause after trail.
  induction trail as [|entry trail IH] in after |- *;
    intros Hinv; [exact Hinv|].
  assert (trail_invariant clauses learned trail) as Htail.
  { now apply trail_invariant_tail with (entry := entry). }
  destruct entry as [decision|propagated cause];
    cbn [pop_to_decision_after].
  - destruct after.
    + exact Htail.
    + destruct (in_dec literal_eq_dec (opposite_literal decision) clause);
        [exact Htail|now apply IH].
  - destruct (in_dec literal_eq_dec (opposite_literal propagated) clause);
      now apply IH.
Qed.

Lemma pop_to_decision_trail_invariant : forall clauses learned clause trail,
  trail_invariant clauses learned trail ->
  trail_invariant clauses learned (pop_to_decision clause trail).
Proof.
  intros clauses learned clause trail Hinv. unfold pop_to_decision.
  now apply pop_to_decision_after_trail_invariant.
Qed.

Lemma literal_value_false_opposite_in : forall m l,
  literal_value m l = Some false -> In (opposite_literal l) m.
Proof.
  intros m l Hfalse. unfold literal_value in Hfalse.
  destruct (find (fun l' => Id.eqb (literal_var l') (literal_var l)) m)
    as [found|] eqn:Hfind; [|discriminate].
  apply find_some in Hfind as [Hin Hvar]. apply Id.eqb_eq in Hvar.
  destruct found as [v|v], l as [w|w]; cbn in Hvar; subst w;
    try discriminate; exact Hin.
Qed.

Lemma satisfies_opposite_true_is_false : forall m l,
  satisfies_literal m (opposite_literal l) = true ->
  satisfies_literal m l = false.
Proof.
  intros m [v|v]; cbn; destruct (m v); cbn; intros H; try discriminate;
    reflexivity.
Qed.

Lemma satisfies_opposite_false_is_true : forall m l,
  satisfies_literal m (opposite_literal l) = false ->
  satisfies_literal m l = true.
Proof.
  intros m [v|v]; cbn; destruct (m v); cbn; intros H; try discriminate;
    reflexivity.
Qed.

Lemma negated_decisions_false : forall trail m,
  existsb (satisfies_literal m) (negated_decisions trail) = false ->
  forall l, In (Decision l) trail -> satisfies_literal m l = true.
Proof.
  intros trail m Hfalse l Hin.
  assert (In (opposite_literal l) (negated_decisions trail)) as Hopposite.
  { apply negated_decisions_spec. exists l. now split. }
  assert (satisfies_literal m (opposite_literal l) = false) as Hoppfalse.
  { destruct (satisfies_literal m (opposite_literal l)) eqn:Hvalue;
      [|reflexivity].
    assert (existsb (satisfies_literal m) (negated_decisions trail) = true).
    { apply existsb_exists. now exists (opposite_literal l). }
    congruence. }
  now apply satisfies_opposite_false_is_true.
Qed.

Lemma justified_trail_sound : forall clauses learned trail m,
  trail_consistent trail ->
  trail_justified clauses learned trail ->
  (forall ci c, ClauseStore.find ci learned = Some c ->
    clause_implied_by_store clauses c) ->
  satisfies_clause_store m clauses ->
  (forall l, In (Decision l) trail -> satisfies_literal m l = true) ->
  forall l, In l (trail_model trail) -> satisfies_literal m l = true.
Proof.
  intros clauses learned trail. induction trail as [|entry trail IH];
    intros m Hconsistent Hjustified Hlearned Hstore Hdecisions l Hin.
  - contradiction.
  - destruct entry as [decision|propagated cause].
    + cbn in Hjustified. destruct Hjustified as [_ Hjustified].
      change (In l (decision :: trail_model trail)) in Hin.
      destruct Hin as [->|Hin].
      * apply Hdecisions. now left.
      * eapply IH; try eassumption.
        -- now apply trail_consistent_tail with (entry := Decision decision).
        -- intros d Hd. apply Hdecisions. now right.
    + cbn in Hjustified.
      destruct Hjustified as [_ [c [Hfind [Hneeds Hjustified]]]].
      change (In l (propagated :: trail_model trail)) in Hin.
      destruct Hin as [->|Hin].
      * assert (Is_true (satisfies_clause m c)) as Hcausesat.
        { unfold find_clause_in in Hfind.
          destruct cause as [cause|cause].
          - exact (Hstore cause c Hfind).
          - exact (Hlearned cause c Hfind m Hstore). }
        apply Is_true_eq_true in Hcausesat.
        unfold satisfies_clause in Hcausesat.
        apply existsb_exists in Hcausesat as [x [Hxc Hxtrue]].
        destruct (literal_eq_dec x l) as [->|Hneq]; [exact Hxtrue|].
        pose proof (proj2 Hneeds x Hxc Hneq) as Hxfalse.
        apply literal_value_false_opposite_in in Hxfalse.
        assert (satisfies_literal m (opposite_literal x) = true) as Hopptrue.
        { eapply IH; try eassumption.
          - now apply trail_consistent_tail with
              (entry := Propagation l cause).
          - intros d Hd. apply Hdecisions. now right. }
        pose proof (satisfies_opposite_true_is_false m x Hopptrue) as Hxfalse'.
        congruence.
      * eapply IH; try eassumption.
        -- now apply trail_consistent_tail with
             (entry := Propagation propagated cause).
        -- intros d Hd. apply Hdecisions. now right.
Qed.

Lemma in_without_literal : forall removed c l,
  In l (without_literal removed c) <-> In l c /\ l <> removed.
Proof.
  intros removed c l. unfold without_literal. rewrite filter_In.
  destruct (literal_eq_dec l removed); cbn; intuition congruence.
Qed.

Lemma in_clause_union : forall left right l,
  In l (clause_union left right) <-> In l left \/ In l right.
Proof.
  intros left right l. induction left as [|x left IH]; cbn.
  - tauto.
  - destruct (in_dec literal_eq_dec x right) as [Hin|Hnotin].
    + rewrite IH. split; [tauto|]. intros [[<-|Hl]|Hr]; tauto.
    + cbn. rewrite IH. tauto.
Qed.

Lemma resolve_clause_satisfied : forall model pivot left right,
  In (opposite_literal pivot) left ->
  In pivot right ->
  Is_true (satisfies_clause model left) ->
  Is_true (satisfies_clause model right) ->
  Is_true (satisfies_clause model (resolve_clause pivot left right)).
Proof.
  intros model pivot left right Hopleft Hpright Hleft Hright.
  apply Is_true_eq_true in Hleft, Hright. unfold satisfies_clause in *.
  apply existsb_exists in Hleft as [x [Hxleft Hxtrue]].
  apply existsb_exists in Hright as [y [Hyright Hytrue]].
  apply Is_true_eq_left, existsb_exists.
  destruct (literal_eq_dec x (opposite_literal pivot)) as [->|Hxneq].
  - assert (y <> pivot) as Hyneq.
    { intros ->. pose proof (satisfies_opposite_true_is_false model pivot Hxtrue).
      congruence. }
    exists y. split; [|exact Hytrue]. unfold resolve_clause.
    apply in_clause_union. right. apply in_without_literal. now split.
  - exists x. split; [|exact Hxtrue]. unfold resolve_clause.
    apply in_clause_union. left. apply in_without_literal. now split.
Qed.

Lemma analyze_conflict_trail_implied : forall clauses learned trail conflict,
  trail_invariant clauses learned trail ->
  (forall ci c, ClauseStore.find ci learned = Some c ->
    clause_implied_by_store clauses c) ->
  clause_implied_by_store clauses conflict ->
  clause_implied_by_store clauses
    (analyze_conflict_trail clauses learned trail conflict).
Proof.
  intros clauses learned trail. induction trail as [|entry trail IH];
    intros conflict Htrail Hlearned Hconflict; [exact Hconflict|].
  assert (Htail : trail_invariant clauses learned trail).
  { now apply trail_invariant_tail with (entry := entry). }
  destruct entry as [decision|propagated cause]; cbn [analyze_conflict_trail].
  - now apply IH.
  - destruct Htrail as [_ Hjustified]. cbn in Hjustified.
    destruct Hjustified as [_ [reason [Hfind [Hneeds _]]]].
    destruct (in_dec literal_eq_dec (opposite_literal propagated) conflict)
      as [Hin|Hnotin].
    + rewrite Hfind. apply IH; try assumption.
      intros model Hstore. eapply resolve_clause_satisfied.
      * exact Hin.
      * exact (proj1 Hneeds).
      * now apply Hconflict.
      * destruct cause as [ci|ci]; cbn in Hfind.
        -- now apply (Hstore ci reason).
        -- now apply (Hlearned ci reason Hfind model Hstore).
    + now apply IH.
Qed.

Theorem analyze_conflict_implied : forall s conflict learned,
  backtrack_invariant s ->
  analyze_conflict s conflict = Some learned ->
  clause_implied_by_store s.(state_clauses) conflict ->
  clause_falsified_by_model s.(state_trail) conflict ->
  clause_implied_by_store s.(state_clauses) learned.
Proof.
  intros s conflict learned Hinv Hanalyze Hconflict Hfalsified.
  pose proof (analyze_conflict_trail_implied s.(state_clauses)
    s.(state_learned) s.(state_trail) conflict
    (state_invariant_trail s (proj1 Hinv))
    (state_invariant_learned s (proj1 Hinv))
    Hconflict) as Hresolved.
  destruct (analyze_conflict_some s conflict learned Hanalyze)
    as [->|[Hempty ->]]; [exact Hresolved|].
  rewrite Hempty in Hresolved. intros model Hstore.
  specialize (Hresolved model Hstore). contradiction.
Qed.

Lemma literal_is_true_complete_model : forall m l,
  literal_is_true m l = true ->
  satisfies_literal (complete_model m) l = true.
Proof.
  intros m [v|v] Htrue.
  - unfold literal_is_true, literal_value,
      satisfies_literal, complete_model, lit_is_me in *. simpl in *.
    destruct (find (fun l => Id.eqb (literal_var l) v) m) as [[w|w]|];
      try discriminate; reflexivity.
  - unfold literal_is_true, literal_value,
      satisfies_literal, complete_model, lit_is_me in *. simpl in *.
    destruct (find (fun l => Id.eqb (literal_var l) v) m) as [[w|w]|];
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

Lemma find_undecided_var_none : forall m vs v,
  find_undecided_var m vs = None -> In v vs -> var_is_assigned m v = true.
Proof.
  intros m vs. induction vs as [|w vs IH]; intros v Hnone Hin;
    [contradiction|].
  cbn in Hnone. destruct (var_is_assigned m w) eqn:Hassigned.
  - cbn in Hin. destruct Hin as [<-|Hin]; [exact Hassigned|].
    now apply (IH v Hnone Hin).
  - destruct (find_undecided_var m vs); discriminate.
Qed.

Lemma stored_clause_var : forall store ci c l,
  ClauseStore.find ci store = Some c -> In l c ->
  In (literal_var l) (clause_store_vars store).
Proof.
  intros store ci c l Hfind Hin. unfold clause_store_vars.
  apply in_flat_map. exists ci. split.
  - apply (proj1 (ClauseStore.keys_complete store ci)).
    rewrite Hfind. discriminate.
  - rewrite Hfind. apply in_map. exact Hin.
Qed.

Lemma assigned_literal_decided : forall m l,
  var_is_assigned m (literal_var l) = true ->
  literal_is_undecided m l = false.
Proof.
  intros m l Hassigned. destruct (literal_is_undecided m l) eqn:Hundecided;
    [|reflexivity].
  apply existsb_exists in Hassigned as [x [Hxm Hvar]].
  apply Id.eqb_eq in Hvar.
  exfalso. apply (literal_undecided_not_InL m l Hundecided).
  destruct x; cbn in Hvar; subst; [left|right]; exact Hxm.
Qed.

Lemma all_clause_literals_decided : forall s c,
  find_undecided_var s.(state_trail) (problem_vars s) = None ->
  (exists ci, ClauseStore.find ci s.(state_clauses) = Some c) ->
  filter (literal_is_undecided s.(state_trail)) c = [].
Proof.
  intros s c Hnone [ci Hfind].
  assert (Hdecided : forall l, In l c ->
      literal_is_undecided s.(state_trail) l = false).
  { intros l Hin.
    pose proof (stored_clause_var s.(state_clauses) ci c l Hfind Hin) as Hvar.
    pose proof (find_undecided_var_none s.(state_trail) (problem_vars s)
      (literal_var l) Hnone Hvar) as Hassigned.
    now apply assigned_literal_decided. }
  clear Hfind Hnone ci.
  induction c as [|l c IH]; [reflexivity|].
  cbn. rewrite Hdecided by now left. apply IH.
  intros x Hin. apply Hdecided. now right.
Qed.

Lemma terminal_state_satisfies_clauses : forall s,
  state_invariant s ->
  falsified_clauses_pending s ->
  rush_has_work s = false ->
  satisfies_clause_store (complete_model s.(state_trail)) s.(state_clauses).
Proof.
  intros s [[Hcover _] _] Hfalsified Hhaswork ci c Hfind.
  destruct (existsb (literal_is_true s.(state_trail)) c) eqn:Hknown.
  - apply Is_true_eq_left. unfold satisfies_clause.
    apply existsb_exists in Hknown as [l [Hlc Hlt]].
    apply existsb_exists. exists l. split; [exact Hlc|].
    now apply literal_is_true_complete_model.
  - assert (Hunsatisfied : Is_true
      (negb (existsb (literal_is_true s.(state_trail)) c))).
    { apply Is_true_eq_left. now rewrite Hknown. }
    specialize (Hcover (Source ci) c Hfind Hunsatisfied).
    destruct Hcover as [Htrivial|[Hwork|[[Hwatched Hundecided]|Hfals]]].
    + now apply opposite_literals_satisfied.
    + contradiction.
    + exfalso. apply Hundecided.
      apply all_clause_literals_decided.
      * unfold rush_has_work in Hhaswork.
        destruct s.(state_pending) as [|p pending]; [|discriminate].
        destruct (find_undecided_var s.(state_trail) (problem_vars s))
          as [v|] eqn:Hundecfind; [discriminate|reflexivity].
      * now exists ci.
    + unfold queued_clause in Hfals.
      destruct Hfals as [Hfals|[p Hpending]].
      * destruct (Hfalsified (Source ci) Hfals) as [l Hin].
        unfold rush_has_work in Hhaswork.
        destruct s.(state_pending) as [|q pending] eqn:Hpendingqueue.
        -- contradiction.
        -- discriminate.
      * unfold rush_has_work in Hhaswork.
        destruct s.(state_pending) as [|q pending] eqn:Hpendingqueue.
        -- contradiction.
        -- discriminate.
Qed.

Lemma propagate_pending_preserved : forall falsified ci s s' l d,
  propagate falsified ci s = Progress s' ->
  In (l, d) s.(state_pending) ->
  In (l, d) s'.(state_pending).
Proof.
  intros falsified ci [m clauses learned cm pending] s' l d Hpropagate Hin.
  unfold propagate, find_clause in Hpropagate. cbn -[find_clause_in] in *.
  destruct (find_clause_in clauses learned ci) as [c|].
  - destruct (scan_clause (map trail_literal m) falsified ci c cm);
      try discriminate; injection Hpropagate as <-; cbn; auto.
  - injection Hpropagate as <-. exact Hin.
Qed.

Lemma propagate_clauses_pending_preserved : forall falsified work s s' l d,
  propagate_clauses falsified work s = Progress s' ->
  In (l, d) s.(state_pending) ->
  In (l, d) s'.(state_pending).
Proof.
  intros falsified work. induction work as [|ci work IH];
    intros s s' l d Hpropagates Hin.
  - injection Hpropagates as <-. exact Hin.
  - cbn [propagate_clauses] in Hpropagates.
    destruct (propagate falsified ci s) as [next|conflict cause]
      eqn:Hpropagate.
    + eapply IH; [exact Hpropagates|].
      eapply propagate_pending_preserved; [exact Hpropagate|exact Hin].
    + destruct (propagate_clauses falsified work conflict); discriminate.
Qed.

Lemma propagate_pointer_not_falsified : forall falsified ci s s',
  propagate falsified ci s = Progress s' ->
  ~ falsified_clause ci s'.
Proof.
  intros falsified ci [m clauses learned cm pending] s' Hpropagate Hfalse.
  unfold propagate, find_clause in Hpropagate.
  cbn -[find_clause_in] in Hpropagate.
  destruct (find_clause_in clauses learned ci) as [c|] eqn:Hfind.
  2:{ injection Hpropagate as <-. destruct Hfalse as [body [Hbody _]].
      change (find_clause_in clauses learned ci = Some body) in Hbody.
      rewrite Hfind in Hbody. discriminate. }
  destruct (scan_clause (map trail_literal m) falsified ci c cm)
    as [l cm'|cm'|cm'|cm'] eqn:Hscan; try discriminate;
    injection Hpropagate as <-; destruct Hfalse as [body [Hbody [Hfalse Hnone]]];
    change (find_clause_in clauses learned ci = Some body) in Hbody;
    rewrite Hfind in Hbody; injection Hbody as <-;
    cbn [state_trail] in Hfalse, Hnone.
  - destruct (scan_clause_inl_spec _ _ _ _ _ _ _ Hscan)
      as [_ [Hlc [Hlu _]]].
    assert (In l (filter (literal_is_undecided m) c)).
    { apply filter_In. now split. }
    now rewrite Hnone in H.
  - destruct (scan_clause_decided_spec _ _ _ _ _ _ Hscan) as [Hsat _].
    change (existsb (literal_is_true m) c = true) in Hsat.
    apply Is_true_eq_true in Hfalse. rewrite Hsat in Hfalse. discriminate.
  - destruct (scan_clause_watched_spec _ _ _ _ _ _ Hscan)
      as [l [l' [_ [Hlc [_ [Hlu _]]]]]].
    assert (In l (filter (literal_is_undecided m) c)).
    { apply filter_In. now split. }
    now rewrite Hnone in H.
Qed.

Lemma propagate_clauses_falsified_iff : forall falsified work s s' d,
  propagate_clauses falsified work s = Progress s' ->
  falsified_clause d s' <-> falsified_clause d s.
Proof.
  intros falsified work s s' d Hpropagates.
  pose proof (propagate_clauses_result_trail falsified work s) as Htrail.
  pose proof (propagate_clauses_result_clauses falsified work s) as Hclauses.
  pose proof (propagate_clauses_result_learned falsified work s) as Hlearned.
  rewrite Hpropagates in Htrail, Hclauses, Hlearned. cbn in Htrail, Hclauses, Hlearned.
  unfold falsified_clause, find_clause. rewrite Htrail, Hclauses, Hlearned.
  reflexivity.
Qed.

Lemma propagate_clauses_work_not_falsified : forall falsified work s s' d,
  propagate_clauses falsified work s = Progress s' ->
  In d work ->
  ~ falsified_clause d s'.
Proof.
  intros falsified work. induction work as [|ci work IH];
    intros s s' d Hpropagates Hin; [contradiction|].
  cbn [propagate_clauses] in Hpropagates.
  destruct (propagate falsified ci s) as [next|conflict cause]
    eqn:Hpropagate.
  - destruct Hin as [<-|Hin].
    + intros Hfalse. apply (propagate_pointer_not_falsified
        falsified ci s next Hpropagate).
      apply (proj1 (propagate_clauses_falsified_iff
        falsified work next s' ci Hpropagates)). exact Hfalse.
    + eapply IH; [exact Hpropagates|exact Hin].
  - destruct (propagate_clauses falsified work conflict); discriminate.
Qed.

Lemma falsified_clause_has_no_opposites : forall s ci,
  trail_consistent s.(state_trail) ->
  falsified_clause ci s ->
  forall c, find_clause ci s = Some c -> ~ has_opposite_literals c.
Proof.
  intros s ci Hconsistent [body [Hbody [Hfalse Hnone]]] c Hfind Hopp.
  rewrite Hfind in Hbody. injection Hbody as <-.
  destruct Hopp as [v [Hpos Hneg]].
  assert (Hposfalse : literal_value s.(state_trail) (Pos v) = Some false).
  { exact (falsified_clause_spec s.(state_trail) c Hfalse Hnone
      (Pos v) Hpos). }
  assert (Hnegfalse : literal_value s.(state_trail) (Neg v) = Some false).
  { exact (falsified_clause_spec s.(state_trail) c Hfalse Hnone
      (Neg v) Hneg). }
  pose proof (literal_value_false_opposite_in _ _ Hposfalse) as Hnegmodel.
  pose proof (literal_value_false_opposite_in _ _ Hnegfalse) as Hposmodel.
  change (In (Neg v) (trail_model s.(state_trail))) in Hnegmodel.
  change (In (Pos v) (trail_model s.(state_trail))) in Hposmodel.
  apply Hconsistent. now exists v.
Qed.

Lemma newly_falsified_classified : forall s l ci,
  state_invariant s ->
  falsified_clauses_pending s ->
  literal_is_undecided s.(state_trail) l = true ->
  falsified_clause ci
    {| state_trail := Decision l :: s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := ClauseMap.clear_falsified l s.(state_watched);
       state_pending := [] |} ->
  In ci (ClauseMap.find_falsified l s.(state_watched)) \/
  exists p, In (p, ci) s.(state_pending).
Proof.
  intros s l ci [Hstaged [Hlearned Harity]] Hfalsified Hlu Hnew.
  destruct Hnew as [c [Hfind [Hfalse Hnone]]].
  cbn [find_clause state_clauses state_learned state_trail] in Hfind, Hfalse, Hnone.
  change (find_clause ci s = Some c) in Hfind.
  assert (Holdfalse : Is_true
      (negb (existsb (literal_is_true s.(state_trail)) c))).
  { apply negb_prop_intro. intros Hsat. apply (negb_prop_elim _ Hfalse).
    now apply satisfied_cons_undecided. }
  destruct (filter (literal_is_undecided s.(state_trail)) c)
    as [|p undecided] eqn:Holdundecided.
  - right. apply Hfalsified. exists c. repeat split; assumption.
  - assert (Hneeds : clause_needs_literal s.(state_trail)
        (opposite_literal l) c).
    { eapply newly_falsified_needs_opposite;
        [exact Hlu|exact Hfalse|exact Hnone|].
      rewrite Holdundecided. discriminate. }
    assert (Htrailconsistent : trail_consistent
        (Decision l :: s.(state_trail))).
    { apply trail_consistent_decision; [exact Hlu|].
      exact (proj1 (state_invariant_trail s
        (conj Hstaged (conj Hlearned Harity)))). }
    assert (Hnoopp : ~ has_opposite_literals c).
    { eapply falsified_clause_has_no_opposites with
        (s := {| state_trail := Decision l :: s.(state_trail);
          state_clauses := s.(state_clauses);
          state_learned := s.(state_learned);
          state_watched := ClauseMap.clear_falsified l s.(state_watched);
          state_pending := [] |}) (ci := ci); eauto.
      exists c. cbn. now repeat split. }
    specialize (Harity ci c Hfind ltac:(simpl; tauto) Hnoopp).
    destruct Harity as [[Htwo Hcard]|[Hnotwo Hcard]].
    + left. assert (ClauseMap.card_of ci s.(state_watched) > 0)
        as Hpositive by lia.
      apply ClauseMap.card_of_pos in Hpositive as [v Hv].
      unfold staged_invariant in Hstaged.
      destruct Hstaged as [_ [_ [Hwatch _]]].
      destruct (Hwatch v ci Hv) as
        [body [Hbody [Hfollow [HinL [Hbody_noopp [Hpos Hneg]]]]]].
      rewrite Hfind in Hbody. injection Hbody as <-.
      destruct (Hfollow ltac:(simpl; tauto)) as [Hfollow_needed _].
      unfold follows_needed_literal in Hfollow_needed.
      assert (Hoppu : literal_is_undecided s.(state_trail)
          (opposite_literal l) = true).
      { destruct l; cbn;
          [now rewrite <- literal_is_undecided_pos_neg|
           now rewrite literal_is_undecided_pos_neg]. }
      specialize (Hfollow_needed s.(state_trail)
        (model_suffix_refl _) (opposite_literal l) Hoppu Hneeds).
      destruct l as [w|w]; cbn in Hfollow_needed |- *;
        unfold ClauseMap.find in Hfollow_needed;
        apply in_app_or in Hfollow_needed as [Hpositive|Hnegative].
      * destruct (Hwatch w ci (in_or_app _ _ _ (or_introl Hpositive))) as
          [body [Hbody [_ [_ [_ [Hposw _]]]]]].
        rewrite Hfind in Hbody. injection Hbody as <-.
        exfalso. apply Hbody_noopp. exists w. split.
        -- now apply Hposw.
        -- exact (proj1 Hneeds).
      * exact Hnegative.
      * exact Hpositive.
      * destruct (Hwatch w ci (in_or_app _ _ _ (or_intror Hnegative))) as
          [body [Hbody [_ [_ [_ [_ Hnegw]]]]]].
        rewrite Hfind in Hbody. injection Hbody as <-.
        exfalso. apply Hbody_noopp. exists w. split.
        -- exact (proj1 Hneeds).
        -- now apply Hnegw.
    + right. unfold staged_invariant in Hstaged.
      destruct Hstaged as [Hcover _].
      specialize (Hcover ci c Hfind Holdfalse).
      destruct Hcover as [Hopp|[Hwork|[[Hwatched Hnonempty]|Hqueued]]].
      * contradiction.
      * contradiction.
      * destruct Hwatched as [v Hv].
        pose proof (ClauseMap.card_of_in _ _ _ Hv) as Hpositive. lia.
      * destruct Hqueued as [Holdfalseclause|Hpending].
        -- destruct Holdfalseclause as [body [Hbody [_ Holdnone]]].
           rewrite Hfind in Hbody. injection Hbody as <-.
           rewrite Holdundecided in Holdnone. discriminate.
        -- exact Hpending.
Qed.

Lemma set_trail_entry_falsified_pending : forall entry s pending s',
  state_invariant s ->
  literal_is_undecided s.(state_trail) (trail_literal entry) = true ->
  falsified_clauses_pending s ->
  (forall d,
    falsified_clause d
      {| state_trail := Decision (trail_literal entry) :: s.(state_trail);
         state_clauses := s.(state_clauses);
         state_learned := s.(state_learned);
         state_watched := ClauseMap.clear_falsified (trail_literal entry)
           s.(state_watched);
         state_pending := [] |} ->
    forall p, In (p, d) s.(state_pending) ->
      exists q, In (q, d) pending) ->
  set_trail_entry entry
    {| state_trail := s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |} = Progress s' ->
  falsified_clauses_pending s'.
Proof.
  intros entry s pending s' Hinv Hlu Hfalsified Hkept Hset ci Hfalse.
  unfold set_trail_entry in Hset.
  cbn [state_trail state_clauses state_learned state_watched state_pending]
    in Hset.
  set (l := trail_literal entry) in *.
  set (base := {| state_trail := entry :: s.(state_trail);
    state_clauses := s.(state_clauses); state_learned := s.(state_learned);
    state_watched := ClauseMap.clear_falsified l s.(state_watched);
    state_pending := pending |}) in *.
  assert (Hbasefalse : falsified_clause ci base).
  { apply (proj1 (propagate_clauses_falsified_iff
      (opposite_literal l) (ClauseMap.find_falsified l s.(state_watched))
      base s' ci Hset)).
    exact Hfalse. }
  assert (Hclassified :
      In ci (ClauseMap.find_falsified l s.(state_watched)) \/
      exists p, In (p, ci) s.(state_pending)).
  { eapply newly_falsified_classified; [exact Hinv|exact Hfalsified|exact Hlu|].
    subst base.
    destruct Hbasefalse as [c [Hfind [Hfalse' Hnone]]].
    exists c. cbn [trail_model trail_literal]
      in Hfind, Hfalse', Hnone |- *. now repeat split. }
  destruct Hclassified as [Hinwork|[p Hinpending]].
  - exfalso. eapply propagate_clauses_work_not_falsified;
      [exact Hset|exact Hinwork|exact Hfalse].
  - destruct (Hkept ci ltac:(
        subst base;
        destruct Hbasefalse as [c [Hfind [Hfalse' Hnone]]];
        exists c; cbn [trail_model trail_literal]
          in Hfind, Hfalse', Hnone |- *; now repeat split)
      p Hinpending) as [q Hq].
    exists q. eapply propagate_clauses_pending_preserved;
      [exact Hset|exact Hq].
Qed.

Lemma progress_falsified_empty : forall s s',
  state_invariant s ->
  falsified_clauses_pending s ->
  progress s = Progress s' ->
  falsified_clauses_pending s'.
Proof.
  intros [m clauses learned cm pending] s' Hinv Hfalsified Hprogress.
  unfold progress in Hprogress. cbn [state_pending state_trail] in Hprogress.
  destruct pending as [|[l ci] pending].
  - unfold progress_state, problem_vars in Hprogress.
    cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
    destruct (find_undecided_var m (clause_store_vars clauses))
      as [v|] eqn:Hfind.
    + unfold set_lit in Hprogress.
      eapply set_trail_entry_falsified_pending
        with (s := {| state_trail := m; state_clauses := clauses;
          state_learned := learned; state_watched := cm;
          state_pending := [] |}) (pending := []) (entry := Decision (Pos v)).
      * exact Hinv.
      * apply var_unassigned_pos_undecided.
        now apply (find_undecided_var_unassigned m
          (clause_store_vars clauses) v).
      * exact Hfalsified.
      * intros d Hnew p Hp. contradiction.
      * exact Hprogress.
    + injection Hprogress as <-. exact Hfalsified.
  - pose proof Hinv as Hpendinginv.
    destruct Hpendinginv as [Hstaged _]. unfold staged_invariant in Hstaged.
    destruct Hstaged as [_ [_ [_ [_ [_ [_ [Hpending _]]]]]]].
    destruct (Hpending l ci (or_introl eq_refl))
      as [c [Hfind [Hneeds Hnoopp]]].
    change (find_clause_in clauses learned ci = Some c) in Hfind.
    destruct (literal_value m l) as [[|]|] eqn:Hvalue.
    + unfold progress_state in Hprogress.
      cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
      rewrite Hvalue in Hprogress. injection Hprogress as <-.
      intros d Hfalse. destruct (Hfalsified d Hfalse) as [p Hp].
      destruct Hp as [Heq|Hp]; [|now exists p].
      injection Heq as <- <-. exfalso.
      destruct Hfalse as [body [Hbody [Hfalse _]]].
      change (find_clause_in clauses learned ci = Some body) in Hbody.
      rewrite Hfind in Hbody. injection Hbody as <-.
      apply (negb_prop_elim _ Hfalse).
      apply Is_true_eq_left, existsb_exists. exists l.
      split; [exact (proj1 Hneeds)|].
      change (literal_is_true m l = true).
      unfold literal_is_true. now rewrite Hvalue.
    + unfold find_clause in Hprogress. cbn -[find_clause_in] in Hprogress.
      rewrite Hfind in Hprogress. discriminate.
    + unfold progress_state in Hprogress.
      cbn [state_pending state_trail state_clauses state_watched] in Hprogress.
      rewrite Hvalue in Hprogress.
      unfold set_propagated_lit in Hprogress.
      eapply set_trail_entry_falsified_pending
        with (s := {| state_trail := m; state_clauses := clauses;
          state_learned := learned; state_watched := cm;
          state_pending := (l, ci) :: pending |}) (pending := pending)
          (entry := Propagation l ci).
      * exact Hinv.
      * change (literal_is_undecided m l = true).
        unfold literal_is_undecided. now rewrite Hvalue.
      * exact Hfalsified.
      * intros d Hnew p Hp. destruct Hp as [Heq|Hp]; [|now exists p].
        injection Heq as <- <-.
        destruct Hnew as [body [Hbody [Hfalse Hnone]]].
        cbn [find_clause state_clauses state_learned state_trail]
          in Hbody, Hfalse, Hnone.
        change (find_clause_in clauses learned ci = Some body) in Hbody.
        rewrite Hfind in Hbody. injection Hbody as <-.
        exfalso. apply (negb_prop_elim _ Hfalse).
        apply Is_true_eq_left, existsb_exists. exists l.
        split; [exact (proj1 Hneeds)|apply literal_is_true_cons_self].
      * exact Hprogress.
Qed.

Lemma below_current_level_model_suffix : forall trail,
  model_suffix (trail_model (below_current_level trail)) (trail_model trail).
Proof.
  intros trail. induction trail as [|entry trail IH];
    [apply model_suffix_refl|].
  destruct entry as [l|l cause]; cbn [below_current_level trail_model].
  - exists [l]. reflexivity.
  - eapply model_suffix_trans; [exact IH|]. exists [l]. reflexivity.
Qed.

Lemma propagation_current_level_falsified : forall s l cause pending,
  current_level_falsified_invariant s ->
  literal_is_undecided s.(state_trail) l = true ->
  current_level_falsified_invariant
    {| state_trail := Propagation l cause :: s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |}.
Proof.
  intros s l cause pending Hcurrent Hlu Hdecision ci c Hfind Hnewfalse.
  cbn [trail_has_decision below_current_level find_clause
    state_trail state_clauses state_learned] in Hdecision, Hfind |- *.
  change (find_clause ci s = Some c) in Hfind.
  change (clause_falsified_by_model
    (trail_model (Propagation l cause :: s.(state_trail))) c) in Hnewfalse.
  destruct (filter (literal_is_undecided s.(state_trail)) c)
    as [|p undecided] eqn:Hundecided.
  - apply (Hcurrent Hdecision ci c Hfind).
    apply falsified_clause_spec.
    + apply negb_prop_intro. intros Hsat.
      pose proof (satisfied_cons_undecided s.(state_trail) l c Hlu Hsat)
        as Hnewsat.
      apply Is_true_eq_true in Hnewsat.
      apply existsb_exists in Hnewsat as [x [Hxc Htrue]].
      specialize (Hnewfalse x Hxc).
      change (literal_value (l :: trail_model s.(state_trail)) x = Some false)
        in Hnewfalse.
      unfold literal_is_true in Htrue. now rewrite Hnewfalse in Htrue.
    + exact Hundecided.
  - intros Hbelowfalse.
    assert (Hpin : In p c /\
        literal_is_undecided s.(state_trail) p = true).
    { apply filter_In. rewrite Hundecided. now left. }
    pose proof (undecided_model_suffix _ _ p
      (below_current_level_model_suffix s.(state_trail)) (proj2 Hpin)) as Hpu.
    specialize (Hbelowfalse p (proj1 Hpin)).
    unfold literal_is_undecided in Hpu. rewrite Hbelowfalse in Hpu.
    discriminate.
Qed.

Lemma decision_current_level_falsified : forall s l pending,
  no_falsified_clauses s ->
  current_level_falsified_invariant
    {| state_trail := Decision l :: s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |}.
Proof.
  intros s l pending Hnone Hdecision ci c Hfind Hnewfalse.
  cbn [below_current_level find_clause state_trail state_clauses state_learned]
    in Hfind |- *.
  change (find_clause ci s = Some c) in Hfind.
  intros Holdfalse. apply (Hnone ci). exists c. split; [exact Hfind|].
  pose proof (falsified_scan_clause_once s.(state_trail) c Holdfalse) as Hscan.
  rewrite scan_clause_once_spec in Hscan.
  injection Hscan as Hsatisfied Hundecided. split; [|exact Hundecided].
  apply Is_true_eq_left. now rewrite Hsatisfied.
Qed.

Lemma set_trail_entry_current_level : forall entry s pending,
  current_level_falsified_invariant
    {| state_trail := entry :: s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |} ->
  current_level_falsified_invariant
    (progress_result_state
      (set_trail_entry entry
        {| state_trail := s.(state_trail);
           state_clauses := s.(state_clauses);
           state_learned := s.(state_learned);
           state_watched := s.(state_watched);
           state_pending := pending |})).
Proof.
  intros entry s pending Hcurrent.
  unfold current_level_falsified_invariant in Hcurrent |- *.
  pose proof (set_trail_entry_result_trail entry
    {| state_trail := s.(state_trail); state_clauses := s.(state_clauses);
       state_learned := s.(state_learned); state_watched := s.(state_watched);
       state_pending := pending |}) as Htrail.
  pose proof (set_trail_entry_result_clauses entry
    {| state_trail := s.(state_trail); state_clauses := s.(state_clauses);
       state_learned := s.(state_learned); state_watched := s.(state_watched);
       state_pending := pending |}) as Hclauses.
  pose proof (set_trail_entry_result_learned entry
    {| state_trail := s.(state_trail); state_clauses := s.(state_clauses);
       state_learned := s.(state_learned); state_watched := s.(state_watched);
       state_pending := pending |}) as Hlearned.
  cbn [state_trail state_clauses state_learned] in Htrail, Hclauses, Hlearned.
  intros Hdecision ci c Hfind Hfalse.
  rewrite Htrail in Hdecision, Hfalse |- *.
  unfold find_clause in Hfind.
  rewrite Hclauses, Hlearned in Hfind.
  exact (Hcurrent Hdecision ci c Hfind Hfalse).
Qed.

Lemma progress_result_current_level : forall s,
  state_invariant s ->
  current_level_falsified_invariant s ->
  falsified_clauses_pending s ->
  current_level_falsified_invariant (progress_result_state (progress s)).
Proof.
  intros s Hinv Hcurrent Hfalsified.
  unfold progress. destruct s.(state_pending) as [|[l ci] pending] eqn:Hpending.
  - unfold progress_state. rewrite Hpending.
    destruct (find_undecided_var s.(state_trail) (problem_vars s)) as [v|].
    + unfold set_lit. apply set_trail_entry_current_level.
      apply decision_current_level_falsified.
      intros ci Hfalse. destruct (Hfalsified ci Hfalse) as [p Hp].
      rewrite Hpending in Hp. contradiction.
    + exact Hcurrent.
  - destruct (literal_value s.(state_trail) l) as [[|]|] eqn:Hvalue.
    + unfold progress_state. rewrite Hpending, Hvalue. exact Hcurrent.
    + destruct (find_clause ci s); exact Hcurrent.
    + unfold progress_state. rewrite Hpending, Hvalue.
      unfold set_propagated_lit. apply set_trail_entry_current_level.
      apply propagation_current_level_falsified; [exact Hcurrent|].
      unfold literal_is_undecided. now rewrite Hvalue.
Qed.

Lemma rush_unfold : forall s,
  rush s =
    if rush_has_work s then
      match progress s with
      | Progress s' => Later (rush s')
      | Conflict s' cause => Now (inr (s', cause))
      end
    else Now (inl s).
Proof.
  intros s.
  transitivity
    (match rush s with Now x => Now x | Later d => Later d end).
  - destruct (rush s); reflexivity.
  - cbn [rush]. destruct (rush_has_work s); [|reflexivity].
    destruct (progress s); reflexivity.
Qed.

Lemma rush_result_model_sound : forall s result,
  state_invariant s ->
  falsified_clauses_pending s ->
  delay_returns (rush s) result ->
  match result with
  | inl s' =>
      satisfies_clause_store (complete_model s'.(state_trail)) s.(state_clauses)
  | inr (s', cause) =>
      clause_implied_by_store s.(state_clauses) cause /\
      clause_falsified_by_model s'.(state_trail) cause
  end.
Proof.
  intros s result Hinv Hfalsified Hreturns.
  remember (rush s) as d eqn:Hrush.
  induction Hreturns as [x|d x Hreturns IH] in s, Hinv, Hfalsified, Hrush |- *.
  - rewrite rush_unfold in Hrush.
    destruct (rush_has_work s) eqn:Hwork.
    + destruct (progress s) as [s'|s' cause] eqn:Hprogress;
        [discriminate|].
      injection Hrush as ->. now apply progress_conflict with (s := s).
    + injection Hrush as ->.
      now apply terminal_state_satisfies_clauses.
  - rewrite rush_unfold in Hrush.
    destruct (rush_has_work s) eqn:Hwork; [|discriminate].
    destruct (progress s) as [s'|s' cause] eqn:Hprogress; [|discriminate].
    injection Hrush as ->.
    assert (Hinv' : state_invariant s') by
      (now apply progress_inv with (s := s)).
    assert (Hfalsified' : falsified_clauses_pending s') by
      (now apply progress_falsified_empty with (s := s)).
    specialize (IH s' Hinv' Hfalsified' eq_refl).
    destruct x as [final|[latest cause]].
    + rewrite <- (progress_clauses s s' Hprogress). exact IH.
    + destruct IH as [Himplied Hfalsifiedcause]. split.
      * rewrite (progress_clauses s s' Hprogress) in Himplied.
        exact Himplied.
      * exact Hfalsifiedcause.
Qed.

Lemma rush_result_inv : forall s result,
  state_invariant s ->
  delay_returns (rush s) result ->
  match result with
  | inl final =>
      state_invariant final /\ final.(state_clauses) = s.(state_clauses)
  | inr (final, _) =>
      state_invariant final /\ final.(state_clauses) = s.(state_clauses)
  end.
Proof.
  intros s result Hinv Hreturns.
  remember (rush s) as d eqn:Hrush.
  induction Hreturns as [x|d x Hreturns IH] in s, Hinv, Hrush |- *.
  - rewrite rush_unfold in Hrush.
    destruct (rush_has_work s) eqn:Hwork.
    + destruct (progress s) as [s'|s' cause] eqn:Hprogress;
        [discriminate|].
      injection Hrush as ->.
      exact (progress_conflict_inv s s' cause Hinv Hprogress).
    + injection Hrush as ->. now split.
  - rewrite rush_unfold in Hrush.
    destruct (rush_has_work s) eqn:Hwork; [|discriminate].
    destruct (progress s) as [s'|s' cause] eqn:Hprogress;
      [|discriminate].
    injection Hrush as ->.
    assert (Hinv' : state_invariant s') by
      (now apply progress_inv with (s := s)).
    specialize (IH s' Hinv' eq_refl).
    destruct x as [final|[latest cause]].
    + destruct IH as [Hfinal Hclauses]. split; [exact Hfinal|].
      rewrite Hclauses. now apply progress_clauses in Hprogress.
    + destruct IH as [Hfinal Hclauses]. split; [exact Hfinal|].
      rewrite Hclauses. now apply progress_clauses in Hprogress.
Qed.

Theorem rush_conflict_inv : forall s final cause,
  state_invariant s ->
  delay_returns (rush s) (inr (final, cause)) ->
  state_invariant final /\ final.(state_clauses) = s.(state_clauses).
Proof.
  intros s final cause Hinv Hreturns.
  exact (rush_result_inv s (inr (final, cause)) Hinv Hreturns).
Qed.

Theorem rush_model_sound : forall s final,
  state_invariant s ->
  falsified_clauses_pending s ->
  delay_returns (rush s) (inl final) ->
  satisfies_clause_store
    (complete_model final.(state_trail)) s.(state_clauses).
Proof.
  intros s final Hinv Hfalsified Hreturns.
  exact (rush_result_model_sound s (inl final) Hinv Hfalsified Hreturns).
Qed.

Theorem rush_conflict_sound : forall s final cause,
  state_invariant s ->
  falsified_clauses_pending s ->
  delay_returns (rush s) (inr (final, cause)) ->
  clause_implied_by_store s.(state_clauses) cause /\
  clause_falsified_by_model final.(state_trail) cause.
Proof.
  intros s final cause Hinv Hfalsified Hreturns.
  exact (rush_result_model_sound s (inr (final, cause))
    Hinv Hfalsified Hreturns).
Qed.

Lemma two_added_watches_arity :
  forall ci c l l' m clauses learned cm pending,
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  clause_has_two_variables c ->
  ClauseMap.card_of ci cm = 0 ->
  staged_clause_arity [ci]
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  staged_clause_arity []
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := ClauseMap.add l' ci (ClauseMap.add l ci cm);
       state_pending := pending |}.
Proof.
  intros ci c l l' m clauses learned cm pending Hfind Hnoopp Htwo
    Hzero Harity d body Hbody _ Hbody_noopp.
  destruct (clause_pointer_eq_dec d ci) as [->|Hneq].
  - change (find_clause_in clauses learned ci = Some body) in Hbody.
    rewrite Hfind in Hbody. injection Hbody as <-. left. split; [exact Htwo|].
    cbn [state_watched]. now rewrite !ClauseMap.card_of_add, Hzero.
  - assert (~ In d [ci]) as Hnotstaged.
    { intros [Heq|Hin]; [apply Hneq; symmetry; exact Heq|contradiction]. }
    specialize (Harity d body Hbody Hnotstaged Hbody_noopp).
    cbn [state_watched].
    rewrite !ClauseMap.card_of_add_neq by exact (not_eq_sym Hneq).
    exact Harity.
Qed.

Lemma add_source_staged_arity : forall s c,
  state_invariant s ->
  staged_clause_arity [Source (fresh_clause_id s)]
    {| state_trail := s.(state_trail);
       state_clauses := ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := s.(state_pending) |}.
Proof.
  intros s c [_ [_ Harity]] [d|d] body Hfind Hnotstaged Hnoopp.
  - cbn [find_clause find_clause_in state_clauses state_learned] in Hfind.
    rewrite ClauseStore.find_add_eq in Hfind.
    destruct (ClauseIdKey.eq_dec (fresh_clause_id s) d) as [Heq|Hneq].
    + subst d. exfalso. apply Hnotstaged. exact (or_introl eq_refl).
    + eapply Harity; [exact Hfind|simpl; tauto|exact Hnoopp].
  - eapply Harity; [exact Hfind|simpl; tauto|exact Hnoopp].
Qed.

Lemma add_learned_staged_arity : forall s c,
  state_invariant s ->
  staged_clause_arity [Learned (fresh_learned_clause_id s)]
    {| state_trail := s.(state_trail); state_clauses := s.(state_clauses);
       state_learned := ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := s.(state_pending) |}.
Proof.
  intros s c [_ [_ Harity]] d body Hfind Hnotstaged Hnoopp.
  pose proof (find_learned_add_cases s c s.(state_trail) s.(state_watched)
    s.(state_pending) d body Hfind) as [[Heq Hbody]|Hold].
  - subst d body. exfalso. apply Hnotstaged. exact (or_introl eq_refl).
  - eapply Harity; [exact Hold|simpl; tauto|exact Hnoopp].
Qed.

Lemma install_watches_decided_inv : forall ci c m clauses learned cm pending,
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  decided_clause ci
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  ClauseMap.card_of ci cm = 0 ->
  (forall v, ~ In ci (ClauseMap.find v cm)) ->
  clause_has_two_undecided m c ->
  staged_invariant [ci]
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  learned_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  staged_clause_arity [ci]
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  state_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := install_watches m ci c cm; state_pending := pending |}.
Proof.
  intros ci c m clauses learned cm pending Hfind Hnoopp Hdecided Hzero
    Hfresh Htwo Hstage Hlearned Hbasearity.
  unfold state_invariant. split.
  - unfold install_watches. rewrite scan_clause_once_spec. cbn [snd].
  destruct (filter (literal_is_undecided m) c) as [|l undecided] eqn:Hfilter.
  + destruct Htwo as [x [y [Hxc [_ [_ [Hxu _]]]]]].
    assert (In x (filter (literal_is_undecided m) c)) by
      (apply filter_In; now split).
    now rewrite Hfilter in H.
  + destruct (find_different_var (literal_var l) undecided) as [l'|]
      eqn:Hdifferent.
    * apply find_different_var_spec in Hdifferent as [Hl'in Hvars].
      assert (Hlin' : In l (filter (literal_is_undecided m) c)) by
        (rewrite Hfilter; now left).
      assert (Hl'in'' : In l' (filter (literal_is_undecided m) c)) by
        (rewrite Hfilter; now right).
      apply filter_In in Hlin' as [Hlin Hlu].
      apply filter_In in Hl'in'' as [Hl'in' Hl'u].
      assert (Hrecent : forall model, model_suffix model m ->
          Is_true (negb (existsb (literal_is_true model) c)) ->
          clause_has_two_undecided model c ->
          literal_is_undecided model l = true /\
          literal_is_undecided model l' = true).
      { intros model Hsuffix _ _. split.
        - exact (undecided_model_suffix (trail_model m) model l Hsuffix Hlu).
        - exact (undecided_model_suffix (trail_model m) model l' Hsuffix Hl'u). }
      eapply watch_two_fresh_inv with (l := l) (l' := l').
      all: try eassumption.
      all: apply Hfresh.
    * exfalso. destruct Htwo as
        [x [y [Hxc [Hyc [Hxy [Hxu Hyu]]]]]].
      assert (Hxin : In x (l :: undecided)).
      { rewrite <- Hfilter. apply filter_In. now split. }
      assert (Hyin : In y (l :: undecided)).
      { rewrite <- Hfilter. apply filter_In. now split. }
      destruct Hxin as [<-|Hxin], Hyin as [<-|Hyin]; try contradiction.
      -- apply Hxy. symmetry.
        exact (find_different_var_none (literal_var l) undecided
          Hdifferent y Hyin).
      -- apply Hxy.
        exact (find_different_var_none (literal_var l) undecided
          Hdifferent x Hxin).
      -- apply Hxy.
        rewrite (find_different_var_none (literal_var l) undecided
          Hdifferent x Hxin),
          (find_different_var_none (literal_var l) undecided
          Hdifferent y Hyin). reflexivity.
  - split; [exact Hlearned|].
    unfold install_watches. rewrite scan_clause_once_spec. cbn [snd].
    destruct (filter (literal_is_undecided m) c) as [|l undecided] eqn:Hfilter.
    + destruct Htwo as [x [y [Hxc [_ [_ [Hxu _]]]]]].
      assert (In x (filter (literal_is_undecided m) c)) by
        (apply filter_In; now split).
      now rewrite Hfilter in H.
    + destruct (find_different_var (literal_var l) undecided) as [l'|]
        eqn:Hdifferent.
      * intros d body Hbody _ Hbody_noopp.
        destruct (clause_pointer_eq_dec d ci) as [->|Hneq].
        -- change (find_clause_in clauses learned ci = Some body) in Hbody.
           rewrite Hfind in Hbody. injection Hbody as <-.
           left. split.
           ++ destruct Htwo as [x [y [Hxc [Hyc [Hxy _]]]]].
              now exists x, y.
           ++ cbn [state_watched]. rewrite !ClauseMap.card_of_add, Hzero.
              reflexivity.
        -- assert (~ In d [ci]) as Hnotstaged.
           { intros [Heq|Hin]; [apply Hneq; symmetry; exact Heq|contradiction]. }
           specialize (Hbasearity d body Hbody Hnotstaged Hbody_noopp).
           cbn [state_watched].
           rewrite !ClauseMap.card_of_add_neq by exact (not_eq_sym Hneq).
           exact Hbasearity.
      * exfalso. destruct Htwo as
          [x [y [Hxc [Hyc [Hxy [Hxu Hyu]]]]]].
        assert (Hxin : In x (l :: undecided)).
        { rewrite <- Hfilter. apply filter_In. now split. }
        assert (Hyin : In y (l :: undecided)).
        { rewrite <- Hfilter. apply filter_In. now split. }
        destruct Hxin as [<-|Hxin], Hyin as [<-|Hyin]; try contradiction.
        -- apply Hxy. symmetry.
           exact (find_different_var_none (literal_var l) undecided
             Hdifferent y Hyin).
        -- apply Hxy.
           exact (find_different_var_none (literal_var l) undecided
             Hdifferent x Hxin).
        -- apply Hxy.
           rewrite (find_different_var_none (literal_var l) undecided
             Hdifferent x Hxin),
             (find_different_var_none (literal_var l) undecided
             Hdifferent y Hyin). reflexivity.
Qed.

Lemma install_watches_pending_inv : forall ci c l undecided (m : Trail)
    clauses learned cm pending,
  find_clause_in clauses learned ci = Some c ->
  ~ has_opposite_literals c ->
  filter (literal_is_undecided m) c = l :: undecided ->
  find_different_var (literal_var l) undecided = None ->
  ClauseMap.card_of ci cm = 0 ->
  (forall v, ~ In ci (ClauseMap.find v cm)) ->
  In (l, ci) pending ->
  staged_invariant [ci]
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  learned_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  staged_clause_arity [ci]
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := cm; state_pending := pending |} ->
  state_invariant
    {| state_trail := m; state_clauses := clauses; state_learned := learned;
       state_watched := install_watches m ci c cm; state_pending := pending |}.
Proof.
  intros ci c l undecided m clauses learned cm pending Hfind Hnoopp
    Hfilter Hdifferent Hzero Hfresh Hpendingci Hstage Hlearned Hbasearity.
  unfold state_invariant. split.
  - unfold install_watches.
    rewrite scan_clause_once_spec. cbn [snd]. rewrite Hfilter, Hdifferent.
  destruct (find_recent_different_clause_literal (literal_var l) m c)
    as [l'|] eqn:Hrecentfind.
  + unfold find_recent_different_clause_literal in Hrecentfind.
    destruct (find_recent_clause_literal_except_some _ _ _ _ Hrecentfind) as
      [before [assigned [after [_ [Hl'in [_ [Hexcluded _]]]]]]].
    assert (Hvars : literal_var l <> literal_var l').
    { intros Heq. apply Hexcluded. exists (literal_var l). now split. }
    assert (Hlin' : In l (filter (literal_is_undecided m) c)) by
      (rewrite Hfilter; now left).
    apply filter_In in Hlin' as [Hlin Hlu].
    assert (Hallassigned : forall x, In x c ->
        ~ excluded_var (Some (literal_var l)) (literal_var x) ->
        literal_is_undecided m x = false).
    { intros x Hxc Hnotexcluded.
      destruct (literal_is_undecided m x) eqn:Hxu; [|reflexivity].
      assert (Hinfilter : In x (l :: undecided)).
      { rewrite <- Hfilter. apply filter_In. now split. }
      destruct Hinfilter as [<-|Hinfilter].
      - exfalso. apply Hnotexcluded. exists (literal_var l). now split.
      - exfalso. apply Hnotexcluded. exists (literal_var l). split; [reflexivity|].
        symmetry. exact (find_different_var_none (literal_var l) undecided
          Hdifferent x Hinfilter). }
    assert (Htrail : trail_invariant clauses learned m).
    { unfold staged_invariant in Hstage. tauto. }
    assert (Hnodup : NoDup (map literal_var (trail_model m))) by
      (now apply trail_invariant_vars_nodup with (clauses := clauses)
        (learned := learned)).
    assert (Hrecent : forall model, model_suffix model m ->
        Is_true (negb (existsb (literal_is_true model) c)) ->
        clause_has_two_undecided model c ->
        literal_is_undecided model l = true /\
        literal_is_undecided model l' = true).
    { intros model Hsuffix _ Htwo. split.
      - exact (undecided_model_suffix (trail_model m) model l Hsuffix Hlu).
      - eapply recent_clause_literal_undecided;
          [exact Hrecentfind|exact Hnodup|exact Hallassigned|exact Hsuffix|exact Htwo]. }
    eapply watch_two_fresh_inv; try eassumption.
    * apply Hfresh.
    * apply Hfresh.
  + eapply drop_decided_zero_inv with (c := c).
    * exact Hfind.
    * exact Hnoopp.
    * exact Hzero.
    * left. exists l. exact Hpendingci.
    * exact Hstage.
  - split; [exact Hlearned|].
    unfold install_watches. rewrite scan_clause_once_spec. cbn [snd].
    rewrite Hfilter, Hdifferent.
    destruct (find_recent_different_clause_literal (literal_var l) m c)
      as [l'|] eqn:Hrecentfind.
    + intros d body Hbody _ Hbody_noopp.
      destruct (clause_pointer_eq_dec d ci) as [->|Hneq].
      * change (find_clause_in clauses learned ci = Some body) in Hbody.
        rewrite Hfind in Hbody. injection Hbody as <-.
        unfold find_recent_different_clause_literal in Hrecentfind.
        destruct (find_recent_clause_literal_except_some _ _ _ _ Hrecentfind)
          as [before [assigned [after [_ [Hl'c [_ [Hexcluded _]]]]]]].
        left. split.
        -- exists l, l'. split.
           ++ assert (Hinfilter : In l (filter (literal_is_undecided m) c))
                by (rewrite Hfilter; now left).
              apply filter_In in Hinfilter. exact (proj1 Hinfilter).
           ++ split; [exact Hl'c|].
              intros Heq. apply Hexcluded. exists (literal_var l). now split.
        -- cbn [state_watched]. rewrite !ClauseMap.card_of_add, Hzero.
           reflexivity.
      * assert (~ In d [ci]) as Hnotstaged.
        { intros [Heq|Hin]; [apply Hneq; symmetry; exact Heq|contradiction]. }
        specialize (Hbasearity d body Hbody Hnotstaged Hbody_noopp).
        cbn [state_watched].
        rewrite !ClauseMap.card_of_add_neq by exact (not_eq_sym Hneq).
        exact Hbasearity.
    + intros d body Hbody _ Hbody_noopp.
      destruct (clause_pointer_eq_dec d ci) as [->|Hneq].
      * change (find_clause_in clauses learned ci = Some body) in Hbody.
        rewrite Hfind in Hbody. injection Hbody as <-.
        right. split; [|exact Hzero].
        intros [x [y [Hxc [Hyc Hxy]]]]. apply Hxy.
        assert (Hall : forall z, In z c -> literal_var z = literal_var l).
        { intros z Hzc. destruct (literal_is_undecided m z) eqn:Hzu.
          - assert (Hzfilter : In z (l :: undecided)).
            { rewrite <- Hfilter. apply filter_In. now split. }
            destruct Hzfilter as [<-|Hzfilter]; [reflexivity|].
            exact (find_different_var_none (literal_var l) undecided
              Hdifferent z Hzfilter).
          - pose proof (decided_literal_InL m z Hzu) as Hzinmodel.
            destruct Hzinmodel as [Hpos|Hneg].
            + destruct (Id.eq_dec (literal_var z) (literal_var l)) as [Heq|Hneq'];
                [exact Heq|exfalso].
              apply (find_recent_clause_literal_except_none
                (Some (literal_var l)) m c Hrecentfind (Pos (literal_var z))
                Hpos).
              * intros [v [Hv1 Hv2]]. injection Hv1 as <-. apply Hneq'.
                now symmetry.
              * exact (literal_InL z c Hzc).
            + destruct (Id.eq_dec (literal_var z) (literal_var l)) as [Heq|Hneq'];
                [exact Heq|exfalso].
              apply (find_recent_clause_literal_except_none
                (Some (literal_var l)) m c Hrecentfind (Neg (literal_var z))
                Hneg).
              * intros [v [Hv1 Hv2]]. injection Hv1 as <-. apply Hneq'.
                now symmetry.
              * exact (literal_InL z c Hzc). }
        now rewrite (Hall x Hxc), (Hall y Hyc).
      * assert (~ In d [ci]) as Hnotstaged.
        { intros [Heq|Hin]; [apply Hneq; symmetry; exact Heq|contradiction]. }
        exact (Hbasearity d body Hbody Hnotstaged Hbody_noopp).
Qed.

Lemma add_source_two_watches_inv : forall s c l undecided l',
  state_invariant s ->
  ~ has_opposite_literals c ->
  filter (literal_is_undecided s.(state_trail)) c = l :: undecided ->
  find_different_var (literal_var l) undecided = Some l' ->
  state_invariant
    {| state_trail := s.(state_trail);
       state_clauses := ClauseStore.add (fresh_clause_id s) c s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := ClauseMap.add l' (Source (fresh_clause_id s))
         (ClauseMap.add l (Source (fresh_clause_id s)) s.(state_watched));
       state_pending := s.(state_pending) |}.
Proof.
  intros s c l undecided l' Hinv Hnoopp Hfilter Hdifferent.
  apply find_different_var_spec in Hdifferent as [Hl'in Hvars].
  assert (Hlin : In l c /\
      literal_is_undecided s.(state_trail) l = true).
  { apply filter_In. rewrite Hfilter. now left. }
  assert (Hl'in' : In l' c /\
      literal_is_undecided s.(state_trail) l' = true).
  { apply filter_In. rewrite Hfilter. now right. }
  unfold state_invariant. split.
  - eapply watch_one_fresh_inv with
      (c := c)
      (cm := ClauseMap.add l (Source (fresh_clause_id s))
        s.(state_watched)) (pending := s.(state_pending)).
    + apply find_added_clause.
    + exact Hnoopp.
    + now apply add_first_watch_staged_inv.
    + intros Hin. apply ClauseMap.find_add in Hin as [[Heq _]|Hin].
      * exact (Hvars (eq_sym Heq)).
      * exact (fresh_clause_not_watched s (literal_var l') Hinv Hin).
    + exact (proj1 Hl'in').
    + split.
      * eapply watched_undecided_follows_needed with (l := l).
        -- exact (proj1 Hlin).
        -- exact (proj2 Hlin).
        -- apply ClauseMap.find_add. right. apply ClauseMap.find_add. now left.
      * intros _. unfold follows_two_undecided.
        intros model Hsuffix Hunsat Htwo. split.
        -- cbn [state_watched]. rewrite !ClauseMap.card_of_add.
           rewrite (fresh_clause_card_zero s Hinv). reflexivity.
        -- pose proof (undecided_model_suffix _ _ l Hsuffix
             (proj2 Hlin)) as Hlumodel.
           pose proof (undecided_model_suffix _ _ l' Hsuffix
             (proj2 Hl'in')) as Hl'umodel.
           destruct (two_added_watches_undecided
             (Source (fresh_clause_id s)) s.(state_watched)
             model l l' (fresh_clause_card_zero s Hinv)
             Hlumodel Hl'umodel) as [Hpos Hneg].
           intros v Hin. unfold ClauseMap.find in Hin.
           apply in_app_or in Hin as [Hin|Hin].
           ++ now apply Hpos.
           ++ rewrite literal_is_undecided_pos_neg. now apply Hneg.
  - split.
    + now apply learned_invariant_after_add, Hinv.
    + eapply two_added_watches_arity.
      * apply find_added_clause.
      * exact Hnoopp.
      * exists l, l'. tauto.
      * now apply fresh_clause_card_zero.
      * now apply add_source_staged_arity.
Qed.

Lemma two_undecided_scan_pair : forall m c,
  clause_has_two_undecided m c ->
  exists l undecided l',
    filter (literal_is_undecided m) c = l :: undecided /\
    find_different_var (literal_var l) undecided = Some l'.
Proof.
  intros m c Htwo.
  destruct (filter (literal_is_undecided m) c) as [|l undecided]
    eqn:Hfilter.
  - destruct Htwo as [x [y [Hxc [_ [_ [Hxu _]]]]]].
    assert (In x (filter (literal_is_undecided m) c)) by
      (apply filter_In; now split).
    now rewrite Hfilter in H.
  - destruct (find_different_var (literal_var l) undecided) as [l'|]
      eqn:Hdifferent.
    + now exists l, undecided, l'.
    + exfalso. destruct Htwo as
        [x [y [Hxc [Hyc [Hxy [Hxu Hyu]]]]]].
      assert (Hxin : In x (l :: undecided)).
      { rewrite <- Hfilter. apply filter_In. now split. }
      assert (Hyin : In y (l :: undecided)).
      { rewrite <- Hfilter. apply filter_In. now split. }
      destruct Hxin as [<-|Hxin], Hyin as [<-|Hyin]; try contradiction.
      * apply Hxy. symmetry.
        exact (find_different_var_none (literal_var l) undecided
          Hdifferent y Hyin).
      * apply Hxy.
        exact (find_different_var_none (literal_var l) undecided
          Hdifferent x Hxin).
      * apply Hxy.
        rewrite (find_different_var_none (literal_var l) undecided
          Hdifferent x Hxin),
          (find_different_var_none (literal_var l) undecided
          Hdifferent y Hyin). reflexivity.
Qed.

Theorem add_clause_inv : forall s c s',
  state_invariant s ->
  (Is_true (existsb (literal_is_true s.(state_trail)) c) ->
    clause_has_two_undecided s.(state_trail) c) ->
  add_clause s c = Progress s' ->
  state_invariant s'.
Proof.
  intros s c s' Hinv Hinstallable Hadd.
  unfold add_clause, add_clause_to, index_clause in Hadd.
  cbn [state_trail state_clauses state_learned state_watched
    state_pending] in Hadd.
  rewrite scan_clause_once_spec in Hadd.
  destruct (clause_has_opposite_literals c) eqn:Hopposite.
  - cbn in Hadd. injection Hadd as <-.
    apply add_resolved_clause_inv; [exact Hinv|].
    now apply clause_has_opposite_literals_spec.
  - assert (Hnoopp : ~ has_opposite_literals c).
    { intros Hopp. apply clause_has_opposite_literals_spec in Hopp. congruence. }
    destruct (existsb (literal_is_true s.(state_trail)) c) eqn:Hsat.
    + cbn in Hadd. injection Hadd as <-.
      assert (Htwo : clause_has_two_undecided s.(state_trail) c).
      { apply Hinstallable. exact I. }
      destruct (two_undecided_scan_pair _ _ Htwo) as
        [l [undecided [l' [Hfilter Hdifferent]]]].
      unfold install_watches. rewrite scan_clause_once_spec. cbn [snd].
      rewrite Hfilter, Hdifferent.
      eapply add_source_two_watches_inv; eauto.
    + cbn in Hadd.
      unfold install_watches in Hadd.
      rewrite scan_clause_once_spec in Hadd. cbn [snd] in Hadd.
      destruct (filter (literal_is_undecided s.(state_trail)) c)
        as [|l undecided] eqn:Hfilter; [discriminate|].
      destruct (find_different_var (literal_var l) undecided)
        as [l'|] eqn:Hdifferent.
      * injection Hadd as <-.
        eapply add_source_two_watches_inv; eauto.
      * injection Hadd as <-.
        assert (Hneeds : clause_needs_literal s.(state_trail) l c).
        { eapply unit_filter_needs; eauto. }
        assert (Hinstalled : state_invariant
          {| state_trail := s.(state_trail);
             state_clauses := ClauseStore.add (fresh_clause_id s) c
               s.(state_clauses);
             state_learned := s.(state_learned);
             state_watched := install_watches s.(state_trail)
               (Source (fresh_clause_id s)) c s.(state_watched);
             state_pending := (l, Source (fresh_clause_id s)) ::
               s.(state_pending) |}).
        { eapply install_watches_pending_inv.
          - apply find_added_clause.
          - exact Hnoopp.
          - exact Hfilter.
          - exact Hdifferent.
          - now apply fresh_clause_card_zero.
          - intros v. now apply fresh_clause_not_watched.
          - now left.
          - now apply add_unit_staged_inv.
          - now apply learned_invariant_after_add, Hinv.
          - pose proof (add_source_staged_arity s c Hinv) as Harity.
            unfold staged_clause_arity in Harity |- *.
            cbn [find_clause state_clauses state_learned state_watched]
              in Harity |- *. exact Harity. }
        unfold install_watches in Hinstalled.
        rewrite scan_clause_once_spec in Hinstalled. cbn [snd] in Hinstalled.
        rewrite Hfilter, Hdifferent in Hinstalled. exact Hinstalled.
Qed.

Lemma add_learned_two_watches_inv : forall s c l undecided l',
  state_invariant s ->
  clause_implied_by_store s.(state_clauses) c ->
  ~ has_opposite_literals c ->
  filter (literal_is_undecided s.(state_trail)) c = l :: undecided ->
  find_different_var (literal_var l) undecided = Some l' ->
  state_invariant
    {| state_trail := s.(state_trail); state_clauses := s.(state_clauses);
       state_learned := ClauseStore.add (fresh_learned_clause_id s) c
         s.(state_learned);
       state_watched := ClauseMap.add l' (Learned (fresh_learned_clause_id s))
         (ClauseMap.add l (Learned (fresh_learned_clause_id s)) s.(state_watched));
       state_pending := s.(state_pending) |}.
Proof.
  intros s c l undecided l' Hinv Himplied Hnoopp Hfilter Hdifferent.
  apply find_different_var_spec in Hdifferent as [Hl'in Hvars].
  assert (Hlin : In l c /\ literal_is_undecided s.(state_trail) l = true).
  { apply filter_In. rewrite Hfilter. now left. }
  assert (Hl'in' : In l' c /\ literal_is_undecided s.(state_trail) l' = true).
  { apply filter_In. rewrite Hfilter. now right. }
  unfold state_invariant. split.
  - eapply watch_one_fresh_inv with
      (c := c)
      (cm := ClauseMap.add l (Learned (fresh_learned_clause_id s))
        s.(state_watched)) (pending := s.(state_pending)).
    + apply find_added_learned_clause.
    + exact Hnoopp.
    + now apply add_learned_first_watch_staged_inv.
    + intros Hin. apply ClauseMap.find_add in Hin as [[Heq _]|Hin].
      * exact (Hvars (eq_sym Heq)).
      * exact (fresh_learned_clause_not_watched s (literal_var l') Hinv Hin).
    + exact (proj1 Hl'in').
    + split.
      * eapply watched_undecided_follows_needed with (l := l).
        -- exact (proj1 Hlin).
        -- exact (proj2 Hlin).
        -- apply ClauseMap.find_add. right. apply ClauseMap.find_add. now left.
      * intros _. unfold follows_two_undecided.
        intros model Hsuffix Hunsat Htwo. split.
        -- cbn [state_watched]. rewrite !ClauseMap.card_of_add.
           rewrite (fresh_learned_clause_card_zero s Hinv). reflexivity.
        -- pose proof (undecided_model_suffix _ _ l Hsuffix
             (proj2 Hlin)) as Hlumodel.
           pose proof (undecided_model_suffix _ _ l' Hsuffix
             (proj2 Hl'in')) as Hl'umodel.
           destruct (two_added_watches_undecided
             (Learned (fresh_learned_clause_id s)) s.(state_watched)
             model l l' (fresh_learned_clause_card_zero s Hinv)
             Hlumodel Hl'umodel) as [Hpos Hneg].
           intros v Hin. unfold ClauseMap.find in Hin.
           apply in_app_or in Hin as [Hin|Hin].
           ++ now apply Hpos.
           ++ rewrite literal_is_undecided_pos_neg. now apply Hneg.
  - split.
    + eapply learned_invariant_after_learned_add; eauto.
      exact (state_invariant_learned s Hinv).
    + eapply two_added_watches_arity.
      * apply find_added_learned_clause.
      * exact Hnoopp.
      * exists l, l'. tauto.
      * now apply fresh_learned_clause_card_zero.
      * now apply add_learned_staged_arity.
Qed.

Theorem add_learned_inv : forall s c s',
  state_invariant s ->
  clause_implied_by_store s.(state_clauses) c ->
  (Is_true (existsb (literal_is_true s.(state_trail)) c) ->
    clause_has_two_undecided s.(state_trail) c) ->
  add_learned s c = Progress s' ->
  state_invariant s'.
Proof.
  intros s c s' Hinv Himplied Hinstallable Hadd.
  unfold add_learned, add_clause_to, index_clause in Hadd.
  cbn [state_trail state_clauses state_learned state_watched
    state_pending] in Hadd.
  rewrite scan_clause_once_spec in Hadd.
  destruct (clause_has_opposite_literals c) eqn:Hopposite.
  - cbn in Hadd. injection Hadd as <-.
    apply add_learned_resolved_clause_inv; [exact Hinv|exact Himplied|].
    now apply clause_has_opposite_literals_spec.
  - assert (Hnoopp : ~ has_opposite_literals c).
    { intros Hopp. apply clause_has_opposite_literals_spec in Hopp. congruence. }
    destruct (existsb (literal_is_true s.(state_trail)) c) eqn:Hsat.
    + cbn in Hadd. injection Hadd as <-.
      assert (Htwo : clause_has_two_undecided s.(state_trail) c).
      { apply Hinstallable. exact I. }
      destruct (two_undecided_scan_pair _ _ Htwo) as
        [l [undecided [l' [Hfilter Hdifferent]]]].
      unfold install_watches. rewrite scan_clause_once_spec. cbn [snd].
      rewrite Hfilter, Hdifferent.
      eapply add_learned_two_watches_inv; eauto.
    + cbn in Hadd. unfold install_watches in Hadd.
      rewrite scan_clause_once_spec in Hadd. cbn [snd] in Hadd.
      destruct (filter (literal_is_undecided s.(state_trail)) c)
        as [|l undecided] eqn:Hfilter; [discriminate|].
      destruct (find_different_var (literal_var l) undecided)
        as [l'|] eqn:Hdifferent.
      * injection Hadd as <-.
        eapply add_learned_two_watches_inv; eauto.
      * injection Hadd as <-.
        assert (Hneeds : clause_needs_literal s.(state_trail) l c).
        { eapply unit_filter_needs; eauto. }
        assert (Hinstalled : state_invariant
          {| state_trail := s.(state_trail);
             state_clauses := s.(state_clauses);
             state_learned := ClauseStore.add (fresh_learned_clause_id s) c
               s.(state_learned);
             state_watched := install_watches s.(state_trail)
               (Learned (fresh_learned_clause_id s)) c s.(state_watched);
             state_pending := (l, Learned (fresh_learned_clause_id s)) ::
               s.(state_pending) |}).
        { eapply install_watches_pending_inv.
          - apply find_added_learned_clause.
          - exact Hnoopp.
          - exact Hfilter.
          - exact Hdifferent.
          - now apply fresh_learned_clause_card_zero.
          - intros v. now apply fresh_learned_clause_not_watched.
          - now left.
          - now apply add_learned_unit_staged_inv.
          - eapply learned_invariant_after_learned_add;
              [exact (state_invariant_learned s Hinv)|exact Himplied].
          - pose proof (add_learned_staged_arity s c Hinv) as Harity.
            unfold staged_clause_arity in Harity |- *.
            cbn [find_clause state_clauses state_learned state_watched]
              in Harity |- *. exact Harity. }
        unfold install_watches in Hinstalled.
        rewrite scan_clause_once_spec in Hinstalled. cbn [snd] in Hinstalled.
        rewrite Hfilter, Hdifferent in Hinstalled. exact Hinstalled.
Qed.

Lemma add_learned_progress_fields : forall s c s',
  add_learned s c = Progress s' ->
  s'.(state_clauses) = s.(state_clauses).
Proof.
  intros s c s' Hadd. unfold add_learned, add_clause_to, index_clause in Hadd.
  cbn [state_trail state_clauses state_learned state_watched
    state_pending] in Hadd.
  destruct (scan_clause_once s.(state_trail) c) as [satisfied undecided].
  destruct (clause_has_opposite_literals c); cbn in Hadd.
  - injection Hadd as <-. reflexivity.
  - destruct satisfied; cbn in Hadd.
    + injection Hadd as <-. reflexivity.
    + destruct undecided as [|l undecided]; [discriminate|].
      destruct (find_different_var (literal_var l) undecided);
        injection Hadd as <-; reflexivity.
Qed.

Lemma add_learned_progress_learned_trail : forall s c s',
  add_learned s c = Progress s' ->
  s'.(state_learned) =
    ClauseStore.add (fresh_learned_clause_id s) c s.(state_learned) /\
  s'.(state_trail) = s.(state_trail).
Proof.
  intros s c s' Hadd. unfold add_learned, add_clause_to, index_clause in Hadd.
  cbn [state_trail state_clauses state_learned state_watched
    state_pending] in Hadd.
  destruct (scan_clause_once s.(state_trail) c) as [satisfied undecided].
  destruct (clause_has_opposite_literals c); cbn in Hadd.
  - injection Hadd as <-. now split.
  - destruct satisfied; cbn in Hadd.
    + injection Hadd as <-. now split.
    + destruct undecided as [|l undecided]; [discriminate|].
      destruct (find_different_var (literal_var l) undecided);
        injection Hadd as <-; now split.
Qed.

Lemma clause_pointers_find : forall s ci c,
  find_clause ci s = Some c -> In ci (clause_pointers s).
Proof.
  intros s [id|id] c Hfind; unfold clause_pointers, find_clause,
    find_clause_in in *.
  - apply in_or_app. left. apply in_map.
    apply ClauseStore.keys_complete. congruence.
  - apply in_or_app. right. apply in_map.
    apply ClauseStore.keys_complete. congruence.
Qed.

Lemma clause_pointers_valid : forall s ci,
  In ci (clause_pointers s) -> exists c, find_clause ci s = Some c.
Proof.
  intros s [id|id] Hin; unfold clause_pointers in Hin;
    apply in_app_or in Hin as [Hin|Hin].
  - apply in_map_iff in Hin as [id' [Heq Hin]]. injection Heq as <-.
    apply ClauseStore.keys_complete in Hin.
    destruct (ClauseStore.find id' s.(state_clauses)) as [c|] eqn:Hfind;
      [now exists c|contradiction].
  - apply in_map_iff in Hin as [id' [Heq _]]. discriminate.
  - apply in_map_iff in Hin as [id' [Heq _]]. discriminate.
  - apply in_map_iff in Hin as [id' [Heq Hin]]. injection Heq as <-.
    apply ClauseStore.keys_complete in Hin.
    destruct (ClauseStore.find id' s.(state_learned)) as [c|] eqn:Hfind;
      [now exists c|contradiction].
Qed.

Lemma reclassify_clauses_pending_sound : forall pointers m s l ci,
  In (l, ci) (reclassify_clauses m s pointers) ->
  In ci pointers /\ exists c undecided,
    find_clause ci s = Some c /\ ~ has_opposite_literals c /\
    scan_clause_once m c = (false, l :: undecided) /\
    find_different_var (literal_var l) undecided = None.
Proof.
  induction pointers as [|pointer pointers IH]; intros m s l ci Hin;
    [contradiction|].
  cbn [reclassify_clauses] in Hin.
  destruct (find_clause pointer s) as [c|] eqn:Hfind; [|].
  - destruct (clause_has_opposite_literals c) eqn:Hopposite.
    + destruct (IH m s l ci Hin) as [Hip Hsem]. split; [now right|exact Hsem].
    + assert (Hnoopp : ~ has_opposite_literals c).
      { intros Hopp. apply clause_has_opposite_literals_spec in Hopp. congruence. }
      destruct (scan_clause_once m c) as [satisfied undecided] eqn:Hscan.
      destruct satisfied; [|destruct undecided as [|p undecided]].
    * destruct (IH m s l ci Hin) as [Hip Hsem]. split; [now right|exact Hsem].
    * destruct (IH m s l ci Hin) as [Hip Hsem]. split; [now right|exact Hsem].
    * destruct (find_different_var (literal_var p) undecided)
        as [different|] eqn:Hdifferent.
      -- destruct (IH m s l ci Hin) as [Hip Hsem].
         split; [now right|exact Hsem].
      -- cbn in Hin. destruct Hin as [Heq|Hin].
        ++ injection Heq as <- <-. split; [now left|].
           exists c, undecided. now repeat split.
        ++ destruct (IH m s l ci Hin) as [Hip Hsem].
           split; [now right|exact Hsem].
  - destruct (IH m s l ci Hin) as [Hip Hsem]. split; [now right|exact Hsem].
Qed.

Lemma reclassify_clauses_pending_complete : forall pointers m s l ci c undecided,
  In ci pointers -> find_clause ci s = Some c ->
  ~ has_opposite_literals c ->
  scan_clause_once m c = (false, l :: undecided) ->
  find_different_var (literal_var l) undecided = None ->
  In (l, ci) (reclassify_clauses m s pointers).
Proof.
  induction pointers as [|pointer pointers IH];
    intros m s l ci c undecided Hin Hfind Hnoopp Hscan Hdifferent;
    [contradiction|].
  cbn [reclassify_clauses].
  destruct Hin as [<-|Hin].
  - rewrite Hfind.
    destruct (clause_has_opposite_literals c) eqn:Hopposite.
    + exfalso. apply Hnoopp. now apply clause_has_opposite_literals_spec.
    + rewrite Hscan, Hdifferent. now left.
  - assert (Hrest : In (l, ci) (reclassify_clauses m s pointers)).
    { now apply (IH m s l ci c undecided). }
    destruct (find_clause pointer s) as [body|].
    + destruct (clause_has_opposite_literals body).
      * exact Hrest.
      * destruct (scan_clause_once m body) as [satisfied undecided'] eqn:Hbody.
        destruct satisfied.
        -- exact Hrest.
        -- destruct undecided' as [|p undecided'].
           ++ exact Hrest.
           ++ destruct (find_different_var (literal_var p) undecided').
              ** exact Hrest.
              ** now right.
    + exact Hrest.
Qed.

Lemma index_clause_result_trail : forall pointer s c result,
  index_clause pointer s c = result ->
  match result with
  | Progress s' => s'.(state_trail) = s.(state_trail)
  | Conflict s' _ => s'.(state_trail) = s.(state_trail)
  end.
Proof.
  intros pointer s c result Hindex. unfold index_clause in Hindex.
  destruct (scan_clause_once s.(state_trail) c) as [satisfied undecided].
  destruct (clause_has_opposite_literals c); cbn in Hindex.
  - destruct result; inversion Hindex; reflexivity.
  - destruct satisfied; cbn in Hindex.
    + destruct result; inversion Hindex; reflexivity.
    + destruct undecided as [|l undecided].
      * destruct result; inversion Hindex; reflexivity.
      * destruct (find_different_var (literal_var l) undecided);
          destruct result; inversion Hindex; reflexivity.
Qed.

Lemma index_clause_result_stores : forall pointer s c result,
  index_clause pointer s c = result ->
  match result with
  | Progress s' | Conflict s' _ =>
      s'.(state_clauses) = s.(state_clauses) /\
      s'.(state_learned) = s.(state_learned)
  end.
Proof.
  intros pointer s c result Hindex. unfold index_clause in Hindex.
  destruct (scan_clause_once s.(state_trail) c) as [satisfied undecided].
  destruct (clause_has_opposite_literals c); cbn in Hindex.
  - destruct result; inversion Hindex; now split.
  - destruct satisfied; cbn in Hindex.
    + destruct result; inversion Hindex; now split.
    + destruct undecided as [|l undecided].
      * destruct result; inversion Hindex; now split.
      * destruct (find_different_var (literal_var l) undecided);
          destruct result; inversion Hindex; now split.
Qed.

Lemma add_learned_result_trail : forall s c result,
  add_learned s c = result ->
  match result with
  | Progress s' => s'.(state_trail) = s.(state_trail)
  | Conflict s' _ => s'.(state_trail) = s.(state_trail)
  end.
Proof.
  intros s c result Hadd. unfold add_learned, add_clause_to in Hadd.
  now apply index_clause_result_trail in Hadd.
Qed.

Lemma add_clause_result_trail : forall s c result,
  add_clause s c = result ->
  match result with
  | Progress s' => s'.(state_trail) = s.(state_trail)
  | Conflict s' _ => s'.(state_trail) = s.(state_trail)
  end.
Proof.
  intros s c result Hadd. unfold add_clause, add_clause_to in Hadd.
  now apply index_clause_result_trail in Hadd.
Qed.

Lemma add_clause_root_unit_inv : forall s c s',
  root_unit_invariant s ->
  trail_has_decision s.(state_trail) = false ->
  add_clause s c = Progress s' ->
  root_unit_invariant s'.
Proof.
  intros s c s' Hroot Hnodecision Hadd ci body
    Hfind Hnoopp Hnotwo Hdecision.
  pose proof (add_clause_result_trail s c (Progress s') Hadd) as Htrail.
  cbn in Htrail. rewrite Htrail, Hnodecision in Hdecision. discriminate.
Qed.

Lemma add_clause_current_level_inv : forall s c s',
  trail_has_decision s.(state_trail) = false ->
  add_clause s c = Progress s' ->
  current_level_falsified_invariant s'.
Proof.
  intros s c s' Hnodecision Hadd Hdecision.
  pose proof (add_clause_result_trail s c (Progress s') Hadd) as Htrail.
  cbn in Htrail. rewrite Htrail, Hnodecision in Hdecision. discriminate.
Qed.

Lemma backtrack_conflict_trail : forall conflict cause s' cause',
  backtrack (conflict, cause) = Some (Conflict s' cause') ->
  exists learned,
    analyze_conflict conflict cause = Some learned /\
    s'.(state_trail) = backtrack_trail learned conflict.(state_trail).
Proof.
  intros conflict cause s' cause' Hbacktrack. unfold backtrack in Hbacktrack.
  cbn [count_conflict] in Hbacktrack.
  destruct (analyze_conflict conflict cause) as [learned|] eqn:Hanalyze;
    [|discriminate].
  remember (reclassify_state
    (trail_model (backtrack_trail learned conflict.(state_trail))) conflict)
    as pending eqn:Hpending.
  remember
    {| state_trail := backtrack_trail learned conflict.(state_trail);
       state_clauses := conflict.(state_clauses);
       state_learned := conflict.(state_learned);
       state_watched := conflict.(state_watched);
       state_pending := pending |} as reset eqn:Hreset.
  assert (Hfinish : Some (add_learned reset learned) =
      Some (Conflict s' cause') ->
      s'.(state_trail) = backtrack_trail learned conflict.(state_trail)).
  { intros Hresult.
    destruct (add_learned reset learned) as [final|final finalcause]
      eqn:Hadd; [discriminate|].
    injection Hresult as <- <-. rewrite (add_learned_result_trail _ _ _ Hadd).
    subst reset. reflexivity. }
  exists learned. split; [reflexivity|].
  destruct (trail_has_decision (backtrack_trail learned conflict.(state_trail)));
    [now apply Hfinish|].
  destruct (scan_clause_once (backtrack_trail learned conflict.(state_trail))
    learned) as [satisfied undecided].
  destruct satisfied; [now apply Hfinish|].
  destruct undecided as [|l undecided]; [discriminate|now apply Hfinish].
Qed.

Lemma backtrack_none_cases : forall s cause,
  backtrack (s, cause) = None ->
  analyze_conflict s cause = None \/
  exists learned,
    analyze_conflict s cause = Some learned /\
    trail_has_decision (backtrack_trail learned s.(state_trail)) = false /\
    scan_clause_once (backtrack_trail learned s.(state_trail)) learned =
      (false, []).
Proof.
  intros s cause Hbacktrack. unfold backtrack in Hbacktrack.
  cbn [count_conflict] in Hbacktrack.
  destruct (analyze_conflict s cause) as [learned|] eqn:Hanalyze;
    [|now left]. right. exists learned. split; [reflexivity|].
  remember (reclassify_state
    (trail_model (backtrack_trail learned s.(state_trail))) s) as pending.
  destruct (trail_has_decision (backtrack_trail learned s.(state_trail)))
    eqn:Htwo; [discriminate|].
  split; [reflexivity|].
  destruct (scan_clause_once (backtrack_trail learned s.(state_trail)) learned)
    as [satisfied undecided] eqn:Hscan.
  destruct satisfied; [discriminate|].
  destruct undecided; [reflexivity|discriminate].
Qed.

Lemma decision_in_negated_decisions : forall trail l,
  In (Decision l) trail -> In (opposite_literal l) (negated_decisions trail).
Proof.
  intros trail l Hin. induction trail as [|entry trail IH]; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst entry. cbn. now left.
  - destruct entry; cbn; [now right; apply IH|now apply IH].
Qed.

Lemma analyze_conflict_none_no_decisions : forall s cause l,
  analyze_conflict s cause = None ->
  ~ In (Decision l) s.(state_trail).
Proof.
  intros s cause l Hanalyze.
  exact (proj1 (analyze_conflict_none_iff s cause) Hanalyze l).
Qed.

Lemma conflict_without_decisions_unsat : forall s cause,
  backtrack_invariant s ->
  clause_implied_by_store s.(state_clauses) cause ->
  clause_falsified_by_model s.(state_trail) cause ->
  analyze_conflict s cause = None ->
  forall m, ~ satisfies_clause_store m s.(state_clauses).
Proof.
  intros s cause Hinv Himplied Hfalse Hanalyze m Hstore.
  pose proof (state_invariant_trail s (proj1 Hinv))
    as [Hconsistent Hjustified].
  pose proof (state_invariant_learned s (proj1 Hinv)) as Hlearned.
  assert (forall l, In l (trail_model s.(state_trail)) ->
      satisfies_literal m l = true) as Htrail.
  { eapply justified_trail_sound; eauto. intros l Hdecision.
    exfalso. now apply (analyze_conflict_none_no_decisions s cause l Hanalyze). }
  specialize (Himplied m Hstore). apply Is_true_eq_true in Himplied.
  unfold satisfies_clause in Himplied.
  apply existsb_exists in Himplied as [l [Hlc Hltrue]].
  pose proof (Hfalse l Hlc) as Hlfalse.
  apply literal_value_false_opposite_in in Hlfalse.
  specialize (Htrail (opposite_literal l) Hlfalse).
  pose proof (satisfies_opposite_true_is_false m l Htrail) as Hlfalse'.
  congruence.
Qed.

Lemma implied_falsified_without_decisions_unsat :
  forall clauses learned trail cause,
  trail_invariant clauses learned trail ->
  (forall ci c, ClauseStore.find ci learned = Some c ->
    clause_implied_by_store clauses c) ->
  (forall l, ~ In (Decision l) trail) ->
  clause_implied_by_store clauses cause ->
  clause_falsified_by_model (trail_model trail) cause ->
  forall m, ~ satisfies_clause_store m clauses.
Proof.
  intros clauses learned trail cause [Hconsistent Hjustified] Hlearned
    Hdecisions Himplied Hfalse m Hstore.
  assert (forall l, In l (trail_model trail) -> satisfies_literal m l = true)
    as Htrail.
  { eapply justified_trail_sound;
      [exact Hconsistent|exact Hjustified|exact Hlearned|exact Hstore|].
    intros l Hin. exfalso. exact (Hdecisions l Hin). }
  specialize (Himplied m Hstore). apply Is_true_eq_true in Himplied.
  unfold satisfies_clause in Himplied.
  apply existsb_exists in Himplied as [l [Hin Hltrue]].
  pose proof (Hfalse l Hin) as Hlfalse.
  apply literal_value_false_opposite_in in Hlfalse.
  specialize (Htrail (opposite_literal l) Hlfalse).
  pose proof (satisfies_opposite_true_is_false m l Htrail) as Hlfalse'.
  congruence.
Qed.

Lemma empty_trail_falsified_clause_empty : forall c,
  clause_falsified_by_model [] c -> c = [].
Proof.
  intros [|l c] Hfalse; [reflexivity|].
  specialize (Hfalse l (or_introl eq_refl)). discriminate.
Qed.

Lemma implied_empty_clause_unsat : forall clauses,
  clause_implied_by_store clauses [] ->
  forall m, ~ satisfies_clause_store m clauses.
Proof.
  intros clauses Himplied m Hstore.
  specialize (Himplied m Hstore). cbn in Himplied. exact Himplied.
Qed.

Lemma index_clause_conflict_spec : forall pointer s c s' cause,
  index_clause pointer s c = Conflict s' cause ->
  cause = c /\
  clause_falsified_by_model s'.(state_trail) c /\
  s'.(state_clauses) = s.(state_clauses).
Proof.
  intros pointer s c s' cause Hindex. unfold index_clause in Hindex.
  rewrite scan_clause_once_spec in Hindex.
  destruct (clause_has_opposite_literals c); cbn in Hindex; [discriminate|].
  destruct (existsb (literal_is_true s.(state_trail)) c) eqn:Hsat;
    cbn in Hindex; [discriminate|].
  destruct (filter (literal_is_undecided s.(state_trail)) c)
    as [|l undecided] eqn:Hfilter.
  - injection Hindex as <- <-. repeat split.
    apply falsified_clause_spec; [|exact Hfilter].
    apply Is_true_eq_left. apply Bool.negb_true_iff. exact Hsat.
  - destruct (find_different_var (literal_var l) undecided); discriminate.
Qed.

Lemma add_learned_conflict_spec : forall s c s' cause,
  add_learned s c = Conflict s' cause ->
  cause = c /\
  clause_falsified_by_model s'.(state_trail) c /\
  s'.(state_clauses) = s.(state_clauses).
Proof.
  intros s c s' cause Hadd.
  unfold add_learned, add_clause_to, index_clause in Hadd.
  cbn [state_trail state_clauses state_learned state_watched
    state_pending] in Hadd.
  rewrite scan_clause_once_spec in Hadd.
  destruct (clause_has_opposite_literals c); cbn in Hadd; [discriminate|].
  destruct (existsb (literal_is_true s.(state_trail)) c) eqn:Hsat;
    cbn in Hadd; [discriminate|].
  destruct (filter (literal_is_undecided s.(state_trail)) c)
    as [|l undecided] eqn:Hfilter.
  - injection Hadd as <- <-. repeat split.
    apply falsified_clause_spec; [|exact Hfilter].
    apply Is_true_eq_left. apply Bool.negb_true_iff. exact Hsat.
  - destruct (find_different_var (literal_var l) undecided); discriminate.
Qed.

Lemma pop_to_decision_after_model_suffix : forall learned after trail,
  model_suffix (trail_model (pop_to_decision_after learned after trail))
    (trail_model trail).
Proof.
  intros learned after trail. induction trail as [|entry trail IH] in after |- *.
  - apply model_suffix_refl.
  - destruct entry as [l|l cause]; cbn [pop_to_decision_after trail_model].
    + destruct after.
      * exists [l]. reflexivity.
      * destruct (in_dec literal_eq_dec (opposite_literal l) learned).
        -- exists [l]. reflexivity.
        -- eapply model_suffix_trans; [apply IH|]. exists [l]. reflexivity.
    + destruct (in_dec literal_eq_dec (opposite_literal l) learned).
      * eapply model_suffix_trans; [apply IH|]. exists [l]. reflexivity.
      * eapply model_suffix_trans; [apply IH|]. exists [l]. reflexivity.
Qed.

Lemma pop_to_decision_model_suffix : forall learned trail,
  model_suffix (trail_model (pop_to_decision learned trail))
    (trail_model trail).
Proof.
  intros learned trail. unfold pop_to_decision.
  apply pop_to_decision_after_model_suffix.
Qed.

Lemma pop_to_root_model_suffix : forall trail,
  model_suffix (trail_model (pop_to_root trail)) (trail_model trail).
Proof.
  intros trail. induction trail as [|entry trail IH]; [apply model_suffix_refl|].
  cbn [pop_to_root]. destruct (trail_has_decision (entry :: trail))
    eqn:Hdecision.
  - eapply model_suffix_trans; [exact IH|].
    exists [trail_literal entry]. reflexivity.
  - apply model_suffix_refl.
Qed.

Lemma pop_to_root_trail_invariant : forall clauses learned trail,
  trail_invariant clauses learned trail ->
  trail_invariant clauses learned (pop_to_root trail).
Proof.
  intros clauses learned trail. induction trail as [|entry trail IH];
    intros Hinv; [exact Hinv|].
  cbn [pop_to_root]. destruct (trail_has_decision (entry :: trail))
    eqn:Hdecision.
  - apply IH. now apply trail_invariant_tail with (entry := entry).
  - exact Hinv.
Qed.

Lemma pop_to_decision_after_no_decision : forall clause after trail,
  trail_has_decision trail = false ->
  pop_to_decision_after clause after trail = [].
Proof.
  intros clause after trail. induction trail as [|entry trail IH] in after |- *;
    intros Hnone; [reflexivity|].
  destruct entry as [decision|propagated cause]; cbn in Hnone.
  - discriminate.
  - cbn [pop_to_decision_after].
    destruct (in_dec literal_eq_dec (opposite_literal propagated) clause);
      now apply IH.
Qed.

Lemma trail_has_decision_false : forall trail,
  trail_has_decision trail = false <->
  forall l, ~ In (Decision l) trail.
Proof.
  intros trail. induction trail as [|entry trail IH].
  - split; [intros _ l Hin|intros _]; [contradiction|reflexivity].
  - destruct entry as [decision|propagated cause].
    + cbn. split; [discriminate|].
      intros Hnone. exfalso. exact (Hnone decision (or_introl eq_refl)).
    + cbn. rewrite IH. split.
      * intros Hnone l [Heq|Hin]; [discriminate|exact (Hnone l Hin)].
      * intros Hnone l Hin. apply Hnone with (l := l). now right.
Qed.

Lemma analyze_conflict_some_has_decision : forall s cause learned,
  analyze_conflict s cause = Some learned ->
  trail_has_decision s.(state_trail) = true.
Proof.
  intros s cause learned Hanalyze.
  destruct (trail_has_decision s.(state_trail)) eqn:Hdecision;
    [reflexivity|].
  exfalso.
  assert (Hnodecision : forall l, ~ In (Decision l) s.(state_trail)).
  { exact (proj1 (trail_has_decision_false s.(state_trail)) Hdecision). }
  pose proof (proj2 (analyze_conflict_none_iff s cause) Hnodecision) as Hnone.
  congruence.
Qed.

Lemma pop_to_root_after_pop_to_decision_after : forall clause after trail,
  pop_to_decision_after clause after trail <> [] ->
  pop_to_root (pop_to_decision_after clause after trail) = pop_to_root trail.
Proof.
  intros clause after trail. induction trail as [|entry trail IH] in after |- *;
    intros Hnonempty; [contradiction|].
  destruct entry as [decision|propagated cause].
  - cbn [pop_to_decision_after] in Hnonempty |- *. destruct after.
    + cbn [pop_to_root trail_has_decision]. reflexivity.
    + destruct (in_dec literal_eq_dec (opposite_literal decision) clause).
      * cbn [pop_to_root trail_has_decision]. reflexivity.
      * rewrite (IH false Hnonempty).
        cbn [pop_to_root trail_has_decision]. reflexivity.
  - cbn [pop_to_decision_after] in Hnonempty |- *.
    destruct (in_dec literal_eq_dec (opposite_literal propagated) clause).
    all: rewrite (IH _ Hnonempty).
    all: cbn [pop_to_root trail_has_decision].
    all: destruct (trail_has_decision trail) eqn:Hdecision; [reflexivity|].
    all: exfalso; apply Hnonempty;
      now apply pop_to_decision_after_no_decision.
Qed.

Lemma pop_to_root_idempotent : forall trail,
  pop_to_root (pop_to_root trail) = pop_to_root trail.
Proof.
  intros trail. induction trail as [|entry trail IH]; [reflexivity|].
  cbn [pop_to_root]. destruct (trail_has_decision (entry :: trail))
    eqn:Hdecision.
  - exact IH.
  - cbn [pop_to_root]. rewrite Hdecision. reflexivity.
Qed.

Lemma trail_has_decision_pop_to_root : forall trail,
  trail_has_decision (pop_to_root trail) = false.
Proof.
  intros trail. induction trail as [|entry trail IH]; [reflexivity|].
  cbn [pop_to_root]. destruct (trail_has_decision (entry :: trail))
    eqn:Hdecision; [exact IH|exact Hdecision].
Qed.

Lemma pop_to_root_no_decision : forall trail,
  trail_has_decision trail = false -> pop_to_root trail = trail.
Proof.
  intros [|entry trail] Hdecision; [reflexivity|].
  cbn [pop_to_root]. now rewrite Hdecision.
Qed.

Lemma pop_to_root_cons_after_decision : forall entry trail,
  trail_has_decision trail = true ->
  pop_to_root (entry :: trail) = pop_to_root trail.
Proof.
  intros [l|l cause] trail Hdecision; cbn [pop_to_root trail_has_decision].
  - reflexivity.
  - now rewrite Hdecision.
Qed.

Lemma set_trail_entry_find_clause : forall entry s ci,
  find_clause ci (progress_result_state (set_trail_entry entry s)) =
  find_clause ci s.
Proof.
  intros entry s ci. unfold find_clause.
  rewrite set_trail_entry_result_clauses, set_trail_entry_result_learned.
  reflexivity.
Qed.

Lemma root_unit_set_after_decision : forall entry s,
  root_unit_invariant s ->
  trail_has_decision s.(state_trail) = true ->
  root_unit_invariant (progress_result_state (set_trail_entry entry s)).
Proof.
  intros entry s Hroot Holdecision ci c Hfind Hnoopp Hnotwo Hdecision.
  rewrite set_trail_entry_find_clause in Hfind.
  specialize (Hroot ci c Hfind Hnoopp Hnotwo Holdecision).
  pose proof (set_trail_entry_result_trail entry s) as Htrail.
  rewrite Htrail, (pop_to_root_cons_after_decision entry _ Holdecision).
  exact Hroot.
Qed.

Lemma root_unit_set_first_decision : forall l s,
  state_invariant s ->
  falsified_clauses_pending s ->
  s.(state_pending) = [] ->
  trail_has_decision s.(state_trail) = false ->
  root_unit_invariant
    (progress_result_state (set_trail_entry (Decision l) s)).
Proof.
  intros l s Hinv Hfalsified Hempty Hnodecision
    ci c Hfind Hnoopp Hnotwo Hdecision.
  rewrite set_trail_entry_find_clause in Hfind.
  pose proof (pending_empty_small_clause_satisfied s ci c
    Hinv Hfalsified Hempty Hfind Hnoopp Hnotwo) as Hsatisfied.
  pose proof (set_trail_entry_result_trail (Decision l) s) as Htrail.
  rewrite Htrail. cbn [pop_to_root trail_has_decision].
  now rewrite (pop_to_root_no_decision _ Hnodecision).
Qed.

Lemma progress_root_unit_inv : forall s,
  state_invariant s ->
  root_unit_invariant s ->
  falsified_clauses_pending s ->
  root_unit_invariant (progress_result_state (progress s)).
Proof.
  intros s Hinv Hroot Hfalsified.
  unfold progress. destruct s.(state_pending) as [|[l ci] pending] eqn:Hpending.
  - unfold progress_state. rewrite Hpending.
    destruct (find_undecided_var s.(state_trail) (problem_vars s)) as [v|].
    + unfold set_lit. destruct (trail_has_decision s.(state_trail))
        eqn:Hdecision.
      * now apply root_unit_set_after_decision.
      * now apply root_unit_set_first_decision.
    + exact Hroot.
  - destruct (literal_value s.(state_trail) l) as [[|]|] eqn:Hvalue.
    + unfold progress_state. rewrite Hpending, Hvalue. cbn.
      intros pointer c Hfind Hnoopp Hnotwo Hdecision.
      apply (Hroot pointer c); try assumption.
    + destruct (find_clause ci s); exact Hroot.
    + unfold progress_state. rewrite Hpending, Hvalue.
      unfold set_propagated_lit.
      destruct (trail_has_decision s.(state_trail)) eqn:Hdecision.
      * now apply root_unit_set_after_decision.
      * intros pointer c Hfind Hnoopp Hnotwo Hnewdecision.
        pose proof (set_trail_entry_result_trail (Propagation l ci)
          {| state_trail := s.(state_trail);
             state_clauses := s.(state_clauses);
             state_learned := s.(state_learned);
             state_watched := s.(state_watched);
             state_pending := pending |}) as Htrail.
        cbn [state_trail] in Htrail.
        rewrite Htrail in Hnewdecision. cbn [trail_has_decision] in Hnewdecision.
        congruence.
Qed.

Lemma backtrack_trail_with_decision : forall learned trail,
  trail_has_decision (backtrack_trail learned trail) = true ->
  backtrack_trail learned trail = pop_to_decision learned trail.
Proof.
  intros learned trail Hdecision. unfold backtrack_trail in *.
  destruct (clause_has_two_variablesb learned); [|].
  - destruct (pop_to_decision learned trail) eqn:Hpop; [|reflexivity].
    rewrite trail_has_decision_pop_to_root in Hdecision. discriminate.
  - rewrite trail_has_decision_pop_to_root in Hdecision. discriminate.
Qed.

Lemma pop_to_root_backtrack_trail : forall learned trail,
  pop_to_root (backtrack_trail learned trail) = pop_to_root trail.
Proof.
  intros learned trail. unfold backtrack_trail.
  destruct (clause_has_two_variablesb learned).
  - destruct (pop_to_decision learned trail) eqn:Hpop.
    + apply pop_to_root_idempotent.
    + rewrite <- Hpop. apply pop_to_root_after_pop_to_decision_after.
      change (pop_to_decision learned trail <> []).
      rewrite Hpop. discriminate.
  - apply pop_to_root_idempotent.
Qed.

Lemma clause_has_two_variablesb_spec : forall c,
  Is_true (clause_has_two_variablesb c) <-> clause_has_two_variables c.
Proof.
  intros [|l c]; [split; [contradiction|intros [x [y [H _]]]; contradiction]|].
  unfold clause_has_two_variablesb.
  destruct (find_different_var (literal_var l) c) as [different|]
    eqn:Hdifferent.
  - split; [intros _|intros _; exact I].
    apply find_different_var_spec in Hdifferent as [Hin Hvars].
    exists l, different. split; [now left|].
    split; [now right|exact Hvars].
  - split; [contradiction|].
    intros [x [y [Hx [Hy Hvars]]]]. exfalso. apply Hvars.
    destruct Hx as [<-|Hx], Hy as [<-|Hy]; try reflexivity.
    + symmetry. now apply find_different_var_none with (ls := c).
    + now apply find_different_var_none with (ls := c).
    + rewrite (find_different_var_none _ _ Hdifferent x Hx),
        (find_different_var_none _ _ Hdifferent y Hy). reflexivity.
Qed.

Lemma backtrack_trail_small_no_decision : forall learned trail,
  ~ clause_has_two_variables learned ->
  trail_has_decision (backtrack_trail learned trail) = false.
Proof.
  intros learned trail Hnotwo. unfold backtrack_trail.
  destruct (clause_has_two_variablesb learned) eqn:Htwo.
  - exfalso. apply Hnotwo, clause_has_two_variablesb_spec.
    now rewrite Htwo.
  - apply trail_has_decision_pop_to_root.
Qed.

Lemma reclassify_backtracked_root_inv : forall s learned pending,
  root_unit_invariant s ->
  trail_has_decision s.(state_trail) = true ->
  root_unit_invariant
    {| state_trail := backtrack_trail learned s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |}.
Proof.
  intros s learned pending Hroot Hdecision ci c Hfind Hnoopp Hnotwo Hnewdecision.
  cbn [find_clause state_clauses state_learned state_trail] in Hfind |- *.
  rewrite pop_to_root_backtrack_trail.
  now apply (Hroot ci c Hfind Hnoopp Hnotwo Hdecision).
Qed.

Lemma add_learned_root_unit_inv : forall s learned final,
  root_unit_invariant s ->
  (~ clause_has_two_variables learned ->
    trail_has_decision s.(state_trail) = false) ->
  add_learned s learned = Progress final ->
  root_unit_invariant final.
Proof.
  intros s learned final Hroot Hlearnedsmall Hadd ci c
    Hfind Hnoopp Hnotwo Hdecision.
  pose proof (add_learned_progress_fields s learned final Hadd) as Hclauses.
  pose proof (add_learned_progress_learned_trail s learned final Hadd)
    as [Hlearned Htrail].
  unfold find_clause, find_clause_in in Hfind.
  rewrite Hclauses, Hlearned in Hfind. rewrite Htrail in Hdecision |- *.
  destruct ci as [id|id].
  - eapply (Hroot (Source id) c); eauto.
  - rewrite ClauseStore.find_add_eq in Hfind.
    destruct (ClauseIdKey.eq_dec (fresh_learned_clause_id s) id)
      as [Heq|Hneq].
    + injection Hfind as <-.
      rewrite (Hlearnedsmall Hnotwo) in Hdecision. discriminate.
    + eapply (Hroot (Learned id) c); eauto.
Qed.

Lemma satisfied_model_suffix_extension : forall model suffix c,
  model_suffix suffix model ->
  NoDup (map literal_var model) ->
  Is_true (existsb (literal_is_true suffix) c) ->
  Is_true (existsb (literal_is_true model) c).
Proof.
  intros model suffix c [prefix ->] Hnodup Hsatisfied.
  induction prefix as [|assigned prefix IH]; cbn [app] in *;
    [exact Hsatisfied|].
  inversion Hnodup as [|? ? Hfresh Hnodup']; subst.
  apply satisfied_cons_undecided.
  - apply not_InL_literal_undecided. rewrite InL_map_literal_var.
    exact Hfresh.
  - now apply IH.
Qed.

Lemma backtrack_trail_model_suffix : forall learned trail,
  model_suffix (trail_model (backtrack_trail learned trail))
    (trail_model trail).
Proof.
  intros learned trail. unfold backtrack_trail.
  destruct (clause_has_two_variablesb learned).
  - destruct (pop_to_decision learned trail) eqn:Hpop.
    + apply pop_to_root_model_suffix.
    + rewrite <- Hpop. apply pop_to_decision_model_suffix.
  - apply pop_to_root_model_suffix.
Qed.

Lemma backtrack_trail_invariant : forall clauses stored learned trail,
  trail_invariant clauses stored trail ->
  trail_invariant clauses stored (backtrack_trail learned trail).
Proof.
  intros clauses stored learned trail Hinv. unfold backtrack_trail.
  destruct (clause_has_two_variablesb learned).
  - destruct (pop_to_decision learned trail) eqn:Hpop.
    + now apply pop_to_root_trail_invariant.
    + rewrite <- Hpop. now apply pop_to_decision_trail_invariant.
  - now apply pop_to_root_trail_invariant.
Qed.

Lemma reclassify_backtracked_inv : forall s learned pending,
  state_invariant s ->
  root_unit_invariant s ->
  trail_has_decision s.(state_trail) = true ->
  reclassify_state
    (trail_model (backtrack_trail learned s.(state_trail))) s =
      pending ->
  state_invariant
    {| state_trail := backtrack_trail learned s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |}.
Proof.
  intros s learned pending [Hstaged [Hlearned Harity]] Hroot Hdecision Hclass.
  unfold staged_invariant in Hstaged.
  destruct Hstaged as [Hcover Hstaged].
  destruct Hstaged as [Hfals Hstaged].
  destruct Hstaged as [Hwatch Hstaged].
  destruct Hstaged as [Hnodup Hstaged].
  destruct Hstaged as [Hwork Hstaged].
  destruct Hstaged as [Hworkvalid Hstaged].
  destruct Hstaged as [Hpending Hstaged].
  destruct Hstaged as [Hworkcard Hstaged].
  destruct Hstaged as [Hcard Htrail].
  pose proof (backtrack_trail_model_suffix learned s.(state_trail)) as Hsuffix.
  set (trail := backtrack_trail learned s.(state_trail)) in *.
  set (m := trail_model trail) in *.
  assert (Htrail' : trail_invariant s.(state_clauses) s.(state_learned) trail).
  { subst trail. now apply backtrack_trail_invariant. }
  assert (Hroot_suffix : model_suffix
      (trail_model (pop_to_root s.(state_trail))) (trail_model trail)).
  { subst trail.
    pose proof (pop_to_root_model_suffix
      (backtrack_trail learned s.(state_trail))) as Hroot_suffix.
    now rewrite pop_to_root_backtrack_trail in Hroot_suffix. }
  assert (Htrail_nodup : NoDup (map literal_var (trail_model trail))).
  { now apply trail_invariant_vars_nodup with
      (clauses := s.(state_clauses)) (learned := s.(state_learned)). }
  subst m.
  assert (Harity' : staged_clause_arity []
      {| state_trail := trail;
         state_clauses := s.(state_clauses);
         state_learned := s.(state_learned);
         state_watched := s.(state_watched);
         state_pending := pending |}).
  { unfold staged_clause_arity in Harity |- *. cbn in Harity |- *.
    exact Harity. }
  split.
  - unfold staged_invariant. cbn.
    split.
    + intros ci c Hfind Hunsatisfied.
      destruct (clause_has_opposite_literals c) eqn:Hopposite.
      * left. now apply clause_has_opposite_literals_spec.
      * assert (Hnoopp : ~ has_opposite_literals c).
        { intros Hopp. apply clause_has_opposite_literals_spec in Hopp.
          congruence. }
        right. right.
      apply Is_true_eq_true in Hunsatisfied.
      apply Bool.negb_true_iff in Hunsatisfied.
      change (existsb (literal_is_true trail) c = false) in Hunsatisfied.
      destruct (filter (literal_is_undecided (trail_model trail)) c)
        as [|l undecided]
        eqn:Hfilter.
      ** right. left. unfold reclassify_state in Hclass.
        exists c. split; [exact Hfind|]. split.
        -- apply Is_true_eq_left. now apply Bool.negb_true_iff.
        -- exact Hfilter.
      ** destruct (find_different_var (literal_var l) undecided)
          as [different|] eqn:Hdifferent.
        -- left. split.
           ++ unfold watched_clause.
              destruct (find_different_var_spec _ _ _ Hdifferent)
                as [Hdifferentin Hvars].
              assert (clause_has_two_variables c) as Htwo.
              { assert (In l (filter (literal_is_undecided trail) c)) as Hl
                  by (rewrite Hfilter; now left).
                assert (In different
                    (filter (literal_is_undecided trail) c)) as Hd
                  by (rewrite Hfilter; now right).
                apply filter_In in Hl as [Hlc _].
                apply filter_In in Hd as [Hdc _].
                exists l, different. now repeat split. }
              specialize (Harity ci c Hfind (fun H => H) Hnoopp).
              destruct Harity as [[_ Htwo_watches]|[Hnotwo _]];
                [|contradiction].
              assert (ClauseMap.card_of ci s.(state_watched) > 0) as Hpositive
                by (rewrite Htwo_watches; lia).
              apply ClauseMap.card_of_pos in Hpositive as [v Hv].
              now exists v.
           ++ change (filter (literal_is_undecided trail) c <> []).
              rewrite Hfilter. discriminate.
        -- destruct (clause_has_two_variablesb c) eqn:Htwob.
           ++ assert (Htwo : clause_has_two_variables c).
              { apply clause_has_two_variablesb_spec. now rewrite Htwob. }
              left. split.
              { unfold watched_clause.
                 specialize (Harity ci c Hfind (fun H => H) Hnoopp).
                 destruct Harity as [[_ Htwo_watches]|[Hnotwo' _]];
                   [|contradiction].
                 assert (ClauseMap.card_of ci s.(state_watched) > 0)
                   as Hpositive by (rewrite Htwo_watches; lia).
                 apply ClauseMap.card_of_pos in Hpositive as [v Hv].
                 now exists v. }
              { change (filter (literal_is_undecided trail) c <> []).
                rewrite Hfilter. discriminate. }
           ++ assert (Hnotwo : ~ clause_has_two_variables c).
              { intros Htwo. apply clause_has_two_variablesb_spec in Htwo.
                now rewrite Htwob in Htwo. }
              exfalso.
              pose proof (satisfied_model_suffix_extension _ _ c
                Hroot_suffix Htrail_nodup
                (Hroot ci c Hfind Hnoopp Hnotwo Hdecision)) as Hsatisfied.
              apply Is_true_eq_true in Hsatisfied.
              congruence.
    + split.
      * intros ci Hin. exact Hin.
      * split.
        -- intros v ci Hin.
           destruct (Hwatch v ci Hin) as
             [c [Hfind [Hsem [HinL [Hnoopp [Hpos Hneg]]]]]].
           exists c. split; [exact Hfind|]. split.
           ++ destruct (Hsem (fun H => H)) as [Hneeds Htwo]. split.
              ** unfold follows_needed_literal in Hneeds |- *.
                 intros suffix Hsuffix' l Hlu Hneeded.
                 eapply Hneeds; [|exact Hlu|exact Hneeded].
                 eapply model_suffix_trans; eauto.
              ** intros Hcardneq. specialize (Htwo Hcardneq).
                 unfold follows_two_undecided in Htwo |- *.
                 intros suffix Hsuffix' Hunsat Htwoundecided.
                 eapply Htwo; [|exact Hunsat|exact Htwoundecided].
                 eapply model_suffix_trans; eauto.
           ++ repeat split; assumption.
        -- split; [exact Hnodup|]. split.
           ++ constructor.
           ++ split.
              ** intros ci Hin. contradiction.
              ** split.
                 --- intros l ci Hin.
                     unfold reclassify_state in Hclass.
                     rewrite <- Hclass in Hin.
                     destruct (reclassify_clauses_pending_sound _ _ _ _ _ Hin)
                       as [_ [c [undecided [Hfind [Hnoopp [Hscan Hdiff]]]]]].
                     exists c. split; [exact Hfind|]. split; [|exact Hnoopp].
                     rewrite scan_clause_once_spec in Hscan.
                     injection Hscan as Hfalse Hfilter.
                     eapply unit_filter_needs; eauto.
                 --- split.
                     { intros ci Hin. contradiction. }
                     split.
                     { intros ci.
                       specialize (Hcard ci). unfold card_of_watch in Hcard |- *.
                       cbn in Hcard |- *.
                       destruct Hcard as [Hzero|[Htwo|[Hone _]]].
                       - now left.
                       - now right; left.
                       - exfalso.
                         assert (ClauseMap.card_of ci s.(state_watched) > 0)
                           as Hpositive by (rewrite Hone; lia).
                         apply ClauseMap.card_of_pos in Hpositive as [v Hv].
                         destruct (Hwatch v ci Hv) as
                           [c [Hfind [_ [_ [Hnoopp _]]]]].
                         specialize (Harity ci c Hfind (fun H => H) Hnoopp).
                         destruct Harity as [[_ Htwo]|[_ Hzero]]; congruence. }
                     exact Htrail'.
  - split; [exact Hlearned|exact Harity'].
Qed.

Lemma literal_false_model_suffix_extension : forall model suffix l,
  model_suffix suffix model ->
  NoDup (map literal_var model) ->
  literal_value suffix l = Some false ->
  literal_value model l = Some false.
Proof.
  intros model suffix l [prefix ->] Hnodup Hfalse.
  induction prefix as [|assigned prefix IH]; cbn [app] in *; [exact Hfalse|].
  inversion Hnodup as [|? ? Hfresh Hnodup']; subst.
  apply literal_false_cons_undecided.
  - apply not_InL_literal_undecided. rewrite InL_map_literal_var.
    exact Hfresh.
  - now apply IH.
Qed.

Lemma resolve_clause_falsified : forall model suffix pivot left reason,
  clause_falsified_by_model model left ->
  clause_needs_literal suffix pivot reason ->
  model_suffix suffix model ->
  NoDup (map literal_var model) ->
  clause_falsified_by_model model (resolve_clause pivot left reason).
Proof.
  intros model suffix pivot left reason Hleft Hneeds Hsuffix Hnodup l Hin.
  unfold resolve_clause in Hin. apply in_clause_union in Hin as [Hin|Hin].
  - apply in_without_literal in Hin as [Hin _]. now apply Hleft.
  - apply in_without_literal in Hin as [Hin Hneq].
    apply literal_false_model_suffix_extension with (suffix := suffix);
      try assumption. now apply (proj2 Hneeds l Hin).
Qed.

Lemma analyze_conflict_trail_falsified :
  forall clauses learned trail conflict model,
  trail_invariant clauses learned trail ->
  model_suffix (trail_model trail) model ->
  NoDup (map literal_var model) ->
  clause_falsified_by_model model conflict ->
  clause_falsified_by_model model
    (analyze_conflict_trail clauses learned trail conflict).
Proof.
  intros clauses learned trail. induction trail as [|entry trail IH];
    intros conflict model Htrail Hsuffix Hnodup Hfalse; [exact Hfalse|].
  assert (Htail : trail_invariant clauses learned trail).
  { now apply trail_invariant_tail with (entry := entry). }
  assert (Htailsuffix : model_suffix (trail_model trail) model).
  { eapply model_suffix_trans; [|exact Hsuffix].
    exists [trail_literal entry]. reflexivity. }
  destruct entry as [decision|propagated cause]; cbn [analyze_conflict_trail].
  - eapply IH; eauto.
  - destruct Htrail as [_ Hjustified]. cbn in Hjustified.
    destruct Hjustified as [_ [reason [Hfind [Hneeds _]]]].
    destruct (in_dec literal_eq_dec (opposite_literal propagated) conflict)
      as [Hin|Hnotin].
    + rewrite Hfind. eapply IH; eauto.
      eapply resolve_clause_falsified; eauto.
    + eapply IH; eauto.
Qed.

Lemma negated_decisions_falsified : forall s,
  state_invariant s ->
  clause_falsified_by_model s.(state_trail)
    (negated_decisions s.(state_trail)).
Proof.
  intros s Hinv l Hin. apply negated_decisions_spec in Hin.
  destruct Hin as [decision [Hdecision ->]].
  pose proof (decisions_hold s decision Hinv Hdecision) as Htrue.
  assert (Hopposite : forall model assigned,
    literal_value model assigned = Some true ->
    literal_value model (opposite_literal assigned) = Some false).
  { intros model [v|v] Hassigned;
      unfold literal_value in Hassigned |- *;
      cbn [opposite_literal literal_var] in *;
      destruct (find (fun l => Id.eqb (literal_var l) v) model)
        as [[w|w]|]; try discriminate; reflexivity. }
  now apply Hopposite.
Qed.

Lemma analyze_conflict_falsified : forall s conflict learned,
  state_invariant s ->
  clause_falsified_by_model s.(state_trail) conflict ->
  analyze_conflict s conflict = Some learned ->
  clause_falsified_by_model s.(state_trail) learned.
Proof.
  intros s conflict learned Hinv Hfalse Hanalyze.
  destruct (analyze_conflict_some s conflict learned Hanalyze)
    as [->|[Hempty ->]].
  - eapply analyze_conflict_trail_falsified.
    + now apply state_invariant_trail.
    + apply model_suffix_refl.
    + apply trail_invariant_vars_nodup with
        (clauses := s.(state_clauses)) (learned := s.(state_learned)).
      now apply state_invariant_trail.
    + exact Hfalse.
  - now apply negated_decisions_falsified.
Qed.

Lemma literal_false_tail_unless_opposite : forall model assigned l,
  literal_is_undecided model assigned = true ->
  literal_value (assigned :: model) l = Some false ->
  l <> opposite_literal assigned ->
  literal_value model l = Some false.
Proof.
  intros model [v|v] [w|w] Hundecided Hfalse Hnotopposite;
    cbn [literal_var opposite_literal] in *;
    destruct (Id.eq_dec v w) as [->|Hneq].
  - unfold literal_value in Hfalse. cbn in Hfalse.
    rewrite Id.eqb_refl in Hfalse. discriminate.
  - rewrite literal_value_cons_other_var in Hfalse; [exact Hfalse|exact Hneq].
  - exfalso. apply Hnotopposite. reflexivity.
  - rewrite literal_value_cons_other_var in Hfalse; [exact Hfalse|exact Hneq].
  - exfalso. apply Hnotopposite. reflexivity.
  - rewrite literal_value_cons_other_var in Hfalse; [exact Hfalse|exact Hneq].
  - unfold literal_value in Hfalse. cbn in Hfalse.
    rewrite Id.eqb_refl in Hfalse. discriminate.
  - rewrite literal_value_cons_other_var in Hfalse; [exact Hfalse|exact Hneq].
Qed.

Lemma opposite_undecided : forall model l,
  literal_is_undecided model l = true ->
  literal_is_undecided model (opposite_literal l) = true.
Proof.
  intros model [v|v] Hundecided; cbn [opposite_literal] in *.
  - now rewrite <- literal_is_undecided_pos_neg.
  - now rewrite literal_is_undecided_pos_neg.
Qed.

Lemma pop_falsified_clause_undecided : forall clauses learned trail c,
  trail_invariant clauses learned trail ->
  c <> [] ->
  clause_falsified_by_model (trail_model trail) c ->
  exists l, In l c /\
    literal_is_undecided (trail_model (pop_to_decision c trail)) l = true.
Proof.
  intros clauses learned trail. induction trail as [|entry trail IH];
    intros c Hinv Hnonempty Hfalse.
  - destruct c as [|l c]; [contradiction|].
    specialize (Hfalse l (or_introl eq_refl)). discriminate.
  - pose proof (trail_invariant_tail clauses learned entry trail Hinv) as Htail.
    destruct entry as [decision|propagated cause].
    + destruct Hinv as [_ Hjustified]. cbn in Hjustified.
      destruct Hjustified as [Hundecided _].
      cbn [pop_to_decision pop_to_decision_after] in *.
      destruct (in_dec literal_eq_dec (opposite_literal decision) c)
        as [Hin|Hnotin].
      * exists (opposite_literal decision). split; [exact Hin|].
        now apply opposite_undecided.
      * apply IH; try assumption. intros l Hin.
        eapply literal_false_tail_unless_opposite; eauto.
        intros ->. contradiction.
    + destruct Hinv as [_ Hjustified]. cbn in Hjustified.
      destruct Hjustified as [Hundecided _].
      cbn [pop_to_decision pop_to_decision_after] in *.
      destruct (in_dec literal_eq_dec (opposite_literal propagated) c)
        as [Hin|Hnotin].
      * exists (opposite_literal propagated). split; [exact Hin|].
        eapply undecided_model_suffix.
        -- apply pop_to_decision_after_model_suffix.
        -- now apply opposite_undecided.
      * apply IH; try assumption. intros l Hin.
        eapply literal_false_tail_unless_opposite; eauto.
        intros ->. contradiction.
Qed.

Lemma literal_true_model_suffix_extension : forall model suffix l,
  model_suffix suffix model ->
  NoDup (map literal_var model) ->
  literal_is_true suffix l = true ->
  literal_is_true model l = true.
Proof.
  intros model suffix l [prefix ->] Hnodup Htrue.
  induction prefix as [|assigned prefix IH]; cbn [app] in *; [exact Htrue|].
  inversion Hnodup as [|? ? Hfresh Hnodup']; subst.
  apply literal_is_true_cons_undecided.
  - apply not_InL_literal_undecided. rewrite InL_map_literal_var.
    exact Hfresh.
  - now apply IH.
Qed.

Lemma falsified_clause_suffix_not_satisfied : forall model suffix c,
  clause_falsified_by_model model c ->
  model_suffix suffix model ->
  NoDup (map literal_var model) ->
  existsb (literal_is_true suffix) c = false.
Proof.
  intros model suffix c Hfalse Hsuffix Hnodup.
  destruct (existsb (literal_is_true suffix) c) eqn:Hsatisfied;
    [|reflexivity].
  apply existsb_exists in Hsatisfied as [l [Hin Htrue]].
  pose proof (literal_true_model_suffix_extension model suffix l Hsuffix
    Hnodup Htrue) as Htrue'.
  specialize (Hfalse l Hin). unfold literal_is_true in Htrue'.
  rewrite Hfalse in Htrue'. discriminate.
Qed.

Lemma analyze_conflict_some_nonempty : forall s cause learned,
  analyze_conflict s cause = Some learned -> learned <> [].
Proof.
  intros s cause learned Hanalyze. unfold analyze_conflict in Hanalyze.
  destruct (negated_decisions s.(state_trail)) as [|decision decisions];
    [discriminate|].
  destruct (analyze_conflict_trail s.(state_clauses) s.(state_learned)
    s.(state_trail) cause) as [|l analyzed]; injection Hanalyze as <-;
    discriminate.
Qed.

Lemma analyzed_clause_undecided_after_pop : forall s cause learned,
  state_invariant s ->
  clause_falsified_by_model s.(state_trail) cause ->
  analyze_conflict s cause = Some learned ->
  exists l, In l learned /\
    literal_is_undecided (pop_to_decision learned s.(state_trail)) l = true.
Proof.
  intros s cause learned Hinv Hcausefalse Hanalyze.
  eapply pop_falsified_clause_undecided.
  - now apply state_invariant_trail.
  - exact (analyze_conflict_some_nonempty s cause learned Hanalyze).
  - eapply analyze_conflict_falsified; eauto.
Qed.

Lemma analyzed_clause_not_satisfied_after_pop : forall s cause learned,
  state_invariant s ->
  clause_falsified_by_model s.(state_trail) cause ->
  analyze_conflict s cause = Some learned ->
  existsb (literal_is_true (backtrack_trail learned s.(state_trail)))
    learned = false.
Proof.
  intros s cause learned Hinv Hcausefalse Hanalyze.
  eapply falsified_clause_suffix_not_satisfied.
  - eapply analyze_conflict_falsified; eauto.
  - apply backtrack_trail_model_suffix.
  - apply trail_invariant_vars_nodup with
      (clauses := s.(state_clauses)) (learned := s.(state_learned)).
    now apply state_invariant_trail.
Qed.

Lemma backtrack_conflict_sound : forall s cause s' cause',
  backtrack_invariant s ->
  clause_implied_by_store s.(state_clauses) cause ->
  clause_falsified_by_model s.(state_trail) cause ->
  backtrack (s, cause) = Some (Conflict s' cause') ->
  clause_implied_by_store s.(state_clauses) cause' /\
  clause_falsified_by_model s'.(state_trail) cause' /\
  s'.(state_clauses) = s.(state_clauses).
Proof.
  intros s cause s' cause' [Hinv [Hroot Hcurrent]] Himplied Hfalse Hbacktrack.
  unfold backtrack in Hbacktrack. cbn [count_conflict] in Hbacktrack.
  destruct (analyze_conflict s cause) as [learned|] eqn:Hanalyze;
    [|discriminate].
  remember (reclassify_state
    (trail_model (backtrack_trail learned s.(state_trail))) s)
    as pending eqn:Hpending.
  remember
    {| state_trail := backtrack_trail learned s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |} as reset eqn:Hreset.
  assert (clause_implied_by_store s.(state_clauses) learned) as Hlearnedimplied.
  { eapply analyze_conflict_implied;
      [exact (conj Hinv (conj Hroot Hcurrent))|
       exact Hanalyze|exact Himplied|exact Hfalse]. }
  assert (state_invariant reset) as Hresetinv.
  { subst reset. eapply reclassify_backtracked_inv;
      [exact Hinv|exact Hroot|
       exact (analyze_conflict_some_has_decision s cause learned Hanalyze)|].
    now symmetry. }
  assert (existsb (literal_is_true reset.(state_trail)) learned = false)
    as Hlearnedfalse.
  { subst reset. cbn.
    exact (analyzed_clause_not_satisfied_after_pop s cause learned
      Hinv Hfalse Hanalyze). }
  assert (Hfinish : Some (add_learned reset learned) =
      Some (Conflict s' cause') ->
      clause_implied_by_store s.(state_clauses) cause' /\
      clause_falsified_by_model s'.(state_trail) cause' /\
      s'.(state_clauses) = s.(state_clauses)).
  { intros Hresult.
    destruct (add_learned reset learned) as [final|final finalcause]
      eqn:Hadd; [discriminate|].
    injection Hresult as <- <-.
    destruct (add_learned_conflict_spec _ _ _ _ Hadd)
      as [-> [Hlearnedfalsified Hclauses]].
    split; [exact Hlearnedimplied|]. split; [exact Hlearnedfalsified|].
    subst reset. cbn in Hclauses. exact Hclauses. }
  destruct (trail_has_decision (backtrack_trail learned s.(state_trail)));
    [now apply Hfinish|].
  destruct (scan_clause_once (backtrack_trail learned s.(state_trail)) learned)
    as [satisfied undecided].
  destruct satisfied; [now apply Hfinish|].
  destruct undecided as [|l undecided]; [discriminate|now apply Hfinish].
Qed.

Lemma backtrack_conflict_inv : forall s cause s' cause',
  backtrack_invariant s ->
  clause_implied_by_store s.(state_clauses) cause ->
  clause_falsified_by_model s.(state_trail) cause ->
  backtrack (s, cause) = Some (Conflict s' cause') ->
  backtrack_invariant s'.
Proof.
  intros s cause s' cause' [Hinv [Hroot Hcurrent]] Himplied Hfalse Hbacktrack.
  unfold backtrack in Hbacktrack. cbn [count_conflict] in Hbacktrack.
  destruct (analyze_conflict s cause) as [learned|] eqn:Hanalyze;
    [|discriminate].
  remember (reclassify_state
    (trail_model (backtrack_trail learned s.(state_trail))) s)
    as pending eqn:Hpending.
  remember
    {| state_trail := backtrack_trail learned s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |} as reset eqn:Hreset.
  assert (state_invariant reset) as Hresetinv.
  { subst reset. eapply reclassify_backtracked_inv;
      [exact Hinv|exact Hroot|
       exact (analyze_conflict_some_has_decision s cause learned Hanalyze)|].
    now symmetry. }
  assert (clause_implied_by_store reset.(state_clauses) learned)
    as Hlearnedimplied.
  { subst reset. cbn. eapply analyze_conflict_implied;
      [exact (conj Hinv (conj Hroot Hcurrent))|
       exact Hanalyze|exact Himplied|exact Hfalse]. }
  assert (existsb (literal_is_true reset.(state_trail)) learned = false)
    as Hlearnedfalse.
  { subst reset. cbn.
    exact (analyzed_clause_not_satisfied_after_pop s cause learned
      Hinv Hfalse Hanalyze). }
  assert (Hresult : Some (add_learned reset learned) =
      Some (Conflict s' cause')).
  { destruct (trail_has_decision
      (backtrack_trail learned s.(state_trail))) eqn:Hdecision.
    - exact Hbacktrack.
    - destruct (scan_clause_once
        (backtrack_trail learned s.(state_trail)) learned)
        as [satisfied undecided].
      destruct satisfied; [exact Hbacktrack|].
      destruct undecided; [discriminate|exact Hbacktrack]. }
  destruct (add_learned reset learned) as [final|final finalcause]
    eqn:Hadd.
  - discriminate Hresult.
  - exfalso.
    destruct (add_learned_conflict_spec _ _ _ _ Hadd)
      as [_ [Hlearnedfalsified _]].
    pose proof (add_learned_result_trail _ _ _ Hadd) as Htrail.
    assert (Hscan : scan_clause_once
        (backtrack_trail learned s.(state_trail)) learned = (false, [])).
    { apply falsified_scan_clause_once.
      subst reset. cbn in Htrail. rewrite <- Htrail.
      exact Hlearnedfalsified. }
    change
      (match trail_has_decision
          (backtrack_trail learned s.(state_trail)),
          scan_clause_once (backtrack_trail learned s.(state_trail)) learned with
       | false, (false, []) => None
       | _, _ => Some (Conflict final finalcause)
       end = Some (Conflict s' cause')) in Hbacktrack.
    destruct (trail_has_decision
      (backtrack_trail learned s.(state_trail))) eqn:Hdecision.
    2:{ rewrite Hscan in Hbacktrack. discriminate. }
    destruct (analyzed_clause_undecided_after_pop s cause learned
      Hinv Hfalse Hanalyze)
      as [l [Hlin Hlu]].
    rewrite <- (backtrack_trail_with_decision learned s.(state_trail)
      Hdecision) in Hlu.
    specialize (Hlearnedfalsified l Hlin).
    subst reset. cbn in Htrail. rewrite <- Htrail in Hlu.
    unfold literal_is_undecided in Hlu.
    rewrite Hlearnedfalsified in Hlu. discriminate.
Qed.

Lemma below_current_level_trail_invariant : forall clauses learned trail,
  trail_invariant clauses learned trail ->
  trail_invariant clauses learned (below_current_level trail).
Proof.
  intros clauses learned trail. induction trail as [|entry trail IH];
    intros Hinv; [exact Hinv|].
  destruct entry as [l|l cause]; cbn [below_current_level].
  - now apply trail_invariant_tail with (entry := Decision l).
  - apply IH. now apply trail_invariant_tail with
      (entry := Propagation l cause).
Qed.

Lemma pop_to_decision_after_below_current_level : forall clause after trail,
  trail_has_decision trail = true ->
  model_suffix (trail_model (pop_to_decision_after clause after trail))
    (trail_model (below_current_level trail)).
Proof.
  intros clause after trail. induction trail as [|entry trail IH] in after |- *;
    intros Hdecision; [discriminate|].
  destruct entry as [l|l cause].
  - cbn [below_current_level pop_to_decision_after]. destruct after.
    + apply model_suffix_refl.
    + destruct (in_dec literal_eq_dec (opposite_literal l) clause).
      * apply model_suffix_refl.
      * apply pop_to_decision_after_model_suffix.
  - cbn [below_current_level pop_to_decision_after trail_has_decision]
      in Hdecision |- *.
    destruct (in_dec literal_eq_dec (opposite_literal l) clause);
      now apply IH.
Qed.

Lemma pop_to_root_below_current_level : forall trail,
  trail_has_decision trail = true ->
  model_suffix (trail_model (pop_to_root trail))
    (trail_model (below_current_level trail)).
Proof.
  intros trail. induction trail as [|entry trail IH];
    intros Hdecision; [discriminate|].
  destruct entry as [l|l cause].
  - cbn [pop_to_root below_current_level trail_has_decision].
    apply pop_to_root_model_suffix.
  - cbn [trail_has_decision] in Hdecision.
    cbn [pop_to_root below_current_level].
    change (model_suffix
      (trail_model (if trail_has_decision trail then pop_to_root trail
        else Propagation l cause :: trail))
      (trail_model (below_current_level trail))).
    rewrite Hdecision.
    now apply IH.
Qed.

Lemma backtrack_trail_below_current_level : forall learned trail,
  trail_has_decision trail = true ->
  model_suffix (trail_model (backtrack_trail learned trail))
    (trail_model (below_current_level trail)).
Proof.
  intros learned trail Hdecision. unfold backtrack_trail.
  destruct (clause_has_two_variablesb learned).
  - destruct (pop_to_decision learned trail) eqn:Hpop.
    + now apply pop_to_root_below_current_level.
    + rewrite <- Hpop. unfold pop_to_decision.
      now apply pop_to_decision_after_below_current_level.
  - now apply pop_to_root_below_current_level.
Qed.

Lemma backtracked_no_falsified_clauses : forall s cause learned pending,
  state_invariant s ->
  current_level_falsified_invariant s ->
  analyze_conflict s cause = Some learned ->
  no_falsified_clauses
    {| state_trail := backtrack_trail learned s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |}.
Proof.
  intros s cause learned pending Hinv Hcurrent Hanalyze ci Hfalse.
  destruct Hfalse as [c [Hfind [Hfalse Hnone]]].
  cbn [find_clause state_clauses state_learned state_trail] in Hfind, Hfalse, Hnone.
  change (find_clause ci s = Some c) in Hfind.
  pose proof (falsified_clause_spec _ _ Hfalse Hnone) as Hbackfalse.
  assert (Hdecision : trail_has_decision s.(state_trail) = true).
  { exact (analyze_conflict_some_has_decision s cause learned Hanalyze). }
  assert (Htrailnodup : NoDup (map literal_var
      (trail_model s.(state_trail)))).
  { apply trail_invariant_vars_nodup with
      (clauses := s.(state_clauses)) (learned := s.(state_learned)).
    now apply state_invariant_trail. }
  assert (Horiginalfalse : clause_falsified_by_model s.(state_trail) c).
  { intros l Hin. eapply literal_false_model_suffix_extension.
    - apply backtrack_trail_model_suffix.
    - exact Htrailnodup.
    - now apply Hbackfalse. }
  specialize (Hcurrent Hdecision ci c Hfind Horiginalfalse).
  apply Hcurrent. intros l Hin. eapply literal_false_model_suffix_extension.
  - now apply backtrack_trail_below_current_level.
  - apply trail_invariant_vars_nodup with
      (clauses := s.(state_clauses)) (learned := s.(state_learned)).
    apply below_current_level_trail_invariant.
    now apply state_invariant_trail.
  - now apply Hbackfalse.
Qed.

Lemma falsified_clause_no_opposites : forall trail c,
  trail_consistent trail ->
  clause_falsified_by_model trail c ->
  ~ has_opposite_literals c.
Proof.
  intros trail c Hconsistent Hfalse [v [Hpos Hneg]].
  pose proof (literal_value_false_opposite_in _ _
    (Hfalse (Pos v) Hpos)) as Hnegmodel.
  pose proof (literal_value_false_opposite_in _ _
    (Hfalse (Neg v) Hneg)) as Hposmodel.
  change (In (Neg v) (trail_model trail)) in Hnegmodel.
  change (In (Pos v) (trail_model trail)) in Hposmodel.
  apply Hconsistent. now exists v.
Qed.

Lemma add_learned_progress_new_not_falsified : forall s learned final,
  trail_consistent s.(state_trail) ->
  add_learned s learned = Progress final ->
  ~ clause_falsified_by_model s.(state_trail) learned.
Proof.
  intros s learned final Hconsistent Hadd Hfalse.
  assert (Hnoopp : ~ has_opposite_literals learned).
  { now apply falsified_clause_no_opposites with (trail := s.(state_trail)). }
  assert (Hopposite : clause_has_opposite_literals learned = false).
  { destruct (clause_has_opposite_literals learned) eqn:Hopp;
      [|reflexivity]. exfalso. apply Hnoopp.
    now apply clause_has_opposite_literals_spec. }
  pose proof (falsified_scan_clause_once s.(state_trail) learned Hfalse)
    as Hscan.
  unfold add_learned, add_clause_to, index_clause in Hadd.
  cbn [state_trail state_clauses state_learned state_watched state_pending]
    in Hadd.
  rewrite Hscan, Hopposite in Hadd. discriminate.
Qed.

Lemma add_learned_progress_no_falsified : forall s learned final,
  trail_consistent s.(state_trail) ->
  no_falsified_clauses s ->
  add_learned s learned = Progress final ->
  no_falsified_clauses final.
Proof.
  intros s learned final Hconsistent Hnone Hadd ci Hfalse.
  destruct Hfalse as [c [Hfind [Hfalse Hdecided]]].
  pose proof (add_learned_progress_fields s learned final Hadd) as Hclauses.
  pose proof (add_learned_progress_learned_trail s learned final Hadd)
    as [Hlearned Htrail].
  assert (Hsemantic : clause_falsified_by_model s.(state_trail) c).
  { rewrite <- Htrail. now apply falsified_clause_spec. }
  unfold find_clause, find_clause_in in Hfind.
  rewrite Hclauses, Hlearned in Hfind.
  destruct ci as [id|id].
  - apply (Hnone (Source id)). exists c. unfold find_clause, find_clause_in.
    rewrite <- Htrail. now repeat split.
  - rewrite ClauseStore.find_add_eq in Hfind.
    destruct (ClauseIdKey.eq_dec (fresh_learned_clause_id s) id)
      as [Heq|Hneq].
    + injection Hfind as <-.
      eapply add_learned_progress_new_not_falsified; eauto.
    + apply (Hnone (Learned id)). exists c. unfold find_clause, find_clause_in.
      rewrite <- Htrail. now repeat split.
Qed.

Lemma backtrack_progress_no_falsified : forall s cause next,
  backtrack_invariant s ->
  clause_implied_by_store s.(state_clauses) cause ->
  clause_falsified_by_model s.(state_trail) cause ->
  backtrack (s, cause) = Some (Progress next) ->
  no_falsified_clauses next.
Proof.
  intros s cause next [Hinv [Hroot Hcurrent]] Himplied Hfalse Hbacktrack.
  unfold backtrack in Hbacktrack. cbn [count_conflict] in Hbacktrack.
  destruct (analyze_conflict s cause) as [learned|] eqn:Hanalyze;
    [|discriminate].
  remember (reclassify_state
    (trail_model (backtrack_trail learned s.(state_trail))) s)
    as pending eqn:Hpending.
  remember
    {| state_trail := backtrack_trail learned s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |} as reset eqn:Hreset.
  assert (Hresetinv : state_invariant reset).
  { subst reset. eapply reclassify_backtracked_inv;
      [exact Hinv|exact Hroot|
       exact (analyze_conflict_some_has_decision s cause learned Hanalyze)|].
    now symmetry. }
  assert (Hresetnone : no_falsified_clauses reset).
  { subst reset. now apply backtracked_no_falsified_clauses with
      (cause := cause). }
  assert (Hresult : Some (add_learned reset learned) = Some (Progress next)).
  { destruct (trail_has_decision
      (backtrack_trail learned s.(state_trail))) eqn:Hdecision.
    - exact Hbacktrack.
    - destruct (scan_clause_once
        (backtrack_trail learned s.(state_trail)) learned)
        as [satisfied undecided].
      destruct satisfied; [exact Hbacktrack|].
      destruct undecided; [discriminate|exact Hbacktrack]. }
  destruct (add_learned reset learned) as [final|final finalcause]
    eqn:Hadd; [|discriminate Hresult].
  injection Hresult as <-.
  assert (Hfinalnone : no_falsified_clauses final).
  { eapply add_learned_progress_no_falsified;
      [|exact Hresetnone|exact Hadd].
    exact (proj1 (state_invariant_trail reset Hresetinv)). }
  exact Hfinalnone.
Qed.

Lemma backtrack_progress_falsified_pending : forall s cause next,
  backtrack_invariant s ->
  clause_implied_by_store s.(state_clauses) cause ->
  clause_falsified_by_model s.(state_trail) cause ->
  backtrack (s, cause) = Some (Progress next) ->
  falsified_clauses_pending next.
Proof.
  intros s cause next Hinv Himplied Hfalse Hbacktrack ci Hfalsified.
  exfalso. eapply backtrack_progress_no_falsified;
    [exact Hinv|exact Himplied|exact Hfalse|exact Hbacktrack|exact Hfalsified].
Qed.

Lemma no_falsified_current_level : forall s,
  no_falsified_clauses s -> current_level_falsified_invariant s.
Proof.
  intros s Hnone Hdecision ci c Hfind Hfalse.
  exfalso. apply (Hnone ci). exists c. split; [exact Hfind|].
  pose proof (falsified_scan_clause_once s.(state_trail) c Hfalse) as Hscan.
  rewrite scan_clause_once_spec in Hscan.
  injection Hscan as Hsatisfied Hundecided.
  split; [|exact Hundecided].
  apply Is_true_eq_left. now rewrite Hsatisfied.
Qed.

Lemma backtrack_progress_inv : forall s cause next,
  backtrack_invariant s ->
  clause_implied_by_store s.(state_clauses) cause ->
  clause_falsified_by_model s.(state_trail) cause ->
  backtrack (s, cause) = Some (Progress next) ->
  backtrack_invariant next /\
  falsified_clauses_pending next /\
  next.(state_clauses) = s.(state_clauses).
Proof.
  intros s cause next [Hinv [Hroot Hcurrent]] Himplied Hfalse Hbacktrack.
  pose proof Hbacktrack as Hbacktrack_safe.
  unfold backtrack in Hbacktrack. cbn [count_conflict] in Hbacktrack.
  destruct (analyze_conflict s cause) as [learned|] eqn:Hanalyze;
    [|discriminate].
  remember (reclassify_state
    (trail_model (backtrack_trail learned s.(state_trail))) s)
    as pending eqn:Hpending.
  remember
    {| state_trail := backtrack_trail learned s.(state_trail);
       state_clauses := s.(state_clauses);
       state_learned := s.(state_learned);
       state_watched := s.(state_watched);
       state_pending := pending |} as reset eqn:Hreset.
  assert (state_invariant reset) as Hresetinv.
  { subst reset. eapply reclassify_backtracked_inv;
      [exact Hinv|exact Hroot|
       exact (analyze_conflict_some_has_decision s cause learned Hanalyze)|].
    now symmetry. }
  assert (root_unit_invariant reset) as Hresetroot.
  { subst reset. apply reclassify_backtracked_root_inv.
    - exact Hroot.
    - exact (analyze_conflict_some_has_decision s cause learned Hanalyze). }
  assert (clause_implied_by_store reset.(state_clauses) learned)
    as Hlearnedimplied.
  { subst reset. cbn. eapply analyze_conflict_implied;
      [exact (conj Hinv (conj Hroot Hcurrent))|
       exact Hanalyze|exact Himplied|exact Hfalse]. }
  assert (existsb (literal_is_true reset.(state_trail)) learned = false)
    as Hlearnedfalse.
  { subst reset. cbn.
    exact (analyzed_clause_not_satisfied_after_pop s cause learned
      Hinv Hfalse Hanalyze). }
  assert (Hresult : Some (add_learned reset learned) = Some (Progress next)).
  { destruct (trail_has_decision
      (backtrack_trail learned s.(state_trail))) eqn:Hdecision.
    - exact Hbacktrack.
    - destruct (scan_clause_once
        (backtrack_trail learned s.(state_trail)) learned)
        as [satisfied undecided].
      destruct satisfied; [exact Hbacktrack|].
      destruct undecided; [discriminate|exact Hbacktrack]. }
  destruct (add_learned reset learned) as [final|final finalcause]
    eqn:Hadd; [|discriminate Hresult].
  injection Hresult as <-.
  assert (state_invariant final) as Hfinalinv.
  { eapply add_learned_inv; [exact Hresetinv|exact Hlearnedimplied| |exact Hadd].
    intros Hsat. apply Is_true_eq_true in Hsat.
    rewrite Hlearnedfalse in Hsat. discriminate. }
  assert (root_unit_invariant final) as Hfinalroot.
  { eapply add_learned_root_unit_inv;
      [exact Hresetroot| |exact Hadd].
    intros Hsmall. subst reset. cbn.
    now apply backtrack_trail_small_no_decision. }
  assert (Hsafe : falsified_clauses_pending final).
  { eapply backtrack_progress_falsified_pending;
      [exact (conj Hinv (conj Hroot Hcurrent))|
       exact Himplied|exact Hfalse|exact Hbacktrack_safe]. }
  assert (Hfinalnone : no_falsified_clauses final).
  { eapply backtrack_progress_no_falsified;
      [exact (conj Hinv (conj Hroot Hcurrent))|
       exact Himplied|exact Hfalse|exact Hbacktrack_safe]. }
  assert (Hfinalcurrent : current_level_falsified_invariant final).
  { now apply no_falsified_current_level. }
  split.
  - exact (conj Hfinalinv (conj Hfinalroot Hfinalcurrent)).
  - split; [exact Hsafe|].
  pose proof (add_learned_progress_fields reset learned final Hadd) as Hclauses.
  subst reset. cbn in Hclauses. exact Hclauses.
Qed.

Inductive delay_returns_in {A : Type} : Delay A -> A -> nat -> Prop :=
  | delay_returns_in_now (x : A) : delay_returns_in (Now x) x 0
  | delay_returns_in_later (d : Delay A) (x : A) (n : nat) :
      delay_returns_in d x n -> delay_returns_in (Later d) x (S n).

Lemma delay_returns_in_returns : forall A (d : Delay A) x n,
  delay_returns_in d x n -> delay_returns d x.
Proof.
  intros A d x n Hreturns. induction Hreturns; constructor; assumption.
Qed.

Lemma delay_returns_returns_in : forall A (d : Delay A) x,
  delay_returns d x -> exists n, delay_returns_in d x n.
Proof.
  intros A d x Hreturns. induction Hreturns.
  - exists 0. constructor.
  - destruct IHHreturns as [n Hn]. exists (S n). now constructor.
Qed.

Lemma delay_bind_unfold : forall A B (d : Delay A) (k : A -> Delay B),
  delay_bind d k =
    match d with
    | Now x => k x
    | Later d' => Later (delay_bind d' k)
    end.
Proof.
  intros A B d k.
  transitivity
    (match delay_bind d k with Now x => Now x | Later d' => Later d' end).
  - destruct (delay_bind d k); reflexivity.
  - destruct d as [x|d].
    + cbn [delay_bind]. destruct (k x); reflexivity.
    + cbn [delay_bind]. reflexivity.
Qed.

Lemma delay_bind_returns_in : forall A B (d : Delay A) (k : A -> Delay B)
    y n,
  delay_returns_in (delay_bind d k) y n ->
  exists x nd nk,
    delay_returns_in d x nd /\
    delay_returns_in (k x) y nk /\
    n = nd + nk.
Proof.
  intros A B d k y n. induction n as [|n IH] in d |- *;
    intros Hreturns.
  - destruct d as [x|d].
    + rewrite delay_bind_unfold in Hreturns.
      exists x, 0, 0. split; [apply delay_returns_in_now|].
      split; [exact Hreturns|lia].
    + rewrite delay_bind_unfold in Hreturns. inversion Hreturns.
  - destruct d as [x|d].
    + rewrite delay_bind_unfold in Hreturns.
      exists x, 0, (S n). split; [apply delay_returns_in_now|].
      split; [exact Hreturns|lia].
    + rewrite delay_bind_unfold in Hreturns.
      inversion Hreturns as [|? ? n' Htail]; subst.
      destruct (IH d Htail) as [x [nd [nk [Hd [Hk Heq]]]]].
      exists x, (S nd), nk. repeat split.
      * now constructor.
      * exact Hk.
      * lia.
Qed.

Lemma backtrack_until_unfold : forall conflict,
  backtrack_until conflict =
    match backtrack conflict with
    | None => Now None
    | Some (Progress s') => Now (Some s')
    | Some (Conflict s' cause) => Later (backtrack_until (s', cause))
    end.
Proof.
  intros conflict.
  transitivity
    (match backtrack_until conflict with
     | Now x => Now x
     | Later d => Later d
     end).
  - destruct (backtrack_until conflict); reflexivity.
  - cbn [backtrack_until].
    destruct (backtrack conflict) as [[s'|s' cause]|]; reflexivity.
Qed.

Lemma backtrack_until_some_inv : forall conflict cause next n,
  backtrack_invariant conflict ->
  clause_implied_by_store conflict.(state_clauses) cause ->
  clause_falsified_by_model conflict.(state_trail) cause ->
  delay_returns_in (backtrack_until (conflict, cause)) (Some next) n ->
  backtrack_invariant next /\
  falsified_clauses_pending next /\
  next.(state_clauses) = conflict.(state_clauses).
Proof.
  intros conflict cause next n. induction n as [|n IH]
    in conflict, cause, next |- *;
    intros Hinv Himplied Hfalse Hreturns;
    rewrite backtrack_until_unfold in Hreturns;
    destruct (backtrack (conflict, cause)) as [[state|state nextcause]|]
      eqn:Hbacktrack.
  - inversion Hreturns; subst.
    now apply backtrack_progress_inv with (cause := cause).
  - inversion Hreturns.
  - inversion Hreturns.
  - inversion Hreturns.
  - inversion Hreturns as [|? ? n' Htail]; subst.
    destruct (backtrack_conflict_sound conflict cause state nextcause
      Hinv Himplied Hfalse Hbacktrack)
      as [Hnextimplied [Hnextfalse Hnextclauses]].
    pose proof (backtrack_conflict_inv conflict cause state nextcause
      Hinv Himplied Hfalse Hbacktrack) as Hnextinv.
    assert (clause_implied_by_store state.(state_clauses) nextcause)
      as Hnextimplied'.
    { now rewrite Hnextclauses. }
    destruct (IH state nextcause next Hnextinv Hnextimplied' Hnextfalse Htail)
      as [Hstate [Hsafe Hclauses]].
    split; [exact Hstate|]. split; [exact Hsafe|].
    now etransitivity; [exact Hclauses|exact Hnextclauses].
  - inversion Hreturns.
Qed.

Lemma backtrack_until_none_unsat : forall conflict cause n,
  backtrack_invariant conflict ->
  clause_implied_by_store conflict.(state_clauses) cause ->
  clause_falsified_by_model conflict.(state_trail) cause ->
  delay_returns_in (backtrack_until (conflict, cause)) None n ->
  forall m, ~ satisfies_clause_store m conflict.(state_clauses).
Proof.
  intros conflict cause n. induction n as [|n IH] in conflict, cause |- *;
    intros Hinv Himplied Hfalse Hreturns m;
    rewrite backtrack_until_unfold in Hreturns;
    destruct (backtrack (conflict, cause)) as [[state|state nextcause]|]
      eqn:Hbacktrack.
  - inversion Hreturns.
  - inversion Hreturns.
  - destruct (backtrack_none_cases conflict cause Hbacktrack)
      as [Hanalyze|[learned [Hanalyze [Hnodecision Hscan]]]].
    + apply conflict_without_decisions_unsat with
        (s := conflict) (cause := cause); assumption.
    + eapply implied_falsified_without_decisions_unsat with
        (learned := conflict.(state_learned))
        (trail := backtrack_trail learned conflict.(state_trail))
        (cause := learned).
      * apply backtrack_trail_invariant.
        now apply state_invariant_trail, (proj1 Hinv).
      * exact (state_invariant_learned conflict (proj1 Hinv)).
      * apply (proj1 (trail_has_decision_false _)). exact Hnodecision.
      * eapply analyze_conflict_implied; eauto.
      * rewrite scan_clause_once_spec in Hscan.
        injection Hscan as Hsatisfied Hundecided.
        apply falsified_clause_spec; [|exact Hundecided].
        apply Is_true_eq_left. now apply Bool.negb_true_iff.
  - inversion Hreturns.
  - inversion Hreturns as [|? ? n' Htail]; subst.
    destruct (backtrack_conflict_sound conflict cause state nextcause
      Hinv Himplied Hfalse Hbacktrack)
      as [Hnextimplied [Hnextfalse Hnextclauses]].
    pose proof (backtrack_conflict_inv conflict cause state nextcause
      Hinv Himplied Hfalse Hbacktrack) as Hnextinv.
    assert (clause_implied_by_store state.(state_clauses) nextcause)
      as Hnextimplied'.
    { now rewrite Hnextclauses. }
    rewrite <- Hnextclauses.
    now apply (IH state nextcause Hnextinv Hnextimplied' Hnextfalse Htail m).
  - destruct (backtrack_none_cases conflict cause Hbacktrack)
      as [Hanalyze|[learned [Hanalyze [Hnodecision Hscan]]]].
    + apply conflict_without_decisions_unsat with
        (s := conflict) (cause := cause); assumption.
    + eapply implied_falsified_without_decisions_unsat with
        (learned := conflict.(state_learned))
        (trail := backtrack_trail learned conflict.(state_trail))
        (cause := learned).
      * apply backtrack_trail_invariant.
        now apply state_invariant_trail, (proj1 Hinv).
      * exact (state_invariant_learned conflict (proj1 Hinv)).
      * apply (proj1 (trail_has_decision_false _)). exact Hnodecision.
      * eapply analyze_conflict_implied; eauto.
      * rewrite scan_clause_once_spec in Hscan.
        injection Hscan as Hsatisfied Hundecided.
        apply falsified_clause_spec; [|exact Hundecided].
        apply Is_true_eq_left. now apply Bool.negb_true_iff.
Qed.

Lemma rush_result_root_unit : forall s result,
  state_invariant s ->
  root_unit_invariant s ->
  falsified_clauses_pending s ->
  delay_returns (rush s) result ->
  match result with
  | inl final => root_unit_invariant final
  | inr (final, _) => root_unit_invariant final
  end.
Proof.
  intros s result Hinv Hroot Hfalsified Hreturns.
  remember (rush s) as d eqn:Hrush.
  induction Hreturns as [x|d x Hreturns IH]
    in s, Hinv, Hroot, Hfalsified, Hrush |- *.
  - rewrite rush_unfold in Hrush.
    destruct (rush_has_work s) eqn:Hwork.
    + destruct (progress s) as [s'|s' cause] eqn:Hprogress;
        [discriminate|].
      injection Hrush as ->.
      pose proof (progress_root_unit_inv s Hinv Hroot Hfalsified) as Hroot'.
      now rewrite Hprogress in Hroot'.
    + injection Hrush as ->. exact Hroot.
  - rewrite rush_unfold in Hrush.
    destruct (rush_has_work s) eqn:Hwork; [|discriminate].
    destruct (progress s) as [s'|s' cause] eqn:Hprogress; [|discriminate].
    injection Hrush as ->.
    assert (Hinv' : state_invariant s') by
      (now apply progress_inv with (s := s)).
    assert (Hfalsified' : falsified_clauses_pending s') by
      (now apply progress_falsified_empty with (s := s)).
    pose proof (progress_root_unit_inv s Hinv Hroot Hfalsified) as Hroot'.
    rewrite Hprogress in Hroot'.
    now apply (IH s' Hinv' Hroot' Hfalsified' eq_refl).
Qed.

Lemma rush_result_current_level : forall s result,
  state_invariant s ->
  current_level_falsified_invariant s ->
  falsified_clauses_pending s ->
  delay_returns (rush s) result ->
  match result with
  | inl final => current_level_falsified_invariant final
  | inr (final, _) => current_level_falsified_invariant final
  end.
Proof.
  intros s result Hinv Hcurrent Hfalsified Hreturns.
  remember (rush s) as d eqn:Hrush.
  induction Hreturns as [x|d x Hreturns IH]
    in s, Hinv, Hcurrent, Hfalsified, Hrush |- *.
  - rewrite rush_unfold in Hrush.
    destruct (rush_has_work s) eqn:Hwork.
    + destruct (progress s) as [s'|s' cause] eqn:Hprogress;
        [discriminate|].
      injection Hrush as ->.
      pose proof (progress_result_current_level s Hinv Hcurrent Hfalsified)
        as Hcurrent'.
      now rewrite Hprogress in Hcurrent'.
    + injection Hrush as ->. exact Hcurrent.
  - rewrite rush_unfold in Hrush.
    destruct (rush_has_work s) eqn:Hwork; [|discriminate].
    destruct (progress s) as [s'|s' cause] eqn:Hprogress; [|discriminate].
    injection Hrush as ->.
    assert (Hinv' : state_invariant s') by
      (now apply progress_inv with (s := s)).
    assert (Hfalsified' : falsified_clauses_pending s') by
      (now apply progress_falsified_empty with (s := s)).
    pose proof (progress_result_current_level s Hinv Hcurrent Hfalsified)
      as Hcurrent'.
    rewrite Hprogress in Hcurrent'.
    now apply (IH s' Hinv' Hcurrent' Hfalsified' eq_refl).
Qed.

Lemma sat_unfold : forall s,
  sat s =
    delay_bind (rush s)
      (fun result =>
        match result with
        | inl final => Now (SAT final.(state_trail))
        | inr conflict =>
            delay_bind (backtrack_until conflict)
              (fun result =>
                match result with
                | Some s' => Later (sat s')
                | None => Now UNSAT
                end)
        end).
Proof.
  intros s.
  transitivity (match sat s with Now x => Now x | Later d => Later d end).
  - destruct (sat s); reflexivity.
  - cbn [sat].
    match goal with
    | |- context [delay_bind ?d ?k] => destruct (delay_bind d k)
    end; reflexivity.
Qed.

Lemma sat_model_sound_in : forall n s model,
  state_invariant s ->
  root_unit_invariant s ->
  current_level_falsified_invariant s ->
  falsified_clauses_pending s ->
  delay_returns_in (sat s) (SAT model) n ->
  satisfies_clause_store (complete_model model) s.(state_clauses).
Proof.
  intros n. induction n using lt_wf_ind;
    intros s model Hinv Hroot Hcurrent Hfalsified Hreturns.
  rewrite sat_unfold in Hreturns.
  destruct (delay_bind_returns_in _ _ _ _ _ _ Hreturns)
    as [result [nrush [ncontinuation
      [Hrush [Hcontinuation Hsteps]]]]].
  destruct result as [final|[conflict cause]].
  - cbn in Hcontinuation. inversion Hcontinuation; subst.
    eapply rush_model_sound; eauto.
    now apply delay_returns_in_returns with (n := nrush).
  - cbn -[delay_bind backtrack_until] in Hcontinuation.
    destruct (delay_bind_returns_in _ _ _ _ _ _ Hcontinuation)
      as [backtracked [nbacktrack [nresume
        [Hbacktrackreturns [Hresume Hbacktracksteps]]]]].
    destruct backtracked as [next|].
    + inversion Hresume as [|? ? nrecursive Hrecursive]; subst.
      pose proof (rush_conflict_sound s conflict cause Hinv Hfalsified
        (delay_returns_in_returns _ _ _ _ Hrush)) as [Himplied Hfalse].
      pose proof (rush_conflict_inv s conflict cause Hinv
        (delay_returns_in_returns _ _ _ _ Hrush))
        as [Hconflictinv Hconflictclauses].
      pose proof (rush_result_root_unit s (inr (conflict, cause))
        Hinv Hroot Hfalsified
        (delay_returns_in_returns _ _ _ _ Hrush)) as Hconflictroot.
      pose proof (rush_result_current_level s (inr (conflict, cause))
        Hinv Hcurrent Hfalsified
        (delay_returns_in_returns _ _ _ _ Hrush)) as Hconflictcurrent.
      assert (clause_implied_by_store conflict.(state_clauses) cause)
        as Hconflictimplied by (now rewrite Hconflictclauses).
      destruct (backtrack_until_some_inv conflict cause next nbacktrack
        (state_invariant_backtrack conflict Hconflictinv Hconflictroot
          Hconflictcurrent)
        Hconflictimplied Hfalse Hbacktrackreturns)
        as [[Hnextinv [Hnextroot Hnextcurrent]]
          [Hnextfalsified Hnextclauses]].
      rewrite <- Hconflictclauses, <- Hnextclauses.
      eapply H; eauto. lia.
    + inversion Hresume.
Qed.

Theorem sat_model_sound : forall s model,
  state_invariant s ->
  root_unit_invariant s ->
  current_level_falsified_invariant s ->
  falsified_clauses_pending s ->
  delay_returns (sat s) (SAT model) ->
  satisfies_clause_store (complete_model model) s.(state_clauses).
Proof.
  intros s model Hinv Hroot Hcurrent Hfalsified Hreturns.
  destruct (delay_returns_returns_in _ _ _ Hreturns) as [n Hreturnsin].
  now apply sat_model_sound_in with (n := n).
Qed.

Lemma sat_unsat_sound_in : forall n s,
  state_invariant s ->
  root_unit_invariant s ->
  current_level_falsified_invariant s ->
  falsified_clauses_pending s ->
  delay_returns_in (sat s) UNSAT n ->
  forall m, ~ satisfies_clause_store m s.(state_clauses).
Proof.
  intros n. induction n using lt_wf_ind;
    intros s Hinv Hroot Hcurrent Hfalsified Hreturns.
  rewrite sat_unfold in Hreturns.
  destruct (delay_bind_returns_in _ _ _ _ _ _ Hreturns)
    as [result [nrush [ncontinuation
      [Hrush [Hcontinuation Hsteps]]]]].
  destruct result as [final|[conflict cause]].
  - cbn in Hcontinuation. inversion Hcontinuation.
  - cbn -[delay_bind backtrack_until] in Hcontinuation.
    destruct (delay_bind_returns_in _ _ _ _ _ _ Hcontinuation)
      as [backtracked [nbacktrack [nresume
        [Hbacktrackreturns [Hresume Hbacktracksteps]]]]].
    pose proof (rush_conflict_sound s conflict cause Hinv Hfalsified
      (delay_returns_in_returns _ _ _ _ Hrush)) as [Himplied Hfalse].
    pose proof (rush_conflict_inv s conflict cause Hinv
      (delay_returns_in_returns _ _ _ _ Hrush))
      as [Hconflictinv Hconflictclauses].
    pose proof (rush_result_root_unit s (inr (conflict, cause))
      Hinv Hroot Hfalsified
      (delay_returns_in_returns _ _ _ _ Hrush)) as Hconflictroot.
    pose proof (rush_result_current_level s (inr (conflict, cause))
      Hinv Hcurrent Hfalsified
      (delay_returns_in_returns _ _ _ _ Hrush)) as Hconflictcurrent.
    assert (clause_implied_by_store conflict.(state_clauses) cause)
      as Hconflictimplied by (now rewrite Hconflictclauses).
    destruct backtracked as [next|].
    + inversion Hresume as [|? ? nrecursive Hrecursive]; subst.
      destruct (backtrack_until_some_inv conflict cause next nbacktrack
        (state_invariant_backtrack conflict Hconflictinv Hconflictroot
          Hconflictcurrent)
        Hconflictimplied Hfalse Hbacktrackreturns)
        as [[Hnextinv [Hnextroot Hnextcurrent]]
          [Hnextfalsified Hnextclauses]].
      rewrite <- Hconflictclauses, <- Hnextclauses.
      eapply H; eauto. lia.
    + inversion Hresume; subst.
      rewrite <- Hconflictclauses.
      eapply backtrack_until_none_unsat.
      * exact (state_invariant_backtrack conflict Hconflictinv Hconflictroot
          Hconflictcurrent).
      * exact Hconflictimplied.
      * exact Hfalse.
      * exact Hbacktrackreturns.
Qed.

Theorem sat_unsat_sound : forall s,
  state_invariant s ->
  root_unit_invariant s ->
  current_level_falsified_invariant s ->
  falsified_clauses_pending s ->
  delay_returns (sat s) UNSAT ->
  forall m, ~ satisfies_clause_store m s.(state_clauses).
Proof.
  intros s Hinv Hroot Hcurrent Hfalsified Hreturns.
  destruct (delay_returns_returns_in _ _ _ Hreturns) as [n Hreturnsin].
  now apply sat_unsat_sound_in with (n := n).
Qed.
