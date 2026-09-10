(* The core loop of a CDCL-based SAT solver *)

Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Structures.OrderedType.
Require Import Stdlib.Sorting.Permutation.
Require Import FMV.FiniteMap.
Require Import FMV.ListMap.
Require Import FMV.Map.
Require Import FMV.Id.

(* General architecture:
   - Iterate until find a model or a definite contradiction:
     - Attempt to guess a model with the `rush` function
       - Rush is simply an iteration of the `progress` function which steps
         through the CDCL algorithm. Either deciding or propagating a literal at
         every iteration.
     - (TODO) Learn a conflict clause and backtrack.
 *)

Definition Var := Id.t.
Variant Literal :=
  | Pos (l : Var)
  | Neg (l : Var)
.

Definition literal_var (l : Literal) : Var :=
  match l with
  | Pos v | Neg v => v
  end.

Definition Clause := list Literal.
Definition ClauseId := Id.t.

Variant ClausePointer :=
  | Source (c : ClauseId)
  | Learned (c : ClauseId).

Definition Problem := list Clause.

(* A partial model. The semantics is that `Pos` literals in the list are known
   to be true, `Neg` literals are known to be false. The rest is (yet)
   undecided. *)
Definition Model := list Literal.
Definition Pending := list (Literal * ClausePointer).

(* This hook is logically inert.  Extraction replaces it with a side effect
   used by the benchmark harness to count conflict-processing steps. *)
Definition count_conflict {A : Type} (value : A) : A := value.

Variant TrailEntry :=
  | Decision (l : Literal)
  | Propagation (l : Literal) (cause : ClausePointer).

Definition Trail := list TrailEntry.

Definition trail_literal (entry : TrailEntry) : Literal :=
  match entry with
  | Decision l | Propagation l _ => l
  end.

Definition trail_model (trail : Trail) : Model := map trail_literal trail.

Global Coercion trail_model : Trail >-> Model.

Definition literal_eq_dec (l r : Literal) : {l = r} + {l <> r}.
Proof.
  decide equality; apply Id.eq_dec.
Defined.

Definition opposite_literal (l : Literal) : Literal :=
  match l with
  | Pos v => Neg v
  | Neg v => Pos v
  end.

Definition literal_eqb (l r : Literal) : bool :=
  if literal_eq_dec l r then true else false.

Definition clause_has_opposite_literals (c : Clause) : bool :=
  existsb
    (fun l => existsb (literal_eqb (opposite_literal l)) c)
    c.

Definition clause_eq_dec : forall l r : Clause, {l = r} + {l <> r} :=
  list_eq_dec literal_eq_dec.

Module IdOrderedKey <: OrderedKey.
  Definition t := Var.
  Definition eq_dec := Id.eq_dec.
  Definition lt (x y : t) := Id.to_nat x < Id.to_nat y.
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof. unfold lt. intros. lia. Qed.
  Lemma lt_not_eq : forall x y, lt x y -> x <> y.
  Proof. unfold lt. intros x y Hlt ->. lia. Qed.
  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    case_eq (Nat.compare (Id.to_nat x) (Id.to_nat y)); intros Hcompare.
    - apply EQ. apply nat_compare_eq in Hcompare.
      rewrite <- (Id.of_nat_to_nat x), <- (Id.of_nat_to_nat y).
      now rewrite Hcompare.
    - apply LT. now apply nat_compare_Lt_lt.
    - apply GT. now apply nat_compare_Gt_gt.
  Defined.
End IdOrderedKey.

Module VarKey := IdOrderedKey.
Module ClauseIdKey := IdOrderedKey.

Module TruthValue.
  Definition t := bool.
End TruthValue.

Module Assignment := Map.Make VarKey TruthValue.

Definition clause_pointer_eq_dec (l r : ClausePointer) : {l = r} + {l <> r}.
Proof.
  decide equality; apply Id.eq_dec.
Defined.

Module ClausePointerElement.
  Definition t := ClausePointer.
  Definition eq_dec := clause_pointer_eq_dec.
End ClausePointerElement.

Record WatchedClauses := {
  pos : list ClausePointer;
  neg : list ClausePointer;
}.

Module WatchedClausesMonoid <: Monoid.
  Definition t := WatchedClauses.
  Definition empty := {| pos := []; neg := [] |}.
  Definition op (x y : t) :=
    {| pos := x.(pos) ++ y.(pos); neg := x.(neg) ++ y.(neg) |}.
  Lemma op_assoc : forall x y z, op x (op y z) = op (op x y) z.
  Proof.
    intros [xp xn] [yp yn] [zp zn]. unfold op. cbn. f_equal; apply app_assoc.
  Qed.
  Lemma op_empty_l : forall x, op empty x = x.
  Proof. now intros [xp xn]. Qed.
  Lemma op_empty_r : forall x, op x empty = x.
  Proof. intros [xp xn]. unfold op, empty. cbn. now rewrite !app_nil_r. Qed.
End WatchedClausesMonoid.

Module ClauseMap.
  Module Buckets := FiniteMap.RawMake VarKey WatchedClausesMonoid.
  Definition t := Buckets.t.
  Definition empty : t := Buckets.empty.

  Definition find_pos (v : Var) (m : t) :=
    (Buckets.find v m).(pos).
  Definition find_neg (v : Var) (m : t) :=
    (Buckets.find v m).(neg).
  Definition find (v : Var) (m : t) := find_pos v m ++ find_neg v m.

  Definition nonempty (w : WatchedClauses) : bool :=
    match w.(pos), w.(neg) with
    | [], [] => false
    | _, _ => true
    end.

  Definition keys (m : t) : list Var :=
    filter (fun v => nonempty (Buckets.find v m)) (Buckets.keys m).

  Definition elements (m : t) : list ClausePointer :=
    flat_map (fun v => find v m) (Buckets.keys m).

  Definition card_of (ci : ClausePointer) (m : t) : nat :=
    count_occ clause_pointer_eq_dec (elements m) ci.

  Definition find_literal (l : Literal) (m : t) : list ClausePointer :=
    match l with
    | Pos v => find_pos v m
    | Neg v => find_neg v m
    end.

  Definition singleton_watch (l : Literal) (ci : ClausePointer) :=
    match l with
    | Pos _ => {| pos := [ci]; neg := [] |}
    | Neg _ => {| pos := []; neg := [ci] |}
    end.

  Definition add (l : Literal) (ci : ClausePointer) (m : t) : t :=
    Buckets.add (literal_var l) (singleton_watch l ci) m.

  Definition remove (v : Var) (m : t) : t := Buckets.remove v m.

  (* Detach one literal's watch list while preserving the watch list for the
     opposite literal.  The detached clauses are scanned after the literal is
     falsified and either put back or moved to another literal. *)
  Definition clear_pos (w : WatchedClauses) : WatchedClauses :=
    {| pos := []; neg := w.(neg) |}.

  Definition clear_neg (w : WatchedClauses) : WatchedClauses :=
    {| pos := w.(pos); neg := [] |}.

  Definition clear_literal (l : Literal) (m : t) : t :=
    match l with
    | Pos v => Buckets.map_at v clear_pos eq_refl m
    | Neg v => Buckets.map_at v clear_neg eq_refl m
    end.

  Definition clear_falsified (l : Literal) (m : t) : t :=
    clear_literal (opposite_literal l) m.

  Lemma find_literal_clear_literal : forall l m,
    find_literal l (clear_literal l m) = [].
  Proof.
    intros [v|v] m.
    - unfold find_literal, clear_literal, find_pos.
      rewrite Buckets.find_map_at_eq.
      destruct (VarKey.eq_dec v v); [reflexivity|contradiction].
    - unfold find_literal, clear_literal, find_neg.
      rewrite Buckets.find_map_at_eq.
      destruct (VarKey.eq_dec v v); [reflexivity|contradiction].
  Qed.

  Definition find_falsified (l : Literal) (m : t) : list ClausePointer :=
    match l with
    | Pos v => find_neg v m
    | Neg v => find_pos v m
    end.

  Lemma find_falsified_clear_falsified : forall l m,
    find_falsified l (clear_falsified l m) = [].
  Proof.
    intros [v|v] m.
    - change (find_literal (Neg v) (clear_literal (Neg v) m) = []).
      apply find_literal_clear_literal.
    - change (find_literal (Pos v) (clear_literal (Pos v) m) = []).
      apply find_literal_clear_literal.
  Qed.

  Lemma find_pos_clear_pos : forall m v v',
    find_pos v' (clear_literal (Pos v) m) =
      if VarKey.eq_dec v v' then [] else find_pos v' m.
  Proof.
    intros. unfold find_pos, clear_literal. rewrite Buckets.find_map_at_eq.
    destruct (VarKey.eq_dec v v'); reflexivity.
  Qed.

  Lemma find_neg_clear_pos : forall m v v',
    find_neg v' (clear_literal (Pos v) m) = find_neg v' m.
  Proof.
    intros. unfold find_neg, clear_literal. rewrite Buckets.find_map_at_eq.
    destruct (VarKey.eq_dec v v'); reflexivity.
  Qed.

  Lemma find_pos_clear_neg : forall m v v',
    find_pos v' (clear_literal (Neg v) m) = find_pos v' m.
  Proof.
    intros. unfold find_pos, clear_literal. rewrite Buckets.find_map_at_eq.
    destruct (VarKey.eq_dec v v'); reflexivity.
  Qed.

  Lemma find_neg_clear_neg : forall m v v',
    find_neg v' (clear_literal (Neg v) m) =
      if VarKey.eq_dec v v' then [] else find_neg v' m.
  Proof.
    intros. unfold find_neg, clear_literal. rewrite Buckets.find_map_at_eq.
    destruct (VarKey.eq_dec v v'); reflexivity.
  Qed.

  Lemma find_clear_literal_in : forall m l v ci,
    In ci (find v (clear_literal l m)) -> In ci (find v m).
  Proof.
    intros m [w|w] v ci Hin; unfold find in *.
    - rewrite find_pos_clear_pos, find_neg_clear_pos in Hin.
      destruct (VarKey.eq_dec w v).
      + apply in_or_app. right. now simpl in Hin.
      + exact Hin.
    - rewrite find_pos_clear_neg, find_neg_clear_neg in Hin.
      destruct (VarKey.eq_dec w v).
      + apply in_or_app. left. now rewrite app_nil_r in Hin.
      + exact Hin.
  Qed.

  Lemma find_clear_literal_other : forall m l v,
    literal_var l <> v -> find v (clear_literal l m) = find v m.
  Proof.
    intros m [w|w] v Hneq; unfold find.
    - rewrite find_pos_clear_pos, find_neg_clear_pos.
      destruct (VarKey.eq_dec w v); [contradiction|reflexivity].
    - rewrite find_pos_clear_neg, find_neg_clear_neg.
      destruct (VarKey.eq_dec w v); [contradiction|reflexivity].
  Qed.

  Lemma find_clear_pos_eq : forall m v,
    find v (clear_literal (Pos v) m) = find_neg v m.
  Proof.
    intros. unfold find. rewrite find_pos_clear_pos, find_neg_clear_pos.
    destruct (VarKey.eq_dec v v); [reflexivity|contradiction].
  Qed.

  Lemma find_clear_neg_eq : forall m v,
    find v (clear_literal (Neg v) m) = find_pos v m.
  Proof.
    intros. unfold find. rewrite find_pos_clear_neg, find_neg_clear_neg.
    destruct (VarKey.eq_dec v v); [now rewrite app_nil_r|contradiction].
  Qed.

  Lemma flat_map_clear_other : forall ks m l,
    ~ In (literal_var l) ks ->
    flat_map (fun v => find v (clear_literal l m)) ks =
    flat_map (fun v => find v m) ks.
  Proof.
    intros ks. induction ks as [|v ks IH]; intros m l Hnotin; simpl.
    - reflexivity.
    - rewrite find_clear_literal_other.
      + f_equal. apply IH. intros Hin. apply Hnotin. now right.
      + intros Heq. apply Hnotin. now left.
  Qed.

  Lemma find_falsified_in : forall l m ci,
    In ci (find_falsified l m) -> In ci (find (literal_var l) m).
  Proof.
    intros [v|v] m ci Hin; unfold find, find_falsified; cbn;
      [now apply in_or_app; right|now apply in_or_app; left].
  Qed.

  Lemma find_pos_empty : forall v, find_pos v empty = [].
  Proof. reflexivity. Qed.
  Lemma find_neg_empty : forall v, find_neg v empty = [].
  Proof. reflexivity. Qed.

  Lemma find_pos_add_pos : forall m ci v v',
    find_pos v' (add (Pos v) ci m) =
      if VarKey.eq_dec v v' then ci :: find_pos v' m else find_pos v' m.
  Proof.
    intros. unfold find_pos, add. rewrite Buckets.find_add_eq. cbn.
    destruct (VarKey.eq_dec v v'); reflexivity.
  Qed.
  Lemma find_neg_add_pos : forall m ci v v',
    find_neg v' (add (Pos v) ci m) = find_neg v' m.
  Proof.
    intros. unfold find_neg, add. rewrite Buckets.find_add_eq. cbn.
    destruct (VarKey.eq_dec v v'); reflexivity.
  Qed.
  Lemma find_pos_add_neg : forall m ci v v',
    find_pos v' (add (Neg v) ci m) = find_pos v' m.
  Proof.
    intros. unfold find_pos, add. rewrite Buckets.find_add_eq. cbn.
    destruct (VarKey.eq_dec v v'); reflexivity.
  Qed.
  Lemma find_neg_add_neg : forall m ci v v',
    find_neg v' (add (Neg v) ci m) =
      if VarKey.eq_dec v v' then ci :: find_neg v' m else find_neg v' m.
  Proof.
    intros. unfold find_neg, add. rewrite Buckets.find_add_eq. cbn.
    destruct (VarKey.eq_dec v v'); reflexivity.
  Qed.

  Lemma find_pos_add : forall m ci watched l v,
    In watched (find_pos v m) -> In watched (find_pos v (add l ci m)).
  Proof.
    intros m ci watched [w|w] v Hin.
    - rewrite find_pos_add_pos. destruct (VarKey.eq_dec w v); simpl; auto.
    - now rewrite find_pos_add_neg.
  Qed.
  Lemma find_neg_add : forall m ci watched l v,
    In watched (find_neg v m) -> In watched (find_neg v (add l ci m)).
  Proof.
    intros m ci watched [w|w] v Hin.
    - now rewrite find_neg_add_pos.
    - rewrite find_neg_add_neg. destruct (VarKey.eq_dec w v); simpl; auto.
  Qed.

  Lemma find_pos_add_old : forall m ci watched l v,
    watched <> ci ->
    In watched (find_pos v (add l ci m)) -> In watched (find_pos v m).
  Proof.
    intros m ci watched [w|w] v Hneq Hin.
    - rewrite find_pos_add_pos in Hin. destruct (VarKey.eq_dec w v);
        simpl in Hin; intuition congruence.
    - now rewrite find_pos_add_neg in Hin.
  Qed.
  Lemma find_neg_add_old : forall m ci watched l v,
    watched <> ci ->
    In watched (find_neg v (add l ci m)) -> In watched (find_neg v m).
  Proof.
    intros m ci watched [w|w] v Hneq Hin.
    - now rewrite find_neg_add_pos in Hin.
    - rewrite find_neg_add_neg in Hin. destruct (VarKey.eq_dec w v);
        simpl in Hin; intuition congruence.
  Qed.

  Lemma find_pos_add_other : forall m ci l v,
    literal_var l <> v -> find_pos v (add l ci m) = find_pos v m.
  Proof.
    intros m ci [w|w] v Hneq; cbn [literal_var] in Hneq.
    - rewrite find_pos_add_pos. destruct (VarKey.eq_dec w v); congruence.
    - apply find_pos_add_neg.
  Qed.
  Lemma find_neg_add_other : forall m ci l v,
    literal_var l <> v -> find_neg v (add l ci m) = find_neg v m.
  Proof.
    intros m ci [w|w] v Hneq; cbn [literal_var] in Hneq.
    - apply find_neg_add_pos.
    - rewrite find_neg_add_neg. destruct (VarKey.eq_dec w v); congruence.
  Qed.

  Lemma find_pos_add_existing : forall m ci watched l v,
    ~ In ci (find (literal_var l) m) ->
    In watched (find v m) ->
    In watched (find_pos v (add l ci m)) -> In watched (find_pos v m).
  Proof.
    intros m ci watched l v Hfresh Hold Hnew.
    destruct (clause_pointer_eq_dec watched ci) as [->|Hneq].
    - rewrite find_pos_add_other in Hnew; [exact Hnew|].
      intros Heq. subst v. contradiction.
    - now apply find_pos_add_old in Hnew.
  Qed.
  Lemma find_neg_add_existing : forall m ci watched l v,
    ~ In ci (find (literal_var l) m) ->
    In watched (find v m) ->
    In watched (find_neg v (add l ci m)) -> In watched (find_neg v m).
  Proof.
    intros m ci watched l v Hfresh Hold Hnew.
    destruct (clause_pointer_eq_dec watched ci) as [->|Hneq].
    - rewrite find_neg_add_other in Hnew; [exact Hnew|].
      intros Heq. subst v. contradiction.
    - now apply find_neg_add_old in Hnew.
  Qed.

  Lemma find_pos_add_nodup : forall m ci l v,
    NoDup (find_pos v m) ->
    ~ In ci (find (literal_var l) m) ->
    NoDup (find_pos v (add l ci m)).
  Proof.
    intros m ci [w|w] v Hnodup Hfresh.
    - rewrite find_pos_add_pos. destruct (VarKey.eq_dec w v) as [->|Hneq].
      + constructor; [|exact Hnodup]. intros Hin. apply Hfresh.
        unfold find. now apply in_or_app; left.
      + exact Hnodup.
    - now rewrite find_pos_add_neg.
  Qed.

  Lemma find_neg_add_nodup : forall m ci l v,
    NoDup (find_neg v m) ->
    ~ In ci (find (literal_var l) m) ->
    NoDup (find_neg v (add l ci m)).
  Proof.
    intros m ci [w|w] v Hnodup Hfresh.
    - now rewrite find_neg_add_pos.
    - rewrite find_neg_add_neg. destruct (VarKey.eq_dec w v) as [->|Hneq].
      + constructor; [|exact Hnodup]. intros Hin. apply Hfresh.
        unfold find. now apply in_or_app; right.
      + exact Hnodup.
  Qed.

  Lemma find_pos_remove : forall m v removed,
    find_pos v (remove removed m) =
      if VarKey.eq_dec removed v then [] else find_pos v m.
  Proof.
    intros. unfold find_pos, remove. rewrite Buckets.find_remove_eq. cbn.
    destruct (VarKey.eq_dec removed v); reflexivity.
  Qed.
  Lemma find_neg_remove : forall m v removed,
    find_neg v (remove removed m) =
      if VarKey.eq_dec removed v then [] else find_neg v m.
  Proof.
    intros. unfold find_neg, remove. rewrite Buckets.find_remove_eq. cbn.
    destruct (VarKey.eq_dec removed v); reflexivity.
  Qed.

  Lemma find_empty : forall v, find v empty = [].
  Proof. reflexivity. Qed.
  Lemma card_of_empty : forall ci, card_of ci empty = 0.
  Proof. reflexivity. Qed.
  Lemma keys_complete : forall m v, find v m <> [] <-> In v (keys m).
  Proof.
    intros m v. unfold keys, find, find_pos, find_neg.
    rewrite filter_In. split.
    - intros Hfind. split.
      + apply Buckets.keys_complete. intros Hempty. rewrite Hempty in Hfind.
        contradiction.
      + destruct (Buckets.find v m) as [p n]. cbn in *.
        destruct p, n; try reflexivity; contradiction.
    - intros [_ Hnonempty]. destruct (Buckets.find v m) as [p n]. cbn in *.
      destruct p, n; discriminate.
  Qed.
  Lemma find_add : forall m x y l v,
    In y (find v (add l x m)) <->
    (v = literal_var l /\ y = x) \/ In y (find v m).
  Proof.
    intros m x y [w|w] v; unfold find.
    - rewrite find_pos_add_pos, find_neg_add_pos.
      destruct (VarKey.eq_dec w v) as [->|Hneq]; simpl;
        rewrite ?in_app_iff; firstorder congruence.
    - rewrite find_pos_add_neg, find_neg_add_neg.
      destruct (VarKey.eq_dec w v) as [->|Hneq]; simpl;
        rewrite ?in_app_iff; firstorder congruence.
  Qed.

  Lemma count_occ_find_add : forall m x y l v,
    count_occ clause_pointer_eq_dec (find v (add l x m)) y =
      if VarKey.eq_dec (literal_var l) v then
        count_occ clause_pointer_eq_dec [x] y +
          count_occ clause_pointer_eq_dec (find v m) y
      else count_occ clause_pointer_eq_dec (find v m) y.
  Proof.
    intros m x y [w|w] v; unfold find.
    - rewrite find_pos_add_pos, find_neg_add_pos.
      destruct (VarKey.eq_dec w v) eqn:Hwv.
      + simpl. rewrite Hwv. rewrite !count_occ_app. simpl.
        destruct (clause_pointer_eq_dec x y); simpl; reflexivity.
      + simpl. now rewrite Hwv.
    - rewrite find_pos_add_neg, find_neg_add_neg.
      destruct (VarKey.eq_dec w v) eqn:Hwv.
      + simpl. rewrite Hwv. rewrite !count_occ_app. simpl.
        destruct (clause_pointer_eq_dec x y); simpl; lia.
      + simpl. now rewrite Hwv.
  Qed.

  Lemma count_occ_flat_map_add_absent : forall ks m l x y,
    ~ In (literal_var l) ks ->
    count_occ clause_pointer_eq_dec
      (flat_map (fun v => find v (add l x m)) ks) y =
    count_occ clause_pointer_eq_dec (flat_map (fun v => find v m) ks) y.
  Proof.
    intros ks. induction ks as [|v ks IH]; intros m l x y Hnotin; simpl.
    - reflexivity.
    - rewrite !count_occ_app, count_occ_find_add.
      destruct (VarKey.eq_dec (literal_var l) v) as [Heq|Hneq].
      + exfalso. apply Hnotin. now left.
      + rewrite IH; [reflexivity|]. intros Hin. apply Hnotin. now right.
  Qed.

  Lemma count_occ_flat_map_add_present : forall ks m l x y,
    NoDup ks -> In (literal_var l) ks ->
    count_occ clause_pointer_eq_dec
      (flat_map (fun v => find v (add l x m)) ks) y =
    count_occ clause_pointer_eq_dec [x] y +
      count_occ clause_pointer_eq_dec (flat_map (fun v => find v m) ks) y.
  Proof.
    intros ks. induction ks as [|v ks IH]; intros m l x y Hnodup Hin;
      [contradiction|].
    inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    cbn [flat_map]. rewrite !count_occ_app, count_occ_find_add.
    destruct (VarKey.eq_dec (literal_var l) v) as [Heq|Hneq].
    - subst v. rewrite count_occ_flat_map_add_absent by exact Hnotin. lia.
    - rewrite IH; [lia|exact Hnodup'|].
      destruct Hin as [Heq|Hin]; [congruence|exact Hin].
  Qed.

  Lemma card_of_add : forall m x l,
    card_of x (add l x m) = S (card_of x m).
  Proof.
    intros m x l. unfold card_of, elements.
    pose proof (Buckets.keys_add_permutation m (singleton_watch l x)
      (literal_var l)) as Hkeys.
    assert (Permutation
      (flat_map (fun v => find v (add l x m)) (Buckets.keys (add l x m)))
      (flat_map (fun v => find v (add l x m))
        (if in_dec VarKey.eq_dec (literal_var l) (Buckets.keys m)
         then Buckets.keys m else literal_var l :: Buckets.keys m)))
      as Helements.
    { now apply Permutation_flat_map. }
    assert (Hcount := Helements).
    rewrite (Permutation_count_occ clause_pointer_eq_dec) in Hcount.
    rewrite (Hcount x).
    destruct (in_dec VarKey.eq_dec (literal_var l) (Buckets.keys m))
      as [Hin|Hnotin] eqn:Hmem.
    - rewrite count_occ_flat_map_add_present;
        [|apply Buckets.keys_nodup|exact Hin].
      simpl. destruct (clause_pointer_eq_dec x x); [lia|contradiction].
    - cbn [flat_map]. rewrite count_occ_app, count_occ_find_add.
      destruct (VarKey.eq_dec (literal_var l) (literal_var l));
        [|contradiction].
      rewrite count_occ_flat_map_add_absent by exact Hnotin.
      assert (Hempty : find (literal_var l) m = []).
      { unfold find, find_pos, find_neg, Buckets.find.
        rewrite (Buckets.lookup_notin_keys m (literal_var l) Hnotin).
        reflexivity. }
      rewrite Hempty. simpl. destruct (clause_pointer_eq_dec x x);
        [lia|contradiction].
  Qed.
  Lemma card_of_add_neq : forall m x y l,
    x <> y -> card_of y (add l x m) = card_of y m.
  Proof.
    intros m x y l Hneq. unfold card_of, elements.
    pose proof (Buckets.keys_add_permutation m (singleton_watch l x)
      (literal_var l)) as Hkeys.
    assert (Permutation
      (flat_map (fun v => find v (add l x m)) (Buckets.keys (add l x m)))
      (flat_map (fun v => find v (add l x m))
        (if in_dec VarKey.eq_dec (literal_var l) (Buckets.keys m)
         then Buckets.keys m else literal_var l :: Buckets.keys m)))
      as Helements.
    { now apply Permutation_flat_map. }
    assert (Hcount := Helements).
    rewrite (Permutation_count_occ clause_pointer_eq_dec) in Hcount.
    rewrite (Hcount y).
    destruct (in_dec VarKey.eq_dec (literal_var l) (Buckets.keys m))
      as [Hin|Hnotin] eqn:Hmem.
    - rewrite count_occ_flat_map_add_present;
        [|apply Buckets.keys_nodup|exact Hin].
      simpl. destruct (clause_pointer_eq_dec x y); [contradiction|lia].
    - cbn [flat_map]. rewrite count_occ_app, count_occ_find_add.
      destruct (VarKey.eq_dec (literal_var l) (literal_var l));
        [|contradiction].
      rewrite count_occ_flat_map_add_absent by exact Hnotin.
      assert (Hempty : find (literal_var l) m = []).
      { unfold find, find_pos, find_neg, Buckets.find.
        rewrite (Buckets.lookup_notin_keys m (literal_var l) Hnotin).
        reflexivity. }
      rewrite Hempty. simpl. destruct (clause_pointer_eq_dec x y);
        [contradiction|lia].
  Qed.

  Lemma filter_remove_absent : forall ks v,
    ~ In v ks ->
    filter (fun v' => if VarKey.eq_dec v v' then false else true) ks = ks.
  Proof.
    intros ks. induction ks as [|v' ks IH]; intros v Hnotin; simpl.
    - reflexivity.
    - destruct (VarKey.eq_dec v v') as [->|Hneq].
      + exfalso. apply Hnotin. now left.
      + simpl. f_equal. apply IH. intros Hin. apply Hnotin. now right.
  Qed.

  Lemma flat_map_remove_absent : forall ks m v,
    ~ In v ks ->
    flat_map (fun v' => if VarKey.eq_dec v v' then [] else find v' m) ks =
      flat_map (fun v' => find v' m) ks.
  Proof.
    intros ks. induction ks as [|v' ks IH]; intros m v Hnotin; simpl.
    - reflexivity.
    - destruct (VarKey.eq_dec v v') as [->|Hneq].
      + exfalso. apply Hnotin. now left.
      + f_equal. apply IH. intros Hin. apply Hnotin. now right.
  Qed.

  Lemma card_of_remove : forall m x v,
    card_of x (remove v m) + count_occ clause_pointer_eq_dec (find v m) x =
    card_of x m.
  Proof.
    intros m x v. unfold card_of, elements.
    pose proof (Buckets.keys_remove_permutation m v) as Hkeys.
    assert (Permutation
      (flat_map (fun v' => find v' (remove v m)) (Buckets.keys (remove v m)))
      (flat_map (fun v' => find v' (remove v m))
        (filter (fun v' => if VarKey.eq_dec v v' then false else true)
          (Buckets.keys m)))) as Helements.
    { now apply Permutation_flat_map. }
    assert (Hcount := Helements).
    rewrite (Permutation_count_occ clause_pointer_eq_dec) in Hcount.
    rewrite (Hcount x).
    assert (Hflat : forall ks,
      flat_map (fun v' => find v' (remove v m)) ks =
      flat_map (fun v' => if VarKey.eq_dec v v' then [] else find v' m) ks).
    { intros ks. induction ks as [|v' ks IH]; [reflexivity|]. simpl.
      rewrite IH. unfold find. rewrite find_pos_remove, find_neg_remove.
      destruct (VarKey.eq_dec v v'); reflexivity. }
    rewrite Hflat.
    destruct (in_dec VarKey.eq_dec v (Buckets.keys m)) as [Hin|Hnotin].
    - apply in_split in Hin as [before [after Hsupport]].
      assert (NoDup (Buckets.keys m)) as Hnodup by
        apply Buckets.keys_of_nodup.
      rewrite Hsupport in Hnodup |- *.
      rewrite filter_app. simpl.
      destruct (VarKey.eq_dec v v) as [_|Habs]; [|contradiction]. simpl.
      pose proof (NoDup_remove_2 _ _ _ Hnodup) as Hnotin_rest.
      assert (~ In v before) as Hnotin_before.
      { intros H. apply Hnotin_rest. apply in_or_app. now left. }
      assert (~ In v after) as Hnotin_after.
      { intros H. apply Hnotin_rest. apply in_or_app. now right. }
      rewrite (filter_remove_absent before v Hnotin_before).
      rewrite (filter_remove_absent after v Hnotin_after).
      rewrite !flat_map_app.
      erewrite flat_map_remove_absent by exact Hnotin_before.
      erewrite flat_map_remove_absent by exact Hnotin_after.
      cbn [flat_map]. rewrite !count_occ_app.
      set (nb := count_occ clause_pointer_eq_dec
        (flat_map (fun v => find v m) before) x).
      set (nv := count_occ clause_pointer_eq_dec (find v m) x).
      set (na := count_occ clause_pointer_eq_dec
        (flat_map (fun v => find v m) after) x).
      change (nb + na + nv = nb + (nv + na)). lia.
    - rewrite (filter_remove_absent (Buckets.keys m) v Hnotin).
      erewrite flat_map_remove_absent by exact Hnotin.
      assert (Hempty : find v m = []).
      { unfold find, find_pos, find_neg, Buckets.find.
        rewrite (Buckets.lookup_notin_keys m v Hnotin). reflexivity. }
      rewrite Hempty. simpl. lia.
  Qed.

  Lemma card_of_clear_literal : forall m x l,
    card_of x (clear_literal l m) +
      count_occ clause_pointer_eq_dec (find_literal l m) x = card_of x m.
  Proof.
    intros m x [v|v]; unfold card_of, elements.
    - pose proof (Buckets.keys_map_at_permutation m v clear_pos eq_refl)
        as Hkeys_clear.
      assert (Permutation
        (flat_map (fun w => find w (clear_literal (Pos v) m))
          (Buckets.keys (clear_literal (Pos v) m)))
        (flat_map (fun w => find w (clear_literal (Pos v) m))
          (Buckets.keys m))) as Helements.
      { now apply Permutation_flat_map. }
      assert (Hcount := Helements).
      rewrite (Permutation_count_occ clause_pointer_eq_dec) in Hcount.
      rewrite (Hcount x).
      change
        (count_occ clause_pointer_eq_dec
           (flat_map (fun w => find w (clear_literal (Pos v) m))
             (Buckets.keys m)) x +
         count_occ clause_pointer_eq_dec (find_pos v m) x =
         count_occ clause_pointer_eq_dec
           (flat_map (fun w => find w m) (Buckets.keys m)) x).
      destruct (in_dec VarKey.eq_dec v (Buckets.keys m)) as [Hin|Hnotin].
      + apply in_split in Hin as [before [after Hkeys]].
        assert (NoDup (Buckets.keys m)) as Hnodup by
          apply Buckets.keys_of_nodup.
        rewrite Hkeys in Hnodup |- *.
        pose proof (NoDup_remove_2 _ _ _ Hnodup) as Hnotinrest.
        assert (~ In v before) as Hbefore.
        { intros H. apply Hnotinrest. apply in_or_app. now left. }
        assert (~ In v after) as Hafter.
        { intros H. apply Hnotinrest. apply in_or_app. now right. }
        rewrite !flat_map_app. cbn [flat_map].
        erewrite flat_map_clear_other by exact Hbefore.
        erewrite flat_map_clear_other by exact Hafter.
        rewrite find_clear_pos_eq. unfold find. rewrite !count_occ_app.
        set (a := count_occ clause_pointer_eq_dec
          (flat_map (fun w => find_pos w m ++ find_neg w m) before) x).
        set (b := count_occ clause_pointer_eq_dec
          (flat_map (fun w => find_pos w m ++ find_neg w m) after) x).
        set (p := count_occ clause_pointer_eq_dec (find_pos v m) x).
        set (n := count_occ clause_pointer_eq_dec (find_neg v m) x).
        change (a + (n + b) + p = a + (p + n + b)). lia.
      + rewrite flat_map_clear_other by exact Hnotin.
        assert (Hempty : find_pos v m = []).
        { unfold find_pos, Buckets.find.
          rewrite (Buckets.lookup_notin_keys m v Hnotin). reflexivity. }
        now rewrite Hempty.
    - pose proof (Buckets.keys_map_at_permutation m v clear_neg eq_refl)
        as Hkeys_clear.
      assert (Permutation
        (flat_map (fun w => find w (clear_literal (Neg v) m))
          (Buckets.keys (clear_literal (Neg v) m)))
        (flat_map (fun w => find w (clear_literal (Neg v) m))
          (Buckets.keys m))) as Helements.
      { now apply Permutation_flat_map. }
      assert (Hcount := Helements).
      rewrite (Permutation_count_occ clause_pointer_eq_dec) in Hcount.
      rewrite (Hcount x).
      change
        (count_occ clause_pointer_eq_dec
           (flat_map (fun w => find w (clear_literal (Neg v) m))
             (Buckets.keys m)) x +
         count_occ clause_pointer_eq_dec (find_neg v m) x =
         count_occ clause_pointer_eq_dec
           (flat_map (fun w => find w m) (Buckets.keys m)) x).
      destruct (in_dec VarKey.eq_dec v (Buckets.keys m)) as [Hin|Hnotin].
      + apply in_split in Hin as [before [after Hkeys]].
        assert (NoDup (Buckets.keys m)) as Hnodup by
          apply Buckets.keys_of_nodup.
        rewrite Hkeys in Hnodup |- *.
        pose proof (NoDup_remove_2 _ _ _ Hnodup) as Hnotinrest.
        assert (~ In v before) as Hbefore.
        { intros H. apply Hnotinrest. apply in_or_app. now left. }
        assert (~ In v after) as Hafter.
        { intros H. apply Hnotinrest. apply in_or_app. now right. }
        rewrite !flat_map_app. cbn [flat_map].
        erewrite flat_map_clear_other by exact Hbefore.
        erewrite flat_map_clear_other by exact Hafter.
        rewrite find_clear_neg_eq. unfold find. rewrite !count_occ_app.
        set (a := count_occ clause_pointer_eq_dec
          (flat_map (fun w => find_pos w m ++ find_neg w m) before) x).
        set (b := count_occ clause_pointer_eq_dec
          (flat_map (fun w => find_pos w m ++ find_neg w m) after) x).
        set (p := count_occ clause_pointer_eq_dec (find_pos v m) x).
        set (n := count_occ clause_pointer_eq_dec (find_neg v m) x).
        change (a + (p + b) + n = a + (p + n + b)). lia.
      + rewrite flat_map_clear_other by exact Hnotin.
        assert (Hempty : find_neg v m = []).
        { unfold find_neg, Buckets.find.
          rewrite (Buckets.lookup_notin_keys m v Hnotin). reflexivity. }
        now rewrite Hempty.
  Qed.
  Lemma card_of_unique : forall m x v v',
    card_of x m = 1 -> In x (find v m) -> In x (find v' m) -> v = v'.
  Proof.
    intros m x v v' Hcard Hv Hv'. destruct (VarKey.eq_dec v v') as [->|Hneq];
      [reflexivity|exfalso].
    assert (In v (Buckets.keys m)) as Hvs.
    { apply Buckets.keys_complete. intros Hempty. unfold find, find_pos, find_neg in Hv.
      rewrite Hempty in Hv. contradiction. }
    assert (In v' (Buckets.keys m)) as Hvs'.
    { apply Buckets.keys_complete. intros Hempty. unfold find, find_pos, find_neg in Hv'.
      rewrite Hempty in Hv'. contradiction. }
    apply in_split in Hvs as [before [after Hsupport]].
    assert (In v' (before ++ after)) as Hv'rest.
    { rewrite Hsupport in Hvs'. apply in_app_or in Hvs' as [Hin|Hin].
      - now apply in_or_app; left.
      - simpl in Hin. destruct Hin as [Heq|Hin]; [congruence|].
        now apply in_or_app; right. }
    assert (In x (flat_map (fun v => find v m) (before ++ after))) as Hrest.
    { apply in_flat_map. exists v'. split; assumption. }
    apply (proj1 (count_occ_In clause_pointer_eq_dec _ _)) in Hv.
    apply (proj1 (count_occ_In clause_pointer_eq_dec _ _)) in Hrest.
    unfold card_of, elements in Hcard. rewrite Hsupport, flat_map_app in Hcard.
    cbn [flat_map] in Hcard. rewrite !count_occ_app in Hcard.
    rewrite flat_map_app, count_occ_app in Hrest. lia.
  Qed.
  Lemma card_of_in : forall m x v, In x (find v m) -> card_of x m > 0.
  Proof.
    intros m x v Hin. unfold card_of. apply count_occ_In.
    apply in_flat_map. exists v. split; [|exact Hin].
    apply Buckets.keys_complete. intros Hempty.
    unfold find, find_pos, find_neg in Hin. rewrite Hempty in Hin. contradiction.
  Qed.
  Lemma card_of_pos : forall m x,
    card_of x m > 0 -> exists v, In x (find v m).
  Proof.
    intros m x Hpos. apply (proj2 (count_occ_In clause_pointer_eq_dec _ _))
      in Hpos. unfold elements in Hpos. apply in_flat_map in Hpos as [v [_ Hin]].
    now exists v.
  Qed.
  Lemma find_remove_eq : forall m v removed,
    find v (remove removed m) =
      if VarKey.eq_dec removed v then [] else find v m.
  Proof.
    intros. unfold find. rewrite find_pos_remove, find_neg_remove.
    destruct (VarKey.eq_dec removed v); reflexivity.
  Qed.
  Lemma find_remove : forall m v x removed,
    In x (find v (remove removed m)) <->
    In x (find v m) /\ v <> removed.
  Proof.
    intros. rewrite find_remove_eq. destruct (VarKey.eq_dec removed v) as [->|Hneq];
      simpl; firstorder congruence.
  Qed.
  Lemma elements_spec : forall m x,
    In x (elements m) <-> exists v, In v (keys m) /\ In x (find v m).
  Proof.
    intros m x. unfold elements. rewrite in_flat_map. split.
    - intros [v [Hsupport Hin]]. exists v. split; [|exact Hin].
      apply keys_complete. intros Hempty. rewrite Hempty in Hin. contradiction.
    - intros [v [Hkey Hin]]. exists v. split; [|exact Hin].
      apply Buckets.keys_complete. intros Hempty.
      unfold find, find_pos, find_neg in Hin. rewrite Hempty in Hin.
      contradiction.
  Qed.
End ClauseMap.

Module ClauseValue.
  Definition t := Clause.
End ClauseValue.

Module ClauseStore := Map.Make ClauseIdKey ClauseValue.

Record State := {
  state_trail : Trail;
  state_assignment : Assignment.t;
  state_clauses : ClauseStore.t;
  state_learned : ClauseStore.t;
  (* `state_watched` implements two-literal watch. *)
  state_watched : ClauseMap.t;
  state_pending : Pending;
}.

Definition empty_state : State :=
  {| state_trail := [];
     state_assignment := Assignment.empty;
     state_clauses := ClauseStore.empty;
     state_learned := ClauseStore.empty;
     state_watched := ClauseMap.empty;
     state_pending := [] |}.

Definition find_clause_in (clauses learned : ClauseStore.t)
    (ci : ClausePointer) : option Clause :=
  match ci with
  | Source c => ClauseStore.find c clauses
  | Learned c => ClauseStore.find c learned
  end.

Definition find_clause (ci : ClausePointer) (s : State) : option Clause :=
  find_clause_in s.(state_clauses) s.(state_learned) ci.

Definition literal_value (assignment : Assignment.t) (l : Literal)
    : option bool :=
  match Assignment.find (literal_var l) assignment with
  | None => None
  | Some value =>
      match l with Pos _ => Some value | Neg _ => Some (negb value) end
  end.

Definition var_is_assigned (assignment : Assignment.t) (v : Var) : bool :=
  match Assignment.find v assignment with Some _ => true | None => false end.

Definition assignment_set_literal (l : Literal) (assignment : Assignment.t)
    : Assignment.t :=
  match l with
  | Pos v => Assignment.add v true assignment
  | Neg v => Assignment.add v false assignment
  end.

Fixpoint assignment_remove_entries (count : nat) (trail : Trail)
    (assignment : Assignment.t) : Assignment.t :=
  match count, trail with
  | S count', entry :: trail' =>
      assignment_remove_entries count' trail'
        (Assignment.remove (literal_var (trail_literal entry)) assignment)
  | _, _ => assignment
  end.

Definition assignment_after_backtrack (old retained : Trail)
    (assignment : Assignment.t) : Assignment.t :=
  assignment_remove_entries (length old - length retained) old assignment.

Definition literal_is_true (assignment : Assignment.t) (l : Literal) : bool :=
  match literal_value assignment l with
  | Some true => true
  | _ => false
  end.

Definition literal_is_undecided (assignment : Assignment.t) (l : Literal)
    : bool :=
  match literal_value assignment l with
  | None => true
  | _ => false
  end.

Definition literal_is_decided (assignment : Assignment.t) (l : Literal) : Prop :=
  literal_is_undecided assignment l = false.

Fixpoint scan_clause_once (assignment : Assignment.t) (c : Clause)
    : bool * list Literal :=
  match c with
  | [] => (false, [])
  | l :: c' =>
      let '(satisfied, undecided) := scan_clause_once assignment c' in
      (orb (literal_is_true assignment l) satisfied,
       if literal_is_undecided assignment l
       then l :: undecided else undecided)
  end.

Variant scan_result :=
  | propagate_literal (l : Literal) (cm : ClauseMap.t)
  | clause_conflict (cm : ClauseMap.t)
  | clause_decided (cm : ClauseMap.t)
  | clause_watched (cm : ClauseMap.t).

Variant progress_result :=
  | Progress (s : State)
  | Conflict (s : State) (cause : Clause).

Fixpoint find_different_var (v : Var) (ls : list Literal) : option Literal :=
  match ls with
  | [] => None
  | l :: ls' =>
      if Id.eqb v (literal_var l) then find_different_var v ls' else Some l
  end.

Definition restore_detached_watch (falsified_watch : Literal)
    (ci : ClausePointer) (c : Clause) (cm : ClauseMap.t) : ClauseMap.t :=
  match find_different_var (literal_var falsified_watch) c with
  | Some _ => ClauseMap.add falsified_watch ci cm
  | None => cm
  end.

(* Scan a clause after [falsified_watch] has been detached.  If the clause is
   already decided, put that watch back so a non-unit clause retains two
   watches.  A physical unit clause deliberately loses its sole watch after
   its root-level propagation. *)
Definition scan_clause (assignment : Assignment.t) (falsified_watch : Literal)
    (ci : ClausePointer) (c : Clause)
    (cm : ClauseMap.t) : scan_result :=
  let '(satisfied, undecided) := scan_clause_once assignment c in
  if satisfied then
      clause_decided (restore_detached_watch falsified_watch ci c cm)
  else
    match undecided with
    | [] =>
        clause_conflict (restore_detached_watch falsified_watch ci c cm)
    | l :: undecided' =>
        match find_different_var (literal_var l) undecided' with
        | None =>
            if in_dec clause_pointer_eq_dec ci
                (ClauseMap.find (literal_var l) cm) then
              propagate_literal l
                (restore_detached_watch falsified_watch ci c cm)
            else
              propagate_literal l
                (ClauseMap.add l ci cm)
        | Some l' =>
            if in_dec clause_pointer_eq_dec ci
                (ClauseMap.find (literal_var l) cm) then
              clause_watched (ClauseMap.add l' ci cm)
            else clause_watched (ClauseMap.add l ci cm)
        end
    end.

Definition propagate (falsified_watch : Literal) (ci : ClausePointer)
    (s : State) : progress_result :=
  match find_clause ci s with
  | None => Progress s
  | Some c =>
    match scan_clause s.(state_assignment) falsified_watch ci c
        s.(state_watched) with
    | propagate_literal l cm =>
      Progress
        {| state_trail := s.(state_trail);
           state_assignment := s.(state_assignment);
           state_clauses := s.(state_clauses);
           state_learned := s.(state_learned);
           state_watched := cm;
           state_pending := (l, ci) :: s.(state_pending) |}
    | clause_conflict cm =>
      Conflict
        {| state_trail := s.(state_trail);
           state_assignment := s.(state_assignment);
           state_clauses := s.(state_clauses);
           state_learned := s.(state_learned);
           state_watched := cm;
           state_pending := s.(state_pending) |}
        c
    | clause_decided cm =>
      Progress
        {| state_trail := s.(state_trail);
           state_assignment := s.(state_assignment);
           state_clauses := s.(state_clauses);
           state_learned := s.(state_learned);
           state_watched := cm;
           state_pending := s.(state_pending) |}
    | clause_watched cm =>
      Progress
        {| state_trail := s.(state_trail);
           state_assignment := s.(state_assignment);
           state_clauses := s.(state_clauses);
           state_learned := s.(state_learned);
           state_watched := cm;
           state_pending := s.(state_pending) |}
    end
  end.

Fixpoint propagate_clauses (falsified_watch : Literal)
    (watched : list ClausePointer) (s : State) : progress_result :=
  match watched with
  | [] => Progress s
  | ci :: watched' =>
      match propagate falsified_watch ci s with
      | Progress s' => propagate_clauses falsified_watch watched' s'
      | Conflict s' cause =>
          (* TODO: we should be able to return immediately from here, saving a
             little bit of time. This will may require proving that the
             falsified clause still verify the two-watch invariant. *)
          match propagate_clauses falsified_watch watched' s' with
          | Progress final => Conflict final cause
          | Conflict final _ => Conflict final cause
          end
      end
  end.

Definition set_trail_entry (entry : TrailEntry) (s : State) : progress_result :=
  let l := trail_literal entry in
  let watched := ClauseMap.find_falsified l s.(state_watched) in
  let falsified_watch := opposite_literal l in
  let cm := ClauseMap.clear_falsified l s.(state_watched) in
  let s' := {| state_trail := entry :: s.(state_trail);
      state_assignment := assignment_set_literal l s.(state_assignment);
      state_clauses := s.(state_clauses); state_watched := cm;
      state_learned := s.(state_learned);
      state_pending := s.(state_pending) |} in
  propagate_clauses falsified_watch watched s'.

Definition set_lit (l : Literal) (s : State) : progress_result :=
  set_trail_entry (Decision l) s.

Definition set_propagated_lit (l : Literal) (cause : ClausePointer) (s : State)
    : progress_result :=
  set_trail_entry (Propagation l cause) s.

Fixpoint find_undecided_var (assignment : Assignment.t) (vs : list Var)
    : option Var :=
  match vs with
  | [] => None
  | v :: vs' =>
      if var_is_assigned assignment v
      then find_undecided_var assignment vs' else Some v
  end.

Definition clause_store_vars (store : ClauseStore.t) : list Var :=
  flat_map
    (fun ci =>
       match ClauseStore.find ci store with
       | Some c => map literal_var c
       | None => []
       end)
    (ClauseStore.keys store).

Definition problem_vars (s : State) : list Var :=
  clause_store_vars s.(state_clauses).

(* Game plan: to progress the state:
   - If there is a pending propagation, assign its literal using its clause as
     the cause.
   - Otherwise
     1. choose an undecided variable
     2. Set it to `true` in the model
     3. Wake up and process every clause currently watching this literal. *)
Definition progress_state (s : State) : progress_result :=
  match s.(state_pending) with
  | (l, c) :: pending =>
      let base :=
        {| state_trail := s.(state_trail);
           state_assignment := s.(state_assignment);
           state_clauses := s.(state_clauses);
           state_learned := s.(state_learned);
           state_watched := s.(state_watched);
           state_pending := pending |} in
      match literal_value s.(state_assignment) l with
      | Some _ => Progress base
      | None => set_propagated_lit l c base
      end
  | [] =>
      match find_undecided_var s.(state_assignment)
          (problem_vars s) with
      | None => Progress s (* All the literal have been decided so no progress can be made *)
      | Some v =>
          set_lit (Pos v) s
      end
  end.

Fixpoint negated_decisions (trail : Trail) : Clause :=
  match trail with
  | [] => []
  | Decision l :: trail' => opposite_literal l :: negated_decisions trail'
  | Propagation _ _ :: trail' => negated_decisions trail'
  end.

Definition without_literal (removed : Literal) (c : Clause) : Clause :=
  filter (fun l => if literal_eq_dec l removed then false else true) c.

Fixpoint clause_union (left right : Clause) : Clause :=
  match left with
  | [] => right
  | l :: left' =>
      if in_dec literal_eq_dec l right then clause_union left' right
      else l :: clause_union left' right
  end.

(* Resolve two clauses on [pivot].  Clauses are represented as lists, so
   [union] also prevents conflict analysis from accumulating duplicates. *)
Definition resolve_clause (pivot : Literal) (left right : Clause) : Clause :=
  clause_union
    (without_literal (opposite_literal pivot) left)
    (without_literal pivot right).

(* Builds a 1-UIP clause (probably). Implemented with explicit clause
   resolution, rather than the usual clever encoding (because I don't even want
   to get into the proof of that). *)
Fixpoint analyze_conflict_trail (clauses learned : ClauseStore.t)
    (trail : Trail) (conflict : Clause) : Clause :=
  match trail with
  | [] => conflict
  | Decision _ :: trail' =>
      analyze_conflict_trail clauses learned trail' conflict
  | Propagation l cause :: trail' =>
      let conflict' :=
        if in_dec literal_eq_dec (opposite_literal l) conflict then
          match find_clause_in clauses learned cause with
          | Some reason => resolve_clause l conflict reason
          | None => conflict
          end
        else conflict in
      analyze_conflict_trail clauses learned trail' conflict'
  end.

Definition analyze_conflict (s : State) (conflict : Clause) : option Clause :=
  match negated_decisions s.(state_trail) with
  | [] => None
  | decisions =>
      match analyze_conflict_trail s.(state_clauses) s.(state_learned)
          s.(state_trail) conflict with
      | [] => Some decisions
      | analyzed => Some analyzed
      end
  end.

Fixpoint pop_to_decision_after (learned : Clause) (after_propagation : bool)
    (trail : Trail) : Trail :=
  match trail with
  | [] => []
  | Decision l :: trail' =>
      if after_propagation then trail'
      else if in_dec literal_eq_dec (opposite_literal l) learned then trail'
      else pop_to_decision_after learned false trail'
  | Propagation l _ :: trail' =>
      pop_to_decision_after learned
        (if in_dec literal_eq_dec (opposite_literal l) learned
         then true else after_propagation)
        trail'
  end.

(* Backtrack to the first relevant decision, or to the decision immediately
   below the first relevant propagation. *)
Definition pop_to_decision (learned : Clause) (trail : Trail) : Trail :=
  pop_to_decision_after learned false trail.

Fixpoint trail_has_decision (trail : Trail) : bool :=
  match trail with
  | [] => false
  | Decision _ :: _ => true
  | Propagation _ _ :: trail' => trail_has_decision trail'
  end.

Fixpoint pop_to_root (trail : Trail) : Trail :=
  match trail with
  | [] => []
  | entry :: trail' =>
      if trail_has_decision trail then pop_to_root trail' else trail
  end.

Definition clause_has_two_variablesb (c : Clause) : bool :=
  match c with
  | [] => false
  | l :: c' =>
      match find_different_var (literal_var l) c' with
      | Some _ => true
      | None => false
      end
  end.

Definition backtrack_trail (learned : Clause) (trail : Trail) : Trail :=
  if clause_has_two_variablesb learned then
    match pop_to_decision learned trail with
    | [] => pop_to_root trail
    | popped => popped
    end
  else pop_to_root trail.

Definition fresh_clause_id (s : State) : ClauseId :=
  match ClauseStore.maximum s.(state_clauses) with
  | None => Id.of_nat 0
  | Some greatest => Id.next greatest
  end.

Definition fresh_learned_clause_id (s : State) : ClauseId :=
  match ClauseStore.maximum s.(state_learned) with
  | None => Id.of_nat 0
  | Some greatest => Id.next greatest
  end.

Variant clause_destination := OriginalClause | LearnedClause.

(* Find the most recently assigned literal of [c], optionally ignoring one
   variable.  Models are newest-first, so the first matching trail literal is
   precisely the literal whose variable was assigned most recently.  We return
   the literal as it occurs in the clause, since its polarity can differ from
   the trail entry's polarity. *)
Fixpoint find_literal_with_var (v : Var) (c : Clause) : option Literal :=
  match c with
  | [] => None
  | l :: c' =>
      if Id.eq_dec v (literal_var l) then Some l
      else find_literal_with_var v c'
  end.

Fixpoint find_recent_clause_literal_except (excluded : option Var)
    (m : Model) (c : Clause) : option Literal :=
  match m with
  | [] => None
  | assigned :: m' =>
      if match excluded with
         | Some v => if Id.eq_dec v (literal_var assigned) then true else false
         | None => false
         end
      then find_recent_clause_literal_except excluded m' c
      else
        match find_literal_with_var (literal_var assigned) c with
        | Some l => Some l
        | None => find_recent_clause_literal_except excluded m' c
        end
  end.

Definition find_recent_clause_literal (m : Model) (c : Clause) : option Literal :=
  find_recent_clause_literal_except None m c.

Definition find_recent_different_clause_literal (v : Var)
    (m : Model) (c : Clause) : option Literal :=
  find_recent_clause_literal_except (Some v) m c.

Definition install_watches (m : Model) (assignment : Assignment.t)
    (ci : ClausePointer)
    (c : Clause) (cm : ClauseMap.t) : ClauseMap.t :=
  let undecided := snd (scan_clause_once assignment c) in
  match undecided with
  | l :: undecided' =>
      match find_different_var (literal_var l) undecided' with
      | Some l' => ClauseMap.add l' ci (ClauseMap.add l ci cm)
      | None =>
          match find_recent_different_clause_literal (literal_var l) m c with
          | Some l' => ClauseMap.add l' ci (ClauseMap.add l ci cm)
          | None => cm
          end
      end
  | [] =>
      match find_recent_clause_literal m c with
      | None => cm
      | Some l =>
          match find_recent_different_clause_literal (literal_var l) m c with
          | Some l' => ClauseMap.add l' ci (ClauseMap.add l ci cm)
          | None => cm
          end
      end
  end.

Definition index_clause (pointer : ClausePointer) (s : State) (c : Clause)
    : progress_result :=
  let '(satisfied, undecided) := scan_clause_once s.(state_assignment) c in
  if clause_has_opposite_literals c then Progress s
  else
    let cm := install_watches s.(state_trail) s.(state_assignment) pointer c
      s.(state_watched) in
    if satisfied then
      Progress
        {| state_trail := s.(state_trail);
           state_assignment := s.(state_assignment);
           state_clauses := s.(state_clauses);
           state_learned := s.(state_learned);
           state_watched := cm;
           state_pending := s.(state_pending) |}
    else
      match undecided with
      | [] =>
          Conflict
            {| state_trail := s.(state_trail);
               state_assignment := s.(state_assignment);
               state_clauses := s.(state_clauses);
               state_learned := s.(state_learned);
               state_watched := cm;
               state_pending := s.(state_pending) |}
            c
      | l :: undecided' =>
          match find_different_var (literal_var l) undecided' with
          | None =>
              Progress
                {| state_trail := s.(state_trail);
                   state_assignment := s.(state_assignment);
                   state_clauses := s.(state_clauses);
                   state_learned := s.(state_learned);
                   state_watched := cm;
                   state_pending := (l, pointer) :: s.(state_pending) |}
          | Some _ =>
              Progress
                {| state_trail := s.(state_trail);
                   state_assignment := s.(state_assignment);
                   state_clauses := s.(state_clauses);
                   state_learned := s.(state_learned);
                   state_watched := cm;
                   state_pending := s.(state_pending) |}
          end
      end.

Definition add_clause_to (destination : clause_destination)
    (s : State) (c : Clause) : progress_result :=
  let ci :=
    match destination with
    | OriginalClause => fresh_clause_id s
    | LearnedClause => fresh_learned_clause_id s
    end in
  let pointer :=
    match destination with
    | OriginalClause => Source ci
    | LearnedClause => Learned ci
    end in
  let base :=
    {| state_trail := s.(state_trail);
       state_assignment := s.(state_assignment);
       state_clauses :=
         match destination with
         | OriginalClause => ClauseStore.add ci c s.(state_clauses)
         | LearnedClause => s.(state_clauses)
         end;
       state_learned :=
         match destination with
         | OriginalClause => s.(state_learned)
         | LearnedClause => ClauseStore.add ci c s.(state_learned)
         end;
       state_watched := s.(state_watched);
       state_pending := s.(state_pending) |} in
  index_clause pointer base c.

Definition add_clause : State -> Clause -> progress_result :=
  add_clause_to OriginalClause.

Definition add_learned : State -> Clause -> progress_result :=
  add_clause_to LearnedClause.

Definition clause_pointers (s : State) : list ClausePointer :=
  map Source (ClauseStore.keys s.(state_clauses)) ++
  map Learned (ClauseStore.keys s.(state_learned)).

(* Rebuild only the unit-propagation queue after backtracking.  Removing trail
   entries cannot falsify a clause, so there is no conflict queue to rebuild. *)
Fixpoint reclassify_clauses (assignment : Assignment.t) (s : State)
    (clauses : list ClausePointer) : Pending :=
  match clauses with
  | [] => []
  | ci :: clauses' =>
      let pending := reclassify_clauses assignment s clauses' in
      match find_clause ci s with
      | None => pending
      | Some c =>
          if clause_has_opposite_literals c then pending
          else
          let '(satisfied, undecided) := scan_clause_once assignment c in
          if satisfied then pending
          else
            match undecided with
            | [] => pending
            | l :: undecided' =>
                match find_different_var (literal_var l) undecided' with
                | None => (l, ci) :: pending
                | Some _ => pending
                end
            end
      end
  end.

Definition pending_clause_pointers (pending : Pending) : list ClausePointer :=
  map snd pending.

Definition reclassify_state (assignment : Assignment.t) (s : State) : Pending :=
  reclassify_clauses assignment s
    (pending_clause_pointers s.(state_pending)).

Definition backtrack (conflict : State * Clause) : option progress_result :=
  let conflict := count_conflict conflict in
  let '(s, cause) := conflict in
  match analyze_conflict s cause with
  | None => None
  | Some learned =>
      let trail := backtrack_trail learned s.(state_trail) in
      let assignment := assignment_after_backtrack s.(state_trail) trail
        s.(state_assignment) in
      let pending := reclassify_state assignment s in
      let backtracked :=
        {| state_trail := trail;
           state_assignment := assignment;
           state_clauses := s.(state_clauses);
           state_learned := s.(state_learned);
           state_watched := s.(state_watched);
           state_pending := pending |} in
      match trail_has_decision trail,
          scan_clause_once assignment learned with
      | false, (false, []) => None
      | _, _ => Some (add_learned backtracked learned)
      end
  end.

Definition progress (s : State) : progress_result :=
  match s.(state_pending) with
  | (l, c) :: _ =>
      match literal_value s.(state_assignment) l with
      | Some false =>
          match find_clause c s with
          | Some clause => Conflict s clause
          | None => Conflict s []
          end
      | _ => progress_state s
      end
  | [] => progress_state s
  end.

Definition is_empty {A} (l : list A) : bool :=
  match l with
  | [] => true
  | _ => false
  end.

Definition rush_has_work (s : State) : bool :=
  match s.(state_pending) with
  | _ :: _ => true
  | [] =>
      match find_undecided_var s.(state_assignment)
          (problem_vars s) with
      | Some _ => true
      | None => false
      end
  end.

(* Define arbitrary tail-recursive functions as co-fixpoint returning a [Delay
   A]. *)
CoInductive Delay A :=
 | Now (x:A)
 | Later (x:Delay A).
Arguments Now {A}.
Arguments Later {A}.

(* Note: here's a termination metric, the lexicographically ordered
   `((number of watched literal - number of pending literal), number of pending literal)` *)
CoFixpoint rush (s : State) : Delay (State + (State * Clause)) :=
  if rush_has_work s then
    match progress s with
    | Progress s' => Later (rush s')
    | Conflict s' cause => Now (inr (s', cause))
    end
  else Now (inl s).

CoFixpoint delay_bind {A B : Type} (d : Delay A) (k : A -> Delay B)
    : Delay B :=
  match d with
  | Now x => k x
  | Later d' => Later (delay_bind d' k)
  end.

Variant sat_result :=
  | SAT (model : Model)
  | UNSAT.

CoFixpoint backtrack_until (conflict : State * Clause) : Delay (option State) :=
  match backtrack conflict with
  | None => Now None
  | Some (Progress s') => Now (Some s')
  | Some (Conflict s' cause) => Later (backtrack_until (s', cause))
  end.

#[bypass_check(guard)]
CoFixpoint sat (s : State) : Delay sat_result :=
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
