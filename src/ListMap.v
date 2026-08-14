Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.micromega.Lia.
Require Import FMV.FiniteMap.

Module ListMonoid (Element : DecidableType) <: Monoid.
  Definition t := list Element.t.
  Definition empty : t := [].
  Definition op : t -> t -> t := @app Element.t.
  Lemma op_assoc : forall x y z, op x (op y z) = op (op x y) z.
  Proof. intros. apply app_assoc. Qed.
  Lemma op_empty_l : forall x, op empty x = x.
  Proof. reflexivity. Qed.
  Lemma op_empty_r : forall x, op x empty = x.
  Proof. intros. apply app_nil_r. Qed.
End ListMonoid.

Module Type ListMapSig (Key : DecidableType) (Element : DecidableType).
  Parameter t : Type.
  Parameter empty : t.
  Parameter find : Key.t -> t -> list Element.t.
  Parameter keys : t -> list Key.t.
  Parameter add : Key.t -> Element.t -> t -> t.
  Parameter remove : Key.t -> t -> t.
  Parameter remove_from : Element.t -> list Element.t -> list Element.t.
  Parameter remove_element : Element.t -> t -> t.
  Parameter card_of : Element.t -> t -> nat.
  Parameter elements : t -> list Element.t.
  Axiom find_empty : forall k, find k empty = [].
  Axiom card_of_empty : forall x, card_of x empty = 0.
  Axiom keys_complete : forall m k, find k m <> [] <-> In k (keys m).
  Axiom find_add : forall m x y k k',
    In y (find k' (add k x m)) <->
    (k' = k /\ y = x) \/ In y (find k' m).
  Axiom find_add_eq : forall m x k k',
    find k' (add k x m) =
      if Key.eq_dec k k' then x :: find k' m else find k' m.
  Axiom card_of_add : forall m x k,
    card_of x (add k x m) = S (card_of x m).
  Axiom card_of_add_neq : forall m x y k,
    x <> y -> card_of y (add k x m) = card_of y m.
  Axiom card_of_remove : forall m x k,
    card_of x (remove k m) + count_occ Element.eq_dec (find k m) x =
      card_of x m.
  Axiom card_of_remove_element_eq : forall m x,
    card_of x (remove_element x m) = 0.
  Axiom card_of_remove_element_neq : forall m x y,
    x <> y -> card_of y (remove_element x m) = card_of y m.
  Axiom card_of_unique : forall m x k k',
    card_of x m = 1 -> In x (find k m) -> In x (find k' m) -> k = k'.
  Axiom card_of_in : forall m x k, In x (find k m) -> card_of x m > 0.
  Axiom find_remove : forall m k x k',
    In x (find k (remove k' m)) <-> In x (find k m) /\ k <> k'.
  Axiom find_remove_eq : forall m k k',
    find k (remove k' m) =
      if Key.eq_dec k' k then [] else find k m.
  Axiom find_remove_element : forall m x y k,
    In y (find k (remove_element x m)) <->
      In y (find k m) /\ y <> x.
  Axiom find_remove_element_eq : forall m x k,
    find k (remove_element x m) = remove_from x (find k m).
  Axiom elements_spec : forall m x,
    In x (elements m) <-> exists k, In k (keys m) /\ In x (find k m).
End ListMapSig.

Module Make (Key : DecidableType) (Element : DecidableType) <: ListMapSig Key Element.
  Module ListMonoid' := ListMonoid Element.

  Module Base := FiniteMap.RawMake Key ListMonoid'.

  Definition t := Base.t.
  Definition empty : t := Base.empty.
  Definition find (k : Key.t) (m : t) : list Element.t := Base.find k m.

  Definition nonempty (xs : list Element.t) : bool :=
    match xs with [] => false | _ :: _ => true end.

  (* Generic finite-map supports may contain bindings whose monoid value is the
     unit.  Lists have a decidable unit, so this view exposes exactly the
     nonempty bindings. *)
  Definition keys (m : t) : list Key.t :=
    filter (fun k => nonempty (find k m)) (Base.keys m).

  Definition add (k : Key.t) (x : Element.t) (m : t) : t :=
    Base.add k [x] m.
  Definition remove (k : Key.t) (m : t) : t := Base.remove k m.

  Definition remove_from (x : Element.t) (xs : list Element.t) : list Element.t :=
    filter (fun y => if Element.eq_dec x y then false else true) xs.

  Definition remove_element (x : Element.t) (m : t) : t :=
    Base.map_values (remove_from x) eq_refl m.

  Definition elements (m : t) : list Element.t :=
    flat_map (fun k => find k m) (Base.keys m).

  Definition card_of (x : Element.t) (m : t) : nat :=
    count_occ Element.eq_dec (elements m) x.

  Lemma find_empty : forall k, find k empty = [].
  Proof. exact Base.find_empty. Qed.

  Lemma card_of_empty : forall x, card_of x empty = 0.
  Proof. reflexivity. Qed.

  Lemma keys_complete : forall m k, find k m <> [] <-> In k (keys m).
  Proof.
    intros m k. unfold keys. rewrite filter_In. split.
    - intros H. split; [now apply Base.keys_complete|].
      destruct (find k m); [contradiction|reflexivity].
    - intros [_ H]. destruct (find k m); discriminate.
  Qed.

  Lemma lookup_notin_support : forall m k,
    ~ In k (Base.keys m) -> find k m = [].
  Proof. exact Base.lookup_notin_support. Qed.

  Lemma find_add_eq : forall m x k k',
    find k' (add k x m) =
      if Key.eq_dec k k' then x :: find k' m else find k' m.
  Proof.
    intros. unfold find, add. rewrite Base.find_add_eq.
    destruct (Key.eq_dec k k'); reflexivity.
  Qed.

  Lemma find_add : forall m x y k k',
    In y (find k' (add k x m)) <->
    (k' = k /\ y = x) \/ In y (find k' m).
  Proof.
    intros. rewrite find_add_eq. destruct (Key.eq_dec k k') as [->|Hneq];
      simpl; firstorder congruence.
  Qed.

  Lemma count_occ_flat_map_add_absent : forall ks f k x y,
    ~ In k ks ->
    count_occ Element.eq_dec
      (flat_map (fun k' => if Key.eq_dec k k' then x :: f k' else f k') ks) y =
    count_occ Element.eq_dec (flat_map f ks) y.
  Proof.
    intros ks. induction ks as [|k' ks IH]; intros f k x y Hnotin; simpl.
    - reflexivity.
    - destruct (Key.eq_dec k k') as [->|Hneq].
      + exfalso. apply Hnotin. now left.
      + rewrite !count_occ_app. rewrite IH; [reflexivity|].
        intros Hin. apply Hnotin. now right.
  Qed.

  Lemma count_occ_flat_map_add_present : forall ks f k x y,
    NoDup ks -> In k ks ->
    count_occ Element.eq_dec
      (flat_map (fun k' => if Key.eq_dec k k' then x :: f k' else f k') ks) y =
    count_occ Element.eq_dec [x] y +
      count_occ Element.eq_dec (flat_map f ks) y.
  Proof.
    intros ks. induction ks as [|k' ks IH]; intros f k x y Hnodup Hin;
      [contradiction|].
    inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    simpl in Hin. cbn [flat_map].
    destruct (Key.eq_dec k k') as [->|Hneq].
    - destruct (Key.eq_dec k' k') as [_|Habs]; [|contradiction].
      rewrite !count_occ_app.
      rewrite (count_occ_flat_map_add_absent ks f k' x y Hnotin).
      destruct (Element.eq_dec x y) eqn:Hxy; simpl; rewrite Hxy; simpl; lia.
    - destruct (Key.eq_dec k k') as [Habs|_]; [contradiction|].
      rewrite !count_occ_app, IH; [lia|exact Hnodup'|].
      destruct Hin as [Heq|Hin]; [congruence|exact Hin].
  Qed.

  Lemma card_of_add : forall m x k,
    card_of x (add k x m) = S (card_of x m).
  Proof.
    intros m x k. unfold card_of, elements, add, find, Base.add. simpl.
    destruct (in_dec Key.eq_dec k (Base.support m)) as [Hin|Hnotin].
    - rewrite count_occ_flat_map_add_present;
        [|exact (proj1 (Base.support_spec m))|exact Hin].
      simpl. destruct (Element.eq_dec x x); [reflexivity|contradiction].
    - simpl. destruct (Key.eq_dec k k) as [_|Habs]; [|contradiction].
      rewrite (Base.lookup_notin_support m k Hnotin).
      rewrite !count_occ_app, count_occ_flat_map_add_absent by exact Hnotin.
      simpl. destruct (Element.eq_dec x x); [reflexivity|contradiction].
  Qed.

  Lemma card_of_add_neq : forall m x y k,
    x <> y -> card_of y (add k x m) = card_of y m.
  Proof.
    intros m x y k Hneq. unfold card_of, elements, add, find, Base.add. simpl.
    destruct (in_dec Key.eq_dec k (Base.support m)) as [Hin|Hnotin].
    - rewrite count_occ_flat_map_add_present;
        [|exact (proj1 (Base.support_spec m))|exact Hin].
      simpl. destruct (Element.eq_dec x y); [contradiction|reflexivity].
    - simpl. destruct (Key.eq_dec k k) as [_|Habs]; [|contradiction].
      rewrite (Base.lookup_notin_support m k Hnotin).
      rewrite !count_occ_app, count_occ_flat_map_add_absent by exact Hnotin.
      simpl. destruct (Element.eq_dec x y); [contradiction|reflexivity].
  Qed.

  Lemma filter_remove_absent : forall ks k,
    ~ In k ks ->
    filter (fun k' => if Key.eq_dec k k' then false else true) ks = ks.
  Proof.
    intros ks. induction ks as [|k' ks IH]; intros k Hnotin; simpl.
    - reflexivity.
    - destruct (Key.eq_dec k k') as [->|Hneq].
      + exfalso. apply Hnotin. now left.
      + simpl. f_equal. apply IH. intros Hin. apply Hnotin. now right.
  Qed.

  Lemma flat_map_remove_absent : forall (ks : list Key.t)
      (f : Key.t -> list Element.t) k,
    ~ In k ks ->
    flat_map (fun k' => if Key.eq_dec k k' then [] else f k') ks = flat_map f ks.
  Proof.
    intros ks. induction ks as [|k' ks IH]; intros f k Hnotin; simpl.
    - reflexivity.
    - destruct (Key.eq_dec k k') as [->|Hneq].
      + exfalso. apply Hnotin. now left.
      + f_equal. apply IH. intros Hin. apply Hnotin. now right.
  Qed.

  Lemma card_of_remove : forall m x k,
    card_of x (remove k m) + count_occ Element.eq_dec (find k m) x =
      card_of x m.
  Proof.
    intros m x k. unfold card_of, elements, remove, find, Base.remove. simpl.
    unfold Base.keys.
    destruct (in_dec Key.eq_dec k (Base.support m)) as [Hin|Hnotin].
    - apply in_split in Hin as [before [after Hsupport]].
      pose proof (proj1 (Base.support_spec m)) as Hnodup.
      rewrite Hsupport in Hnodup |- *.
      rewrite filter_app. simpl.
      destruct (Key.eq_dec k k) as [_|Habs]; [|contradiction]. simpl.
      pose proof (NoDup_remove_2 _ _ _ Hnodup) as Hnotin_rest.
      assert (~ In k before) as Hnotin_before.
      { intros H. apply Hnotin_rest. apply in_or_app. now left. }
      assert (~ In k after) as Hnotin_after.
      { intros H. apply Hnotin_rest. apply in_or_app. now right. }
      rewrite (filter_remove_absent before k Hnotin_before).
      rewrite (filter_remove_absent after k Hnotin_after).
      rewrite !flat_map_app.
      erewrite flat_map_remove_absent by exact Hnotin_before.
      erewrite flat_map_remove_absent by exact Hnotin_after.
      cbn [flat_map]. rewrite !count_occ_app.
      set (nb := count_occ Element.eq_dec
        (flat_map (fun k => Base.lookup m k) before) x).
      set (nk := count_occ Element.eq_dec (Base.lookup m k) x).
      set (na := count_occ Element.eq_dec
        (flat_map (fun k => Base.lookup m k) after) x).
      change (nb + na + nk = nb + (nk + na)). lia.
    - rewrite (filter_remove_absent (Base.support m) k Hnotin).
      erewrite flat_map_remove_absent by exact Hnotin.
      unfold Base.find. rewrite (Base.lookup_notin_support m k Hnotin).
      simpl.
      change (count_occ Element.eq_dec
        (flat_map (fun k => Base.lookup m k) (Base.support m)) x + 0 =
        count_occ Element.eq_dec
          (flat_map (fun k => Base.lookup m k) (Base.support m)) x).
      lia.
  Qed.

  Lemma count_occ_remove_from_eq : forall xs x,
    count_occ Element.eq_dec (remove_from x xs) x = 0.
  Proof.
    intros xs. induction xs as [|y xs IH]; intros x; simpl.
    - reflexivity.
    - destruct (Element.eq_dec x y) as [->|Hneq]; simpl.
      + exact (IH y).
      + destruct (Element.eq_dec y x); [congruence|exact (IH x)].
  Qed.

  Lemma count_occ_remove_from_neq : forall xs x y,
    x <> y ->
    count_occ Element.eq_dec (remove_from x xs) y =
      count_occ Element.eq_dec xs y.
  Proof.
    intros xs. induction xs as [|z xs IH]; intros x y Hneq; simpl.
    - reflexivity.
    - destruct (Element.eq_dec x z) as [->|Hxz]; simpl.
      + destruct (Element.eq_dec z y); [congruence|]. apply IH. exact Hneq.
      + destruct (Element.eq_dec z y); simpl; rewrite IH by exact Hneq;
          reflexivity.
  Qed.

  Lemma card_of_remove_element_eq : forall m x,
    card_of x (remove_element x m) = 0.
  Proof.
    intros m x. unfold card_of, elements, remove_element, find,
      Base.map_values. simpl.
    unfold Base.keys. induction (Base.support m) as [|k ks IH];
      simpl; [reflexivity|].
    rewrite count_occ_app, count_occ_remove_from_eq, IH. reflexivity.
  Qed.

  Lemma card_of_remove_element_neq : forall m x y,
    x <> y -> card_of y (remove_element x m) = card_of y m.
  Proof.
    intros m x y Hneq. unfold card_of, elements, remove_element, find,
      Base.map_values. simpl.
    unfold Base.keys. induction (Base.support m) as [|k ks IH];
      simpl; [reflexivity|].
    rewrite !count_occ_app, count_occ_remove_from_neq by exact Hneq.
    now rewrite IH.
  Qed.

  Lemma find_remove_eq : forall m k k',
    find k (remove k' m) =
      if Key.eq_dec k' k then [] else find k m.
  Proof. reflexivity. Qed.

  Lemma find_remove : forall m k x k',
    In x (find k (remove k' m)) <-> In x (find k m) /\ k <> k'.
  Proof.
    intros. rewrite find_remove_eq. destruct (Key.eq_dec k' k) as [->|Hneq];
      simpl; firstorder congruence.
  Qed.

  Lemma find_remove_element_eq : forall m x k,
    find k (remove_element x m) = remove_from x (find k m).
  Proof. reflexivity. Qed.

  Lemma find_remove_element : forall m x y k,
    In y (find k (remove_element x m)) <->
      In y (find k m) /\ y <> x.
  Proof.
    intros. rewrite find_remove_element_eq. unfold remove_from.
    rewrite filter_In. destruct (Element.eq_dec x y) as [->|Hneq].
    - destruct (Element.eq_dec y y) as [_|Habs]; [|contradiction].
      split.
      + intros [_ H]. discriminate.
      + intros [_ H]. contradiction.
    - destruct (Element.eq_dec x y) as [Habs|_]; [contradiction|].
      simpl. firstorder congruence.
  Qed.

  Lemma elements_spec : forall m x,
    In x (elements m) <-> exists k, In k (keys m) /\ In x (find k m).
  Proof.
    intros m x. unfold elements. rewrite in_flat_map. split.
    - intros [k [Hsupport Hin]]. exists k. split; [|exact Hin].
      apply keys_complete. intros Hempty. rewrite Hempty in Hin. contradiction.
    - intros [k [Hkey Hin]]. exists k. split; [|exact Hin].
      apply Base.keys_complete. apply keys_complete. exact Hkey.
  Qed.

  Lemma card_of_in : forall m x k, In x (find k m) -> card_of x m > 0.
  Proof.
    intros m x k Hin. unfold card_of. apply count_occ_In.
    apply elements_spec. exists k. split; [|exact Hin].
    apply keys_complete. intros Hempty. rewrite Hempty in Hin. contradiction.
  Qed.

  Lemma card_of_unique : forall m x k k',
    card_of x m = 1 -> In x (find k m) -> In x (find k' m) -> k = k'.
  Proof.
    intros m x k k' Hcard Hk Hk'. destruct (Key.eq_dec k k') as [->|Hneq];
      [reflexivity|exfalso].
    unfold find in Hk, Hk'.
    assert (In k (Base.keys m)) as Hks.
    { apply Base.keys_complete. intros Hempty. rewrite Hempty in Hk. contradiction. }
    assert (In k' (Base.keys m)) as Hks'.
    { apply Base.keys_complete. intros Hempty. rewrite Hempty in Hk'. contradiction. }
    apply in_split in Hks as [before [after Hsupport]].
    assert (In k' (before ++ after)) as Hk'rest.
    { rewrite Hsupport in Hks'. apply in_app_or in Hks' as [Hin|Hin].
      - now apply in_or_app; left.
      - simpl in Hin. destruct Hin as [Heq|Hin]; [congruence|].
        now apply in_or_app; right. }
    assert (In x (flat_map (fun k => find k m) (before ++ after))) as Hrest.
    { apply in_flat_map. exists k'. split; assumption. }
    apply (proj1 (count_occ_In Element.eq_dec _ _)) in Hk.
    change (count_occ Element.eq_dec (find k m) x > 0) in Hk.
    apply (proj1 (count_occ_In Element.eq_dec _ _)) in Hrest.
    unfold card_of, elements in Hcard. rewrite Hsupport, flat_map_app in Hcard.
    cbn [flat_map] in Hcard. rewrite !count_occ_app in Hcard.
    rewrite flat_map_app, count_occ_app in Hrest. lia.
  Qed.
End Make.
