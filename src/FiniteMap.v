Require Import Stdlib.Lists.List.
Require Import Stdlib.Structures.OrderedType.
Require Import Stdlib.FSets.FMapAVL.
Require Import Stdlib.FSets.FMapFacts.
Require Import Stdlib.Sorting.Permutation.
Import ListNotations.

Module Type DecidableType.
  Parameter t : Type.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End DecidableType.

Module Type OrderedKey.
  Parameter t : Type.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  Parameter lt : t -> t -> Prop.
  Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y, lt x y -> x <> y.
  Parameter compare : forall x y, Compare lt eq x y.
End OrderedKey.

Module Type Monoid.
  Parameter t : Type.
  Parameter empty : t.
  Parameter op : t -> t -> t.
  Axiom op_assoc : forall x y z, op x (op y z) = op (op x y) z.
  Axiom op_empty_l : forall x, op empty x = x.
  Axiom op_empty_r : forall x, op x empty = x.
End Monoid.

Module Type FiniteMapSig (Key : OrderedKey) (Value : Monoid).
  Parameter t : Type.
  Parameter lookup : t -> Key.t -> Value.t.
  Parameter find : Key.t -> t -> Value.t.
  Parameter keys : t -> list Key.t.
  Parameter maximum : t -> option Key.t.
  Axiom maximum_spec : forall m,
    match maximum m with
    | None => keys m = []
    | Some greatest =>
        In greatest (keys m) /\
        forall k, In k (keys m) -> ~ Key.lt greatest k
    end.
  Parameter empty : t.
  Parameter add : Key.t -> Value.t -> t -> t.
  Parameter remove : Key.t -> t -> t.
  Parameter map_values : forall (f : Value.t -> Value.t),
    f Value.empty = Value.empty -> t -> t.
  Axiom find_empty : forall k, find k empty = Value.empty.
  Axiom find_add_eq : forall m x k k',
    find k' (add k x m) =
      if Key.eq_dec k k' then Value.op x (find k' m) else find k' m.
  Axiom find_remove_eq : forall m k k',
    find k' (remove k m) =
      if Key.eq_dec k k' then Value.empty else find k' m.
  Axiom keys_complete : forall m k,
    find k m <> Value.empty -> In k (keys m).
  Axiom keys_nodup : forall m, NoDup (keys m).
  Axiom lookup_notin_keys : forall m k,
    ~ In k (keys m) -> lookup m k = Value.empty.
End FiniteMapSig.

Module RawMake (Key : OrderedKey) (Value : Monoid).
  Module KeyOT <: OrderedType.OrderedType.
    Definition t := Key.t.
    Definition eq := @eq t.
    Definition lt := Key.lt.
    Definition eq_refl := @eq_refl t.
    Definition eq_sym := @eq_sym t.
    Definition eq_trans := @eq_trans t.
    Definition lt_trans := Key.lt_trans.
    Definition lt_not_eq := Key.lt_not_eq.
    Definition compare := Key.compare.
    Definition eq_dec := Key.eq_dec.
  End KeyOT.

  Module Tree := FMapAVL.Make KeyOT.
  Module TreeFacts := FMapFacts.WFacts_fun KeyOT Tree.

  Definition keys_of (bindings : Tree.t Value.t) : list Key.t :=
    map fst (Tree.elements bindings).

  Lemma keys_of_spec : forall bindings k,
    In k (keys_of bindings) <-> Tree.In k bindings.
  Proof.
    intros bindings k. unfold keys_of. rewrite in_map_iff.
    rewrite TreeFacts.elements_in_iff. split.
    - intros [[k' value] [Hkey Hin]]. cbn in Hkey. subst k'.
      exists value. rewrite InA_alt. exists (k, value). split; [reflexivity|].
      exact Hin.
    - intros [value Hin]. rewrite InA_alt in Hin.
      destruct Hin as [[k' value'] [[Hkey _] Hin]]. cbn in Hkey. subst k'.
      exists (k, value'). split; [reflexivity|exact Hin].
  Qed.

  Lemma keys_of_nodup : forall bindings, NoDup (keys_of bindings).
  Proof.
    intros bindings. unfold keys_of.
    pose proof (Tree.elements_3w bindings) as Hnodup.
    induction Hnodup as [|[k value] elements Hnotin Hnodup IH]; simpl.
    - constructor.
    - constructor; [|exact IH]. intros Hin. apply in_map_iff in Hin.
      destruct Hin as [[k' value'] [Hkey Hin]]. cbn in Hkey. subst k'.
      apply Hnotin. rewrite InA_alt. exists (k, value').
      split; [reflexivity|exact Hin].
  Qed.

  Fixpoint maximum_list (keys : list Key.t) : option Key.t :=
    match keys with
    | [] => None
    | k :: keys' =>
        match maximum_list keys' with
        | None => Some k
        | Some greatest =>
            match Key.compare greatest k with
            | LT _ => Some k
            | _ => Some greatest
            end
        end
    end.

  Lemma maximum_list_spec : forall keys,
    match maximum_list keys with
    | None => keys = []
    | Some greatest =>
        In greatest keys /\
        forall k, In k keys -> ~ Key.lt greatest k
    end.
  Proof.
    intros keys. induction keys as [|k keys IH]; [reflexivity|].
    cbn [maximum_list]. destruct (maximum_list keys) as [greatest|] eqn:Hmax.
    - destruct IH as [Hin Hgreatest].
      destruct (Key.compare greatest k) as [Hlt|Heq|Hgt].
      + split; [now left|]. intros x [<-|Hin']; intros Hkx.
        * now apply (Key.lt_not_eq k k Hkx).
        * apply (Hgreatest x Hin').
          eapply Key.lt_trans; [exact Hlt|exact Hkx].
      + split; [now right|]. intros x [<-|Hin']; intros Hgx.
        * apply (Key.lt_not_eq greatest k Hgx). exact Heq.
        * now apply (Hgreatest x Hin').
      + split; [now right|]. intros x [<-|Hin']; intros Hgx.
        * pose proof (Key.lt_trans greatest k greatest Hgx Hgt) as Hirr.
          exact (Key.lt_not_eq greatest greatest Hirr eq_refl).
        * now apply (Hgreatest x Hin').
    - subst keys. split; [now left|].
      intros x [<-|[]] Hlt.
      exact (Key.lt_not_eq k k Hlt eq_refl).
  Qed.

  Definition insert_maximum (k : Key.t) (maximum : option Key.t) :=
    match maximum with
    | None => Some k
    | Some greatest =>
        match Key.compare greatest k with
        | LT _ => Some k
        | _ => Some greatest
        end
    end.

  Lemma insert_maximum_spec : forall keys maximum k,
    (match maximum with
     | None => keys = []
     | Some greatest =>
         In greatest keys /\
         forall x, In x keys -> ~ Key.lt greatest x
     end) ->
    match insert_maximum k maximum with
    | None => k :: keys = []
    | Some greatest =>
        In greatest (k :: keys) /\
        forall x, In x (k :: keys) -> ~ Key.lt greatest x
    end.
  Proof.
    intros keys [greatest|] k Hspec.
    - destruct Hspec as [Hin Hgreatest]. unfold insert_maximum.
      destruct (Key.compare greatest k) as [Hlt|Heq|Hgt].
      + split; [now left|]. intros x [<-|Hin']; intros Hkx.
        * exact (Key.lt_not_eq k k Hkx eq_refl).
        * apply (Hgreatest x Hin').
          eapply Key.lt_trans; [exact Hlt|exact Hkx].
      + split; [now right|]. intros x [<-|Hin']; intros Hgx.
        * apply (Key.lt_not_eq greatest k Hgx). exact Heq.
        * now apply (Hgreatest x Hin').
      + split; [now right|]. intros x [<-|Hin']; intros Hgx.
        * pose proof (Key.lt_trans greatest k greatest Hgx Hgt) as Hirr.
          exact (Key.lt_not_eq greatest greatest Hirr eq_refl).
        * now apply (Hgreatest x Hin').
    - subst keys. split; [now left|].
      intros x [<-|[]] Hlt. exact (Key.lt_not_eq k k Hlt eq_refl).
  Qed.

  Record representation := make {
      bindings : Tree.t Value.t;
      maximum_key : option Key.t;
      maximum_specification :
        match maximum_key with
        | None => keys_of bindings = []
        | Some greatest =>
            In greatest (keys_of bindings) /\
            forall k, In k (keys_of bindings) -> ~ Key.lt greatest k
        end
    }.
  Definition t := representation.

  Definition lookup (m : t) (k : Key.t) : Value.t :=
    match Tree.find k m.(bindings) with
    | Some value => value
    | None => Value.empty
    end.
  Definition find (k : Key.t) (m : t) : Value.t := lookup m k.
  Definition keys (m : t) : list Key.t := keys_of m.(bindings).
  Definition maximum (m : t) : option Key.t := m.(maximum_key).

  Definition empty : t.
  Proof.
    refine {| bindings := Tree.empty Value.t; maximum_key := None |}.
    reflexivity.
  Defined.

  Lemma keys_of_add : forall bindings k value k',
    In k' (keys_of (Tree.add k value bindings)) <->
      k' = k \/ In k' (keys_of bindings).
  Proof.
    intros. rewrite !keys_of_spec, TreeFacts.add_in_iff.
    destruct (Key.eq_dec k k'); intuition congruence.
  Qed.

  Lemma add_maximum_spec : forall bindings maximum k value,
    (match maximum with
     | None => keys_of bindings = []
     | Some greatest =>
         In greatest (keys_of bindings) /\
         forall x, In x (keys_of bindings) -> ~ Key.lt greatest x
     end) ->
    match insert_maximum k maximum with
    | None => keys_of (Tree.add k value bindings) = []
    | Some greatest =>
        In greatest (keys_of (Tree.add k value bindings)) /\
        forall x, In x (keys_of (Tree.add k value bindings)) ->
          ~ Key.lt greatest x
    end.
  Proof.
    intros bindings maximum k value Hspec.
    pose proof (insert_maximum_spec (keys_of bindings) maximum k Hspec)
      as Hinsert.
    destruct (insert_maximum k maximum) as [greatest|]; [|discriminate Hinsert].
    destruct Hinsert as [Hin Hupper]. split.
    - apply keys_of_add. simpl in Hin. intuition congruence.
    - intros x Hin'. apply Hupper. apply keys_of_add in Hin'.
      simpl. intuition congruence.
  Qed.

  Definition add (k : Key.t) (x : Value.t) (m : t) : t :=
    {| bindings := Tree.add k (Value.op x (lookup m k)) m.(bindings);
       maximum_key := insert_maximum k m.(maximum_key);
       maximum_specification := add_maximum_spec m.(bindings)
         m.(maximum_key) k (Value.op x (lookup m k))
         m.(maximum_specification) |}.

  Definition remove (k : Key.t) (m : t) : t.
  Proof.
    refine
      {| bindings := Tree.remove k m.(bindings);
         maximum_key := maximum_list
           (keys_of (Tree.remove k m.(bindings))) |}.
    exact (maximum_list_spec (keys_of (Tree.remove k m.(bindings)))).
  Defined.

  Definition map_values (f : Value.t -> Value.t)
      (f_empty : f Value.empty = Value.empty) (m : t) : t.
  Proof.
    refine {| bindings := Tree.map f m.(bindings);
              maximum_key := m.(maximum_key); maximum_specification := _ |}.
    pose proof m.(maximum_specification) as Hspec.
    destruct m.(maximum_key) as [greatest|] eqn:Hmaximum.
    - cbn in Hspec. destruct Hspec as [Hin Hupper]. split.
      + rewrite keys_of_spec, TreeFacts.map_in_iff. now apply keys_of_spec.
      + intros k Hin'. apply Hupper. apply keys_of_spec in Hin'.
        rewrite TreeFacts.map_in_iff in Hin'. now apply keys_of_spec.
    - cbn in Hspec.
      destruct (keys_of (Tree.map f m.(bindings))) as [|k keys] eqn:Hkeys;
        [reflexivity|].
      exfalso. assert (In k (keys_of (Tree.map f m.(bindings)))) as Hin.
      { rewrite Hkeys. now left. }
      apply keys_of_spec in Hin.
      rewrite TreeFacts.map_in_iff in Hin. apply keys_of_spec in Hin.
      rewrite Hspec in Hin. exact Hin.
  Defined.

  (* Update one existing binding.  An absent key is left absent. *)
  Definition update_binding (k : Key.t) (f : Value.t -> Value.t)
      (bindings : Tree.t Value.t) : Tree.t Value.t :=
    match Tree.find k bindings with
    | Some value => Tree.add k (f value) bindings
    | None => bindings
    end.

  Lemma update_binding_in_iff : forall k f bindings k',
    Tree.In k' (update_binding k f bindings) <-> Tree.In k' bindings.
  Proof.
    intros k f bindings k'. unfold update_binding.
    destruct (Tree.find k bindings) as [value|] eqn:Hfind; [|reflexivity].
    rewrite TreeFacts.add_in_iff. split; [|now right].
    intros [Heq|Hin]; [subst k'|exact Hin].
    exists value. now apply TreeFacts.find_mapsto_iff.
  Qed.

  Lemma update_binding_maximum_spec : forall k f m,
    match m.(maximum_key) with
    | None => keys_of (update_binding k f m.(bindings)) = []
    | Some greatest =>
        In greatest (keys_of (update_binding k f m.(bindings))) /\
        forall x, In x (keys_of (update_binding k f m.(bindings))) ->
          ~ Key.lt greatest x
    end.
  Proof.
    intros k f m.
    pose proof m.(maximum_specification) as Hspec.
    destruct m.(maximum_key) as [greatest|].
    - cbn in Hspec. destruct Hspec as [Hin Hupper]. split.
      + apply keys_of_spec, update_binding_in_iff, keys_of_spec. exact Hin.
      + intros x Hin'. apply Hupper.
        apply keys_of_spec, update_binding_in_iff, keys_of_spec in Hin'.
        exact Hin'.
    - cbn in Hspec.
      destruct (keys_of (update_binding k f m.(bindings))) as [|x xs] eqn:Hkeys;
        [reflexivity|].
      exfalso. assert (In x (keys_of (update_binding k f m.(bindings)))) as Hin.
      { rewrite Hkeys. now left. }
      apply keys_of_spec, update_binding_in_iff, keys_of_spec in Hin.
      now rewrite Hspec in Hin.
  Qed.

  Definition map_at (k : Key.t) (f : Value.t -> Value.t)
      (f_empty : f Value.empty = Value.empty) (m : t) : t :=
    {| bindings := update_binding k f m.(bindings);
       maximum_key := m.(maximum_key);
       maximum_specification := update_binding_maximum_spec k f m |}.

  Lemma find_empty : forall k, find k empty = Value.empty.
  Proof. intros k. reflexivity. Qed.

  Lemma find_add_eq : forall m x k k',
    find k' (add k x m) =
      if Key.eq_dec k k' then Value.op x (find k' m) else find k' m.
  Proof.
    intros m x k k'.
    assert
      (match Tree.find k'
        (Tree.add k (Value.op x (lookup m k)) m.(bindings)) with
       | Some value => value
       | None => Value.empty
       end =
       if Key.eq_dec k k' then Value.op x (lookup m k') else lookup m k')
      as Hlookup.
    {
      destruct (Key.eq_dec k k') as [->|Hneq].
      - rewrite TreeFacts.add_eq_o by reflexivity. reflexivity.
      - now rewrite TreeFacts.add_neq_o by exact Hneq.
    }
    exact Hlookup.
  Qed.

  Lemma find_remove_eq : forall m k k',
    find k' (remove k m) =
      if Key.eq_dec k k' then Value.empty else find k' m.
  Proof.
    intros m k k'.
    change
      (match Tree.find k' (Tree.remove k m.(bindings)) with
       | Some value => value
       | None => Value.empty
       end = if Key.eq_dec k k' then Value.empty else lookup m k').
    destruct (Key.eq_dec k k') as [->|Hneq].
    - now rewrite TreeFacts.remove_eq_o by reflexivity.
    - now rewrite TreeFacts.remove_neq_o by exact Hneq.
  Qed.

  Lemma keys_add_iff : forall m x k k',
    In k' (keys (add k x m)) <-> k' = k \/ In k' (keys m).
  Proof. intros. exact (keys_of_add m.(bindings) k _ k'). Qed.

  Lemma keys_add_permutation : forall m x k,
    Permutation (keys (add k x m))
      (if in_dec Key.eq_dec k (keys m) then keys m else k :: keys m).
  Proof.
    intros m x k. apply NoDup_Permutation.
    - apply keys_of_nodup.
    - destruct (in_dec Key.eq_dec k (keys m));
        [apply keys_of_nodup|now constructor; [|apply keys_of_nodup]].
    - intros k'. rewrite keys_add_iff.
      destruct (in_dec Key.eq_dec k (keys m));
        simpl; intuition congruence.
  Qed.

  Lemma keys_remove_iff : forall m k k',
    In k' (keys (remove k m)) <-> k' <> k /\ In k' (keys m).
  Proof.
    intros m k k'. unfold keys.
    change (In k' (keys_of (Tree.remove k m.(bindings))) <->
      k' <> k /\ In k' (keys_of m.(bindings))).
    rewrite !keys_of_spec, TreeFacts.remove_in_iff.
    destruct (Key.eq_dec k k'); intuition congruence.
  Qed.

  Lemma keys_remove_permutation : forall m k,
    Permutation (keys (remove k m))
      (filter (fun k' => if Key.eq_dec k k' then false else true) (keys m)).
  Proof.
    intros m k. apply NoDup_Permutation.
    - apply keys_of_nodup.
    - apply NoDup_filter, keys_of_nodup.
    - intros k'. rewrite keys_remove_iff, filter_In.
      destruct (Key.eq_dec k k'); simpl; intuition congruence.
  Qed.

  Lemma find_map_at_eq : forall m k k' f f_empty,
    find k' (map_at k f f_empty m) =
      if Key.eq_dec k k' then f (find k' m) else find k' m.
  Proof.
    intros m k k' f f_empty.
    change
      (match Tree.find k' (update_binding k f m.(bindings)) with
       | Some value => value
       | None => Value.empty
       end = if Key.eq_dec k k' then f (lookup m k') else lookup m k').
    unfold update_binding.
    destruct (Tree.find k m.(bindings)) as [value|] eqn:Hfind.
    - destruct (Key.eq_dec k k') as [->|Hneq].
      + rewrite TreeFacts.add_eq_o by reflexivity. unfold lookup. now rewrite Hfind.
      + now rewrite TreeFacts.add_neq_o by exact Hneq.
    - destruct (Key.eq_dec k k') as [->|Hneq].
      + unfold lookup. now rewrite Hfind, f_empty.
      + reflexivity.
  Qed.

  Lemma keys_map_at_permutation : forall m k f f_empty,
    Permutation (keys (map_at k f f_empty m)) (keys m).
  Proof.
    intros m k f f_empty. apply NoDup_Permutation.
    - apply keys_of_nodup.
    - apply keys_of_nodup.
    - intros k'. unfold keys.
      change (In k' (keys_of (update_binding k f m.(bindings))) <->
        In k' (keys_of m.(bindings))).
      rewrite !keys_of_spec, update_binding_in_iff. reflexivity.
  Qed.

  Lemma keys_complete : forall m k,
    find k m <> Value.empty -> In k (keys m).
  Proof.
    intros m k Hfind. apply keys_of_spec.
    unfold find, lookup in Hfind.
    destruct (Tree.find k m.(bindings)) as [value|] eqn:Hlookup.
    - exists value. now apply TreeFacts.find_mapsto_iff.
    - contradiction.
  Qed.

  Lemma lookup_notin_keys : forall m k,
    ~ In k (keys m) -> lookup m k = Value.empty.
  Proof.
    intros m k Hnotin. unfold keys in Hnotin. unfold lookup.
    destruct (Tree.find k m.(bindings)) as [value|] eqn:Hfind; [|reflexivity].
    exfalso. apply Hnotin, keys_of_spec. exists value.
    now apply TreeFacts.find_mapsto_iff.
  Qed.

  Lemma keys_nodup : forall m, NoDup (keys m).
  Proof. intros m. apply keys_of_nodup. Qed.

  Lemma maximum_spec : forall m,
    match maximum m with
    | None => keys m = []
    | Some greatest =>
        In greatest (keys m) /\
        forall k, In k (keys m) -> ~ Key.lt greatest k
    end.
  Proof.
    intros m. exact m.(maximum_specification).
  Qed.
End RawMake.

(* The public functor seals the representation.  RawMake is kept available to
   specializations whose proofs use the concrete AVL operations. *)
Module Make (Key : OrderedKey) (Value : Monoid) : FiniteMapSig Key Value :=
  RawMake Key Value.
