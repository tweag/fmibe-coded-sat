Require Import Stdlib.Lists.List.
Require Import Stdlib.Structures.OrderedType.
Require Import Stdlib.FSets.FMapAVL.
Require Import Stdlib.FSets.FMapFacts.
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
  Parameter support : t -> list Key.t.
  Axiom support_spec : forall m,
    NoDup (support m) /\
    forall k, ~ In k (support m) -> lookup m k = Value.empty.
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
  Axiom lookup_notin_support : forall m k,
    ~ In k (support m) -> lookup m k = Value.empty.
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

  Lemma insert_maximum_spec : forall support maximum k,
    (match maximum with
     | None => support = []
     | Some greatest =>
         In greatest support /\
         forall x, In x support -> ~ Key.lt greatest x
     end) ->
    match insert_maximum k maximum with
    | None => k :: support = []
    | Some greatest =>
        In greatest (k :: support) /\
        forall x, In x (k :: support) -> ~ Key.lt greatest x
    end.
  Proof.
    intros support [greatest|] k Hspec.
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
    - subst support. split; [now left|].
      intros x [<-|[]] Hlt. exact (Key.lt_not_eq k k Hlt eq_refl).
  Qed.

  Record representation := make {
      bindings : Tree.t Value.t;
      support : list Key.t;
      maximum_key : option Key.t;
      support_spec : NoDup support /\
        forall k, ~ In k support ->
          match Tree.find k bindings with
          | Some value => value
          | None => Value.empty
          end = Value.empty;
      maximum_specification :
        match maximum_key with
        | None => support = []
        | Some greatest =>
            In greatest support /\
            forall k, In k support -> ~ Key.lt greatest k
        end
    }.
  Definition t := representation.

  Definition lookup (m : t) (k : Key.t) : Value.t :=
    match Tree.find k m.(bindings) with
    | Some value => value
    | None => Value.empty
    end.
  Definition find (k : Key.t) (m : t) : Value.t := lookup m k.
  Definition keys (m : t) : list Key.t := m.(support).
  Definition maximum (m : t) : option Key.t := m.(maximum_key).

  Definition empty : t.
  Proof.
    refine {| bindings := Tree.empty Value.t; support := [];
              maximum_key := None |}.
    split; [constructor|]. intros k _. unfold lookup.
    now rewrite TreeFacts.empty_o.
    reflexivity.
  Defined.

  Definition add (k : Key.t) (x : Value.t) (m : t) : t.
  Proof.
    destruct (in_dec Key.eq_dec k m.(support)) as [Hin|Hnotin].
    - refine
        {| bindings := Tree.add k (Value.op x (lookup m k)) m.(bindings);
           support := m.(support); maximum_key := m.(maximum_key);
           support_spec := _; maximum_specification := _ |}.
      + split; [exact (proj1 m.(support_spec))|].
        intros k' Habsent. unfold lookup.
        destruct (Key.eq_dec k k') as [->|Hneq].
        * exfalso. now apply Habsent.
        * rewrite TreeFacts.add_neq_o by exact Hneq.
          now apply (proj2 m.(support_spec)).
      + exact m.(maximum_specification).
    - refine
        {| bindings := Tree.add k (Value.op x (lookup m k)) m.(bindings);
           support := k :: m.(support);
           maximum_key := insert_maximum k m.(maximum_key);
           support_spec := _; maximum_specification := _ |}.
      + split.
        * constructor; [assumption|exact (proj1 m.(support_spec))].
        * intros k' Habsent. unfold lookup.
          destruct (Key.eq_dec k k') as [->|Hneq].
          -- exfalso. apply Habsent. now left.
          -- rewrite TreeFacts.add_neq_o by exact Hneq.
             apply (proj2 m.(support_spec)).
             intros Hin. apply Habsent. now right.
      + exact (insert_maximum_spec m.(support) m.(maximum_key) k
          m.(maximum_specification)).
  Defined.

  Definition remove (k : Key.t) (m : t) : t.
  Proof.
    remember (filter (fun k' => if Key.eq_dec k k' then false else true)
      m.(support)) as remaining.
    subst remaining.
    refine
      {| bindings := Tree.remove k m.(bindings);
         support := filter (fun k' => if Key.eq_dec k k' then false else true)
           m.(support);
         maximum_key := maximum_list
           (filter (fun k' => if Key.eq_dec k k' then false else true)
             m.(support));
         support_spec := _; maximum_specification := _ |}.
    - split; [apply NoDup_filter; exact (proj1 m.(support_spec))|].
      intros k' Hnotin. unfold lookup. destruct (Key.eq_dec k k') as [->|Hneq].
      + now rewrite TreeFacts.remove_eq_o.
      + rewrite TreeFacts.remove_neq_o by exact Hneq.
        apply (proj2 m.(support_spec)). intros Hin. apply Hnotin.
        apply filter_In. split; [exact Hin|].
        destruct (Key.eq_dec k k'); [contradiction|reflexivity].
    - exact (maximum_list_spec
        (filter (fun k' => if Key.eq_dec k k' then false else true)
          m.(support))).
  Defined.

  Definition map_values (f : Value.t -> Value.t)
      (f_empty : f Value.empty = Value.empty) (m : t) : t.
  Proof.
    refine {| bindings := Tree.map f m.(bindings); support := m.(support);
              maximum_key := m.(maximum_key); support_spec := _;
              maximum_specification := _ |}.
    - split; [exact (proj1 m.(support_spec))|].
      intros k Hnotin. unfold lookup. rewrite TreeFacts.map_o.
      specialize (proj2 m.(support_spec) k Hnotin).
      destruct (Tree.find k m.(bindings)); cbn; congruence.
    - exact m.(maximum_specification).
  Defined.

  (* Update one existing binding.  Requiring the unit to remain the unit means
     that keeping the old support is sound even when [k] was absent. *)
  Definition map_at (k : Key.t) (f : Value.t -> Value.t)
      (f_empty : f Value.empty = Value.empty) (m : t) : t.
  Proof.
    refine
      {| bindings := Tree.add k (f (lookup m k)) m.(bindings);
         support := m.(support); maximum_key := m.(maximum_key);
         support_spec := _; maximum_specification := _ |}.
    - split; [exact (proj1 m.(support_spec))|].
      intros k' Hnotin. unfold lookup. destruct (Key.eq_dec k k') as [->|Hneq].
      + rewrite TreeFacts.add_eq_o by reflexivity.
        rewrite (proj2 m.(support_spec) k' Hnotin). exact f_empty.
      + rewrite TreeFacts.add_neq_o by exact Hneq.
        now apply (proj2 m.(support_spec)).
    - exact m.(maximum_specification).
  Defined.

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
    unfold add. destruct (in_dec Key.eq_dec k m.(support));
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

  Lemma keys_add_eq : forall m x k,
    keys (add k x m) =
      if in_dec Key.eq_dec k (keys m) then keys m else k :: keys m.
  Proof.
    intros m x k. unfold add, keys.
    destruct (in_dec Key.eq_dec k m.(support)); reflexivity.
  Qed.

  Lemma keys_remove_eq : forall m k,
    keys (remove k m) =
      filter (fun k' => if Key.eq_dec k k' then false else true) (keys m).
  Proof. reflexivity. Qed.

  Lemma find_map_at_eq : forall m k k' f f_empty,
    find k' (map_at k f f_empty m) =
      if Key.eq_dec k k' then f (find k' m) else find k' m.
  Proof.
    intros m k k' f f_empty.
    change
      (match Tree.find k' (Tree.add k (f (lookup m k)) m.(bindings)) with
       | Some value => value
       | None => Value.empty
       end = if Key.eq_dec k k' then f (lookup m k') else lookup m k').
    destruct (Key.eq_dec k k') as [->|Hneq].
    - rewrite TreeFacts.add_eq_o by reflexivity. reflexivity.
    - now rewrite TreeFacts.add_neq_o by exact Hneq.
  Qed.

  Lemma keys_complete : forall m k,
    find k m <> Value.empty -> In k (keys m).
  Proof.
    intros m k Hfind. unfold find, keys.
    destruct (in_dec Key.eq_dec k m.(support)); [assumption|].
    exfalso. apply Hfind. now apply (proj2 m.(support_spec)).
  Qed.

  Lemma lookup_notin_support : forall m k,
    ~ In k m.(support) -> lookup m k = Value.empty.
  Proof. intros m k Hnotin. now apply (proj2 m.(support_spec)). Qed.

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
   the list specialization, whose proofs use the concrete support operations. *)
Module Make (Key : OrderedKey) (Value : Monoid) : FiniteMapSig Key Value :=
  RawMake Key Value.
