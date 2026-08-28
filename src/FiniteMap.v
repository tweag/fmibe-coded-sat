Require Import Stdlib.Lists.List.
Import ListNotations.

Module Type DecidableType.
  Parameter t : Type.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End DecidableType.

Module Type Monoid.
  Parameter t : Type.
  Parameter empty : t.
  Parameter op : t -> t -> t.
  Axiom op_assoc : forall x y z, op x (op y z) = op (op x y) z.
  Axiom op_empty_l : forall x, op empty x = x.
  Axiom op_empty_r : forall x, op x empty = x.
End Monoid.

Module Type FiniteMapSig (Key : DecidableType) (Value : Monoid).
  Parameter t : Type.
  Parameter lookup : t -> Key.t -> Value.t.
  Parameter support : t -> list Key.t.
  Axiom support_spec : forall m,
    NoDup (support m) /\
    forall k, ~ In k (support m) -> lookup m k = Value.empty.
  Parameter find : Key.t -> t -> Value.t.
  Parameter keys : t -> list Key.t.
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

Module RawMake (Key : DecidableType) (Value : Monoid).
  Record representation := make {
      lookup : Key.t -> Value.t;
      support : list Key.t;
      support_spec : NoDup support /\
        forall k, ~ In k support -> lookup k = Value.empty
    }.
  Definition t := representation.

  Definition find (k : Key.t) (m : t) : Value.t := m.(lookup) k.
  Definition keys (m : t) : list Key.t := m.(support).

  Definition empty : t.
  Proof.
    refine {| lookup := fun _ => Value.empty; support := [] |}.
    split; [constructor|]. intros k _. reflexivity.
  Defined.

  Definition add (k : Key.t) (x : Value.t) (m : t) : t.
  Proof.
    refine
      {| lookup := fun k' =>
           if Key.eq_dec k k' then Value.op x (m.(lookup) k')
           else m.(lookup) k';
         support := if in_dec Key.eq_dec k m.(support)
           then m.(support) else k :: m.(support) |}.
    split.
    - destruct (in_dec Key.eq_dec k m.(support)).
      + exact (proj1 m.(support_spec)).
      + constructor; [assumption|exact (proj1 m.(support_spec))].
    - intros k' Hnotin.
      destruct (Key.eq_dec k k') as [->|Hneq].
      + destruct (in_dec Key.eq_dec k' m.(support)) as [Hin|Habs].
        * exfalso. apply Hnotin. exact Hin.
        * exfalso. apply Hnotin. simpl. now left.
      + simpl. destruct (Key.eq_dec k k') as [Heq|_]; [contradiction|].
        apply (proj2 m.(support_spec)).
        destruct (in_dec Key.eq_dec k m.(support)); simpl in Hnotin;
          [exact Hnotin|].
        intros Hin. apply Hnotin. now right.
  Defined.

  Definition remove (k : Key.t) (m : t) : t.
  Proof.
    refine
      {| lookup := fun k' => if Key.eq_dec k k' then Value.empty
           else m.(lookup) k';
         support := filter (fun k' => if Key.eq_dec k k' then false else true)
           m.(support) |}.
    split; [apply NoDup_filter; exact (proj1 m.(support_spec))|].
    intros k' Hnotin. destruct (Key.eq_dec k k') as [->|Hneq].
    - simpl. destruct (Key.eq_dec k' k') as [_|Habs];
        [reflexivity|contradiction].
    - simpl. destruct (Key.eq_dec k k') as [Heq|_]; [contradiction|].
      apply (proj2 m.(support_spec)). intros Hin. apply Hnotin.
      apply filter_In. split; [exact Hin|].
      destruct (Key.eq_dec k k'); [contradiction|reflexivity].
  Defined.

  Definition map_values (f : Value.t -> Value.t)
      (f_empty : f Value.empty = Value.empty) (m : t) : t.
  Proof.
    refine {| lookup := fun k => f (m.(lookup) k); support := m.(support) |}.
    split; [exact (proj1 m.(support_spec))|].
    intros k Hnotin. rewrite (proj2 m.(support_spec) k Hnotin).
    exact f_empty.
  Defined.

  (* Update one existing binding.  Requiring the unit to remain the unit means
     that keeping the old support is sound even when [k] was absent. *)
  Definition map_at (k : Key.t) (f : Value.t -> Value.t)
      (f_empty : f Value.empty = Value.empty) (m : t) : t.
  Proof.
    refine
      {| lookup := fun k' =>
           if Key.eq_dec k k' then f (m.(lookup) k') else m.(lookup) k';
         support := m.(support) |}.
    split; [exact (proj1 m.(support_spec))|].
    intros k' Hnotin. destruct (Key.eq_dec k k') as [->|Hneq].
    - rewrite (proj2 m.(support_spec) k' Hnotin). exact f_empty.
    - now apply (proj2 m.(support_spec)).
  Defined.

  Lemma find_empty : forall k, find k empty = Value.empty.
  Proof. reflexivity. Qed.

  Lemma find_add_eq : forall m x k k',
    find k' (add k x m) =
      if Key.eq_dec k k' then Value.op x (find k' m) else find k' m.
  Proof. reflexivity. Qed.

  Lemma find_remove_eq : forall m k k',
    find k' (remove k m) =
      if Key.eq_dec k k' then Value.empty else find k' m.
  Proof. reflexivity. Qed.

  Lemma keys_complete : forall m k,
    find k m <> Value.empty -> In k (keys m).
  Proof.
    intros m k Hfind. unfold find, keys.
    destruct (in_dec Key.eq_dec k m.(support)); [assumption|].
    exfalso. apply Hfind. now apply (proj2 m.(support_spec)).
  Qed.

  Lemma lookup_notin_support : forall m k,
    ~ In k m.(support) -> m.(lookup) k = Value.empty.
  Proof. intros m k Hnotin. now apply (proj2 m.(support_spec)). Qed.
End RawMake.

(* The public functor seals the representation.  RawMake is kept available to
   the list specialization, whose proofs use the concrete support operations. *)
Module Make (Key : DecidableType) (Value : Monoid) : FiniteMapSig Key Value :=
  RawMake Key Value.
