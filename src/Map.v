Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import FMV.FiniteMap.

Module Type ValueType.
  Parameter t : Type.
End ValueType.

(* Left-biased option composition: the first present value wins. *)
Module OptionMonoid (Value : ValueType) <: Monoid.
  Definition t := option Value.t.
  Definition empty : t := None.
  Definition op (x y : t) : t :=
    match x with
    | None => y
    | Some _ => x
    end.

  Lemma op_assoc : forall x y z, op x (op y z) = op (op x y) z.
  Proof. intros [x|] y z; reflexivity. Qed.

  Lemma op_empty_l : forall x, op empty x = x.
  Proof. reflexivity. Qed.

  Lemma op_empty_r : forall x, op x empty = x.
  Proof. intros [x|]; reflexivity. Qed.
End OptionMonoid.

Module Type MapSig (Key : OrderedKey) (Value : ValueType).
  Parameter t : Type.
  Parameter empty : t.
  Parameter find : Key.t -> t -> option Value.t.
  Parameter keys : t -> list Key.t.
  Parameter maximum : t -> option Key.t.
  Parameter add : Key.t -> Value.t -> t -> t.
  Parameter remove : Key.t -> t -> t.

  Axiom find_empty : forall k, find k empty = None.
  Axiom find_add_eq : forall m x k k',
    find k' (add k x m) =
      if Key.eq_dec k k' then Some x else find k' m.
  Axiom find_remove_eq : forall m k k',
    find k' (remove k m) =
      if Key.eq_dec k k' then None else find k' m.
  Axiom keys_nodup : forall m, NoDup (keys m).
  Axiom keys_complete : forall m k,
    find k m <> None <-> In k (keys m).
  Axiom maximum_none : forall m,
    maximum m = None -> keys m = [].
  Axiom maximum_upper : forall m greatest k,
    maximum m = Some greatest -> In k (keys m) -> ~ Key.lt greatest k.
End MapSig.

Module Make (Key : OrderedKey) (Value : ValueType) : MapSig Key Value.
  Module OptionMonoid' := OptionMonoid Value.
  Module Base := FiniteMap.RawMake Key OptionMonoid'.

  Definition t := Base.t.
  Definition empty : t := Base.empty.
  Definition find (k : Key.t) (m : t) : option Value.t := Base.find k m.
  Definition add (k : Key.t) (x : Value.t) (m : t) : t :=
    Base.add k (Some x) m.
  Definition remove (k : Key.t) (m : t) : t := Base.remove k m.

  Definition present (x : option Value.t) : bool :=
    match x with
    | Some _ => true
    | None => false
    end.

  Definition keys (m : t) : list Key.t :=
    filter (fun k => present (find k m)) (Base.keys m).
  Definition maximum (m : t) : option Key.t := Base.maximum m.

  Lemma find_empty : forall k, find k empty = None.
  Proof. exact Base.find_empty. Qed.

  Lemma find_add_eq : forall m x k k',
    find k' (add k x m) =
      if Key.eq_dec k k' then Some x else find k' m.
  Proof.
    intros m x k k'. unfold find, add. rewrite Base.find_add_eq.
    destruct (Key.eq_dec k k'); reflexivity.
  Qed.

  Lemma find_remove_eq : forall m k k',
    find k' (remove k m) =
      if Key.eq_dec k k' then None else find k' m.
  Proof. exact Base.find_remove_eq. Qed.

  Lemma keys_nodup : forall m, NoDup (keys m).
  Proof.
    intros m. unfold keys. apply NoDup_filter.
    apply Base.keys_nodup.
  Qed.

  Lemma keys_complete : forall m k,
    find k m <> None <-> In k (keys m).
  Proof.
    intros m k. unfold keys. rewrite filter_In. split.
    - intros Hfind. split; [now apply Base.keys_complete|].
      destruct (find k m); [reflexivity|contradiction].
    - intros [_ Hpresent]. destruct (find k m); discriminate.
  Qed.

  Lemma maximum_none : forall m,
    maximum m = None -> keys m = [].
  Proof.
    intros m Hmaximum. unfold maximum in Hmaximum.
    pose proof (Base.maximum_spec m) as Hspec. rewrite Hmaximum in Hspec.
    unfold keys. now rewrite Hspec.
  Qed.

  Lemma maximum_upper : forall m greatest k,
    maximum m = Some greatest -> In k (keys m) -> ~ Key.lt greatest k.
  Proof.
    intros m greatest k Hmaximum Hin.
    unfold maximum in Hmaximum.
    pose proof (Base.maximum_spec m) as Hspec. rewrite Hmaximum in Hspec.
    destruct Hspec as [_ Hgreatest]. apply Hgreatest.
    unfold keys in Hin. now apply filter_In in Hin.
  Qed.
End Make.
