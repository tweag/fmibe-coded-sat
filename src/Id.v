Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Module Type S.
  Parameter t : Type.

  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  Parameter eqb : t -> t -> bool.
  Axiom eqb_refl : forall x, eqb x x = true.
  Axiom eqb_eq : forall x y, eqb x y = true <-> x = y.
  Axiom eqb_neq : forall x y, eqb x y = false <-> x <> y.

  Parameter of_nat : nat -> t.
  Parameter to_nat : t -> nat.
  Axiom to_nat_of_nat : forall n, to_nat (of_nat n) = n.
  Axiom of_nat_to_nat : forall x, of_nat (to_nat x) = x.

  Parameter fresh : list t -> t.
  Axiom fresh_not_in : forall ids, ~ In (fresh ids) ids.
End S.

(* Keep the representation private so clients use only the identifier
   operations above.  Extraction can still implement this module with OCaml
   integers. *)
Module Id : S.
  Definition t := nat.

  Definition eq_dec := Nat.eq_dec.
  Definition eqb := Nat.eqb.
  Lemma eqb_refl : forall x, eqb x x = true.
  Proof. exact Nat.eqb_refl. Qed.
  Lemma eqb_eq : forall x y, eqb x y = true <-> x = y.
  Proof. exact Nat.eqb_eq. Qed.
  Lemma eqb_neq : forall x y, eqb x y = false <-> x <> y.
  Proof. exact Nat.eqb_neq. Qed.

  Definition of_nat (n : nat) : t := n.
  Definition to_nat (x : t) : nat := x.
  Lemma to_nat_of_nat : forall n, to_nat (of_nat n) = n.
  Proof. reflexivity. Qed.
  Lemma of_nat_to_nat : forall x, of_nat (to_nat x) = x.
  Proof. reflexivity. Qed.

  Lemma fold_max_ge : forall xs x,
    In x xs -> x <= fold_right Nat.max 0 xs.
  Proof.
    intros xs. induction xs as [|y ys IH]; intros x Hin; [contradiction|].
    simpl. destruct Hin as [->|Hin].
    - apply Nat.le_max_l.
    - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
  Qed.

  Definition fresh (ids : list t) : t :=
    S (fold_right Nat.max 0 ids).

  Lemma fresh_not_in : forall ids, ~ In (fresh ids) ids.
  Proof.
    intros ids Hin. unfold fresh in Hin.
    pose proof (fold_max_ge _ _ Hin). lia.
  Qed.
End Id.
