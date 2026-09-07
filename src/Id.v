Require Import Stdlib.Arith.PeanoNat.
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

  Parameter next : t -> t.
  Axiom next_strict : forall x, to_nat x < to_nat (next x).

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

  Definition next (x : t) : t := S x.
  Lemma next_strict : forall x, to_nat x < to_nat (next x).
  Proof. intros x. unfold to_nat, next. lia. Qed.

End Id.
