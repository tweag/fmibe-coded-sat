(* The core loop of a CDCL-based SAT solver *)

Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.

Definition Var := nat.
Variant Literal :=
  | Pos (l : Var)
  | Neg (l : Var)
.
Definition Clause := list Literal.

Definition Problem := list Clause.

(* A partial model. The semantics is that `Pos` literals in the list are known
   to be true, `Neg` literals are known to be false. The rest is (yet)
   undecided. *)
Definition Model := list Literal.

Definition literal_eq_dec (l r : Literal) : {l = r} + {l <> r}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition clause_eq_dec : forall l r : Clause, {l = r} + {l <> r} :=
  list_eq_dec literal_eq_dec.

Module Type ClauseMapSig.
  Parameter t : Type.

  Parameter empty : t.
  Parameter find : Var -> t -> list Clause.
  Parameter keys : t -> list Var.
  Parameter add : Var -> Clause -> t -> t.
  Parameter remove : Var -> t -> t.
  Parameter remove_clause : Clause -> t -> t.
  Parameter card_of : Clause -> t -> nat.
  Parameter elements : t -> list Clause.

  Axiom find_empty : forall v, find v empty = [].
  Axiom card_of_empty : forall c, card_of c empty = 0.
  Axiom keys_complete : forall m v, find v m <> [] <-> In v (keys m).
  Axiom find_add : forall m c d v x,
    In d (find x (add v c m)) <->
    (x = v /\ d = c) \/ In d (find x m).
  Axiom find_add_eq : forall m c v x,
    find x (add v c m) =
      if Nat.eq_dec v x then c :: find x m else find x m.
  Axiom card_of_add : forall m c v,
    card_of c (add v c m) = S (card_of c m).
  Axiom card_of_add_neq : forall m c d v,
    c <> d -> card_of d (add v c m) = card_of d m.
  Axiom card_of_remove : forall m c v,
    card_of c (remove v m) + count_occ clause_eq_dec (find v m) c =
      card_of c m.
  Axiom card_of_remove_clause_eq : forall m c,
    card_of c (remove_clause c m) = 0.
  Axiom card_of_remove_clause_neq : forall m c d,
    c <> d -> card_of d (remove_clause c m) = card_of d m.
  Axiom card_of_unique : forall m c v v',
    card_of c m = 1 -> In c (find v m) -> In c (find v' m) -> v = v'.
  Axiom card_of_in : forall m c v, In c (find v m) -> card_of c m > 0.
  Axiom find_remove : forall m v d v',
    In d (find v (remove v' m)) <-> In d (find v m) /\ v <> v'.
  Axiom find_remove_eq : forall m v v',
    find v (remove v' m) =
      if Nat.eq_dec v' v then [] else find v m.
  Axiom find_remove_clause : forall m c d v,
    In d (find v (remove_clause c m)) <-> In d (find v m) /\ d <> c.
  Axiom find_remove_clause_eq : forall m c v,
    find v (remove_clause c m) =
      filter (fun c' => if clause_eq_dec c c' then false else true) (find v m).
  Axiom elements_spec : forall m c,
    In c (elements m) <-> exists v, In v (keys m) /\ In c (find v m).
End ClauseMapSig.

(* Clauses indexed by variable. An empty list represents an absent entry. An
   explicit support makes it possible to enumerate the finite map. *)
Module ClauseMap : ClauseMapSig.
  Record representation := make {
      lookup : Var -> list Clause;
      support : list Var;
      support_spec : NoDup support /\
        forall v, lookup v <> [] <-> In v support
    }.
  Definition t := representation.

  Definition find (v : Var) (m : t) : list Clause := m.(lookup) v.
  Definition keys (m : t) : list Var := m.(support).

  Definition empty : t.
  Proof.
    refine {| lookup := fun _ => []; support := [] |}.
    split; [constructor|]. intros v. split; intros H; contradiction.
  Defined.

  Definition add (v : Var) (c : Clause) (m : t) : t.
  Proof.
    refine
      {| lookup := fun v' =>
           if Nat.eq_dec v v' then c :: m.(lookup) v' else m.(lookup) v';
         support := if in_dec Nat.eq_dec v m.(support)
           then m.(support) else v :: m.(support) |}.
    split.
    - destruct (in_dec Nat.eq_dec v m.(support)).
      + exact (proj1 m.(support_spec)).
      + constructor; [assumption|exact (proj1 m.(support_spec))].
    - intros v'.
    destruct (Nat.eq_dec v v') as [-> | Hneq].
      + simpl. split; [|intros _; discriminate].
        intros _. destruct (in_dec Nat.eq_dec v' m.(support)); [assumption|now left].
      + simpl. destruct (Nat.eq_dec v v') as [Heq | _]; [contradiction|].
        rewrite (proj2 m.(support_spec) v').
        destruct (in_dec Nat.eq_dec v m.(support)); simpl; intuition congruence.
  Defined.

  Definition remove_from (c : Clause) (cs : list Clause) : list Clause :=
    filter (fun c' => if clause_eq_dec c c' then false else true) cs.

  Definition nonempty (cs : list Clause) : bool :=
    match cs with
    | [] => false
    | _ :: _ => true
    end.

  Definition remove (v : Var) (m : t) : t.
  Proof.
    refine
      {| lookup := fun v' => if Nat.eq_dec v v' then [] else m.(lookup) v';
         support := filter (fun v' => negb (Nat.eqb v v')) m.(support) |}.
    split; [apply NoDup_filter; exact (proj1 m.(support_spec))|].
    intros v'.
    destruct (Nat.eq_dec v v') as [->|Hneq].
    - simpl. split.
      + intros H. contradiction.
      + intros H. apply filter_In in H as [_ Hneqb].
        rewrite Nat.eqb_refl in Hneqb. discriminate.
    - assert (Nat.eqb v v' = false) as Heqb by now apply Nat.eqb_neq.
      simpl. destruct (Nat.eq_dec v v') as [Heq|_]; [contradiction|].
      rewrite filter_In, Heqb. simpl.
      rewrite (proj2 m.(support_spec) v'). tauto.
  Defined.

  Definition remove_clause (c : Clause) (m : t) : t.
  Proof.
    refine
      {| lookup := fun v =>
           remove_from c (m.(lookup) v);
         support := filter
           (fun v => nonempty (remove_from c (m.(lookup) v)))
           m.(support) |}.
    split; [apply NoDup_filter; exact (proj1 m.(support_spec))|].
    intros v. split.
    - intros H.
      apply filter_In. split.
      + apply (proj2 m.(support_spec)). intro Heq.
        rewrite Heq in H. exact (H eq_refl).
      + destruct (remove_from c (m.(lookup) v)); [contradiction|reflexivity].
    - intros H.
      apply filter_In in H as [_ Hnonempty].
      destruct (remove_from c (m.(lookup) v)); discriminate.
  Defined.

  Definition elements (m : t) : list Clause :=
    flat_map m.(lookup) m.(support).

  Definition card_of (c : Clause) (m : t) : nat :=
    count_occ clause_eq_dec (elements m) c.

  Lemma find_empty : forall v, find v empty = [].
  Proof. reflexivity. Qed.

  Lemma card_of_empty : forall c, card_of c empty = 0.
  Proof. reflexivity. Qed.

  Lemma keys_complete : forall m v, find v m <> [] <-> In v (keys m).
  Proof. intros m v. exact (proj2 m.(support_spec) v). Qed.

  Lemma lookup_notin_support : forall m v,
    ~ In v m.(support) -> m.(lookup) v = [].
  Proof.
    intros m v Hnotin. destruct (m.(lookup) v) as [|c cs] eqn:Hlookup;
      [reflexivity|].
    exfalso. apply Hnotin. apply (proj2 m.(support_spec) v).
    rewrite Hlookup. discriminate.
  Qed.

  Lemma find_add : forall m c d v x,
    In d (find x (add v c m)) <->
    (x = v /\ d = c) \/ In d (find x m).
  Proof.
    intros m c d v x. unfold find, add. simpl.
    destruct (Nat.eq_dec v x) as [->|Hneq]; simpl.
    - firstorder.
    - split; [now right|]. intros [[Heq _]|H]; [congruence|exact H].
  Qed.

  Lemma find_add_eq : forall m c v x,
    find x (add v c m) =
      if Nat.eq_dec v x then c :: find x m else find x m.
  Proof. reflexivity. Qed.

  Lemma count_occ_flat_map_add_absent : forall vs f v c d,
    ~ In v vs ->
    count_occ clause_eq_dec
      (flat_map (fun x => if Nat.eq_dec v x then c :: f x else f x) vs) d =
    count_occ clause_eq_dec (flat_map f vs) d.
  Proof.
    intros vs. induction vs as [|x xs IH]; intros f v c d Hnotin; simpl.
    - reflexivity.
    - destruct (Nat.eq_dec v x) as [->|Hneq].
      + exfalso. apply Hnotin. now left.
      +
      rewrite !count_occ_app. rewrite IH; [reflexivity|].
      now intros Hin; apply Hnotin; right.
  Qed.

  Lemma count_occ_flat_map_add_present : forall vs f v c d,
    NoDup vs -> In v vs ->
    count_occ clause_eq_dec
      (flat_map (fun x => if Nat.eq_dec v x then c :: f x else f x) vs) d =
    count_occ clause_eq_dec [c] d +
      count_occ clause_eq_dec (flat_map f vs) d.
  Proof.
    intros vs. induction vs as [|x xs IH]; intros f v c d Hnodup Hin;
      [contradiction|].
    inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    simpl in Hin. cbn [flat_map].
    destruct (Nat.eq_dec v x) as [->|Hneq].
    - destruct (Nat.eq_dec x x) as [_|Habs]; [|contradiction].
      rewrite !count_occ_app.
      rewrite (count_occ_flat_map_add_absent xs f x c d Hnotin).
      destruct (clause_eq_dec c d) eqn:Hcd; simpl; rewrite Hcd; simpl; lia.
    - destruct (Nat.eq_dec v x) as [Habs|_]; [contradiction|].
      rewrite !count_occ_app, IH; [lia|exact Hnodup'|].
      destruct Hin as [Heq|Hin]; [congruence|exact Hin].
  Qed.

  Lemma card_of_add : forall m c v,
    card_of c (add v c m) = S (card_of c m).
  Proof.
    intros m c v. unfold card_of, elements, add. simpl.
    destruct (in_dec Nat.eq_dec v m.(support)) as [Hin|Hnotin].
    - rewrite count_occ_flat_map_add_present;
        [|exact (proj1 m.(support_spec))|exact Hin].
      simpl. destruct (clause_eq_dec c c) eqn:Hcc;
        [simpl; reflexivity|contradiction].
    - simpl. destruct (Nat.eq_dec v v) as [_|Habs]; [|contradiction].
      rewrite (lookup_notin_support m v Hnotin).
      rewrite !count_occ_app, count_occ_flat_map_add_absent by exact Hnotin.
      simpl. destruct (clause_eq_dec c c) eqn:Hcc;
        [simpl; reflexivity|contradiction].
  Qed.

  Lemma card_of_add_neq : forall m c d v,
    c <> d -> card_of d (add v c m) = card_of d m.
  Proof.
    intros m c d v Hneq. unfold card_of, elements, add. simpl.
    destruct (in_dec Nat.eq_dec v m.(support)) as [Hin|Hnotin].
    - rewrite count_occ_flat_map_add_present;
        [|exact (proj1 m.(support_spec))|exact Hin].
      simpl. destruct (clause_eq_dec c d) eqn:Hcd;
        [contradiction|simpl; reflexivity].
    - simpl. destruct (Nat.eq_dec v v) as [_|Habs]; [|contradiction].
      rewrite (lookup_notin_support m v Hnotin).
      rewrite !count_occ_app, count_occ_flat_map_add_absent by exact Hnotin.
      simpl. destruct (clause_eq_dec c d) eqn:Hcd;
        [contradiction|simpl; reflexivity].
  Qed.

  Lemma filter_remove_absent : forall vs v,
    ~ In v vs -> filter (fun v' => negb (Nat.eqb v v')) vs = vs.
  Proof.
    intros vs. induction vs as [|x xs IH]; intros v Hnotin; simpl.
    - reflexivity.
    - destruct (v =? x) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst. exfalso. apply Hnotin. now left.
      + simpl. f_equal. apply IH. intros Hin. apply Hnotin. now right.
  Qed.

  Lemma flat_map_remove_absent : forall (vs : list Var)
      (f : Var -> list Clause) v,
    ~ In v vs ->
    flat_map (fun x => if Nat.eq_dec v x then [] else f x) vs = flat_map f vs.
  Proof.
    intros vs. induction vs as [|x xs IH]; intros f v Hnotin; simpl.
    - reflexivity.
    - destruct (Nat.eq_dec v x) as [->|Hneq].
      + exfalso. apply Hnotin. now left.
      + f_equal. apply IH. intros Hin. apply Hnotin. now right.
  Qed.

  Lemma card_of_remove : forall m c v,
    card_of c (remove v m) + count_occ clause_eq_dec (find v m) c =
      card_of c m.
  Proof.
    intros m c v. unfold card_of, elements, find, remove. simpl.
    destruct (in_dec Nat.eq_dec v m.(support)) as [Hin|Hnotin].
    - apply in_split in Hin as [before [after Hsupport]].
      pose proof (proj1 m.(support_spec)) as Hnodup.
      rewrite Hsupport in Hnodup |- *.
      rewrite filter_app. simpl. rewrite Nat.eqb_refl. simpl.
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
      set (nb := count_occ clause_eq_dec (flat_map m.(lookup) before) c).
      set (nv := count_occ clause_eq_dec (m.(lookup) v) c).
      set (na := count_occ clause_eq_dec (flat_map m.(lookup) after) c).
      change (nb + na + nv = nb + (nv + na)). lia.
    - rewrite (filter_remove_absent m.(support) v Hnotin).
      erewrite flat_map_remove_absent by exact Hnotin.
      rewrite (lookup_notin_support m v Hnotin). simpl. lia.
  Qed.

  Lemma flat_map_filter_nonempty : forall (vs : list Var)
      (f : Var -> list Clause),
    flat_map f (filter (fun v => nonempty (f v)) vs) = flat_map f vs.
  Proof.
    intros vs. induction vs as [|v vs IH]; intros f; simpl.
    - reflexivity.
    - destruct (f v) as [|x xs] eqn:Hf; simpl.
      + rewrite IH. reflexivity.
      + rewrite Hf, IH. reflexivity.
  Qed.

  Lemma count_occ_remove_from_eq : forall cs c,
    count_occ clause_eq_dec (remove_from c cs) c = 0.
  Proof.
    intros cs. induction cs as [|d cs IH]; intros c; simpl.
    - reflexivity.
    - destruct (clause_eq_dec c d) as [->|Hneq]; simpl.
      + exact (IH d).
      + destruct (clause_eq_dec d c) as [Heq|_]; [congruence|]. exact (IH c).
  Qed.

  Lemma count_occ_remove_from_neq : forall cs c d,
    c <> d ->
    count_occ clause_eq_dec (remove_from c cs) d = count_occ clause_eq_dec cs d.
  Proof.
    intros cs. induction cs as [|x xs IH]; intros c d Hneq; simpl.
    - reflexivity.
    - destruct (clause_eq_dec c x) as [->|Hcx]; simpl.
      + destruct (clause_eq_dec x d) as [Heq|_]; [congruence|].
        apply IH. exact Hneq.
      + destruct (clause_eq_dec x d); simpl; rewrite IH by exact Hneq;
          reflexivity.
  Qed.

  Lemma card_of_remove_clause_eq : forall m c,
    card_of c (remove_clause c m) = 0.
  Proof.
    intros m c. unfold card_of, elements, remove_clause. simpl.
    rewrite flat_map_filter_nonempty.
    induction m.(support) as [|v vs IH]; simpl; [reflexivity|].
    rewrite count_occ_app, count_occ_remove_from_eq, IH. reflexivity.
  Qed.

  Lemma card_of_remove_clause_neq : forall m c d,
    c <> d -> card_of d (remove_clause c m) = card_of d m.
  Proof.
    intros m c d Hneq. unfold card_of, elements, remove_clause. simpl.
    rewrite flat_map_filter_nonempty.
    induction m.(support) as [|v vs IH]; simpl; [reflexivity|].
    rewrite !count_occ_app, count_occ_remove_from_neq by exact Hneq.
    now rewrite IH.
  Qed.

  Lemma card_of_unique : forall m c v v',
    card_of c m = 1 -> In c (find v m) -> In c (find v' m) -> v = v'.
  Proof.
    intros m c v v' Hcard Hv Hv'. destruct (Nat.eq_dec v v') as [->|Hneq];
      [reflexivity|exfalso].
    assert (In v m.(support)) as Hvs.
    { apply keys_complete. intro Hempty. rewrite Hempty in Hv. contradiction. }
    assert (In v' m.(support)) as Hvs'.
    { apply keys_complete. intro Hempty. rewrite Hempty in Hv'. contradiction. }
    apply in_split in Hvs as [before [after Hsupport]].
    assert (In v' (before ++ after)) as Hv'rest.
    { rewrite Hsupport in Hvs'.
      apply in_app_or in Hvs' as [Hin|Hin].
      - now apply in_or_app; left.
      - simpl in Hin. destruct Hin as [Heq|Hin]; [congruence|].
        now apply in_or_app; right. }
    assert (In c (flat_map m.(lookup) (before ++ after))) as Hcrest.
    { apply in_flat_map. exists v'. split; [exact Hv'rest|exact Hv']. }
    unfold find in Hv, Hv'.
    apply (proj1 (count_occ_In clause_eq_dec _ _)) in Hv.
    apply (proj1 (count_occ_In clause_eq_dec _ _)) in Hcrest.
    unfold card_of, elements, find in Hcard, Hv'.
    rewrite Hsupport, flat_map_app in Hcard. cbn [flat_map] in Hcard.
    rewrite !count_occ_app in Hcard.
    rewrite flat_map_app, count_occ_app in Hcrest. lia.
  Qed.

  Lemma card_of_in : forall m c v, In c (find v m) -> card_of c m > 0.
  Proof.
    intros m c v Hin. unfold card_of. apply count_occ_In.
    unfold elements. apply in_flat_map. exists v. split; [|exact Hin].
    apply keys_complete.
    intros Hempty. rewrite Hempty in Hin. contradiction.
  Qed.

  Lemma find_remove : forall m v d v',
    In d (find v (remove v' m)) <-> In d (find v m) /\ v <> v'.
  Proof.
    intros m v d v'. unfold find, remove. simpl.
    destruct (Nat.eq_dec v' v) as [->|Hneq].
    - simpl. firstorder.
    - simpl. firstorder congruence.
  Qed.

  Lemma find_remove_eq : forall m v v',
    find v (remove v' m) =
      if Nat.eq_dec v' v then [] else find v m.
  Proof. reflexivity. Qed.

  Lemma find_remove_clause : forall m c d v,
    In d (find v (remove_clause c m)) <-> In d (find v m) /\ d <> c.
  Proof.
    intros m c d v. unfold find, remove_clause. simpl. unfold remove_from.
    rewrite filter_In.
    destruct (clause_eq_dec c d) as [->|Hneq].
    - destruct (clause_eq_dec d d) as [_|Habs]; [|contradiction].
      simpl. intuition congruence.
    - destruct (clause_eq_dec c d) as [Habs|_]; [contradiction|].
      simpl. intuition congruence.
  Qed.

  Lemma find_remove_clause_eq : forall m c v,
    find v (remove_clause c m) =
      filter (fun c' => if clause_eq_dec c c' then false else true) (find v m).
  Proof. reflexivity. Qed.

  Lemma elements_spec : forall m c,
    In c (elements m) <-> exists v, In v (keys m) /\ In c (find v m).
  Proof.
    intros m c. unfold elements, keys, find. apply in_flat_map.
  Qed.
End ClauseMap.

Record State := {
  state_model : Model;
  (*  `state_clauses` implements two-literal watch*)
  state_clauses : ClauseMap.t;
  state_satisfied : list Clause;
  state_falsified : list Clause;
  state_pending : list Clause;
}.

Definition literal_var (l : Literal) : Var :=
  match l with
  | Pos v | Neg v => v
  end.

Definition var_is_assigned (m : Model) (v : Var) : bool :=
  existsb (fun l => Nat.eqb (literal_var l) v) m.

Definition literal_value (m : Model) (l : Literal) : option bool :=
  match find (fun l' => Nat.eqb (literal_var l') (literal_var l)) m with
  | None => None
  | Some (Pos _) =>
      match l with Pos _ => Some true | Neg _ => Some false end
  | Some (Neg _) =>
      match l with Pos _ => Some false | Neg _ => Some true end
  end.

Definition literal_is_true (m : Model) (l : Literal) : bool :=
  match literal_value m l with Some true => true | _ => false end.

Definition literal_is_undecided (m : Model) (l : Literal) : bool :=
  match literal_value m l with None => true | _ => false end.

Fixpoint scan_clause_once (m : Model) (c : Clause) : bool * list Literal :=
  match c with
  | [] => (false, [])
  | l :: c' =>
      let '(satisfied, undecided) := scan_clause_once m c' in
      (orb (literal_is_true m l) satisfied,
       if literal_is_undecided m l then l :: undecided else undecided)
  end.

Variant scan_result :=
  | propagate_literal (l : Literal)
  | clause_decided (cm : ClauseMap.t) (sat fals : list Clause)
  | clause_watched (cm : ClauseMap.t).

Fixpoint find_different_var (v : Var) (ls : list Literal) : option Literal :=
  match ls with
  | [] => None
  | l :: ls' =>
      if Nat.eqb v (literal_var l) then find_different_var v ls' else Some l
  end.

(* Is [c] satisfied? falsified? otherwise watch an additional literal *)
Definition scan_clause (m : Model) (c : Clause)
    (cm : ClauseMap.t) (sat fals : list Clause) : scan_result :=
  let '(satisfied, undecided) := scan_clause_once m c in
  if satisfied then
      clause_decided (ClauseMap.remove_clause c cm) (c :: sat) fals
  else
    match undecided with
    | [] => clause_decided (ClauseMap.remove_clause c cm) sat (c :: fals)
    | l :: undecided' =>
        match find_different_var (literal_var l) undecided' with
        | None => propagate_literal l
        | Some l' =>
            if in_dec clause_eq_dec c (ClauseMap.find (literal_var l) cm) then
              clause_watched (ClauseMap.add (literal_var l') c cm)
            else clause_watched (ClauseMap.add (literal_var l) c cm)
        end
    end.

Definition set_lit (l : Literal) (m : State) : State :=
  let watched := ClauseMap.find (literal_var l) m.(state_clauses) in
  let cm := ClauseMap.remove (literal_var l) m.(state_clauses) in
  let pending := watched ++ m.(state_pending) in
  {| state_model := l :: m.(state_model); 
     state_clauses := cm;
     state_satisfied := m.(state_satisfied);
     state_falsified := m.(state_falsified);
     state_pending := pending |}.

Definition remove_clause_from_list (c : Clause) (cs : list Clause) : list Clause :=
  filter (fun d => if clause_eq_dec c d then false else true) cs.

(* The fuel is initially larger than the number of literals in the problem.
   Every recursive call assigns a previously undecided literal. *)
Definition propagate (c : Clause) (s : State) : State :=
      match scan_clause s.(state_model) c s.(state_clauses) s.(state_satisfied) s.(state_falsified) with
      | propagate_literal l =>
          set_lit l
            {| state_model := s.(state_model);
               state_clauses := ClauseMap.remove_clause c s.(state_clauses);
               state_satisfied := c :: s.(state_satisfied);
               state_falsified := s.(state_falsified);
               state_pending :=
                 remove_clause_from_list c s.(state_pending) |}
      | clause_decided cm sat fals =>
          {| state_model := s.(state_model);
             state_clauses := cm;
             state_satisfied := sat;
             state_falsified := fals;
             state_pending := remove_clause_from_list c s.(state_pending) |}
      | clause_watched cm =>
          {| state_model := s.(state_model);
             state_clauses := cm;
             state_satisfied := s.(state_satisfied);
             state_falsified := s.(state_falsified);
             state_pending := s.(state_pending) |}
  end.

(* Game plan: to progress the state:
   - If there are pending clauses, find a new undecided literal to watch or propagate their only literal or mark the clause as satisfied or falsified.
   - Otherwise
     1. choose an undecided variable
     2. Set it to `true` in the model
     3. Wake up any clause currently watching this literal, make them all pending. *)
Definition progress (s : State) : State :=
  match s.(state_pending) with
  | c :: pending =>
      propagate c
        {| state_model := s.(state_model);
           state_clauses := s.(state_clauses);
           state_satisfied := s.(state_satisfied);
           state_falsified := s.(state_falsified);
           state_pending := pending |}
  | [] =>
      match hd_error (ClauseMap.keys s.(state_clauses)) with
      | None => s (* All the literal have been decided so no progress can be made *)
      | Some v =>
          set_lit (Pos v) s
      end
  end.

Definition is_empty {A} (l : list A) : bool :=
  match l with
  | [] => true
  | _ => false
  end.

(* TODO: Do I use *)
(* Guard structural arguments of recursive occurrences with [guard] to ensure
   normalisation when the guard condition check is bypassed. *)
Definition guard {A} (x:A) := x.
Lemma unguard : forall A (x:A), guard x = x.
Proof.
  reflexivity.
Qed.
Opaque guard.

(* Define arbitrary tail-recursive functions as co-fixpoint returning a [Delay
   A]. *)
CoInductive Delay A :=
 | Now (x:A)
 | Later (x:Delay A).
Arguments Now {A}.
Arguments Later {A}.

CoFixpoint rush (s : State) : Delay (option Model) :=
  if is_empty (s.(state_falsified)) then
    Now None
      (* TODO: add an is_empty predicate to ClauseMap directly *)
  else
    if is_empty (ClauseMap.keys s.(state_clauses)) then
      Now (Some s.(state_model))
    else
      Later (rush (progress s)).
    
