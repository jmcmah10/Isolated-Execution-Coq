From Coq Require Import FSets.FMapList.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.

Require Import OrderedType.
Require Import ZArith_base.
Require Import PeanoNat.
Require Import Ascii String.
Require Import NArith Ndec.

Require Import RuntimeDefinitions.

Definition nat_map : Type := NatMap.t nat.

Require Import Coq.FSets.FMapFacts.
Module P := WProperties_fun Nat_as_OT NatMap.

Definition enclave_contains (id: raw_enclave_ID) (e: enclave_ID) : Prop :=
  match e with
  | enclave_ID_active x => (eq x id)
  | enclave_ID_inactive => False
  end.

Definition contains_one (test_map : nat_map) : Prop :=
  if NatMap.find 1 test_map then True else False.

(*
Fixpoint all_zeroes (l: nat_map) : Prop :=
  match l with
  | 
  end.
Compute (NatMap.fold (NatMap.add 2 2 (NatMap.add 1 1 (NatMap.empty nat)))).
*)

Compute (NatMap.empty nat).
Compute (NatMap.add 1 1 (NatMap.empty nat)).
Compute (NatMap.add 2 2 (NatMap.add 1 1 (NatMap.empty nat))).
Compute (NatMap.add 1 2 (NatMap.add 1 1 (NatMap.empty nat))).
Compute (NatMap.remove 1 (NatMap.add 2 2 (NatMap.add 1 1 (NatMap.empty nat)))).
Compute (NatMap.find 1 (NatMap.add 2 20 (NatMap.add 1 10 (NatMap.empty nat)))).
Compute (NatMap.find 3 (NatMap.add 2 2 (NatMap.add 1 1 (NatMap.empty nat)))).
Compute (P.for_all (fun _ v => v =? 0) (NatMap.add 2 0 (NatMap.add 1 0 (NatMap.empty nat)))).
Compute (P.for_all (fun _ v => v =? 0) (NatMap.add 2 1 (NatMap.add 1 0 (NatMap.empty nat)))).


Compute P.to_list (NatMap.add 3 3 (NatMap.add 2 2 (NatMap.add 1 1 (NatMap.empty nat)))).
Compute length (P.to_list (NatMap.add 3 3 (NatMap.add 2 2 (NatMap.add 1 1 (NatMap.empty nat))))).


Lemma test : forall (test_map : nat_map), contains_one (NatMap.add 1 1 test_map).
Proof.
  intros.
Admitted.

Compute (PairMap.add (0, 0) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (PairMap.empty way_set_cache_value)).
Compute (PairMap.add (0, 0) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (
  PairMap.add (0, 3) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (PairMap.empty way_set_cache_value))).
Compute (PairMap.add (0, 0) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (
  PairMap.add (0, 3) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (
  PairMap.add (1, 1) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (
  PairMap.add (2, 0) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (PairMap.empty way_set_cache_value))))).

Compute (PairMap.find (1, 1) (PairMap.add (0, 0) (valid_bit_tag_and_data dirty_bit 8 (NatMap.empty data)) (
  PairMap.add (0, 3) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (
  PairMap.add (1, 1) (valid_bit_tag_and_data dirty_bit 6 (NatMap.empty data)) (
  PairMap.add (2, 0) (valid_bit_tag_and_data dirty_bit 5 (NatMap.empty data)) (PairMap.empty way_set_cache_value)))))).
Compute (PairMap.find (2, 1) (PairMap.add (0, 0) (valid_bit_tag_and_data dirty_bit 8 (NatMap.empty data)) (
  PairMap.add (0, 3) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (
  PairMap.add (1, 1) (valid_bit_tag_and_data dirty_bit 6 (NatMap.empty data)) (
  PairMap.add (2, 0) (valid_bit_tag_and_data dirty_bit 5 (NatMap.empty data)) (PairMap.empty way_set_cache_value)))))).

Module Nat_as_OT2 <: UsualOrderedType.

  Definition t := nat.

  Definition eq := @eq nat.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt := lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt; intros; apply lt_trans with y; auto. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq. intros ?. intros ?. intros LT. intros ->. revert LT. apply Nat.lt_irrefl. Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    case_eq (Nat.compare x y); intro.
    - apply EQ. now apply nat_compare_eq.
    - apply LT. now apply nat_compare_Lt_lt.
    - apply GT. now apply nat_compare_Gt_gt.
  Defined.

  Definition eq_dec := eq_nat_dec.

End Nat_as_OT2.

Module PairOrderedType(O1 O2:OrderedType) <: OrderedType.
 Module MO1:=OrderedTypeFacts(O1).
 Module MO2:=OrderedTypeFacts(O2).

 Definition t := prod O1.t O2.t.

 Definition eq x y := O1.eq (fst x) (fst y) /\ O2.eq (snd x) (snd y).

 Definition lt x y :=
    O1.lt (fst x) (fst y) \/
    (O1.eq (fst x) (fst y) /\ O2.lt (snd x) (snd y)).

 Lemma eq_refl : forall x : t, eq x x.
 Proof.
 intros (x1,x2). red. simpl. auto with ordered_type.
 Qed.

 Lemma eq_sym : forall x y : t, eq x y -> eq y x.
 Proof.
 intros (x1,x2) (y1,y2); unfold eq; simpl; intuition.
 Qed.

 Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
 Proof.
 intros (x1,x2) (y1,y2) (z1,z2); unfold eq; simpl; intuition eauto with ordered_type.
 Qed.

 Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
 Proof.
 intros (x1,x2) (y1,y2) (z1,z2); unfold eq, lt; simpl; intuition.
 left; eauto with ordered_type.
 left; eapply MO1.lt_eq; eauto.
 left; eapply MO1.eq_lt; eauto.
 right; split; eauto with ordered_type.
 Qed.

 Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 Proof.
 intros (x1,x2) (y1,y2); unfold eq, lt; simpl; intuition.
 apply (O1.lt_not_eq H0 H1).
 apply (O2.lt_not_eq H3 H2).
 Qed.

 Definition compare : forall x y : t, Compare lt eq x y.
 intros (x1,x2) (y1,y2).
 destruct (O1.compare x1 y1).
 apply LT; unfold lt; auto.
 destruct (O2.compare x2 y2).
 apply LT; unfold lt; auto.
 apply EQ; unfold eq; auto.
 apply GT; unfold lt; auto with ordered_type.
 apply GT; unfold lt; auto.
 Defined.

 Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
 Proof.
 intros; elim (compare x y); intro H; [ right | left | right ]; auto.
 auto using lt_not_eq.
 assert (~ eq y x); auto using lt_not_eq, eq_sym.
 Defined.

End PairOrderedType.







