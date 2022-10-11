From Coq Require Import Lists.List.
From Coq Require Import FSets.FMapList.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require Import Structures.OrderedType.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Compare.
From Coq Require Import Bool.Bool.
Require Import Lia.

Module Import NatMap := FMapList.Make(Nat_as_OT).

(* Identifiers and Atomic Values *)
Definition core_ID := nat.
Definition physical_cache_unit_ID := nat.
Definition way_ID := nat.
Definition set_ID := nat.
Definition block_ID := nat.
Definition register_ID := nat.
Definition raw_enclave_ID := nat.
Definition data_offset := nat.
Definition cache_tag_value := nat.
Inductive memory_address :=
| address : block_ID -> data_offset -> memory_address.
Definition instruction := nat.
Definition number := nat.
Definition process_ID := nat.


(* Memory/Register-Related Structures *)
Inductive data : Type :=
| data_value : number -> data
| data_none : data.
Inductive memory_value : Type :=
| memory_value_instruction : instruction -> memory_value
| memory_value_data : data -> memory_value.


(* Enclave-Related Structures *)
Inductive enclave_memory_range_value :=
| enclave_address_and_data : memory_address -> data -> enclave_memory_range_value.
Inductive enclave_ID : Type :=
| enclave_ID_active : raw_enclave_ID -> enclave_ID
| enclave_ID_inactive : enclave_ID.
Definition enclave_memory_range : Type := NatMap.t enclave_memory_range_value.
Inductive enclave_state : Type := 
| enclave_state_value : enclave_ID -> enclave_memory_range -> enclave_state.


(* CC-Related Structures *)
Definition way_mask := list way_ID.
Inductive validity_bit : Type :=
| valid_bit : validity_bit
| dirty_bit : validity_bit.
Inductive cachelet_index : Type :=
| cachelet_index_value : way_ID -> set_ID -> cachelet_index.
Inductive nullable_cachelet_index : Type :=
| cachelet_index_defined : cachelet_index -> nullable_cachelet_index
| cachelet_index_none : nullable_cachelet_index.


(*
(* An ordered cachelet_index is needed *)
Module cachelet_index_as_OT <: UsualOrderedType.
  Definition t := cachelet_index.
  Definition lt_ci (x: t) (y: t) : Prop :=
  match x with
  | cachelet_index_value w1 s1 =>
    match y with
    | cachelet_index_value w2 s2 => ((lt w1 w2) \/ ((eq w1 w2) /\ (lt s1 s2)))
    end
  end.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt := lt_ci.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    destruct x, y, z.
    unfold lt, lt_ci in *.
    lia.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, lt_ci, eq.
    intros.
    intros ->.
    revert H.
    destruct y.
    lia.
  Qed.

  Definition comp (x: t) (y: t) : comparison :=
  match x, y with
  | cachelet_index_value wx sx, cachelet_index_value wy sy => 
    if (eqb wx wy) then (sx ?= sy) else (wx ?= wy)
  end.
  Notation "A ?=ci B" := (comp A B) (at level 70).

  Lemma contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
  Proof. intros. intro contra. apply H0. apply H. exact contra. Qed.

  Definition compare (x: t) (y: t) : Compare lt eq x y.
  Proof.
    case_eq (x ?=ci y); intros.
    - apply EQ.
      unfold comp in H.
      give_up.
    - apply LT.
      unfold comp in H.
      unfold lt, lt_ci.
    - apply GT. give_up.
  Qed.

  Definition eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.

End cachelet_index_as_OT.
*)

Module CI_as_OT <: OrderedType.
  Definition t := cachelet_index.
  Definition eq x y :=
  match x, y with
  | cachelet_index_value w0 s0, cachelet_index_value w1 s1 => w0 = w1 /\ s0 = s1
  end.
  Definition lt x y :=
  match x, y with
  | cachelet_index_value w0 s0, cachelet_index_value w1 s1 => w0 < w1 \/ (w0 = w1 /\ s0 < s1)
  end.
  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    intros. destruct x. unfold eq. auto.
  Qed.
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intros. destruct x, y.
    unfold eq in *.
    lia.
  Qed.
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros. destruct x, y, z.
    unfold eq in *.
    lia.
  Qed.
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros. destruct x, y, z.
    unfold lt in *.
    lia.
  Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros. destruct x, y.
    unfold lt, eq, not in *.
    lia.
  Qed.
  Definition comp (x: t) (y: t) : comparison :=
    match x, y with
    | cachelet_index_value wx sx, cachelet_index_value wy sy => 
      match (compare wx wy) with
      | Eq => (compare sx sy)
      | Lt => Lt
      | Gt => Gt
      end
    end.
  (*
  Definition comp (x: t) (y: t) : comparison :=
    match x, y with
    | cachelet_index_value wx sx, cachelet_index_value wy sy => 
      if (Nat.eqb wx wy) then (sx ?= sy) else (wx ?= wy)
    end.
  *)
  Lemma contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
  Proof. intros. intro contra. apply H0. apply H. exact contra. Qed.
  Notation "A ?=ci B" := (comp A B) (at level 70).
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y.
    case_eq (x ?=ci y).
    - intros H.
      destruct x, y.
      apply EQ.
      unfold comp in H.
      unfold eq.
      destruct (Nat.compare w w0).
      destruct (Nat.compare s s0).
      give_up.
      discriminate.
      discriminate.
      discriminate.
      discriminate.
    - intros H.
      destruct x, y.
      apply LT.
      unfold comp in H.
      unfold lt.
      destruct (Nat.compare w w0).
      destruct (Nat.compare s s0).
      discriminate.
      give_up.
      discriminate.
      give_up.
      discriminate.
    - intros H.
      destruct x, y.
      apply GT.
      unfold comp in H.
      unfold lt.
      destruct (Nat.compare w w0).
      destruct (Nat.compare s s0).
      discriminate.
      discriminate.
      give_up.
      discriminate.
      give_up.
  Admitted.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros. elim (compare x y); intro H; [ right | left | right ]; auto.
    auto using lt_not_eq.
    assert (~eq y x); auto using lt_not_eq, eq_sym.
  Qed.
End CI_as_OT.

(*
Module Import CacheletMap := FMapList.Make(cachelet_index_as_OT).
*)
Module Import CacheletMap := FMapList.Make(CI_as_OT).

Definition data_block := NatMap.t data.
Definition remapping_list := NatMap.t way_mask.
(* Extra structure to hold data in way_set_cache *)
Inductive way_set_cache_value : Type :=
| valid_bit_tag_and_data : validity_bit -> cache_tag_value -> data_block -> way_set_cache_value.
Definition way_set_cache := CacheletMap.t way_set_cache_value.
(* NEED A MAP HERE *)
Definition VPT := NatMap.t remapping_list.
Definition CAT := list cachelet_index.


(* PLRU-Related Structures *)
Inductive selection_bit : Type :=
| LMRU : selection_bit
| RMRU : selection_bit.
Inductive PLRU_leaf : Type :=
| leaf : way_ID -> enclave_ID -> PLRU_leaf.
Inductive PLRU_tree : Type :=
| subtree : selection_bit -> enclave_ID -> PLRU_tree -> PLRU_tree -> PLRU_tree
| subtree_leaf : PLRU_leaf -> PLRU_tree.
Definition set_indexed_PLRU := NatMap.t PLRU_tree.


(* Multi-Level Cache *)
Inductive single_level_cache_unit : Type :=
| single_level_cache : CAT -> VPT -> way_set_cache -> set_indexed_PLRU -> single_level_cache_unit.
Definition multi_level_cache := NatMap.t single_level_cache_unit.


(* Top-Level Structures *)
Inductive process : Type :=
| process_value : enclave_state -> memory_address -> core_ID -> process.
Definition processes := NatMap.t process.
Definition registers := NatMap.t memory_value.
Definition memory := NatMap.t data_block.
Inductive runtime_state : Type :=
| runtime_state_value : multi_level_cache -> memory -> registers -> processes -> runtime_state.