From Coq Require Import Lists.List.
From Coq Require Import FSets.FMapList.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require Import Structures.OrderedType.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Compare.
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
    | cachelet_index_value w2 s2 => (lt w1 w2) \/ ((eq w1 w2) /\ (lt s1 s2))
    end
  end.
  Definition eq_ci (x: t) (y: t) : Prop :=
  match x with
  | cachelet_index_value w1 s1 =>
    match y with
    | cachelet_index_value w2 s2 => (eq w1 w2) /\ (eq s1 s2)
    end
  end.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt := lt_ci.
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z H0 H1.
    destruct x. destruct y. destruct z.
    unfold lt in *. unfold lt_ci in *.
    lia.
  Qed.
  Lemma lt_implies_not_eq : forall x y : nat, x < y -> x <> y.
  Proof.
    lia.
  Qed.
  Lemma eq_cachelet2 : forall x y z w: nat, x = z /\ y = w -> cachelet_index_value x y = cachelet_index_value z w.
  Proof.
    intros.
    destruct H.
    rewrite -> H.
    rewrite -> H0.
    auto.
  Qed.
  Lemma contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
  Proof. intros. intro. apply H0.  apply H. exact H1. Qed.
  Lemma unequal_cachelet : forall x y z w: nat, x <> z \/ y <> w -> cachelet_index_value x y <> cachelet_index_value z w.
  Proof.
    intros.
    specialize H.
  Admitted.
  Lemma eq_cachelet : forall x y z w : nat, cachelet_index_value x y = cachelet_index_value z w -> x = z /\ y = w.
  Proof.
    intros.
    split.
    induction x.
    induction y.
    induction z.
    induction w.
    auto. auto.
    discriminate.
    apply IHy.
    rewrite <- H.
  Admitted.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H0.
    destruct x. destruct y.
    unfold eq.
    unfold lt in H0. unfold lt_ci in H0.
    destruct H0.
    {
      apply lt_implies_not_eq in H.
      unfold not.
      destruct eq.
    }
    lia.
  Qed.
  Definition compare x y := if x <=? y then (if y <=? x then Eq else Lt) else Gt.
  Lemma eq_ci_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros.
    destruct x. destruct y.
  Admitted.
  Definition eq_dec := eq_ci_dec.
End cachelet_index_as_OT.
*)



Definition data_block := NatMap.t data.
Definition remapping_list := NatMap.t way_mask.
(* Extra structure to hold data in way_set_cache *)
Inductive way_set_cache_value : Type :=
| valid_bit_tag_and_data : validity_bit -> cache_tag_value -> data_block -> way_set_cache_value.
Inductive way_set_cache_mapping :=
| wsc_mapping : cachelet_index -> way_set_cache_value -> way_set_cache_mapping.
Definition way_set_cache := list way_set_cache_mapping.
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