Require Import RuntimeDefinitions.
From Coq Require Import Bool.Bool.

Fixpoint eq_nat (n : nat) (m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | 0, S _ => false
  | S _, 0 => false
  | S n1, S m1 => eq_nat n1 m1
  end.

Definition equal_enclave_IDs (e0 : enclave_ID) (e1 : enclave_ID) : bool :=
  match e0, e1 with
  | enclave_ID_active e0_val, enclave_ID_active e1_val => eq_nat e0_val e1_val
  | _, _ => false
  end.

Fixpoint contains_way_id (w : way_ID) (T : PLRU_tree) : bool :=
  match T with
  | subtree sigma e T1 T2 => (contains_way_id w T1) || (contains_way_id w T2)
  | subtree_leaf L => 
    match L with
    | leaf w' e => eq_nat w w'
    end
  end.

Definition common_enclave (T1 : PLRU_tree) (T2 : PLRU_tree) : enclave_ID :=
  match T1, T2 with
  | subtree _ e _ _, subtree _ e' _ _ =>
    if equal_enclave_IDs e e'
    then e
    else enclave_ID_inactive
  | _, _ => enclave_ID_inactive
  end.

Fixpoint update (T : PLRU_tree) (w : way_ID) (e: enclave_ID) : PLRU_tree :=
  match T with
  | subtree select_bit e0 T1 T2 =>
    if equal_enclave_IDs e e0
    then
      if (contains_way_id w T1) 
      then subtree LMRU e (update T1 w e) T2
      else
        if (contains_way_id w T2)
        then subtree RMRU e T1 (update T2 w e)
        else subtree select_bit e T1 T2
    else subtree select_bit (common_enclave T1 T2) (update T1 w e) (update T2 w e)
  | subtree_leaf L =>
    match L with
    | leaf w' e' =>
      match e' with
      | enclave_ID_inactive =>
        if (eq_nat w w')
        then subtree_leaf (leaf w e)
        else subtree_leaf L
      | enclave_ID_active _ => subtree_leaf L
      end
    end
  end.