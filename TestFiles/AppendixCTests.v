Require Import RuntimeDefinitions.
Require Import Lists.List.
Require Import AppendixC.
From Coq Require Import Init.Nat.
From Coq Require Import Numbers.NatInt.NZDiv.
From Coq Require Import Numbers.NatInt.NZLog.
From Coq Require Import Numbers.NatInt.NZBits.

(* Way First Allocation *)
Compute (way_first_allocation nil).
Compute (way_first_allocation ((2, 0) :: nil)).
Compute (way_first_allocation ((4, 0) :: (3, 1) :: nil)).
Compute (way_first_allocation ((9, 4) :: (6, 3) :: (2, 10) :: (3, 7) :: (4, 9) :: nil)).

(* Cachelet Invalidation *)
Compute (cachelet_invalidation (CacheletMap.add (0, 0) (valid_bit_tag_and_data valid_bit 7 (NatMap.empty data)) (CacheletMap.empty way_set_cache_value)) (1, 1)).
Compute (cachelet_invalidation (CacheletMap.add (2, 0) (valid_bit_tag_and_data valid_bit 0 (NatMap.empty data)) (CacheletMap.empty way_set_cache_value)) (2, 0)).

(* Beta Function *)
Definition set4 := (NatMap.add 0 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 1 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 2 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 3 (subtree_leaf (leaf 0 enclave_ID_inactive)) (NatMap.empty PLRU_tree))))).
Definition set8 := (NatMap.add 0 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 1 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 2 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 3 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 4 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 5 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 6 (subtree_leaf (leaf 0 enclave_ID_inactive))
  (NatMap.add 7 (subtree_leaf (leaf 0 enclave_ID_inactive)) (NatMap.empty PLRU_tree))))))))).
Compute (block_to_set_and_tag 0 set4).
Compute (block_to_set_and_tag 3 set4).
Compute (block_to_set_and_tag 4 set4).
Compute (block_to_set_and_tag 67 set4).
Compute (block_to_set_and_tag 68 set4).
Compute (block_to_set_and_tag 0 set8).
Compute (block_to_set_and_tag 7 set8).
Compute (block_to_set_and_tag 8 set8).
Compute (block_to_set_and_tag 67 set8).
Compute (block_to_set_and_tag 101 set8).


(* Find Way ID *)
Definition E3 := enclave_state_value (enclave_ID_active 3) (NatMap.empty enclave_memory_range_value).
Definition E6 := enclave_state_value (enclave_ID_active 6) (NatMap.empty enclave_memory_range_value).
Definition E8 := enclave_state_value (enclave_ID_active 8) (NatMap.empty enclave_memory_range_value).
Definition W1 := 1 :: nil.
Definition W2 := 1 :: 2 :: 0 :: nil.
Definition W3 := 2 :: 3 :: nil.
Definition W4 := 0 :: nil.
Definition L1: remapping_list := NatMap.add 0 W1 (NatMap.add 1 W2 (NatMap.add 2 W3 (NatMap.add 3 W4 (NatMap.empty way_mask)))).
Definition L2: remapping_list := NatMap.add 0 W1 (NatMap.add 1 W1 (NatMap.add 2 W4 (NatMap.add 3 W1 (NatMap.empty way_mask)))).
Definition L3: remapping_list := NatMap.add 0 W3 (NatMap.add 1 W4 (NatMap.add 2 W3 (NatMap.add 3 W2 (NatMap.empty way_mask)))).
Definition V: VPT := NatMap.add 3 L1 (NatMap.add 6 L2 (NatMap.add 2 L3 (NatMap.empty remapping_list))).
Definition cache_val1 := valid_bit_tag_and_data valid_bit 14 (NatMap.empty data).
Definition cache_val2 := valid_bit_tag_and_data valid_bit 8 (NatMap.empty data).
Definition cache_val3 := valid_bit_tag_and_data valid_bit 9 (NatMap.empty data).
Definition cache_val4 := valid_bit_tag_and_data valid_bit 2 (NatMap.empty data).
Definition cache_val_dirty := valid_bit_tag_and_data dirty_bit 3 (NatMap.empty data).
Definition c1 := (3, 2).
Definition c2 := (1, 1).
Definition c3 := (3, 3).
Definition c4 := (0, 3).
Definition cdirty := (2, 2).
Definition C: way_set_cache := CacheletMap.add c1 cache_val1 
  (CacheletMap.add c2 cache_val2
  (CacheletMap.add c3 cache_val3
  (CacheletMap.add c4 cache_val4
  (CacheletMap.add cdirty cache_val_dirty (CacheletMap.empty way_set_cache_value))))).

(* PASS *)
Compute (find_way_ID_with_cache_tag E3 3 2 V C).
Compute (find_way_ID_with_cache_tag E6 1 8 V C).
Compute (find_way_ID_with_cache_tag E3 2 14 V C).
(* dirty bit in cache value should still pass *)
Compute (find_way_ID_with_cache_tag E3 2 3 V C).

(* FAIL *)
Compute (find_way_ID_with_cache_tag E3 0 0 V C).
(* no enclave mapping in VPT *)
Compute (find_way_ID_with_cache_tag E8 1 8 V C).

