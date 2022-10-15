Require Import RuntimeDefinitions.
Require Import Lists.List.
Require Import AppendixC.

(* Way First Allocation *)
Compute (way_first_allocation nil).
Compute (way_first_allocation ((2, 0) :: nil)).
Compute (way_first_allocation ((4, 0) :: (3, 1) :: nil)).
Compute (way_first_allocation ((9, 4) :: (6, 3) :: (2, 10) :: (3, 7) :: (4, 9) :: nil)).

(* Cachelet Invalidation *)
Compute (cachelet_invalidation (CacheletMap.add (0, 0) (valid_bit_tag_and_data valid_bit 7 (NatMap.empty data)) (CacheletMap.empty way_set_cache_value)) (1, 1)).
Compute (cachelet_invalidation (CacheletMap.add (2, 0) (valid_bit_tag_and_data valid_bit 0 (NatMap.empty data)) (CacheletMap.empty way_set_cache_value)) (2, 0)).
