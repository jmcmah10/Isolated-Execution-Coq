Require Import RuntimeDefinitions.
Require Import Lists.List.
Require Import AppendixC.

(* Way First Allocation *)
Compute (way_first_allocation nil).
Compute (way_first_allocation ((2, 0) :: nil)).
Compute (way_first_allocation ((4, 0) :: (3, 1) :: nil)).
Compute (way_first_allocation ((9, 4) :: (6, 3) :: (2, 10) :: (3, 7) :: (4, 9) :: nil)).