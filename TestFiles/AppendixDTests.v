Require Import RuntimeDefinitions.
Require Import AppendixD.

Definition e := enclave_ID_active.
Definition T1 := (subtree LMRU (e 5) (subtree LMRU (e 3) (subtree_leaf (leaf 0 (e 2))) (subtree_leaf (leaf 1 (e 1)))) (subtree LMRU (e 5) (subtree_leaf (leaf 5 (e 6))) (subtree_leaf (leaf 3 (e 5))))).


(* Contains Way ID *)
(* True *)
Compute (contains_way_ID 0 T1).
Compute (contains_way_ID 1 T1).
Compute (contains_way_ID 5 T1).
Compute (contains_way_ID 3 T1).

(* False *)
Compute (contains_way_ID 2 T1).
Compute (contains_way_ID 4 T1).
Compute (contains_way_ID 6 T1).


(* Update *)
Compute T1.
Compute (update T1 3 (e 5)).
Compute (update T1 0 (e 2)).
Compute (update T1 1 enclave_ID_inactive).