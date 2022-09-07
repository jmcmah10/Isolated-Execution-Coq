From Coq Require Import Lists.List.

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
Definition memory_address := nat.
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
Definition enclave_memory_range : Type := list (raw_enclave_ID -> enclave_memory_range_value).
Inductive enclave_state : Type := 
| enclave_state_value : enclave_ID -> enclave_memory_range -> enclave_state.


(* CC-Related Structures *)
Definition way_mask := list way_ID.
Inductive validity_bit : Type :=
| valid_bit : validity_bit
| dirty_bit : validity_bit.
Inductive cachelet_index : Type :=
| cachelet_index_value : way_ID -> set_ID -> cachelet_index.
Definition data_block := list (data_offset -> data).
Definition remapping_list := list (set_ID -> way_mask).

(* Extra structure to hold data in way_set_cache *)
Inductive way_set_cache_value : Type :=
| valid_bit_tag_and_data : validity_bit -> cache_tag_value -> data_block -> way_set_cache_value.

Definition way_set_cache := list (cachelet_index -> way_set_cache_value).
Definition VPT := list (enclave_ID -> remapping_list).
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
Definition set_indexed_PLRU := list (set_ID -> PLRU_tree).


(* Multi-Level Cache *)
Inductive single_level_cache_unit : Type :=
| single_level_cache : CAT -> VPT -> way_set_cache -> set_indexed_PLRU -> single_level_cache_unit.
Definition multi_level_cache := list (physical_cache_unit_ID -> single_level_cache_unit).


(* Top-Level Structures *)
Inductive process : Type :=
| process_value : enclave_state -> memory_address -> core_ID -> process.
Definition processes := list (process_ID -> process).
Definition registers := list (register_ID -> memory_value).
Definition memory := list (block_ID -> data_block).
Inductive runtime_state : Type :=
| runtime_state_value : multi_level_cache -> memory -> registers -> processes -> runtime_state.