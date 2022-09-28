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
Inductive enclave_memory_range_mapping := 
| emr_mapping : raw_enclave_ID -> enclave_memory_range_value -> enclave_memory_range_mapping.
Definition enclave_memory_range : Type := list enclave_memory_range_mapping.
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


Inductive data_block_mapping :=
| db_mapping : data_offset -> data -> data_block_mapping.
Definition data_block := list data_block_mapping.
Inductive remapping_mapping :=
| remap_mapping : set_ID -> way_mask -> remapping_mapping.
Definition remapping_list := list remapping_mapping.

(* Extra structure to hold data in way_set_cache *)
Inductive way_set_cache_value : Type :=
| valid_bit_tag_and_data : validity_bit -> cache_tag_value -> data_block -> way_set_cache_value.
Inductive way_set_cache_mapping :=
| wsc_mapping : cachelet_index -> way_set_cache_value -> way_set_cache_mapping.
Definition way_set_cache := list way_set_cache_mapping.
Inductive VPT_mapping :=
| vpt_mapping : enclave_ID -> remapping_list -> VPT_mapping.
Definition VPT := list VPT_mapping.
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
Inductive set_indexed_PLRU_mapping :=
| si_plru_mapping : set_ID -> PLRU_tree -> set_indexed_PLRU_mapping.
Definition set_indexed_PLRU := list set_indexed_PLRU_mapping.


(* Multi-Level Cache *)
Inductive single_level_cache_unit : Type :=
| single_level_cache : CAT -> VPT -> way_set_cache -> set_indexed_PLRU -> single_level_cache_unit.
Inductive multi_level_cache_mapping :=
| mlc_mapping : physical_cache_unit_ID -> single_level_cache_unit -> multi_level_cache_mapping.
Definition multi_level_cache := list multi_level_cache_mapping.


(* Top-Level Structures *)
Inductive process : Type :=
| process_value : enclave_state -> memory_address -> core_ID -> process.
Inductive process_mapping :=
| p_mapping : process_ID -> process -> process_mapping.
Definition processes := list process_mapping.
Inductive register_mapping :=
| reg_mapping : register_ID -> memory_value -> register_mapping.
Definition registers := list register_mapping.
Inductive memory_mapping :=
| m_mapping : block_ID -> data_block -> memory_mapping.
Definition memory := list memory_mapping.
Inductive runtime_state : Type :=
| runtime_state_value : multi_level_cache -> memory -> registers -> processes -> runtime_state.