From Coq Require Import Lists.List.
Require Import RuntimeDefinitions.


(* Placeholder Cache Hierarchy Tree *)
Inductive cache_hierarchy_tree : Type :=
| ch_tree: physical_cache_unit_ID -> (list cache_hierarchy_tree) -> cache_hierarchy_tree
| ch_leaf: core_ID -> cache_hierarchy_tree.