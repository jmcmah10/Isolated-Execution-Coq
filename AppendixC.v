From Coq Require Import Lists.List.
From Coq Require Import Init.Nat.
Require Import RuntimeDefinitions.
Require Import AppendixD.

Definition lt_way_ID (c1: nullable_cachelet_index) (c2: nullable_cachelet_index) : nullable_cachelet_index :=
  match c1, c2 with
  | cachelet_index_defined v1, cachelet_index_defined v2 =>
    match v1, v2 with
    | (w1, _), (w2, _) =>
      if ltb w1 w2 then c1 else c2
    end
  | _, cachelet_index_none => c1
  | _, _ => c2
  end.
Definition eq_cachelet_index (c1: cachelet_index) (c2: cachelet_index): bool :=
  match c1, c2 with
  | (w1, s1), (w2, s2) => andb (eqb w1 w2) (eqb s1 s2)
  end.

Definition nullify_cachelet_index (c: cachelet_index): nullable_cachelet_index := cachelet_index_defined c.
Definition nullify_cachelet_index_list (l: (list cachelet_index)): (list nullable_cachelet_index) :=
  map (nullify_cachelet_index) l.

(* Way First Allocation *)
Definition cachelet_min_way_ID (l: (list cachelet_index)): nullable_cachelet_index :=
  fold_right lt_way_ID cachelet_index_none (nullify_cachelet_index_list l).
Definition way_first_allocation (F: CAT): nullable_cachelet_index := cachelet_min_way_ID F.

(* Cachelet Invalidation*)
Definition cachelet_invalidation (C: way_set_cache) (ci: cachelet_index): way_set_cache :=
  match (CacheletMap.find ci C) with
  | Some (valid_bit_tag_and_data _ c d) => CacheletMap.add ci (valid_bit_tag_and_data dirty_bit c d) C
  | None => C
  end.

(* Cachelet Allocation *)

(* Cachelet Deallocation *)

(* CC Hit Read *)
Inductive validatable_cc_hit_read : Type :=
  | cc_hit_read_valid: data_block -> data_offset -> cachelet_index -> single_level_cache_unit -> validatable_cc_hit_read
  | cc_hit_read_error: validatable_cc_hit_read.
Definition cc_hit_read (psi: single_level_cache_unit) (state: enclave_state) (l: memory_address): validatable_cc_hit_read :=
  

(* CC Hit Write *)

(* CC Update *)