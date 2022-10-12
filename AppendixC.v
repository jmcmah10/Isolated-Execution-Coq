Require Import RuntimeDefinitions.
From Coq Require Import Lists.List.
From Coq Require Import Init.Nat.

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

(* Cachelet Invalidation*) (*
Fixpoint recursive_cachelet_invalidation (C: list way_set_cache_mapping) (c: cachelet_index): (list way_set_cache_mapping) :=
  match C with
  | nil => nil
  | x :: l =>
    match x with
    | wsc_mapping index value =>
      if eq_cachelet_index index c
      then 
        match value with
        | valid_bit_tag_and_data _ t D  => (wsc_mapping c (valid_bit_tag_and_data dirty_bit t D)) :: (recursive_cachelet_invalidation l c)
        end
      else x :: (recursive_cachelet_invalidation l c)
    end
  end. *)
(*
Definition cachelet_invalidation (C: way_set_cache) (ci: cachelet_index): way_set_cache :=
  match (CacheletMap.find ci C) with
  | Some (valid_bit_tag_and_data _ c d) => CacheletMap.add ci (valid_bit_tag_and_data dirty_bit c d) C
  | None => C
  end.

Compute (cachelet_invalidation (CacheletMap.add (cachelet_index_value 0 0) (valid_bit_tag_and_data dirty_bit 7 (NatMap.empty data)) (CacheletMap.empty way_set_cache_value)) (cachelet_index_value 1 1)).
Compute (cachelet_invalidation (CacheletMap.add (cachelet_index_value 0 0) (valid_bit_tag_and_data valid_bit 0 (NatMap.empty data)) (CacheletMap.empty way_set_cache_value)) (cachelet_index_value 0 0)).
*)
(* Cachelet Allocation *)
(*Definition cachelet_allocation (psi: single_level_cache_unit) (e: raw_enclave_ID) (num_cachelets: nat): single_level_cache_unit := *)

(* Cachelet Deallocation *)

(* CC Hit Read *)
(*
Definition cc_hit_read (psi: single_level_cache_unit) (state: enclave_state) (l: memory_address): single_level_cache_unit :=
*)

(* CC Hit Write *)

(* CC Update *)