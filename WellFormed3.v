From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Lia.
From Coq Require Import FSets.FMapList.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import Init.Nat.
From Coq Require Import Structures.OrderedTypeEx.
Require Import RuntimeDefinitions.
Require Import AppendixD.
Require Import AppendixC.
Require Import AppendixF.
Require Import AppendixE.
Require Import Semantics.
Require Import MLCOperations.
Require Import WellFormed.

Module NatMapFacts := NatMapProperties.F.
Module CacheletMapFacts := CacheletMapProperties.F.

(* Well-Formed 6 *)
Definition wf6 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R p state E l0 q e l k_num l0 b0 delta0 D0,
  (sigma = runtime_state_value k mu rho pi) ->
  NatMap.find p pi = Some (process_value (enclave_state_value state E) l0 q) ->
  NatMap.find e E = Some (enclave_address_and_data l k_num) ->
  l0 = memory_address b0 delta0 -> NatMap.find b0 mu = Some D0
  (exists i, NatMap.find delta0 D0 = Some (memory_value_instruction i)) /\
  (forall n l' b' delta' D', n < k -> l' = add_to_memory_address mu l n -> l' = memory_address b' delta' ->
  NatMap.find b' mu = Some D' -> exists n_k, NatMap.find delta' D' = Some (memory_value_data n_k)).
  
