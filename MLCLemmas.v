From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
Require Import RuntimeDefinitions.
Require Import AppendixD.
Require Import Semantics.
Require Import MLCOperations.

Lemma mlc_deallocation_C : forall state k lambda h_tree k',
  (mlc_deallocation

(*
Lemma mlc_read_effects : forall k lambda state mu l h_tree D' delta' obs' k',
  (mlc_read k lambda state mu l h_tree = mlc_read_valid D' delta' obs' k') ->
  (forall lambda', match (NatMap.find lambda' k) with
    | Some (single_level_cache F V C R) =>
      match (NatMap.find lambda' k') with
      | Some (single_level_cache F' V' C' R') =>
      | None => False
    | None => True
    end).
*)