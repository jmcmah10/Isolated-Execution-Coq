From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
Require Import RuntimeDefinitions.
Require Import AppendixD.
Require Import AppendixC.
Require Import AppendixF.
Require Import AppendixE.
Require Import Semantics.
Require Import MLCOperations.

Definition tree_in_PLRU (R: set_indexed_PLRU) T: Prop :=
  exists x, (NatMap.find x R = Some T).

Notation "'<<' sigma ';' obs '>>'" := (state_and_trace sigma obs).

(*
Inductive wf1: runtime_state -> Prop :=
  | WF1 : forall sigma k mu rho pi F V C R lambda c,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (In c F) -> (CacheletMap.find c C <> None) ->
  (wf1 sigma).
*)

(*
Definition wf1 (sigma: runtime_state): Prop :=
  match sigma with
  | runtime_state_value k mu rho pi =>
    (forall lambda F V C R c,
    ((NatMap.find lambda k = Some (single_level_cache F V C R)) ->
    (In c F) -> (CacheletMap.find c C <> None)))
  end.
*)

Definition wf1 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda c F V C R,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k) = Some (single_level_cache F V C R) ->
  (In c F) -> (CacheletMap.find c C <> None).

Lemma wf1_preservation : forall sigma obs sigma' obs',
  wf1 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf1 sigma'.
Proof.
  unfold wf1 in *.
  intros.
  destruct sigma.
  destruct sigma'.
  inversion H0.
  inversion H15.
  give_up. give_up. give_up. give_up.
  destruct sigma'.

Definition wf1 (sigma: runtime_state): Prop :=
  forall k mu rho pi,
  (sigma = runtime_state_value k mu rho pi) ->
  (forall lambda c F V C R, (NatMap.find lambda k) = Some (single_level_cache F V C R) ->
  ((In c F) -> (CacheletMap.find c C <> None))).

Lemma wf1_preservation : forall sigma obs sigma' obs',
  wf1 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf1 sigma'.
Proof.
  intros.
  unfold wf1 in *.
  intros.



Definition wf1 (sigma: runtime_state): Prop :=
  match sigma with
  | runtime_state_value k mu rho pi =>
    (forall lambda c,
      match (NatMap.find lambda k) with
      | Some (single_level_cache F V C R) => ((In c F) -> (CacheletMap.find c C <> None))
      | None => True
      end)
  end.



Lemma wf1_C : forall state k lambda h_tree k',
  (mlc_deallocation state k lambda h_tree = Some k') ->
  (forall lambda', match (NatMap.find lambda' k) with
    | Some (single_level_cache F V C R) =>
      match (NatMap.find lambda' k') with
      | Some (single_level_cache F' V' C' R') =>
        (F = F' /\ C = C') \/ (exists l, F' = l ++ F)
      | None => False
      end
    | None => True
    end).
Proof.
  intros.
  remember (NatMap.find lambda' k) as s.
  remember (NatMap.find lambda' k') as s'.
  case s; case s'.
  intros.
  destruct s1. destruct s0.
  unfold mlc_deallocation in H. unfold recursive_mlc_deallocation in H.
  destruct state. destruct e. induction (get_hierarchy_tree_height h_tree).
  discriminate.
Admitted.

Lemma wf1_preservation : forall sigma obs sigma' obs',
  wf1 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf1 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf1 in *.
  intros.
  inversion H0.
  - inversion H12.
    give_up. give_up. give_up. give_up.
    rewrite <- H22; apply (H lambda c).
    rewrite <- H22; apply (H lambda c).
    rewrite <- H22; apply (H lambda c).
    rewrite <- H22; apply (H lambda c).
  - rewrite <- H7; apply (H lambda c).
Admitted.

(*
Lemma lemmaA1 : forall sigma obs sigma' obs',
  wf1 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf1 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf1 in *.
  intros.
  inversion H0.
  - destruct H14.
    give_up. give_up. give_up. give_up.
    apply (H lambda F V C R c).
    give_up. give_up. give_up. give_up. give_up.
  - apply (H lambda F V C R c).
    rewrite -> H9; exact H1. exact H2.
Admitted.
*)

(*
Proof.
  destruct sigma; destruct sigma'.
  unfold wf1 in *.
  intros.
  inversion H0.
  - induction H14.
    give_up. give_up. give_up. give_up.
    apply (H lambda F V C R c).
    rewrite <- H3.
  - apply (H lambda F V C R c).
    rewrite -> H9; exact H1. exact H2.
Admitted.
*)


  intros.
  auto.
  split.
  - give_up.
  - split.
  { give_up. }
  { intros.
    inversion H0.
    - give_up.
    - induction k0.
  auto.
Qed.
  inversion H0.
  - give_up.
  -

Inductive well_formed: runtime_state -> Prop :=
  | WF1 : forall sigma k mu rho pi F V C R lambda c,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (In c F) -> (CacheletMap.find c C <> None) ->
  (well_formed sigma)
  | WF2 : forall sigma k mu rho pi F V C R lambda e L w s W,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (NatMap.find e V = Some L) -> (NatMap.find s L = Some W) ->
  (In w W) -> (CacheletMap.find (w, s) C <> None) ->
  (well_formed sigma)
  | WF3 : forall sigma k mu rho pi F V C R lambda L W e w s,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (NatMap.find e V = Some L) -> (NatMap.find s L = Some W) ->
  (((In (w, s) F) -> ~(In w W)) /\ ((In w W) -> ~(In (w, s) F))) ->
  (well_formed sigma)
  | WF4 : forall sigma k mu rho pi F V C R lambda p state l q e E,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (NatMap.find p pi = Some (process_value state l q)) ->
  ((state = enclave_state_value enclave_ID_inactive E) \/
  ((state = enclave_state_value (enclave_ID_active e) E) /\ (NatMap.find e E <> None))) ->
  (well_formed sigma)
  | WF5 : forall sigma k mu rho pi F V C R lambda e p state l q E,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (NatMap.find p pi = Some (process_value state l q)) ->
  (state = enclave_state_value (enclave_ID_active e) E) ->
  (NatMap.find e V <> None) ->
  (well_formed sigma)
  | WF6 : forall sigma k mu rho pi F V C R lambda p state l0 q i e E l m,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (NatMap.find p pi = Some (process_value state l0 q)) ->
  (state = enclave_state_value e E) ->
  (exists x, NatMap.find x E = Some (enclave_address_and_data l m)) ->
  ((memory_read mu l0 = Some (memory_value_instruction i)) /\ (forall m0 n l', m0 < m ->
  add_to_memory_address mu l m0 = Some l' ->  memory_read mu l' = Some (memory_value_data n))) ->
  (well_formed sigma)
  | WF7 : forall sigma k mu rho pi F V C R lambda w s,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  ((CacheletMap.find (w, s) C <> None) <-> (NatMap.find s R <> None)) ->
  (well_formed sigma)
  | WF8 : forall sigma k mu rho pi F V C R lambda w s T,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  ((CacheletMap.find (w, s) C <> None) <-> ((contains_way_ID_prop w T) /\ (tree_in_PLRU R T))) ->
  (well_formed sigma)
  | WF9 : forall sigma k mu rho pi F V C R lambda e e_raw T,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  ((contains_enclave_prop e T) /\ (tree_in_PLRU R T)) -> (e = enclave_ID_inactive \/
  (e = (enclave_ID_active e_raw) /\ (NatMap.find e_raw V <> None))) ->
  (well_formed sigma).

(*
  | WF : forall sigma k mu rho pi F V C R lambda,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->




Inductive wf9 (V: VPT) (R: set_indexed_PLRU): Prop := forall e e_raw T,
  .

Inductive wf6 (mu: memory) (pi: processes): Prop := forall,.


Inductive wf sigma k mu rho pi: Prop := forall F V C R lambda,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (wf1 F C /\ wf2 V C /\ wf3 F V /\ wf4 pi /\ wf5 V pi /\ wf6 mu pi /\ wf7 C R /\ wf8 C R /\ wf9 V R).
Inductive well_formed (sigma: runtime_state): Prop :=
  match sigma with
  | runtime_state_value k mu rho pi => wf sigma k mu rho pi
  end.
*)
