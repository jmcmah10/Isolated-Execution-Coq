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

Definition wf4 (sigma: runtime_state): Prop :=
  forall k mu rho pi p l q e E,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find p pi = Some (process_value (enclave_state_value e E) l q)) ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E)).

Lemma wf4_active_enclave_update : forall e E e' E' r,
  active_enclave_update (enclave_state_value e E) r = 
  enclave_state_valid (enclave_state_value e' E') ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E)) ->
  (e' = enclave_ID_inactive \/ (exists raw_e', e' = enclave_ID_active raw_e' /\ NatMap.In raw_e' E')).
Proof.
  intros.
  destruct r.
  unfold active_enclave_update in H.
  case_eq (NatMap.find r E). intros. assert (A1 := H1).
  destruct (NatMap.find r E) in A1, H.
  injection A1; injection H; intros; subst; clear A1.
  right. eexists r. split.
  reflexivity.
  assert (NatMap.find r E' <> None).
  intros contra. rewrite -> H1 in contra. discriminate.
  apply NatMapFacts.in_find_iff in H2. exact H2.
  discriminate.
  intros; destruct (NatMap.find r E).
  discriminate.
  discriminate.
  unfold active_enclave_update in H.
  injection H; intros; subst.
  left; reflexivity.
Qed.

Lemma wf4_enclave_creation : forall e E e' E' mu n x y,
  enclave_creation (enclave_state_value e E) mu n x y = enclave_state_valid (enclave_state_value e' E') ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E)) ->
  (e' = enclave_ID_inactive \/ (exists raw_e', e' = enclave_ID_active raw_e' /\ NatMap.In raw_e' E')).
Proof.
  intros.
  unfold enclave_creation in H.
  destruct x.
  case_eq (NatMap.find b mu). intros.
  assert (A0 := H1). destruct (NatMap.find b mu) in A0 , H.
  case_eq (is_all_zeroes mu b d (length (NatMapProperties.to_list d1)) y).
  intros. assert (DIS := H2).
  destruct (is_all_zeroes mu b d (length (NatMapProperties.to_list d1)) y) in DIS, H.
  unfold add_new_enclave_to_enclave_state in H.
  case_eq (NatMap.find n E). intros.
  assert (A1 := H3). destruct (NatMap.find n E) in A1, H.
  discriminate.
  discriminate.
  intros; destruct (NatMap.find n E).
  discriminate.
  injection A0; injection H; intros; subst; clear A0.
  destruct H0.
  left; exact H0.
  destruct H0. right.
  eexists x.
  destruct H0; split. exact H0.
  case_eq (eqb n x).
  intros; apply cmp_to_eq in H5; subst.
  apply NatMapFacts.add_in_iff; left; reflexivity.
  intros; apply cmp_to_uneq in H5.
  apply NatMapFacts.add_in_iff; right; exact H4.
  discriminate.
  intros; destruct (is_all_zeroes mu b d (length (NatMapProperties.to_list d1)) y).
  discriminate.
  discriminate.
  discriminate.
  intros; destruct (NatMap.find b mu).
  discriminate.
  discriminate.
Qed.

Lemma wf4_enclave_elimination : forall e E e' E' r,
  ((enclave_elimination (enclave_state_value e E) r) = enclave_state_value e' E') ->
  (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E) ->
  (exists raw_e', e' = enclave_ID_active raw_e' /\ NatMap.In raw_e' E').
Proof.
  intros.
  destruct e'.
  unfold enclave_elimination in H.
  injection H; intros; subst.
  destruct H0.
  destruct H0.
  case_eq (eqb r x).
  intros; apply cmp_to_eq in H2; subst.
  eexists x. split. injection H0; intros; subst; reflexivity.
  (* this case is actually not possible *)
  give_up.
  intros; apply cmp_to_uneq in H2.
  injection H0; intros; subst.
  destruct H0.
  eexists x. split. reflexivity.
  apply NatMapFacts.remove_in_iff.
  split. exact H2. exact H1.
  injection H; intros; subst.
  destruct H0.
  destruct H0.
  discriminate.
Admitted.

Lemma wf4_preservation : forall sigma obs sigma' obs',
  wf4 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf4 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf4 in *.
  intros; injection H1; intros.
  inversion H0. inversion H18.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H m mu rho p p2 l0 q0 e E).
    reflexivity.
    exact H19.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H m mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    destruct e0.
    assert (e0 = enclave_ID_inactive \/ (exists raw_e : raw_enclave_ID,
    e0 = enclave_ID_active raw_e /\ NatMap.In raw_e e1)).
    apply (H m mu rho p p2 l0 q0 e0 e1).
    reflexivity.
    exact H19.
    apply (wf4_enclave_creation e0 e1 e E mu n r_val2_addr r_val3).
    exact H39.
    exact H4.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H m mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H m m0 rho p p2 l0 q0 e E).
    reflexivity.
    exact H19.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H m m0 rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value (enclave_elimination (enclave_state_value
    (enclave_ID_active e_raw) mem) r_val) l' q0) p) = Some (process_value (enclave_elimination
    (enclave_state_value (enclave_ID_active e_raw) mem) r_val) l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    right.
    (* issue with enclave elimination definition *)
    give_up.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value (enclave_elimination (enclave_state_value
    (enclave_ID_active e_raw) mem) r_val) l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H m m0 rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    destruct e0.
    assert (e0 = enclave_ID_inactive \/ (exists raw_e : raw_enclave_ID,
    e0 = enclave_ID_active raw_e /\ NatMap.In raw_e e1)).
    apply (H k mu rho p p2 l0 q0 e0 e1).
    reflexivity.
    exact H19.
    apply (wf4_active_enclave_update e0 e1 e E (enclave_ID_active r_val)).
    exact H35.
    exact H4.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    destruct e0.
    assert (e0 = enclave_ID_inactive \/ (exists raw_e : raw_enclave_ID,
    e0 = enclave_ID_active raw_e /\ NatMap.In raw_e e1)).
    apply (H k mu rho p p2 l0 q0 e0 e1).
    reflexivity.
    exact H19.
    apply (wf4_active_enclave_update e0 e1 e E enclave_ID_inactive).
    exact H34.
    exact H4.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H k mu rho p p2 l0 q0 e E).
    reflexivity.
    exact H19.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H k mu rho p p2 l0 q0 e E).
    reflexivity.
    exact H19.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
  - subst. case_eq (eqb p1 p2).
    intros. apply cmp_to_eq in H3. subst.
    assert (NatMap.find p2 (NatMap.add p2 (process_value e0 l0 q') p)
    = Some (process_value e0 l0 q')).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    apply (H k mu rho p p2 l0 q0 e E).
    reflexivity.
    exact H9.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e0 l0 q') p) = NatMap.find p1 p).
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
    apply (H k mu rho p p1 l q e E).
    reflexivity.
    rewrite <- H4. exact H2.
Admitted.

Definition wf5 (sigma: runtime_state): Prop :=
  forall k mu rho pi index F V C R p l q e E,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find index k = Some (single_level_cache F V C R)) ->
  (NatMap.find p pi = Some (process_value (enclave_state_value (enclave_ID_active e) E) l q)) ->
  (NatMap.In e V).

Lemma wf5_preservation : forall sigma obs sigma' obs',
  wf5 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf5 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf5 in *.
  intros; injection H1; intros.
  inversion H0. inversion H19.
  - subst. give_up.
  - subst. give_up.
  - subst. give_up.
  - subst. give_up.
  - subst. give_up.
  - subst. give_up.
  - subst. give_up.
  - subst. give_up.
  - subst. give_up.
Admitted.