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

Definition wf3 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R c e ranV,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (V_range V e = Some ranV) ->
  ((In c ranV -> ~In c F) /\ (In c F -> ~In c ranV)).

(* WF3 MLC Read *)
Lemma wf3_mlc_read : forall lambda h_tree k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R' c enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V enc = Some ranV ->
  V_range V' enc = Some ranV' ->
  ((In c ranV -> ~In c F) /\ (In c F -> ~In c ranV)) ->
  ((In c ranV' -> ~In c F') /\ (In c F' -> ~In c ranV')).
Proof.
  unfold mlc_read.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros.
    unfold recursive_mlc_read in H1.
    subst.
    destruct l0.
    destruct (NatMap.find b m0).
    injection H1; intros; subst.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    rewrite -> H6 in H7.
    injection H7; intros; subst.
    exact H8.
    discriminate.
  }
  {
    intros lambda IHTREE. intros.
    unfold recursive_mlc_read in H0.
    fold recursive_mlc_read in H0.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H8). destruct (NatMap.find a k) in A0, H0.
    case_eq (cc_hit_read s0 e' l0). intros.
    assert (A1 := H9). destruct (cc_hit_read s0 e' l0) in A1, H0.
    injection H0; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H10 := H9).
    destruct s; destruct s1.
    apply (cc_hit_read_f (single_level_cache c1 v w s) e' l0 D obs1 c0
    (single_level_cache c2 v0 w0 s0) c1 v w s c2 v0 w0 s0) in H9.
    apply (cc_hit_read_v (single_level_cache c1 v w s) e' l0 D obs1 c0
    (single_level_cache c2 v0 w0 s0) c1 v w s c2 v0 w0 s0) in H10.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H3. subst.
        rewrite -> H1 in H8.
        injection H8; intros; subst c2 v0 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache F V w0 s0) k) =
        Some (single_level_cache F V w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H2.
        injection H2; intros; subst F' V' w0 s0.
        rewrite -> H5 in H6; injection H6; intros; subst.
        exact H7.
      }
      {
        intros. apply cmp_to_uneq in H3.
        assert (NatMap.find index (NatMap.add a (single_level_cache c2 v0 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H3.
        rewrite -> H2 in H4.
        rewrite -> H1 in H4.
        injection H4; intros; subst F' V' C' R'.
        rewrite -> H5 in H6; injection H6; intros; subst.
        exact H7.
      }
    }
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_read s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_read k e' m0 l0 l). intros.
    assert (A1 := H10). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H0.
    case_eq (cc_update s0 e' d1 l0). intros.
    assert (A2 := H11). destruct (cc_update s0 e' d1 l0) in A2, H0.
    injection H0; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H3. subst a.
        destruct s.
        assert (H12 := H11).
        destruct s1.
        apply (cc_update_f (single_level_cache c1 v w s) e' D l0 c0 (single_level_cache c2 v0 w0 s0)
        c1 v w s c2 v0 w0 s0) in H11.
        apply (cc_update_v (single_level_cache c1 v w s) e' D l0 c0 (single_level_cache c2 v0 w0 s0)
        c1 v w s c2 v0 w0 s0) in H12.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c2 v0 w0 s0) m) =
        Some (single_level_cache c2 v0 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H2.
        rewrite -> H8 in H1.
        injection H1; injection H2; intros; subst.
        rewrite -> H5 in H6; injection H6; intros; subst.
        exact H7.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        intros. apply cmp_to_uneq in H3.
        assert (WFH := H).
        unfold well_defined_cache_tree in H.
        destruct H as [ WFH1 ]. destruct H as [ WFH2 ]. destruct H as [ WFH3 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' c enc ranV ranV').
          exact WFH.
          unfold mlc_write. exact H10.
          exact H1.
          rewrite <- H2. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H3.
          reflexivity.
          reflexivity.
          exact H5.
          exact H6.
          exact H7.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in IHTREE. discriminate.
          specialize (WFH3 c1 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst.
          apply (H p0 p l) in IHTREE.
          apply (IHl (cache_node p) IHTREE k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' c enc ranV ranV').
          exact WFH.
          unfold mlc_write. exact H10.
          exact H1.
          rewrite <- H2. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H3.
          reflexivity.
          reflexivity.
          exact H5.
          exact H6.
          exact H7.
        }
      }
    }
    discriminate.
    intros; destruct (cc_update s0 e' d1 l0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 l).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree).
  discriminate.
  discriminate.
Qed.

(* WF3 MLC Allocation *)

(* WF3 MLC Write *)
Lemma wf3_mlc_write : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index psi psi'
  F V C R F' V' C' R' c enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V enc = Some ranV ->
  V_range V' enc = Some ranV' ->
  ((In c ranV -> ~In c F) /\ (In c F -> ~In c ranV)) ->
  ((In c ranV' -> ~In c F') /\ (In c F' -> ~In c ranV')).
Proof.
  unfold mlc_write.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' c enc ranV ranV' WFH1; intros.
    destruct (get_cache_ID_path lambda h_tree).
    injection IHTREE; intros; subst.
    unfold recursive_mlc_write in H.
    subst. destruct l0.
    destruct (NatMap.find b m0). destruct v.
    discriminate.
    injection H; intros; subst.
    rewrite -> H0 in H1.
    injection H1; intros; subst.
    rewrite -> H4 in H5.
    injection H5; intros; subst.
    exact H6.
    discriminate.
    discriminate.
  }
  {
    intros lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' c enc ranV ranV' WFH1; intros.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H7). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros.
    assert (A1 := H8). destruct (cc_hit_write s0 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H9 := H8).
    destruct s; destruct s1.
    apply (cc_hit_write_f (single_level_cache c1 v0 w s) e' (address b d1) v D c0
    (single_level_cache c2 v1 w0 s0) c1 v0 w s c2 v1 w0 s0) in H8.
    apply (cc_hit_write_v (single_level_cache c1 v0 w s) e' (address b d1) v D c0
    (single_level_cache c2 v1 w0 s0) c1 v0 w s c2 v1 w0 s0) in H9.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H2. subst.
        rewrite -> H0 in H7.
        injection H7; intros; subst c2 v1 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache F V w0 s0) k) =
        Some (single_level_cache F V w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        injection H1; intros; subst F' V' w0 s0.
        rewrite -> H4 in H5; injection H5; intros; subst.
        exact H6.
      }
      {
        intros. apply cmp_to_uneq in H2.
        assert (NatMap.find index (NatMap.add a (single_level_cache c2 v1 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H2.
        rewrite -> H1 in H3.
        rewrite -> H0 in H3.
        injection H3; intros; subst F' V' C' R'.
        rewrite -> H4 in H5; injection H5; intros; subst.
        exact H6.
      }
    }
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_write s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_write k e' m0 l0 v l). intros.
    assert (A1 := H9). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H.
    case_eq (cc_update s0 e' d0 l0). intros.
    assert (A2 := H10). destruct (cc_update s0 e' d0 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H2. subst a.
        destruct s.
        assert (H11 := H10).
        destruct s1.
        apply (cc_update_f (single_level_cache c1 v0 w s) e' D l0 c0 (single_level_cache c2 v1 w0 s0)
        c1 v0 w s c2 v1 w0 s0) in H10.
        apply (cc_update_v (single_level_cache c1 v0 w s) e' D l0 c0 (single_level_cache c2 v1 w0 s0)
        c1 v0 w s c2 v1 w0 s0) in H11.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c2 v1 w0 s0) m1) =
        Some (single_level_cache c2 v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        rewrite -> H7 in H0.
        injection H0; injection H1; intros; subst.
        rewrite -> H4 in H5; injection H5; intros; subst.
        exact H6.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        intros. apply cmp_to_uneq in H2.
        assert (WFH := WFH1).
        unfold well_defined_cache_tree in WFH1.
        destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 v D o mu m1 index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' c enc ranV ranV').
          exact WFH.
          unfold mlc_write. exact H9.
          exact H0.
          rewrite <- H1. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H2.
          reflexivity.
          reflexivity.
          exact H4.
          exact H5.
          exact H6.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in IHTREE. discriminate.
          specialize (WFH3 c1 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst.
          apply (WFH4 p0 p l) in IHTREE.
          apply (IHl (cache_node p) IHTREE k e' m0 l0 v D o mu m1 index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' c enc ranV ranV').
          exact WFH.
          unfold mlc_write. exact H9.
          exact H0.
          rewrite <- H1. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H2.
          reflexivity.
          reflexivity.
          exact H4.
          exact H5.
          exact H6.
        }
      }
    }
    discriminate.
    intros; destruct (cc_update s0 e' d0 l0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (recursive_mlc_write k e' m0 l0 v l).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree).
  discriminate.
  discriminate.
Qed.

(* WF3 MLC Deallocation *)
Lemma clear_remapping_list_v : forall r r1 F V C R F' V' C' R' enc,
  NatMap.In r V ->
  clear_remapping_list r (NatMapProperties.to_list r1) F V C R = Some (single_level_cache F' V' C' R') ->
  (NatMap.In enc V <-> NatMap.In enc V').
Proof.
  intros r r0.
  induction (NatMapProperties.to_list r0).
  {
    intros.
    unfold clear_remapping_list in H0.
    injection H0; intros; subst.
    split.
    intros.
    apply NatMapFacts.add_in_iff.
    right. exact H1.
    intros.
    apply NatMapFacts.add_in_iff in H1.
    destruct H1.
    subst. exact H.
    exact H1.
  }
  {
    intros.
    unfold clear_remapping_list in H0.
    fold clear_remapping_list in H0.
    case_eq a. intros.
    destruct a.
    injection H1; intros; subst k0 w0; clear H1.
    case_eq (free_cachelets r k w F V C R); intros.
    assert (A0 := H1). destruct (free_cachelets r k w F V C R) in A0, H0.
    injection A0; intros; subst s0; clear A0.
    destruct s.
    apply (free_cachelets_v w r k F V C R c v w0 s) in H1. subst v.
    apply (IHl c V w0 s F' V' C' R' enc).
    exact H. exact H0.
    discriminate.
    destruct (free_cachelets r k w F V C R).
    discriminate.
    discriminate.
  }
Qed.

Lemma V_range_add_empty : forall V r enc ranV ranV' c,
  V_range V enc = Some ranV ->
  V_range (NatMap.add r (NatMap.empty way_mask) V) enc = Some ranV' ->
  In c ranV' -> In c ranV.
Proof.
  intros.
  unfold V_range in *.
  case_eq (NatMap.find enc V). intros.
  assert (A0 := H2). destruct (NatMap.find enc V) in H, A0.
  case_eq (NatMap.find (elt:=remapping_list) enc (NatMap.add r (NatMap.empty way_mask) V)). intros.
  assert (A1 := H3). destruct (NatMap.find (elt:=remapping_list) enc (NatMap.add r (NatMap.empty way_mask) V)) in H0, A1.
  injection A0; injection A1; intros; subst r3 r0; clear A0 A1.
  case_eq (eqb r enc); intros.
  apply cmp_to_eq in H4; subst r.
  assert (NatMap.find (elt:=remapping_list) enc (NatMap.add enc (NatMap.empty way_mask) V) = Some (NatMap.empty way_mask)).
  apply NatMapFacts.add_eq_o. reflexivity.
  rewrite -> H3 in H4.
  injection H4; intros; subst.
  injection H0; intros; subst.
  unfold In in H1. destruct H1.
  apply cmp_to_uneq in H4.
  assert (NatMap.find (elt:=remapping_list) enc (NatMap.add r (NatMap.empty way_mask) V)
  = NatMap.find (elt:=remapping_list) enc V).
  apply NatMapFacts.add_neq_o. exact H4.
  rewrite -> H2 in H5.
  rewrite -> H3 in H5.
  injection H5; intros; subst r2.
  rewrite -> H0 in H.
  injection H; intros; subst ranV'.
  exact H1.
  discriminate.
  intros; destruct (NatMap.find (elt:=remapping_list) enc (NatMap.add r (NatMap.empty way_mask) V)).
  discriminate.
  discriminate.
  discriminate.
  intros; destruct (NatMap.find enc V).
  discriminate.
  discriminate.
Qed.

Lemma wf3_free_cachelets : forall w0 r k F V C R F' V' C' R' r0 c enc ranV ranV',
  ((In c ranV -> ~In c F) /\ (In c F -> ~In c ranV)) ->
  V_range V enc = Some ranV ->
  V_range V' enc = Some ranV' ->
  NatMap.find r V = Some r0 ->
  free_cachelets r k w0 F V C R = Some (single_level_cache F' V' C' R') ->
  ((In c ranV' -> ~In c F') /\ (In c F' -> ~In c ranV')).
Proof.
  intros w0.
  induction w0.
  {
    intros.
    unfold free_cachelets in H3.
    injection H3; intros; subst.
    rewrite -> H0 in H1.
    injection H1; intros; subst.
    exact H.
  }
  {
    intros.
    unfold free_cachelets in H3.
    fold free_cachelets in H3.
    case_eq (NatMap.find k R). intros.
    assert (A0 := H4). destruct (NatMap.find k R) in A0, H3.
    case_eq (cachelet_invalidation C (a, k)). intros.
    assert (A1 := H5). destruct (cachelet_invalidation C (a, k)) in A1, H3.
    injection A0; injection A1; intros; subst p0 w1; clear A0 A1.
    apply (IHw0 r k ((a, k) :: F) V w (NatMap.add k (update p a (enclave_ID_active r)) R)
    F' V' C' R' r0 c enc ranV ranV').
    destruct H.
    split.
    {
      intros.
      intros contra.
      apply in_inv in contra.
      destruct contra.
      give_up.
      apply H6 in H8.
      apply H8 in H7.
      exact H7.
    }
    give_up.
    give_up.
    give_up.
    give_up.
    give_up.
    give_up.
    give_up.
    give_up.
    give_up.
  }
Admitted.

Lemma wf3_clear_remapping_list : forall r r1 F V C R F' V' C' R' c enc ranV ranV',
  ((In c ranV -> ~In c F) /\ (In c F -> ~In c ranV)) ->
  V_range V enc = Some ranV ->
  V_range V' enc = Some ranV' ->
  NatMap.In r V ->
  clear_remapping_list r (NatMapProperties.to_list r1) F V C R = Some (single_level_cache F' V' C' R') ->
  ((In c ranV' -> ~In c F') /\ (In c F' -> ~In c ranV')).
Proof.
  intros r r0.
  induction (NatMapProperties.to_list r0).
  {
    intros.
    assert (H4 := H3).
    apply (clear_remapping_list_v r (NatMap.empty way_mask) F V C R F' V' C' R' enc) in H4.
    unfold clear_remapping_list in H3.
    injection H3; intros; subst F' V' C' R'.
    assert (In c ranV' -> In c ranV).
    apply (V_range_add_empty V r enc ranV ranV' c).
    exact H0. exact H1.
    destruct H.
    split.
    {
      intros.
      apply H.
      apply H5.
      exact H7.
    }
    {
      intros.
      intros contra.
      apply H5 in contra.
      apply H in contra.
      apply contra in H7.
      destruct H7.
    }
    exact H2.
  }
  {
    intros.
    unfold clear_remapping_list in H3.
    fold clear_remapping_list in H3.
    destruct a.
    case_eq (free_cachelets r k w F V C R). intros.
    assert (A0 := H4). destruct (free_cachelets r k w F V C R) in A0, H3.
    destruct s; destruct s0.
    injection A0; intros; subst; clear A0.
    give_up.
    give_up.
    give_up.
  }
Admitted.


Lemma wf3_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R' c enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V enc = Some ranV ->
  V_range V' enc = Some ranV' ->
  ((In c ranV -> ~In c F) /\ (In c F -> ~In c ranV)) ->
  ((In c ranV' -> ~In c F') /\ (In c F' -> ~In c ranV')).
Proof.
  unfold mlc_deallocation.
  intros lambda h_tree state.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros lambda IHTREE k k' index psi psi' F V C R
    F' V' C' R' c enc ranV ranV' WFH; intros.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    injection H; intros; subst k'.
    rewrite -> H0 in H1.
    injection H1; intros; subst psi psi'.
    injection H7; intros; subst F' V' C' R'.
    rewrite -> H5 in H4; injection H4; intros; subst.
    exact H6.
    discriminate.
  }
  {
    intros lambda IHTREE k k' index psi psi' F V C R
    F' V' C' R' c enc ranV ranV' WFH; intros.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    fold recursive_mlc_deallocation in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H7). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_deallocation r s0). intros.
    assert (A1 := H8). destruct (cachelet_deallocation r s0) in A1, H.
    injection A0; injection A1; intros; subst s0 s2; clear A0 A1.
    assert (WFH1 := WFH).
    unfold well_defined_cache_tree in WFH1.
    destruct WFH1 as [ WFH1 WFH2 ]. destruct WFH2 as [ WFH2 WFH3 ]. destruct WFH3 as [ WFH3 WFH4 ].
    case_eq (eqb index a).
    {
      intros; apply cmp_to_eq in H9; subst a.
      rewrite -> H7 in H0.
      injection H0; intros; subst s.
      destruct s1.
      case_eq (V_range v enc). intros.
      destruct l.
      {
        apply (IHl root_node WFH1 (NatMap.add index (single_level_cache c0 v w s) k) k' index
        (single_level_cache c0 v w s) psi' c0 v w s F' V' C' R' c enc l0 ranV').
        exact WFH.
        unfold mlc_deallocation. exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H3.
        exact H9.
        exact H5.
        unfold cachelet_deallocation in H8. destruct psi.
        case_eq (NatMap.find r v0). intros.
        assert (A0 := H10). destruct (NatMap.find r v0) in A0, H8.
        injection A0; injection H2; intros; subst c1 v0 w0 s0 r1; clear A0.
        (* apply (wf3_clear_remapping_list r r1 (single_level_cache c1 v0 w0 s0) (single_level_cache c0 v w s)
        c1 v0 w0 s0 c0 v w s c) in H8. *)
        give_up.
        discriminate.
        intros; destruct (NatMap.find r v0).
        discriminate.
        discriminate.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c1 index (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 index (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 index p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE (NatMap.add index (single_level_cache c0 v w s) k) k' index
        (single_level_cache c0 v w s) psi' c0 v w s F' V' C' R' c enc l0 ranV').
        exact WFH.
        unfold mlc_deallocation. exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H3.
        exact H9.
        exact H5.
        destruct psi.
        (*
        apply (wf2_cachelet_deallocation r psi (single_level_cache c0 v w s) F V C R
        c0 v w s enc ranV l0 c).
        exact H9. exact H2. reflexivity. exact H4.
        exact H10. exact H6. exact H7.
        *)
        give_up.
      }
      {
        intros. destruct psi.
        injection H2; intros; subst c1 v0 w0 s0.
        apply (cachelet_deallocation_v r (single_level_cache F V C R) (single_level_cache c0 v w s)
        F V C R c0 v w s enc) in H8.
        apply V_range_in in H4. apply V_range_not_in in H9.
        apply H8 in H4.
        apply H9 in H4.
        destruct H4.
        reflexivity.
        reflexivity.
      }
    }
    {
      intros; apply cmp_to_uneq in H9.
      destruct l.
      {
        apply (IHl root_node WFH1 (NatMap.add a s1 k) k' index
        psi psi' F V C R F' V' C' R' c enc ranV ranV').
        exact WFH.
        unfold mlc_deallocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H9.
        exact H1.
        exact H2.
        exact H3.
        exact H4.
        exact H5.
        exact H6.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c0 a (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 a (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 a p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE (NatMap.add a s1 k) k' index
        psi psi' F V C R F' V' C' R' c enc ranV ranV').
        exact WFH.
        unfold mlc_deallocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H9.
        exact H1.
        exact H2.
        exact H3.
        exact H4.
        exact H5.
        exact H6.
      }
    }
    discriminate.
    intros; destruct (cachelet_deallocation r s0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
    discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree).
  discriminate.
  destruct state; destruct e; discriminate.
Admitted.

Lemma wf3_preservation : forall sigma obs sigma' obs',
  wf3 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf3 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf3 in *.
  intros; injection H1; intros.
  inversion H0. inversion H19; subst.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    case_eq (V_range v e); intros.
    assert (V_range v e = Some l1 -> (In c l1 -> ~ In c c0) /\ (In c c0 -> ~In c l1)).
    apply (H m mu rho p lambda c0 v w s c e l1). reflexivity. exact H4.
    apply (wf3_mlc_read lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c0 v w s)
    (single_level_cache F V C R) c0 v w s F V C R c e l1 ranV).
    exact H25. exact H36. exact H4. exact H2. reflexivity.
    reflexivity. exact H5. exact H3. apply H6 in H5. exact H5.
    apply (wf2_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c0 v w s)
    (single_level_cache F V C R) c0 v w s F V C R e) in H5.
    rewrite -> H3 in H5. discriminate.
    exact H25. exact H36. exact H4. exact H2. reflexivity.
    reflexivity.
    apply (wf_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H25. exact H36.
  - give_up.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    case_eq (V_range v0 e); intros.
    assert (V_range v0 e = Some l1 -> (In c l1 -> ~ In c c0) /\ (In c c0 -> ~In c l1)).
    apply (H m m0 rho p lambda c0 v0 w s c e l1). reflexivity. exact H4.
    apply (wf3_mlc_write lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c0 v0 w s)
    (single_level_cache F V C R) c0 v0 w s F V C R c e l1 ranV).
    exact H25. exact H36. exact H4. exact H2. reflexivity.
    reflexivity. exact H5. exact H3. apply H6 in H5. exact H5.
    apply (wf2_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c0 v0 w s)
    (single_level_cache F V C R) c0 v0 w s F V C R) in H5.
    rewrite -> H5 in H3. discriminate.
    exact H25. exact H36. exact H4. exact H2. reflexivity. reflexivity.
    apply (wf_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda) in H4.
    rewrite -> H4 in H2.
    discriminate. exact H25. exact H36.
  - give_up.
  - apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3.
  - apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3.
  - apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3.
  - apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3.
  - subst. apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3.
Admitted.

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
  ((enclave_elimination (enclave_state_value e E) r) = enclave_state_valid (enclave_state_value e' E')) ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E)) ->
  (e = enclave_ID_inactive \/ (exists raw_e', e' = enclave_ID_active raw_e' /\ NatMap.In raw_e' E')).
Proof.
  intros.
  destruct H0. left. exact H0.
  destruct e'.
  {
    right.
    unfold enclave_elimination in H.
    destruct e.
    case_eq (r =? r1); intros.
    assert (A0 := H1). destruct (r =? r1) in H, A0.
    discriminate.
    discriminate.
    intros. assert (H2 := H1). apply cmp_to_uneq in H1.
    destruct (r =? r1).
    discriminate.
    injection H; intros; subst.
    destruct H0.
    destruct H0.
    injection H0; intros; subst.
    eexists x.
    split. reflexivity.
    apply NatMapFacts.remove_in_iff.
    split. exact H1. exact H3.
    destruct H0.
    destruct H0.
    discriminate.
  }
  {
    unfold enclave_elimination in H.
    destruct e.
    destruct (r =? r0).
    discriminate.
    discriminate.
    left. reflexivity.
  }
Qed.

Lemma enclave_elimination_state : forall e E e' E' r,
  ((enclave_elimination (enclave_state_value e E) r) = enclave_state_valid (enclave_state_value e' E')) ->
  e = e'.
Proof.
  intros.
  unfold enclave_elimination in H.
  destruct e.
  destruct (r =? r0).
  discriminate.
  injection H; intros; subst; reflexivity.
  injection H; intros; subst; reflexivity.
Qed.

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
    exact H40.
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
    assert (NatMap.find p2 (NatMap.add p2 (process_value e' l' q0) p)
    = Some (process_value e' l' q0)).
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite -> H2 in H3.
    injection H3; intros; subst.
    assert (H40 := H39).
    apply (enclave_elimination_state (enclave_ID_active e_raw) mem e E r_val) in H40. subst e.
    assert (enclave_ID_active e_raw = enclave_ID_inactive \/ (exists raw_e : raw_enclave_ID,
    enclave_ID_active e_raw = enclave_ID_active raw_e /\ NatMap.In raw_e mem)).
    apply (H m m0 rho p p2 l0 q0 (enclave_ID_active e_raw) mem).
    reflexivity.
    exact H19.
    apply (wf4_enclave_elimination (enclave_ID_active e_raw) mem (enclave_ID_active e_raw) E r_val).
    exact H39. exact H4.
    intros; apply cmp_to_uneq in H3.
    assert (NatMap.find p1 (NatMap.add p2 (process_value e' l' q0) p) = NatMap.find p1 p).
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
Qed.

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