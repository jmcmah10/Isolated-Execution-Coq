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

Definition disjoint_VPT (V: VPT): Prop :=
  forall e ranV, NatMap.find e V = Some ranV ->
  (forall e' ranV', e <> e' -> NatMap.find e' V = Some ranV' ->
   (forall c, In c ranV -> ~In c ranV') /\ (forall c, In c ranV' -> ~In c ranV)).

Definition wf3 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R e ranV,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (NatMap.find e V = Some ranV) ->
  ((forall c, In c ranV -> ~In c F) /\ (forall c, In c F -> ~In c ranV)) /\ NoDup(F) /\ NoDup(ranV) /\ disjoint_VPT(V).

(* WF3 MLC Read *)
Lemma wf3_mlc_read : forall lambda h_tree k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R' enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  NatMap.find enc V = Some ranV ->
  NatMap.find enc V' = Some ranV' ->
  ((forall c, In c ranV -> ~In c F) /\ (forall c, In c F -> ~In c ranV)) /\ NoDup(F) /\ NoDup(ranV) /\ disjoint_VPT(V) ->
  ((forall c, In c ranV' -> ~In c F') /\ (forall c, In c F' -> ~In c ranV')) /\ NoDup(F') /\ NoDup(ranV') /\ disjoint_VPT(V').
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
    apply (cc_hit_read_f (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H9.
    apply (cc_hit_read_v (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H10.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H3. subst.
        rewrite -> H1 in H8.
        injection H8; intros; subst c1 v0 w s.
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
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v0 w0 s0) k) = NatMap.find index k).
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
        apply (cc_update_f (single_level_cache c0 v w s) e' D l0 c (single_level_cache c1 v0 w0 s0)
        c0 v w s c1 v0 w0 s0) in H11.
        apply (cc_update_v (single_level_cache c0 v w s) e' D l0 c (single_level_cache c1 v0 w0 s0)
        c0 v w s c1 v0 w0 s0) in H12.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w0 s0) m) =
        Some (single_level_cache c1 v0 w0 s0)).
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
          (single_level_cache F' V' C' R') F V C R F' V' C' R' enc ranV ranV').
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
          specialize (WFH3 c0 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst.
          apply (H p0 p l) in IHTREE.
          apply (IHl (cache_node p) IHTREE k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' enc ranV ranV').
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
  F V C R F' V' C' R' enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  NatMap.find enc V = Some ranV ->
  NatMap.find enc V' = Some ranV' ->
  ((forall c, In c ranV -> ~In c F) /\ (forall c, In c F -> ~In c ranV)) /\ NoDup(F) /\ NoDup(ranV) /\ disjoint_VPT(V) ->
  ((forall c, In c ranV' -> ~In c F') /\ (forall c, In c F' -> ~In c ranV')) /\ NoDup(F') /\ NoDup(ranV') /\ disjoint_VPT(V').
Proof.
  unfold mlc_write.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' enc ranV ranV' WFH1; intros.
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
    F V C R F' V' C' R' enc ranV ranV' WFH1; intros.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H7). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros.
    assert (A1 := H8). destruct (cc_hit_write s0 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H9 := H8).
    destruct s; destruct s1.
    apply (cc_hit_write_f (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0) in H8.
    apply (cc_hit_write_v (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0) in H9.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H2. subst.
        rewrite -> H0 in H7.
        injection H7; intros; subst c1 v1 w s.
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
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v1 w0 s0) k) = NatMap.find index k).
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
        apply (cc_update_f (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0) in H10.
        apply (cc_update_v (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0) in H11.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w0 s0) m1) =
        Some (single_level_cache c1 v1 w0 s0)).
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
          (single_level_cache F' V' C' R') F V C R F' V' C' R' enc ranV ranV').
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
          specialize (WFH3 c0 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst.
          apply (WFH4 p0 p l) in IHTREE.
          apply (IHl (cache_node p) IHTREE k e' m0 l0 v D o mu m1 index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' enc ranV ranV').
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
Lemma wf3_clear_remapping_list : forall r ranV F V C R F' V' C' R' ranV',
  clear_remapping_list r ranV F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find r V = Some ranV ->
  NatMap.find r V' = Some ranV' ->
  ((forall c, In c ranV -> ~ In c F) /\ (forall c, In c F -> ~ In c ranV)) /\ NoDup(F) /\ NoDup(ranV) /\ disjoint_VPT(V)  ->
  ((forall c, In c ranV' -> ~ In c F') /\ (forall c, In c F' -> ~ In c ranV')) /\ NoDup(F') /\ NoDup(ranV') /\ disjoint_VPT(V') .
Proof.
  intros r l.
  induction l.
  {
    intros.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    assert (NatMap.find r (NatMap.remove r V) = None).
    apply NatMapFacts.remove_eq_o; reflexivity.
    rewrite -> H3 in H1. discriminate.
  }
  {
    intros.
    unfold clear_remapping_list in H.
    fold clear_remapping_list in H.
    destruct a.
    case_eq (NatMap.find s R). intros.
    assert (A0 := H3). destruct (NatMap.find s R) in A0, H.
    case_eq (cachelet_invalidation C (w, s)). intros.
    assert (A1 := H4). destruct (cachelet_invalidation C (w, s)) in A1, H.
    injection A0; injection A1; intros; subst w1 p; clear A0 A1.
    apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p0 w
    (enclave_ID_active r)) R) F' V' C' R' ranV').
    exact H.
    apply NatMapFacts.add_eq_o; reflexivity.
    exact H1.
    {
      destruct H2; destruct H2; destruct H5; destruct H7.
      split; split.
      intros. intros contra.
      apply in_inv in contra. destruct contra.
      subst c.
      apply NoDup_cons_iff in H7. destruct H7.
      apply H7 in H9. exact H9.
      apply H6 in H10.
      assert (In c ((w, s) :: l)).
      apply in_cons; exact H9.
      apply H10 in H11. exact H11.
      intros. intros contra.
      apply in_inv in H9. destruct H9.
      subst c.
      apply NoDup_cons_iff in H7. destruct H7.
      apply H7 in contra. exact contra.
      apply H6 in H9.
      assert (In c ((w, s) :: l)).
      apply in_cons; exact contra.
      apply H9 in H10. exact H10.
      constructor.
      apply NoDup_cons_iff in H7. destruct H7.
      intros contra.
      apply H6 in contra.
      unfold not in contra.
      assert (In (w, s) ((w, s) :: l)).
      apply in_eq; reflexivity.
      apply contra in H10. exact H10.
      exact H5. split.
      apply NoDup_cons_iff in H7. destruct H7. exact H9.
      {
        unfold disjoint_VPT in *.
        intros e ranV H9 e' ranV'0 H10 H11.
        case_eq (eqb e r); case_eq (eqb e' r); intros.
        apply cmp_to_eq in H12, H13; subst.
        unfold not in H10; destruct H10; reflexivity.
        apply cmp_to_uneq in H12; apply cmp_to_eq in H13; subst.
        assert (NatMap.find (elt:=remapping_list) r (NatMap.add r l V) = Some l).
        apply NatMapFacts.add_eq_o; reflexivity.
        rewrite -> H9 in H13; injection H13; intros; subst.
        assert (NatMap.find (elt:=remapping_list) e' (NatMap.add r l V) = NatMap.find e' V).
        apply NatMapFacts.add_neq_o; exact H10.
        rewrite -> H11 in H14; apply eq_sym in H14.
        specialize (H8 r ((w, s) :: l) H0 e' ranV'0 H10 H14); destruct H8.
        split; intros.
        intros contra. apply H15 in contra.
        apply (in_cons (w, s) c l) in H16.
        apply contra in H16. destruct H16.
        intros contra. apply (in_cons (w, s) c l) in contra.
        apply H8 in contra. apply contra in H16. destruct H16.
        apply cmp_to_eq in H12; apply cmp_to_uneq in H13; subst.
        assert (NatMap.find (elt:=remapping_list) e (NatMap.add r l V) = NatMap.find e V).
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H10.
        rewrite -> H9 in H12; apply eq_sym in H12.
        assert (NatMap.find (elt:=remapping_list) r (NatMap.add r l V) = Some l).
        apply NatMapFacts.add_eq_o; reflexivity.
        rewrite -> H11 in H14; injection H14; intros; subst.
        specialize (H8 e ranV H12 r ((w, s) :: l) H10 H0); destruct H8.
        split; intros.
        intros contra. apply (in_cons (w, s) c l) in contra.
        apply H15 in contra. apply contra in H16. destruct H16.
        intros contra. apply H8 in contra.
        apply (in_cons (w, s) c l) in H16.
        apply contra in H16. destruct H16.
        apply cmp_to_uneq in H12, H13.
        assert (NatMap.find (elt:=remapping_list) e (NatMap.add r l V) = NatMap.find e V).
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H13.
        assert (NatMap.find (elt:=remapping_list) e' (NatMap.add r l V) = NatMap.find e' V).
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H12.
        rewrite -> H9 in H14. rewrite -> H11 in H15. apply eq_sym in H14, H15.
        specialize (H8 e ranV H14 e' ranV'0 H10 H15); exact H8.
      }
    }
    discriminate.
    intros; destruct (cachelet_invalidation C (w, s)).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find s R).
    discriminate.
    discriminate.
  }
Qed.

Lemma clear_remapping_list_ranV : forall r l F V C R F' V' C' R' e ranV ranV',
  r <> e -> clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find e V = Some ranV ->
  NatMap.find e V' = Some ranV' ->
  ranV = ranV'.
Proof.
  intros r l.
  induction l.
  {
    intros.
    unfold clear_remapping_list in H0.
    injection H0; intros; subst.
    assert (NatMap.find e (NatMap.remove r V) = NatMap.find e V).
    apply NatMapFacts.remove_neq_o; exact H.
    rewrite -> H1 in H3; rewrite -> H2 in H3;
    injection H3; intros; subst.
    reflexivity.
  }
  {
    intros.
    unfold clear_remapping_list in H0.
    fold clear_remapping_list in H0.
    destruct a.
    destruct (NatMap.find s R). destruct (cachelet_invalidation C (w, s)).
    apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p w
    (enclave_ID_active r)) R) F' V' C' R' e ranV ranV').
    exact H. exact H0.
    rewrite <- H1.
    apply NatMapFacts.add_neq_o; exact H.
    exact H2.
    discriminate.
    discriminate.
  }
Qed.

Lemma disjoint_VPT_remove : forall r V,
  disjoint_VPT V -> disjoint_VPT (NatMap.remove r V).
Proof.
  intros.
  unfold disjoint_VPT in *; intros.
  assert (NatMap.find (elt:=remapping_list) r (NatMap.remove r V) = None).
  apply NatMapFacts.remove_eq_o; reflexivity.
  case_eq (eqb e r); intros.
  apply cmp_to_eq in H4; subst.
  rewrite -> H0 in H3; discriminate.
  case_eq (eqb e' r); intros.
  apply cmp_to_eq in H5; subst.
  rewrite -> H2 in H3; discriminate.
  apply cmp_to_uneq in H4, H5.
  assert (NatMap.find (elt:=remapping_list) e (NatMap.remove r V) = NatMap.find e V).
  apply NatMapFacts.remove_neq_o; apply not_eq_sym; exact H4.
  assert (NatMap.find (elt:=remapping_list) e' (NatMap.remove r V) = NatMap.find e' V).
  apply NatMapFacts.remove_neq_o; apply not_eq_sym; exact H5.
  rewrite -> H0 in H6; rewrite -> H2 in H7; apply eq_sym in H6, H7.
  specialize (H e ranV H6 e' ranV' H1 H7).
  exact H.
Qed.

Lemma disjoint_VPT_add : forall r V q l,
  NatMap.find r V = Some (q :: l) ->
  disjoint_VPT V -> disjoint_VPT (NatMap.add r l V).
Proof.
  intros.
  unfold disjoint_VPT in *; intros.
  case_eq (eqb e r); case_eq (eqb e' r); intros.
  apply cmp_to_eq in H4, H5; subst.
  unfold not in H2; destruct H2; reflexivity.
  apply cmp_to_uneq in H4; apply cmp_to_eq in H5; subst.
  assert (NatMap.find (elt:=remapping_list) r (NatMap.add r l V) = Some l).
  apply NatMapFacts.add_eq_o; reflexivity.
  assert (NatMap.find (elt:=remapping_list) e' (NatMap.add r l V)
  = NatMap.find (elt:=remapping_list) e' V).
  apply NatMapFacts.add_neq_o; exact H2.
  rewrite -> H1 in H5; injection H5; intros; subst.
  rewrite -> H3 in H6; apply eq_sym in H6.
  specialize (H0 r (q :: l) H e' ranV' H2 H6); destruct H0.
  split; intros.
  apply (in_cons q c l) in H8. apply H0 in H8. exact H8.
  apply H7 in H8. intros contra. apply (in_cons q c l) in contra.
  apply H8 in contra. exact contra.
  apply cmp_to_uneq in H5; apply cmp_to_eq in H4; subst.
  assert (NatMap.find (elt:=remapping_list) r (NatMap.add r l V) = Some l).
  apply NatMapFacts.add_eq_o; reflexivity.
  assert (NatMap.find (elt:=remapping_list) e (NatMap.add r l V)
  = NatMap.find (elt:=remapping_list) e V).
  apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H2.
  rewrite -> H3 in H4; injection H4; intros; subst.
  rewrite -> H1 in H6; apply eq_sym in H6.
  specialize (H0 e ranV H6 r (q :: l) H2 H); destruct H0.
  split; intros.
  apply H0 in H8. intros contra. apply (in_cons q c l) in contra.
  apply H8 in contra. exact contra.
  apply (in_cons q c l) in H8. apply H7 in H8. exact H8.
  apply cmp_to_uneq in H4, H5.
  assert (NatMap.find (elt:=remapping_list) e (NatMap.add r l V)
  = NatMap.find (elt:=remapping_list) e V).
  apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
  assert (NatMap.find (elt:=remapping_list) e' (NatMap.add r l V)
  = NatMap.find (elt:=remapping_list) e' V).
  apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
  rewrite -> H1 in H6; rewrite -> H3 in H7; apply eq_sym in H6, H7.
  apply (H0 e ranV H6 e' ranV' H2 H7).
Qed.

Lemma wf3_clear_remapping_list_uneq : forall r l F V C R F' V' C' R' e ranV ranV',
  e <> r -> clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find r V = Some l ->
  NatMap.find e V = Some ranV ->
  NatMap.find e V' = Some ranV' ->
  ((forall c, In c ranV -> ~ In c F) /\ (forall c, In c F -> ~ In c ranV)) /\ NoDup(F) /\ NoDup(ranV) /\ disjoint_VPT(V) ->
  ((forall c, In c l -> ~ In c F) /\ (forall c, In c F -> ~ In c l)) /\ NoDup(l) ->
  ((forall c, In c ranV' -> ~ In c F') /\ (forall c, In c F' -> ~ In c ranV')) /\ NoDup(F') /\ NoDup(ranV') /\ disjoint_VPT(V').
Proof.
  intros r l.
  induction l.
  {
    intros.
    unfold clear_remapping_list in H0.
    injection H0; intros; subst.
    assert (NatMap.find e (NatMap.remove r V) = NatMap.find e V).
    apply NatMapFacts.remove_neq_o; apply not_eq_sym; exact H.
    rewrite -> H3 in H6; rewrite -> H2 in H6.
    injection H6; intros; subst.
    split; destruct H4. exact H4.
    split; destruct H7. exact H7.
    split; destruct H8. exact H8.
    apply disjoint_VPT_remove; exact H9.
  }
  {
    intros.
    unfold clear_remapping_list in H0.
    fold clear_remapping_list in H0.
    destruct a.
    case_eq (NatMap.find s R). intros.
    assert (A0 := H6). destruct (NatMap.find s R) in A0, H0.
    case_eq (cachelet_invalidation C (w, s)). intros.
    assert (A1 := H7). destruct (cachelet_invalidation C (w, s)) in A1, H0.
    injection A0; injection A1; intros; subst w1 p; clear A0 A1.
    assert (ranV = ranV').
    apply (clear_remapping_list_ranV r l ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s
    (update p0 w (enclave_ID_active r)) R) F' V' C' R' e ranV ranV').
    apply not_eq_sym; exact H. exact H0.
    rewrite <- H2. apply NatMapFacts.add_neq_o. apply not_eq_sym; exact H.
    exact H3. subst ranV'.
    apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p0 w
    (enclave_ID_active r)) R) F' V' C' R' e ranV ranV).
    exact H. exact H0.
    apply NatMapFacts.add_eq_o; reflexivity.
    rewrite <- H2. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H.
    exact H3.
    {
      destruct H4; destruct H4; destruct H8; destruct H10.
      destruct H5 as [ H5 N ]. destruct H5 as [ H5 H5' ].
      assert (V0 := H11).
      unfold disjoint_VPT in H11.
      specialize (H11 e ranV H2 r ((w, s) :: l) H H1); destruct H11.
      split; split.
      intros. intros contra.
      apply in_inv in contra. destruct contra.
      subst c. apply H11 in H13.
      unfold In in H13. destruct H13. left; reflexivity.
      apply H9 in H14. apply H14 in H13. exact H13.
      intros. intros contra.
      apply in_inv in H13. destruct H13.
      subst c. apply H11 in contra.
      unfold In in contra. destruct contra. left; reflexivity.
      apply H9 in H13. apply H13 in contra. exact contra.
      constructor.
      assert (In (w, s) ((w, s) :: l)).
      apply in_eq; reflexivity.
      apply H5 in H13. exact H13. exact H8.
      split. exact H10.
      apply (disjoint_VPT_add r V (w, s) l).
      exact H1. exact V0.
    }
    destruct H5; destruct H5.
    split. split; intros.
    intros contra. apply in_inv in contra. destruct contra. subst c.
    apply NoDup_cons_iff in H8. destruct H8.
    apply H8 in H10. exact H10.
    apply (in_cons (w, s) c l) in H10. apply H9 in H11.
    apply H11 in H10. exact H10.
    intros contra. apply in_inv in H10. destruct H10. subst c.
    apply NoDup_cons_iff in H8. destruct H8.
    apply H8 in contra. exact contra.
    apply (in_cons (w, s) c l) in contra. apply H9 in H10.
    apply H10 in contra. exact contra.
    apply NoDup_cons_iff in H8. destruct H8. exact H10.
    discriminate.
    intros; destruct (cachelet_invalidation C (w, s)).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find s R).
    discriminate.
    discriminate.
  }
Qed.

Lemma hard : forall r l F V C R F' V' C' R' e ranV ranV',
  clear_remapping_list r l F V C R = Some (single_level_cache F' V' C' R') ->
  NatMap.find r V = Some l ->
  NatMap.find e V = Some ranV ->
  NatMap.find e V' = Some ranV' ->
  (forall e' l', NatMap.find e' V = Some l' -> ((forall c, In c l' -> ~ In c F) /\ (forall c, In c F -> ~ In c l'))
  /\ NoDup(F) /\ NoDup(l') /\ disjoint_VPT(V)) ->
  (forall e' l', NatMap.find e' V' = Some l' -> ((forall c, In c l' -> ~ In c F') /\ (forall c, In c F' -> ~ In c l'))
  /\ NoDup(F') /\ NoDup(l') /\ disjoint_VPT(V')).
Proof.
  intros r l.
  induction l.
  {
    intros.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    case_eq (eqb e r); intros V0.
    {
      apply cmp_to_eq in V0; subst.
      assert (NatMap.find r (NatMap.remove r V) = None).
      apply NatMapFacts.remove_eq_o; reflexivity.
      rewrite -> H2 in H5. discriminate.
    }
    {
      apply cmp_to_uneq in V0.
      assert (NatMap.find e (NatMap.remove r V) = NatMap.find e V).
      apply NatMapFacts.remove_neq_o; apply not_eq_sym; exact V0.
      rewrite -> H2 in H5; rewrite -> H1 in H5.
      injection H5; intros; subst.
      specialize (H3

(* TODO *)

      split; destruct H4. exact H4.
      split; destruct H7. exact H7.
      split; destruct H8. exact H8.
      apply disjoint_VPT_remove; exact H9.
    }
  }

Lemma wf3_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R' enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  NatMap.find (elt:=remapping_list) enc V = Some ranV ->
  NatMap.find (elt:=remapping_list) enc V' = Some ranV' ->
  (forall e l, NatMap.find e V = Some l -> ((forall c, In c ranV -> ~In c F) /\ (forall c, In c F -> ~In c ranV)) /\ NoDup(F) /\ NoDup(ranV) /\ disjoint_VPT(V)) ->
  ((forall c, In c ranV' -> ~In c F') /\ (forall c, In c F' -> ~In c ranV')) /\ NoDup(F') /\ NoDup(ranV') /\ disjoint_VPT(V').
Proof.
  unfold mlc_deallocation.
  intros lambda h_tree state.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros lambda IHTREE k k' index psi psi' F V C R
    F' V' C' R' enc ranV ranV' WFH; intros.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    injection H; intros; subst k'.
    rewrite -> H0 in H1.
    injection H1; intros; subst psi psi'.
    injection H7; intros; subst F' V' C' R'.
    rewrite -> H5 in H4; injection H4; intros; subst.
    apply (H6 enc ranV). exact H5.
    discriminate.
  }
  {
    intros lambda IHTREE k k' index psi psi' F V C R
    F' V' C' R' enc ranV ranV' WFH; intros.
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
      case_eq (NatMap.find enc v). intros.
      destruct l.
      {
        apply (IHl root_node WFH1 (NatMap.add index (single_level_cache c v w s) k) k' index
        (single_level_cache c v w s) psi' c v w s F' V' C' R' enc r0 ranV').
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
        injection A0; injection H2; intros; subst c0 v0 w0 s0 r1; clear A0.
        case_eq (eqb r enc); intros.
        apply cmp_to_eq in H11; subst enc.
        apply (wf3_clear_remapping_list r r2 F V C R c v w s r0) in H8.
        exact H8. exact H10. exact H9.
        rewrite -> H4 in H10.
        injection H10; intros; subst.
        exact H6.
        apply cmp_to_uneq in H11.
        apply (wf3_clear_remapping_list_uneq r r2 F V C R c v w s enc ranV r0).
        apply not_eq_sym; exact H11. exact H8. exact H10.
        exact H4. exact H9. exact H6.
        destruct H6. destruct H12.


        assert (H12 := H8).
        apply (clear_remapping_list_ranV r r2 F V C R c v w s enc ranV r0) in H8.
        subst r0.
        destruct H6; destruct H6; destruct H8.
        split; split.
        intros. intros contra.
        apply H6 in H15.
        assert (In c0 F -> In c0 c).
        apply (clear_remapping_list_f r r2 F V C R c v w s c0) in H12.
        intros; exact H12. exact H10.
        




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