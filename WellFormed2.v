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

(* Disjoint VPT (used in wf3) *)
Definition disjoint_VPT (V: VPT): Prop :=
  forall e ranV, NatMap.find e V = Some ranV ->
  (forall e' ranV', e <> e' -> NatMap.find e' V = Some ranV' ->
   (forall c, In c ranV -> ~In c ranV') /\ (forall c, In c ranV' -> ~In c ranV)).

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

Lemma disjoint_VPT_add2 : forall r V q l,
  NatMap.find r V = Some l ->
  (forall e l', NatMap.find e V = Some l' -> ~In q l') ->
  disjoint_VPT V -> disjoint_VPT (NatMap.add r (q :: l) V).
Proof.
  intros.
  unfold disjoint_VPT in *; intros.
  case_eq (eqb e r); case_eq (eqb e' r); intros.
  apply cmp_to_eq in H5, H6; subst.
  assert (r = r). reflexivity. apply H3 in H5. destruct H5.
  apply cmp_to_eq in H6. apply cmp_to_uneq in H5. subst e.
  assert (Some ranV = Some (q :: l)).
  rewrite <- H2. apply NatMapFacts.add_eq_o; reflexivity.
  injection H6; intros; subst.
  assert (NatMap.find (elt:=remapping_list) e' V = Some ranV').
  apply eq_sym. rewrite <- H4. apply NatMapFacts.add_neq_o; exact H3.
  split; intros. intros contra. apply in_inv in H8. destruct H8. subst.
  specialize (H0 e' ranV' H7). apply H0 in contra. exact contra.
  specialize (H1 r l H e' ranV' H3 H7). destruct H1. apply H1 in H8.
  apply H8 in contra. exact contra.
  intros contra. apply in_inv in contra. destruct contra. subst.
  specialize (H0 e' ranV' H7). apply H0 in H8. exact H8.
  specialize (H1 r l H e' ranV' H3 H7). destruct H1. apply H1 in H9.
  apply H9 in H8. exact H8.
  apply cmp_to_uneq in H6. apply cmp_to_eq in H5. subst e'.
  assert (Some ranV' = Some (q :: l)).
  rewrite <- H4. apply NatMapFacts.add_eq_o; reflexivity.
  injection H5; intros; subst.
  assert (NatMap.find (elt:=remapping_list) e V = Some ranV).
  apply eq_sym. rewrite <- H2. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H3.
  split; intros. intros contra. apply in_inv in contra. destruct contra. subst.
  specialize (H0 e ranV H7). apply H0 in H8. exact H8.
  specialize (H1 e ranV H7 r l H3 H). destruct H1. apply H1 in H8.
  apply H8 in H9. exact H9.
  intros contra. apply in_inv in H8. destruct H8. subst.
  specialize (H0 e ranV H7). apply H0 in contra. exact contra.
  specialize (H1 e ranV H7 r l H3 H). destruct H1. apply H9 in H8.
  apply H8 in contra. exact contra.
  apply cmp_to_uneq in H5, H6.
  assert (NatMap.find e V = Some ranV). apply eq_sym.
  rewrite <- H2. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H6.
  assert (NatMap.find e' V = Some ranV'). apply eq_sym.
  rewrite <- H4. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
  specialize (H1 e ranV H7 e' ranV' H3 H8). destruct H1.
  split; intros.
  apply H1. exact H10.
  apply H9. exact H10.
Qed.

(* Well-Formed 3 *)
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
Lemma NoDup_append : forall l l' (c : cachelet_index),
  NoDup(l) /\ NoDup(l') -> l = c :: nil -> ~In c l' -> NoDup(l ++ l').
Proof.
  intros.
  destruct H.
  rewrite -> H0.
  constructor. exact H1. exact H2.
Qed.

Lemma NoDup_remove : forall c F,
  NoDup(F) -> NoDup(remove eq_dec_cachelet c F).
Proof.
  intros.
  induction F.
  assert (~In c nil). unfold In; unfold not; auto.
  apply (notin_remove eq_dec_cachelet nil c) in H0.
  rewrite -> H0. exact H.
  apply NoDup_cons_iff in H. destruct H.
  unfold remove. case_eq (eq_dec_cachelet c a). intros.
  apply IHF. exact H0.
  intros. constructor. intros contra. apply H.
  assert (In a F /\ a <> c -> In a F). intros. destruct H2. exact H2.
  apply H2. apply (in_remove eq_dec_cachelet F a c). exact contra.
  apply IHF. exact H0.
Qed.

Lemma remove_CAT_not_in : forall c F remF,
  remove_CAT c F = Some remF -> ~In c remF.
Proof.
  intros.
  unfold remove_CAT in H.
  destruct (in_bool c F).
  injection H; intros; subst.
  apply remove_In. discriminate.
Qed.

Lemma remove_CAT_in : forall b c F remF,
  remove_CAT b F = Some remF -> b <> c -> In c F -> In c remF.
Proof.
  intros.
  unfold remove_CAT in H.
  case_eq (in_bool b F); intros.
  assert (A0 := H2). destruct (in_bool b F) in A0, H.
  injection H; intros; subst.
  apply in_bool_iff in H2. apply in_in_remove.
  apply not_eq_sym; exact H0. exact H1.
  discriminate.
  assert (A0 := H2).
  destruct (in_bool b F) in A0, H; discriminate.
Qed.

Lemma remove_CAT_inv_subset : forall w s w0 s0 F remF,
  remove_CAT (w, s) F = Some remF ->
  w0 <> w \/ s0 <> s ->
  ~In (w0, s0) F -> ~In (w0, s0) remF.
Proof.
  intros. unfold remove_CAT in H.
  destruct (in_bool (w, s) F).
  injection H; intros; subst.
  intros contra. apply in_remove in contra.
  destruct contra. apply H1 in H2. exact H2.
  discriminate.
Qed.

Lemma wf3_cachelet_allocation : forall n r F V C R F' V' C' R' e ranV ranV',
  cachelet_allocation n r (single_level_cache F V C R) = Some (single_level_cache F' V' C' R') ->
  NatMap.find e V = Some ranV ->
  NatMap.find e V' = Some ranV' ->
  (forall e' l', NatMap.find e' V = Some l' -> ((forall c, In c l' -> ~ In c F) /\ (forall c, In c F -> ~ In c l'))
  /\ NoDup(F) /\ NoDup(l') /\ disjoint_VPT(V)) ->
  (forall e' l', NatMap.find e' V' = Some l' -> ((forall c, In c l' -> ~ In c F') /\ (forall c, In c F' -> ~ In c l'))
  /\ NoDup(F') /\ NoDup(l') /\ disjoint_VPT(V')).
Proof.
  intros n r.
  induction n.
  {
    intros.
    unfold cachelet_allocation in H.
    unfold recursive_cachelet_allocation in H.
    injection H; intros; subst F' V' C' R'.
    specialize (H2 e' l' H3); exact H2.
  }
  {
    intros F V C R F' V' C' R' e ranV ranV' H H0 H1 H2.
    unfold cachelet_allocation in H.
    unfold recursive_cachelet_allocation in H.
    fold recursive_cachelet_allocation in H.
    case_eq (way_first_allocation F). intros c H3.
    assert (A0 := H3). destruct (way_first_allocation F) in H, A0.
    destruct c0.
    case_eq (NatMap.find s R). intros p H4.
    assert (A1 := H4). destruct (NatMap.find s R) in H, A1.
    case_eq (NatMap.find r V). intros r0 H5.
    assert (A2 := H5). destruct (NatMap.find r V) in H, A2.
    case_eq (remove_CAT (w, s) F). intros c0 F0.
    assert (A3 := F0). destruct (remove_CAT (w, s) F) in H, A3.
    injection A0; injection A1; injection A2; injection A3;
    intros X0 X1 X2 X3; subst; clear A0 A1 A2.
    case_eq (eqb r e); intros V0.
    {
      apply cmp_to_eq in V0; subst e.
      apply (IHn c0 (NatMap.add r ((w, s) :: r0) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R' r ((w, s) :: r0) ranV').
      unfold cachelet_allocation; exact H.
      apply NatMapFacts.add_eq_o; reflexivity. exact H1.
      intros; case_eq (eqb e' r); intros V0.
      {
        apply cmp_to_eq in V0; subst e'.
        assert (NatMap.find (elt:=remapping_list) r (NatMap.add r ((w, s) :: r0) V)
        = Some ((w, s) :: r0)).
        apply NatMapFacts.add_eq_o;  reflexivity.
        rewrite -> H6 in H7; injection H7; intros; subst. assert (FV := H2).
        specialize (H2 r ranV H0); destruct H2; destruct H2; destruct H8; destruct H10.
        assert (DJV := H11); unfold disjoint_VPT in H11.
        rewrite -> H0 in H5. injection H5; intros; subst.
        split; split. intros. intros contra.
        apply in_inv in H12; destruct H12. subst.
        apply remove_CAT_not_in in F0. apply F0 in contra. exact contra.
        apply (remove_CAT_f c (w, s) F c0) in contra.
        apply H9 in contra. apply contra in H12. destruct H12. exact F0.
        intros; intros contra. apply in_inv in contra. destruct contra. subst.
        apply (remove_CAT_not_in (w, s) F c0) in F0. apply F0 in H12. exact H12.
        intros. apply (remove_CAT_f c (w, s) F c0) in H12. apply H9 in H12.
        apply H12 in H13. exact H13. exact F0.
        unfold remove_CAT in F0. destruct (in_bool (w, s) F).
        injection F0; intros; subst. apply NoDup_remove. exact H8.
        discriminate.
        split. constructor. intros contra. unfold remove_CAT in F0.
        case_eq (in_bool (w, s) F). intros. assert (A0 := H12).
        destruct (in_bool (w, s) F) in A0, H. apply in_bool_iff in H12.
        apply H9 in H12. apply H12 in contra. exact contra.
        discriminate.
        intros; destruct (in_bool (w, s) F); discriminate. exact H10.
        apply (disjoint_VPT_add2 r V (w, s) r0). exact H0.
        intros. specialize (FV e l' H12). destruct FV. destruct H13.
        apply H15. unfold remove_CAT in F0. case_eq (in_bool (w, s) F); intros.
        assert (A0 := H16). destruct (in_bool (w, s) F) in F0, A0.
        apply in_bool_iff in H16. exact H16.
        discriminate.
        intros; destruct (in_bool (w, s) F); discriminate. exact DJV.
      }
      {
        apply cmp_to_uneq in V0.
        assert (NatMap.find e' V = Some l').
        rewrite <- H6. apply eq_sym. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact V0.
        specialize (H2 e' l' H7) as FV.
        destruct FV; destruct H8; destruct H9; destruct H11.
        assert (DJV := H12); unfold disjoint_VPT in H12.
        split; split. intros.
        case_eq (eq_cachelet_index c (w, s)); intros;
        unfold eq_cachelet_index in H14; destruct c.
        apply cmp_to_eq_and in H14; destruct H14; subst w0 s0.
        apply (remove_CAT_not_in (w, s) F c0). exact F0.
        apply cmp_to_uneq_and in H14.
        apply H8 in H13. 
        apply (remove_CAT_inv_subset w s w0 s0 F c0).
        exact F0. exact H14. exact H13.
        intros; intros contra. apply H8 in contra.
        apply (remove_CAT_f c (w, s) F c0) in F0. apply contra in F0.
        exact F0. exact H13.
        unfold remove_CAT in F0. destruct (in_bool (w, s) F).
        injection F0; intros; subst.
        apply NoDup_remove. exact H9. discriminate.
        split. exact H11.
        apply (disjoint_VPT_add2 r V (w, s) r0). exact H5.
        intros. specialize (H2 e l'0 H13). destruct H2. destruct H2.
        apply H15. unfold remove_CAT in F0. case_eq (in_bool (w, s) F); intros.
        assert (A0 := H16). destruct (in_bool (w, s) F) in F0, A0.
        apply in_bool_iff in H16. exact H16.
        discriminate.
        intros; destruct (in_bool (w, s) F); discriminate. exact DJV.
      }
    }
    {
      apply cmp_to_uneq in V0.
      apply (IHn c0 (NatMap.add r ((w, s) :: r0) V) C
      (NatMap.add s (update p w (enclave_ID_active r)) R) F' V' C' R' e ranV ranV').
      unfold cachelet_allocation; exact H.
      rewrite <- H0. apply NatMapFacts.add_neq_o; exact V0. exact H1.
      intros; case_eq (eqb e' r); intros V1.
      {
        apply cmp_to_eq in V1; subst e'.
        assert (Some l' = Some ((w, s) :: r0)).
        rewrite <- H6. apply NatMapFacts.add_eq_o; reflexivity.
        injection H7; intros; subst.
        assert (V2 := H2). specialize (H2 r r0 H5).
        destruct H2; destruct H2; destruct H8; destruct H10.
        assert (DJV := H11); unfold disjoint_VPT in H11.
        split; split. intros.
        apply in_inv in H12. destruct H12. subst.
        apply (remove_CAT_not_in (w, s) F c0). exact F0.
        intros contra. apply (remove_CAT_f c (w, s) F c0) in contra.
        apply H9 in contra. apply contra in H12. exact H12. exact F0.
        intros. intros contra. apply in_inv in contra. destruct contra. subst.
        apply (remove_CAT_not_in (w, s) F c0) in F0. apply F0 in H12. exact H12.
        apply (remove_CAT_f c (w, s) F c0) in H12. apply H9 in H12.
        apply H12 in H13. exact H13. exact F0.
        unfold remove_CAT in F0. destruct (in_bool (w, s) F).
        injection F0; intros; subst.
        apply NoDup_remove. exact H8. discriminate.
        split. constructor.
        apply H9. unfold remove_CAT in F0.
        case_eq (in_bool (w, s) F); intros.
        apply in_bool_iff; exact H12.
        destruct (in_bool (w, s) F); discriminate. exact H10.
        apply (disjoint_VPT_add2 r V (w, s) r0). exact H5.
        intros. specialize (V2 e0 l' H12). destruct V2. destruct H13.
        apply H15. unfold remove_CAT in F0. case_eq (in_bool (w, s) F); intros.
        assert (A0 := H16). destruct (in_bool (w, s) F) in F0, A0.
        apply in_bool_iff in H16. exact H16.
        discriminate.
        intros; destruct (in_bool (w, s) F); discriminate. exact DJV.
      }
      {
        apply cmp_to_uneq in V1.
        assert (NatMap.find e' V = Some l').
        apply eq_sym; rewrite <- H6; apply NatMapFacts.add_neq_o; apply not_eq_sym; exact V1.
        specialize (H2 e' l' H7) as FV.
        destruct FV; destruct H8; destruct H9; destruct H11.
        assert (DJV := H12); unfold disjoint_VPT in H12.
        split; split. intros. intros contra.
        apply (remove_CAT_f c (w, s) F c0) in contra.
        apply H10 in contra. apply contra in H13. exact H13. exact F0.
        intros. apply H10. apply (remove_CAT_f c (w, s) F c0).
        exact F0. exact H13.
        unfold remove_CAT in F0. destruct (in_bool (w, s) F).
        injection F0; intros; subst.
        apply NoDup_remove. exact H9. discriminate.
        split. exact H11.
        apply (disjoint_VPT_add2 r V (w, s) r0). exact H5.
        intros. specialize (H2 e0 l'0 H13). destruct H2. destruct H2.
        apply H15. unfold remove_CAT in F0. case_eq (in_bool (w, s) F); intros.
        assert (A0 := H16). destruct (in_bool (w, s) F) in F0, A0.
        apply in_bool_iff in H16. exact H16.
        discriminate.
        intros; destruct (in_bool (w, s) F); discriminate. exact DJV.
      }
    }
    discriminate.
    intros; destruct (remove_CAT (w, s) F).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find r V).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find s R).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (way_first_allocation F).
    discriminate.
    discriminate.
  }
Qed.

Lemma wf3_mlc_alloc : forall lambda h_tree n state k k' index psi psi' F V C R F' V' C' R' enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_allocation n state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  NatMap.find (elt:=remapping_list) enc V = Some ranV ->
  NatMap.find (elt:=remapping_list) enc V' = Some ranV' ->
  (forall e l, NatMap.find e V = Some l -> ((forall c, In c l -> ~In c F) /\ (forall c, In c F -> ~In c l)) /\ NoDup(F) /\ NoDup(l) /\ disjoint_VPT(V)) ->
  ((forall c, In c ranV' -> ~In c F') /\ (forall c, In c F' -> ~In c ranV')) /\ NoDup(F') /\ NoDup(ranV') /\ disjoint_VPT(V').
Proof.
  unfold mlc_allocation.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros lambda IHTREE n state k k' index psi psi' F V C R
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
    intros lambda IHTREE n state k k' index psi psi' F V C R
    F' V' C' R' enc ranV ranV' WFH; intros.
    destruct state; destruct e.
    unfold recursive_mlc_allocation in H.
    fold recursive_mlc_allocation in H.
    destruct n. discriminate.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H7). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_allocation n r s0). intros.
    assert (A1 := H8). destruct (cachelet_allocation n r s0) in A1, H.
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
        apply (IHl root_node WFH1 n0 (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add index (single_level_cache c v w s) k) k' index (single_level_cache c v w s) psi' c v w s F' V' C' R' enc r0 ranV').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H3.
        exact H9.
        exact H5.
        subst psi. apply (wf3_cachelet_allocation n r F V C R c v w s enc ranV r0).
        exact H8. exact H4. exact H9. exact H6.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c0 index (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 index (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 index p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE n0 (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add index (single_level_cache c v w s) k) k' index (single_level_cache c v w s) psi' c v w s F' V' C' R' enc r0 ranV').
        exact WFH.
        exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        exact H3.
        exact H9.
        exact H5.
        subst psi. apply (wf3_cachelet_allocation n r F V C R c v w s enc ranV r0).
        exact H8. exact H4. exact H9. exact H6.
      }
      {
        intros. destruct psi.
        injection H2; intros; subst c0 v0 w0 s0.
        apply (cachelet_allocation_v n r F V C R c v w s enc) in H8.
        assert (NatMap.find enc V <> None).
        intros contra; rewrite -> contra in H4; discriminate.
        apply NatMapFacts.in_find_iff in H10.
        apply NatMapFacts.not_find_in_iff in H9.
        apply H8 in H10. apply H9 in H10. destruct H10.
      }
    }
    {
      intros; apply cmp_to_uneq in H9.
      destruct l.
      {
        apply (IHl root_node WFH1 n0 (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add a s1 k) k' index psi psi' F V C R F' V' C' R' enc ranV ranV').
        exact WFH.
        unfold mlc_allocation. exact H.
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
        specialize (WFH3 c a (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 a (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 a p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE n0 (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add a s1 k) k' index psi psi' F V C R F' V' C' R' enc ranV ranV').
        exact WFH.
        unfold mlc_allocation. exact H.
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
    intros; destruct (cachelet_allocation n r s0).
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
Qed.

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

Lemma wf3_clear_remapping_list : forall r l F V C R F' V' C' R' e ranV ranV',
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
    case_eq (eqb e' r); intros V0.
    {
      apply cmp_to_eq in V0; subst.
      assert (NatMap.find r (NatMap.remove r V) = None).
      apply NatMapFacts.remove_eq_o; reflexivity.
      rewrite -> H4 in H5. discriminate.
    }
    {
      apply cmp_to_uneq in V0.
      assert (NatMap.find (elt:=remapping_list) e' (NatMap.remove r V) = NatMap.find e' V).
      apply NatMapFacts.remove_neq_o; apply not_eq_sym; exact V0.
      rewrite -> H4 in H5; apply eq_sym in H5.
      specialize (H3 e' l' H5).
      destruct H3; split. exact H3.
      destruct H6; split. exact H6.
      destruct H7; split. exact H7.
      apply disjoint_VPT_remove; exact H8.
    }
  }
  {
    intros F V C R F' V' C' R' e ranV ranV' H H0 H1 H2 H3.
    unfold clear_remapping_list in H.
    fold clear_remapping_list in H.
    destruct a.
    case_eq (NatMap.find s R). intros p H4.
    assert (A0 := H4). destruct (NatMap.find s R) in A0, H.
    case_eq (cachelet_invalidation C (w, s)). intros w0 H5.
    assert (A1 := H5). destruct (cachelet_invalidation C (w, s)) in A1, H.
    injection A0; injection A1; intros X Y; subst w1 p; clear A0 A1.
    case_eq (eqb e r); intros V0.
    {
      apply cmp_to_eq in V0; subst e.
      apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p0 w
      (enclave_ID_active r)) R) F' V' C' R' r l ranV').
      exact H.
      apply NatMapFacts.add_eq_o; reflexivity.
      apply NatMapFacts.add_eq_o; reflexivity.
      exact H2.
      intros.
      case_eq (eqb e' r); intros.
      {
        apply cmp_to_eq in H7; subst e'.
        assert (NatMap.find (elt:=remapping_list) r (NatMap.add r l V) = Some l).
        apply NatMapFacts.add_eq_o; reflexivity.
        rewrite -> H6 in H7; injection H7; intros; subst l'.
        rewrite -> H0 in H1; injection H1; intros; subst ranV.
        assert (FV := H3). specialize (H3 r ((w, s) :: l) H0).
        destruct H3; destruct H3; destruct H8; destruct H10.
        split; split. intros. intros contra.
        apply in_inv in contra. destruct contra. subst c.
        apply NoDup_cons_iff in H10. destruct H10. apply H10 in H12. exact H12.
        apply H9 in H13. apply (in_cons (w, s) c l) in H12.
        apply H13 in H12. exact H12.
        intros. intros contra.
        apply in_inv in H12. destruct H12. subst c.
        apply NoDup_cons_iff in H10. destruct H10. apply H10 in contra. exact contra.
        apply H9 in H12. apply (in_cons (w, s) c l) in contra.
        apply H12 in contra. exact contra.
        constructor.
        specialize (FV r ((w, s) :: l) H0). destruct FV; destruct H12.
        intros contra. apply H14 in contra.
        assert (In (w, s) ((w, s) :: l)). apply in_eq; reflexivity.
        apply contra in H15; exact H15. exact H8.
        split. apply NoDup_cons_iff in H10; destruct H10; exact H12.
        apply (disjoint_VPT_add r V (w, s) l). exact H0. exact H11.
      }
      {
        apply cmp_to_uneq in H7.
        assert (NatMap.find (elt:=remapping_list) e' (NatMap.add r l V) = NatMap.find e' V).
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H7.
        rewrite -> H8 in H6.
        rewrite -> H0 in H1; injection H1; intros; subst ranV.
        assert (FV := H3). specialize (H3 e' l' H6).
        destruct H3; destruct H3; destruct H9; destruct H11.
        assert (DJV := H12). unfold disjoint_VPT in H12.
        split; split. intros. intros contra.
        apply in_inv in contra. destruct contra. subst c.
        specialize (H12 e' l' H6 r ((w, s) :: l) H7 H0). destruct H12.
        apply H12 in H13.
        assert (In (w, s) ((w, s) :: l)). apply in_eq; reflexivity.
        apply H13 in H15. exact H15.
        apply H10 in H14. apply H14 in H13. exact H13.
        intros. intros contra.
        apply in_inv in H13. destruct H13. subst c.
        specialize (H12 e' l' H6 r ((w, s) :: l) H7 H0). destruct H12.
        apply H12 in contra.
        assert (In (w, s) ((w, s) :: l)). apply in_eq; reflexivity.
        apply contra in H14. exact H14.
        apply H10 in H13. apply H13 in contra. exact contra.
        constructor.
        specialize (FV r ((w, s) :: l) H0). destruct FV. destruct H13.
        apply H13. apply in_eq; reflexivity. exact H9.
        split. exact H11.
        apply (disjoint_VPT_add r V (w, s) l). exact H0. exact DJV.
      }
    }
    {
      apply cmp_to_uneq in V0.
      apply (IHl ((w, s) :: F) (NatMap.add r l V) w0 (NatMap.add s (update p0 w
      (enclave_ID_active r)) R) F' V' C' R' e ranV ranV').
      exact H.
      apply NatMapFacts.add_eq_o; reflexivity.
      rewrite <- H1. apply NatMapFacts.add_neq_o; apply not_eq_sym; exact V0.
      exact H2.
      intros.
      case_eq (eqb e' r); intros.
      {
        apply cmp_to_eq in H7; subst e'.
        assert (NatMap.find (elt:=remapping_list) r (NatMap.add r l V) = Some l).
        apply NatMapFacts.add_eq_o; reflexivity.
        rewrite -> H6 in H7; injection H7; intros; subst l'.
        specialize (H3 r ((w, s) :: l) H0).
        destruct H3; destruct H3; destruct H8; destruct H10.
        split; split.
        intros. intros contra.
        apply in_inv in contra. destruct contra. subst c.
        apply NoDup_cons_iff in H10. destruct H10. apply H10 in H12.
        exact H12. apply H9 in H13. apply (in_cons (w, s) c l) in H12.
        apply H13 in H12. exact H12.
        intros. intros contra.
        apply in_inv in H12. destruct H12. subst c.
        apply NoDup_cons_iff in H10. destruct H10. apply H10 in contra.
        exact contra. apply H9 in H12. apply (in_cons (w, s) c l) in contra.
        apply H12 in contra. exact contra.
        apply NoDup_cons_iff. split. intros contra.
        assert (In (w, s) ((w, s) :: l)). apply in_eq; reflexivity.
        apply H3 in H12. apply H12 in contra. exact contra. exact H8.
        split. apply NoDup_cons_iff in H10. destruct H10. exact H12.
        apply (disjoint_VPT_add r V (w, s) l). exact H0. exact H11.
      }
      {
        apply cmp_to_uneq in H7.
        assert (NatMap.find (elt:=remapping_list) e' (NatMap.add r l V) = NatMap.find e' V).
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H7.
        rewrite -> H8 in H6.
        assert (FV := H3). specialize (H3 e' l' H6).
        destruct H3; destruct H3; destruct H9; destruct H11.
        assert (DJV := H12). unfold disjoint_VPT in H12.
        split; split. intros. intros contra.
        apply in_inv in contra. destruct contra. subst c.
        assert (In (w, s) ((w, s) :: l)).
        apply in_eq; reflexivity. specialize (H12 e' l' H6 r ((w, s) :: l) H7 H0).
        destruct H12. apply H12 in H13. apply H13 in H14. exact H14.
        apply H10 in H14. apply H14 in H13. exact H13.
        intros. intros contra.
        apply in_inv in H13. destruct H13. subst c.
        assert (In (w, s) ((w, s) :: l)).
        apply in_eq; reflexivity. specialize (H12 e' l' H6 r ((w, s) :: l) H7 H0).
        destruct H12. apply H12 in H13. exact H13. exact contra.
        apply H10 in H13. apply H13 in contra. exact contra.
        constructor.
        assert (In (w, s) ((w, s) :: l)).
        apply in_eq; reflexivity.
        specialize (FV r ((w, s) :: l) H0). destruct FV; destruct H14.
        apply H14 in H13. exact H13. exact H9. split. exact H11.
        apply (disjoint_VPT_add r V (w, s) l). exact H0. exact DJV.
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

Lemma wf3_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R' enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  NatMap.find (elt:=remapping_list) enc V = Some ranV ->
  NatMap.find (elt:=remapping_list) enc V' = Some ranV' ->
  (forall e l, NatMap.find e V = Some l -> ((forall c, In c l -> ~In c F) /\ (forall c, In c F -> ~In c l)) /\ NoDup(F) /\ NoDup(l) /\ disjoint_VPT(V)) ->
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
        case_eq (NatMap.find r v0). intros r1 H10.
        assert (A0 := H10). destruct (NatMap.find r v0) in A0, H8.
        injection A0; injection H2; intros X0 X1 X2 X3 X4; subst c0 v0 w0 s0 r1; clear A0.
        apply (wf3_clear_remapping_list r r2 F V C R c v w s enc ranV r0).
        exact H8. exact H10. exact H4. exact H9. exact H6.
        discriminate.
        intros; destruct (NatMap.find r v0).
        discriminate.
        discriminate.
      }
      {
        destruct lambda.
        rewrite -> WFH1 in IHTREE. discriminate.
        specialize (WFH3 c0 index (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 index (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 index p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE (NatMap.add index (single_level_cache c v w s) k) k' index
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
        case_eq (NatMap.find r v0). intros r1 H10.
        assert (A0 := H10). destruct (NatMap.find r v0) in A0, H8.
        injection A0; injection H2; intros X0 X1 X2 X3 X4; subst c0 v0 w0 s0 r1; clear A0.
        apply (wf3_clear_remapping_list r r2 F V C R c v w s enc ranV r0).
        exact H8. exact H10. exact H4. exact H9. exact H6.
        discriminate.
        intros; destruct (NatMap.find r v0).
        discriminate.
        discriminate.
      }
      {
        intros. destruct psi.
        injection H2; intros; subst c0 v0 w0 s0.
        case_eq (eqb r enc); intros V0.
        {
          apply cmp_to_eq in V0; subst enc.
          apply (wf2_mlc_dealloc_helper r l k k' (NatMap.add index (single_level_cache c v w s) k)
          index F V C R c v w s F' V' C' R' ranV) in H.
          rewrite -> H in H5; discriminate.
          exact H7. subst psi'; exact H1. exact H4. exact H9.
          apply NatMapFacts.add_eq_o; reflexivity.
        }
        {
          apply (cachelet_deallocation_v r (single_level_cache F V C R) (single_level_cache c v w s)
          F V C R c v w s enc) in H8.
          assert (NatMap.find enc V <> None). intros contra.
          rewrite -> H4 in contra. discriminate.
          apply NatMapFacts.in_find_iff in H10.
          apply NatMapFacts.not_find_in_iff in H9.
          apply H8 in H10.
          apply H9 in H10.
          destruct H10.
          reflexivity.
          reflexivity.
          apply cmp_to_uneq in V0; exact V0.
        }
      }
    }
    {
      intros; apply cmp_to_uneq in H9.
      destruct l.
      {
        apply (IHl root_node WFH1 (NatMap.add a s1 k) k' index
        psi psi' F V C R F' V' C' R' enc ranV ranV').
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
        specialize (WFH3 c a (p :: l) IHTREE).
        unfold get_cache_ID_path in IHTREE. discriminate.
        specialize (WFH2 p0 a (p :: l) IHTREE).
        injection WFH2; intros; subst p0.
        apply (WFH4 a p l) in IHTREE.
        apply (IHl (cache_node p) IHTREE (NatMap.add a s1 k) k' index
        psi psi' F V C R F' V' C' R' enc ranV ranV').
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
Qed.

(* WF3 Preservation *)
Lemma wf3_preservation : forall sigma obs sigma' obs',
  wf3 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf3 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf3 in *.
  intros; injection H1; intros.
  inversion H0. inversion H19; subst.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    case_eq (NatMap.find e v); intros.
    apply (wf3_mlc_read lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R e r ranV).
    exact H25. exact H36. exact H4. exact H2. reflexivity.
    reflexivity. exact H5. exact H3.
    apply (H m mu rho p lambda c v w s e r).
    reflexivity. exact H4. exact H5.
    apply (wf2_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R e) in H5.
    rewrite -> H3 in H5. discriminate.
    exact H25. exact H36. exact H4. exact H2. reflexivity.
    reflexivity.
    apply (wf_mlc_read_none lambda0 h_tree m e' mu l0 D delta obs0 k lambda) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H25. exact H36.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    case_eq (NatMap.find e v); intros.
    apply (wf3_mlc_alloc lambda0 h_tree r_bar_val e0 m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R e r ranV).
    exact H32. exact H42. exact H4. exact H2. reflexivity.
    reflexivity. exact H5. exact H3.
    intros. apply (H m mu rho p lambda c v w s e1 l0).
    reflexivity. exact H4. exact H6.
    assert (NatMap.find e V = None).
    apply (wf2_mlc_alloc_none lambda0 h_tree r_bar_val e0 m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R e).
    exact H32. exact H42. exact H4. exact H2. reflexivity.
    reflexivity. exact H5.
    rewrite -> H6 in H3. discriminate.
    apply (wf_mlc_alloc_none lambda0 h_tree r_bar_val e0 m k lambda) in H42.
    rewrite -> H42 in H2.
    discriminate. exact H32. exact H4.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    case_eq (NatMap.find e v0); intros.
    apply (wf3_mlc_write lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c v0 w s)
    (single_level_cache F V C R) c v0 w s F V C R e r ranV).
    exact H25. exact H36. exact H4. exact H2. reflexivity.
    reflexivity. exact H5. exact H3.
    apply (H m m0 rho p lambda c v0 w s e r).
    reflexivity. exact H4. exact H5.
    apply (wf2_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda (single_level_cache c v0 w s)
    (single_level_cache F V C R) c v0 w s F V C R e) in H5.
    rewrite -> H3 in H5. discriminate.
    exact H25. exact H36. exact H4. exact H2. reflexivity.
    reflexivity.
    apply (wf_mlc_write_none lambda0 h_tree m e' m0 l0 v D obs1 mu k lambda) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H25. exact H36.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    case_eq (NatMap.find e v); intros.
    apply (wf3_mlc_dealloc lambda0 h_tree (enclave_state_value (enclave_ID_active e_raw) mem) m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R e r ranV).
    exact H30. exact H37. exact H4. exact H2. reflexivity.
    reflexivity. exact H5. exact H3.
    intros. apply (H m m0 rho p lambda c v w s e0 l0).
    reflexivity. exact H4. exact H6.
    assert (NatMap.find e V = None).
    apply (wf2_mlc_dealloc_none lambda0 h_tree (enclave_state_value (enclave_ID_active e_raw) mem) m k lambda (single_level_cache c v w s)
    (single_level_cache F V C R) c v w s F V C R e).
    exact H30. exact H37. exact H4. exact H2.
    reflexivity. reflexivity. exact H5.
    rewrite -> H6 in H3. discriminate.
    apply (wf_mlc_dealloc_none lambda0 h_tree (enclave_state_value (enclave_ID_active e_raw) mem) m k lambda) in H37.
    rewrite -> H37 in H2.
    discriminate. exact H30. exact H4.
  - apply (H k mu rho p lambda F V C R e ranV).
    reflexivity. exact H2. exact H3.
  - apply (H k mu rho p lambda F V C R e ranV).
    reflexivity. exact H2. exact H3.
  - apply (H k mu rho p lambda F V C R e ranV).
    reflexivity. exact H2. exact H3.
  - apply (H k mu rho p lambda F V C R e ranV).
    reflexivity. exact H2. exact H3.
  - subst; apply (H k mu rho p lambda F V C R e ranV).
    reflexivity. exact H2. exact H3.
Qed.

(* Well-Formed 4 *)
Definition wf4 (sigma: runtime_state): Prop :=
  forall k mu rho pi p l q e E,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find p pi = Some (process_value (enclave_state_value e E) l q)) ->
  (e = enclave_ID_inactive \/ (exists raw_e, e = enclave_ID_active raw_e /\ NatMap.In raw_e E)).

(* WF4 Active Enclave Update *)
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

(* WF4 Enclave Creation *)
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

(* WF4 Enclave Elimination *)
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

(* WF4 Preservation *)
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

(* Well-Formed 5 *)
Definition wf5 (sigma: runtime_state): Prop :=
  forall k mu rho pi index F V C R p l q e E,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find index k = Some (single_level_cache F V C R)) ->
  (NatMap.find p pi = Some (process_value (enclave_state_value (enclave_ID_active e) E) l q)) ->
  (NatMap.In e V).

(* WF5 MLC Read *)
Lemma mlc_read_v : forall lambda h_tree k e' m0 l0 D obs1 mu k' index F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some (single_level_cache F V C R) ->
  NatMap.find index k' = Some (single_level_cache F' V' C' R') ->
  V = V'.
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
    destruct l0. destruct (NatMap.find b m0).
    injection H1; intros; subst.
    rewrite -> H2 in H3.
    injection H3; intros; subst F' V' C' R'.
    reflexivity.
    discriminate.
  }
  {
    intros.
    unfold recursive_mlc_read in H1.
    fold recursive_mlc_read in H1.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H4). destruct (NatMap.find a k) in A0, H1.
    injection A0; intros; subst s0.
    case_eq (cc_hit_read s e' l0). intros.
    assert (A1 := H5). destruct (cc_hit_read s e' l0) in A1, H1.
    injection A1; injection H1; intros; subst; clear A0 A1.
    destruct s; destruct s0.
    apply (cc_hit_read_v (single_level_cache c0 v w s) e' l0 d d0 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H5.
    subst v0.
    {
      case_eq (eqb index a); intros.
      {
        apply cmp_to_eq in H5; subst a.
        rewrite -> H2 in H4.
        injection H4; intros; subst c0 v w s.
        assert (Some (single_level_cache F' V' C' R') = Some (single_level_cache c1 V w0 s0)).
        rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
        injection H5; intros; subst.
        reflexivity.
      }
      {
        apply cmp_to_uneq in H5.
        assert (NatMap.find index k = Some (single_level_cache F' V' C' R')).
        rewrite <- H3. apply eq_sym.
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
        rewrite -> H2 in H6.
        injection H6; intros; subst.
        reflexivity.
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_read s e' l0).
    discriminate.
    clear A0.
    case_eq (recursive_mlc_read k e' m0 l0 l); intros.
    assert (A0 := H6). destruct (recursive_mlc_read k e' m0 l0 l) in A0, H1.
    case_eq (cc_update s e' d1 l0); intros.
    assert (A1 := H7). destruct (cc_update s e' d1 l0) in A1, H1.
    injection A0; injection A1; injection H1; intros; subst; clear A0 A1.
    {
      case_eq (eqb index a); intros.
      {
        apply cmp_to_eq in H8. subst a.
        destruct s. rewrite -> H2 in H4; injection H4; intros; subst c0 v w s.
        destruct s0.
        apply (cc_update_v (single_level_cache F V C R) e' d l0 c (single_level_cache c0 v w s)
        F V C R c0 v w s) in H7.
        subst v.
        assert (NatMap.find index (NatMap.add index (single_level_cache c0 V w s) m) =
        Some (single_level_cache c0 V w s)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H7; injection H7; intros; subst c0 V' w s.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        apply cmp_to_uneq in H8.
        assert (WFH := H0).
        unfold well_defined_cache_tree in H0.
        destruct H0 as [ WFH1 ]. destruct H0 as [ WFH2 ]. destruct H0 as [ WFH3 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 d d0 o m index F V C R F' V' C' R').
          exact WFH. exact H6. exact H2.
          rewrite <- H3. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H8.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in H. discriminate.
          specialize (WFH3 c0 a (p :: l) H).
          unfold get_cache_ID_path in H. discriminate.
          specialize (WFH2 p0 a (p :: l) H).
          injection WFH2; intros; subst.
          apply (H0 p0 p l) in H.
          apply (IHl (cache_node p) H k e' m0 l0 d d0 o m index F V C R F' V' C' R').
          exact WFH. exact H6. exact H2.
          rewrite <- H3. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H8.
        }
      }
    }
    discriminate.
    destruct (cc_update s e' d1 l0); discriminate.
    discriminate.
    destruct (recursive_mlc_read k e' m0 l0 l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF5 MLC Write *)
Lemma mlc_write_v : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index F V C R F' V' C' R',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some (single_level_cache F V C R) ->
  NatMap.find index k' = Some (single_level_cache F' V' C' R') ->
  V = V'.
Proof.
  unfold mlc_write.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda.
  induction l.
  {
    intros.
    unfold recursive_mlc_write in H1.
    destruct l0. destruct (NatMap.find b m0). destruct v.
    discriminate.
    injection H1; intros; subst.
    rewrite -> H2 in H3.
    injection H3; intros; subst F' V' C' R'.
    reflexivity.
    discriminate.
  }
  {
    intros.
    unfold recursive_mlc_write in H1.
    fold recursive_mlc_write in H1.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H4). destruct (NatMap.find a k) in A0, H1.
    injection A0; intros; subst s0.
    case_eq (cc_hit_write s e' l0 v). intros.
    assert (A1 := H5). destruct (cc_hit_write s e' l0 v) in A1, H1.
    destruct l0. injection A1; injection H1; intros; subst; clear A0 A1.
    destruct s; destruct s0.
    apply (cc_hit_write_v (single_level_cache c0 v0 w s) e' (address b d1) v d c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0) in H5.
    subst v1.
    {
      case_eq (eqb index a); intros.
      {
        apply cmp_to_eq in H5; subst a.
        rewrite -> H2 in H4.
        injection H4; intros; subst.
        assert (Some (single_level_cache F' V' C' R') = Some (single_level_cache c1 v0 w0 s0)).
        rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
        injection H5; intros; subst.
        reflexivity.
      }
      {
        apply cmp_to_uneq in H5.
        assert (NatMap.find index k = Some (single_level_cache F' V' C' R')).
        rewrite <- H3. apply eq_sym.
        apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
        rewrite -> H2 in H6.
        injection H6; intros; subst.
        reflexivity.
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_write s e' l0 v).
    discriminate.
    clear A0.
    case_eq (recursive_mlc_write k e' m0 l0 v l); intros.
    assert (A0 := H6). destruct (recursive_mlc_write k e' m0 l0 v l) in A0, H1.
    case_eq (cc_update s e' d0 l0); intros.
    assert (A1 := H7). destruct (cc_update s e' d0 l0) in A1, H1.
    injection A0; injection A1; injection H1; intros; subst; clear A0 A1.
    {
      case_eq (eqb index a); intros.
      {
        apply cmp_to_eq in H8. subst a.
        destruct s. rewrite -> H2 in H4; injection H4; intros; subst c0 v0 w s.
        destruct s0.
        apply (cc_update_v (single_level_cache F V C R) e' d l0 c (single_level_cache c0 v0 w s)
        F V C R c0 v0 w s) in H7.
        subst v0.
        assert (NatMap.find index (NatMap.add index (single_level_cache c0 V w s) m1) =
        Some (single_level_cache c0 V w s)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H7; injection H7; intros; subst c0 V' w s.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        apply cmp_to_uneq in H8.
        assert (WFH := H0).
        unfold well_defined_cache_tree in H0.
        destruct H0 as [ WFH1 ]. destruct H0 as [ WFH2 ]. destruct H0 as [ WFH3 ].
        destruct l.
        {
          apply (IHl root_node WFH1 k e' m0 l0 v d o m m1 index F V C R F' V' C' R').
          exact WFH. exact H6. exact H2.
          rewrite <- H3. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H8.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in H. discriminate.
          specialize (WFH3 c0 a (p :: l) H).
          unfold get_cache_ID_path in H. discriminate.
          specialize (WFH2 p0 a (p :: l) H).
          injection WFH2; intros; subst.
          apply (H0 p0 p l) in H.
          apply (IHl (cache_node p) H k e' m0 l0 v d o m m1 index F V C R F' V' C' R').
          exact WFH. exact H6. exact H2.
          rewrite <- H3. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H8.
        }
      }
    }
    discriminate.
    destruct (cc_update s e' d0 l0); discriminate.
    discriminate.
    destruct (recursive_mlc_write k e' m0 l0 v l); discriminate.
    discriminate.
    intros; destruct (NatMap.find a k); discriminate.
  }
  intros; destruct (get_cache_ID_path lambda h_tree); discriminate.
Qed.

(* WF5 Preservation *)
Lemma wf5_preservation : forall sigma obs sigma' obs',
  wf5 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf5 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf5 in *.
  intros; injection H1; intros.
  inversion H0. inversion H19.
  - subst.
    case_eq (NatMap.find index m); intros. destruct s.
    apply (mlc_read_v lambda h_tree m e' mu l1 D delta obs0 k index c v w s F V C R) in H36.
    subst v.
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H5; subst p2.
    assert (Some (process_value (enclave_state_value (enclave_ID_active e) E) l q) =
    Some (process_value e' l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H m mu rho p index c V w s p1 l0 q0 e E).
    reflexivity. exact H4. exact H20.
    apply cmp_to_uneq in H5.
    apply (H m mu rho p index c V w s p1 l q e E).
    reflexivity. exact H4.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
    exact H25. exact H4. exact H2.
    apply (wf_mlc_read_none lambda h_tree m e' mu l1 D delta obs0 k index) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H25. exact H36.
  - subst. give_up.
  - subst.
    case_eq (NatMap.find index m); intros. destruct s.
    apply (mlc_write_v lambda h_tree m e' m0 l1 v D obs1 mu k index c v0 w s F V C R) in H36.
    subst v0.
    case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H5; subst p2.
    assert (Some (process_value (enclave_state_value (enclave_ID_active e) E) l q) =
    Some (process_value e' l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    injection H5; intros; subst.
    apply (H m m0 rho p index c V w s p1 l0 q0 e E).
    reflexivity. exact H4. exact H20.
    apply cmp_to_uneq in H5.
    apply (H m m0 rho p index c V w s p1 l q e E).
    reflexivity. exact H4.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H5.
    exact H25. exact H4. exact H2.
    apply (wf_mlc_write_none lambda h_tree m e' m0 l1 v D obs1 mu k index) in H4.
    rewrite -> H2 in H4.
    discriminate. exact H25. exact H36.
  - subst. give_up.
  - subst. case_eq (eqb p1 p2); intros.
    apply cmp_to_eq in H4; subst p2.
    assert (Some (process_value (enclave_state_value (enclave_ID_active e) E) l q)
    = Some (process_value e' l' q0)).
    rewrite <- H3. apply NatMapFacts.add_eq_o; reflexivity.
    apply (H k mu rho p index F V C R p1 l q e E).
    reflexivity. exact H2.
    give_up.
    apply cmp_to_uneq in H4.
    apply (H k mu rho p index F V C R p1 l q e E).
    reflexivity. exact H2.
    rewrite <- H3. apply eq_sym.
    apply NatMapFacts.add_neq_o; apply not_eq_sym; exact H4.
  - subst. give_up.
  - subst. give_up.
  - subst. give_up.
  - subst. give_up.
Admitted.