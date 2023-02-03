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

Module NatMapFacts := NatMapProperties.F.
Module CacheletMapFacts := CacheletMapProperties.F.

Definition tree_in_PLRU (R: set_indexed_PLRU) T: Prop :=
  exists x, (NatMap.find x R = Some T).

Notation "'<<' sigma ';' obs '>>'" := (state_and_trace sigma obs).

(* Helper Lemmas *)
Lemma cmp_to_eq : forall x y, (x =? y) = true -> x = y.
Proof.
  intro x.
  induction x.
  intros y H.
  destruct y. reflexivity. simpl in *. congruence.
  intros y H. destruct y.
  simpl in *. congruence. f_equal ; auto.
Qed.

Lemma cmp_uneq_helper1 : forall n m : nat,
    n <> m -> S n <> S m.
Proof.
  unfold not; intros.
  apply H. injection H0. intro. assumption.
Qed.
Lemma cmp_uneq_helper2 : forall n m : nat,
    S n <> S m -> n <> m.
Proof.
  unfold not; intros.
  apply H. lia.
Qed.
Lemma cmp_to_uneq : forall x y, (x =? y) = false <-> x <> y.
Proof.
  induction x. split.
  simpl. destruct y. discriminate. discriminate.
  simpl. destruct y. intros. contradiction. intros. reflexivity.
  simpl. destruct y.
  split. intros. discriminate. intros. reflexivity.
  split. intros. apply IHx in H. apply cmp_uneq_helper1. exact H.
  intros. apply cmp_uneq_helper2 in H. apply IHx in H. exact H.
Qed.

Lemma cmp_to_eq_and : forall x y z w, (x =? y) && (z =? w) = true -> x = y /\ z = w.
Proof.
  intros.
  apply andb_true_iff in H.
  destruct H.
  split.
  apply cmp_to_eq; exact H.
  apply cmp_to_eq; exact H0.
Qed.

Lemma cmp_to_uneq_and : forall x y z w, (x =? y) && (z =? w) = false -> x <> y \/ z <> w.
Proof.
  intros.
  apply andb_false_iff in H.
  destruct H.
  left. apply cmp_to_uneq in H. exact H.
  right. apply cmp_to_uneq in H. exact H.
Qed.

(* Cachelet Allocation Lemmas *)
Lemma cachelet_allocation_c : forall n e psi psi' F V C R F' V' C' R',
  cachelet_allocation n e psi = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  C = C'.
Proof.
  intros.
  unfold cachelet_allocation in H.
  case_eq psi; intros; destruct psi.
  injection H0; injection H2; intros; subst c v w s; subst c0 v0 w0 s0; clear H0 H2.
  subst psi'.
  unfold recursive_cachelet_allocation in H.
  generalize dependent e;
  generalize dependent F;
  generalize dependent V;
  generalize dependent C;
  generalize dependent R;
  generalize dependent F';
  generalize dependent V';
  generalize dependent C';
  generalize dependent R'.
  induction n.
  intros; injection H; intros; subst; auto.
  fold recursive_cachelet_allocation in *.
  intros.
  case_eq (way_first_allocation F); intros; destruct (way_first_allocation F).
  destruct c0.
  case_eq (NatMap.find s R); intros; destruct (NatMap.find s R).
  case_eq (NatMap.find e V); intros; destruct (NatMap.find e V).
  case_eq (NatMap.find s r0); intros; destruct (NatMap.find s r0).
  injection H0; injection H1; injection H2; injection H3; intros; subst p r w1 c; clear H0 H1 H2.
  specialize (IHn R' C' V' F' (NatMap.add s (update p0 w (enclave_ID_active e)) R) C
  (NatMap.add e (NatMap.add s (w :: w0) r0) V) (remove_CAT (w, s) F) e) as H_app.
  apply H_app. exact H.
  discriminate.
  discriminate.
  specialize (IHn R' C' V' F' (NatMap.add s (update p0 w (enclave_ID_active e)) R) C
  (NatMap.add e (NatMap.add s (w :: nil) r0) V) (remove_CAT (w, s) F) e) as H_app.
  apply H_app. exact H.
  discriminate.
  discriminate.
  specialize (IHn R' C' V' F' (NatMap.add s (update p0 w (enclave_ID_active e)) R) C
  (NatMap.add e (NatMap.add s (w :: nil) (NatMap.empty (list way_ID))) V) (remove_CAT (w, s) F) e) as H_app.
  apply H_app. exact H.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.

Lemma remove_CAT_f : forall c c' F,
  In c (recursive_remove_from_CAT c' F) -> In c F.
Proof.
  intros.
  unfold recursive_remove_from_CAT in H.
  induction F. exact H.
  case_eq (eq_cachelet_index c' a); intros; destruct (eq_cachelet_index c' a).
  apply (in_cons a c F). exact H.
  discriminate.
  discriminate.
  apply in_inv in H.
  fold recursive_remove_from_CAT in *.
  destruct H.
  subst.
  apply in_eq.
  apply in_cons.
  apply IHF.
  exact H.
Qed.


Lemma remove_CAT_f2_helper : forall a c c' F,
  (In c (recursive_remove_from_CAT c' F) \/ c = a) \/ c = c' ->
  In c (a :: recursive_remove_from_CAT c' F) \/ c = c'.
Proof.
  intros.
  destruct H.
  destruct H.
  left; apply in_cons; exact H.
  left; subst; apply in_eq; reflexivity.
  right; exact H.
Qed.

Lemma remove_CAT_f2_helper2 : forall P Q R,
  (P \/ Q) \/ R -> (P \/ R) \/ Q.
Proof.
  intros.
  destruct H.
  destruct H.
  left; left; exact H.
  right; exact H.
  left; right; exact H.
Qed.

Lemma remove_CAT_f2 : forall c c' F,
  In c F -> In c (recursive_remove_from_CAT c' F) \/ c = c'.
Proof.
  intros.
  induction F.
  simpl in H. left. simpl. exact H.
  unfold recursive_remove_from_CAT.
  case_eq (eq_cachelet_index c' a); intros; destruct (eq_cachelet_index c' a) in IHF.
  apply in_inv in H.
  destruct H.
  subst.
  unfold eq_cachelet_index in H0.
  destruct c'. destruct c.
  apply cmp_to_eq_and in H0.
  destruct H0. subst. right. auto.
  left. auto.
  apply in_inv in H.
  destruct H.
  subst.
  unfold eq_cachelet_index in H0.
  destruct c'. destruct c.
  apply cmp_to_eq_and in H0.
  destruct H0. subst. right. auto.
  left. auto. (* not exactly sure why that happens *)
  fold recursive_remove_from_CAT.
  apply in_inv in H. destruct H.
  destruct a; destruct c; destruct c'.
  injection H; intros; subst w0 s0.
  left. apply in_eq.
  apply remove_CAT_f2_helper.
  apply remove_CAT_f2_helper2.
  left. apply IHF. exact H.
  fold recursive_remove_from_CAT.
  apply in_inv in H. destruct H.
  destruct a; destruct c; destruct c'.
  injection H; intros; subst w0 s0.
  left. apply in_eq.
  apply remove_CAT_f2_helper.
  apply remove_CAT_f2_helper2.
  left. apply IHF. exact H.
Qed.

Lemma cachelet_allocation_f : forall n e psi psi' F V C R F' V' C' R' c,
  cachelet_allocation n e psi = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  In c F' -> In c F.
Proof.
  intros n.
  induction n.
  intros.
  unfold cachelet_allocation in H.
  subst psi psi'.
  unfold recursive_cachelet_allocation in H.
  injection H; intros; subst; exact H2.
  intros.
  unfold cachelet_allocation in H.
  subst psi.
  unfold recursive_cachelet_allocation in H.
  case_eq (way_first_allocation F); intros; destruct (way_first_allocation F).
  destruct c1.
  case_eq (NatMap.find s R); intros; destruct (NatMap.find s R).
  case_eq (NatMap.find e V); intros; destruct (NatMap.find e V).
  case_eq (NatMap.find s r0); intros; destruct (NatMap.find s r0).
  fold recursive_cachelet_allocation in H.
  injection H3; injection H4; injection H5; injection H0; intros;
  subst p r w1 c0; clear H3 H4 H5 H0.
  specialize (IHn e (single_level_cache (remove_CAT (w, s) F) (NatMap.add e (NatMap.add s (w :: w0) r0) V)
  C (NatMap.add s (update p0 w (enclave_ID_active e)) R)) psi' (remove_CAT (w, s) F)
  (NatMap.add e (NatMap.add s (w :: w0) r0) V) C (NatMap.add s (update p0 w (enclave_ID_active e)) R)
  F' V' C' R' c) as H_app.
  apply (remove_CAT_f c (w, s) F).
  unfold remove_CAT in H_app.
  apply H_app.
  unfold cachelet_allocation; exact H.
  reflexivity.
  exact H1.
  exact H2.
  discriminate.
  discriminate.
  fold recursive_cachelet_allocation in H.
  injection H3; injection H4; injection H0; intros;
  subst p r c0; clear H3 H4 H5 H0.
  specialize (IHn e (single_level_cache (remove_CAT (w, s) F) (NatMap.add e (NatMap.add s (w :: nil) r0) V)
  C (NatMap.add s (update p0 w (enclave_ID_active e)) R)) psi' (remove_CAT (w, s) F)
  (NatMap.add e (NatMap.add s (w :: nil) r0) V) C (NatMap.add s (update p0 w (enclave_ID_active e)) R)
  F' V' C' R' c) as H_app.
  apply (remove_CAT_f c (w, s) F).
  unfold remove_CAT in H_app.
  apply H_app.
  unfold cachelet_allocation; exact H.
  reflexivity.
  exact H1.
  exact H2.
  discriminate.
  discriminate.
  fold recursive_cachelet_allocation in H.
  injection H3; injection H0; intros;
  subst p c0; clear H3 H4 H0.
  specialize (IHn e (single_level_cache (remove_CAT (w, s) F) (NatMap.add e (NatMap.add s (w :: nil) (NatMap.empty (list way_ID))) V)
  C (NatMap.add s (update p0 w (enclave_ID_active e)) R)) psi' (remove_CAT (w, s) F)
  (NatMap.add e (NatMap.add s (w :: nil) (NatMap.empty (list way_ID))) V) C (NatMap.add s (update p0 w (enclave_ID_active e)) R)
  F' V' C' R' c) as H_app.
  apply (remove_CAT_f c (w, s) F).
  unfold remove_CAT in H_app.
  apply H_app.
  unfold cachelet_allocation; exact H.
  reflexivity.
  exact H1.
  exact H2.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.

(* Cachelet Deallocation Lemmas *)


(* First Well-Formed Lemmas *)
Lemma wf1_mlc_alloc : forall n state k lambda h_tree k' index psi psi' F V C R F' V' C' R' c,
  mlc_allocation n state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (In c F -> CacheletMap.In c C) -> (In c F' -> CacheletMap.In c C').
Proof.
  intros n.
  induction n.
  {
    intros.
    unfold mlc_allocation in H.
    destruct state. destruct e.
    unfold recursive_mlc_allocation in H.
    injection H; intros; subst k'.
    rewrite -> H0 in H1.
    injection H1; intros; subst psi' psi.
    injection H6; intros; subst.
    apply H4; exact H5.
    discriminate. 
  }
  {
    intros.
    unfold mlc_allocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_allocation in H.
    case_eq (NatMap.find lambda k).
    intros. assert (H6' := H6). destruct (NatMap.find lambda k) in H, H6'.
    case_eq (cachelet_allocation a r s0).
    intros. assert (H7' := H7). destruct (cachelet_allocation a r s0) in H, H7'.
    case_eq (get_cache_hierarchy_parent (cache_node lambda) h_tree).
    intros. assert (H8' := H8). destruct (get_cache_hierarchy_parent (cache_node lambda) h_tree) in H, H8'.
    case_eq c1.
    intros. subst c1.
    fold recursive_mlc_allocation in H.
    injection H6'; injection H7'; injection H8'; intros; subst s0 s2 c0; clear H6' H7' H8'.
    {
      case_eq (eqb lambda index).
      {
        intros. apply cmp_to_eq in H9.
        subst.
        destruct s1.
        specialize (IHn (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add index (single_level_cache c0 v w s0) k) p h_tree k' index (single_level_cache c0 v w s0)
        (single_level_cache F' V' C' R') c0 v w s0 F' V' C' R' c) as H_app.
        apply H_app; clear H_app.
        unfold mlc_allocation. exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        reflexivity.
        intros. destruct s. rewrite -> H6 in H0.
        injection H0; intros; subst c1 v0 w0 s; clear H0.
        assert (HF := H7); apply (cachelet_allocation_f a r (single_level_cache F V C R) (single_level_cache c0 v w s0)
        F V C R c0 v w s0 c) in HF.
        assert (HC := H7); apply (cachelet_allocation_c a r (single_level_cache F V C R) (single_level_cache c0 v w s0)
        F V C R c0 v w s0) in HC. subst w.
        apply H4 in HF. exact HF.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
        exact H2.
        exact H5.
      }
      {
        intros. apply cmp_to_uneq in H9.
        specialize (IHn (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add lambda s1 k) p h_tree k' index psi psi' F V C R F' V' C' R') as H_app.
        apply H_app; clear H_app.
        unfold mlc_allocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o. exact H9.
        exact H1.
        exact H2.
        exact H3.
        exact H4.
        exact H5.
      }
    }
    intros; subst c1; discriminate.
    discriminate.
    intros; destruct (get_cache_hierarchy_parent (cache_node lambda) h_tree).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (cachelet_allocation a r s0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find lambda k).
    discriminate.
    discriminate.
    discriminate.
  }
Qed.

Lemma wf1_mlc_alloc_none : forall n state k lambda h_tree k' index,
  mlc_allocation n state k lambda h_tree = Some k' ->
  NatMap.find index k = None ->
  NatMap.find index k' = None.
Proof.
  intros n.
  induction n.
  {
    intros.
    unfold mlc_allocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_allocation in H.
    injection H; intros; subst k'.
    exact H0.
    discriminate.
  }
  {
    intros.
    unfold mlc_allocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_allocation in H.
    case_eq (NatMap.find lambda k).
    intros. assert (H1' := H1). destruct (NatMap.find lambda k) in H, H1'.
    case_eq (cachelet_allocation a r s0).
    intros. assert (H2' := H2). destruct (cachelet_allocation a r s0) in H, H2'.
    case_eq (get_cache_hierarchy_parent (cache_node lambda) h_tree).
    intros. assert (H3' := H3). destruct (get_cache_hierarchy_parent (cache_node lambda) h_tree) in H, H3'.
    case_eq c0.
    intros. subst c0.
    fold recursive_mlc_allocation in H.
    injection H1'; injection H2'; injection H3'; intros; subst s0 s2 c; clear H1' H2' H3'.
    {
      case_eq (eqb index lambda); intros.
      {
        intros. apply cmp_to_eq in H4.
        subst lambda.
        destruct s1.
        specialize (IHn (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add index (single_level_cache c v w s0) k) p h_tree k' index) as H_app.
        apply H_app; clear H_app.
        unfold mlc_allocation. exact H.
        rewrite -> H0 in H1. discriminate.
      }
      {
        intros. apply cmp_to_uneq in H4.
        destruct s1.
        specialize (IHn (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add lambda (single_level_cache c v w s0) k) p h_tree k' index) as H_app.
        apply H_app; clear H_app.
        unfold mlc_allocation. exact H.
        rewrite <- H0.
        apply NatMapFacts.add_neq_o.
        auto.
      }
    }
    intros; injection H3'; intros; subst; discriminate.
    discriminate.
    intros; destruct (get_cache_hierarchy_parent (cache_node lambda) h_tree).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (cachelet_allocation a r s0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find lambda k).
    discriminate.
    discriminate.
    discriminate.
  }
Qed.

(* Well-Formed Definitions *)
Definition wf1 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda c F V C R,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.MapsTo lambda (single_level_cache F V C R) k) ->
  ((In c F) -> (CacheletMap.In c C)).

Definition wf_c (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda psi F V C R,
  (sigma = runtime_state_value k mu rho pi) ->
  psi = single_level_cache F V C R ->
  (NatMap.find lambda k = Some psi) ->
  (forall w s state l cache_val delta, cc_unfold psi state l = cc_unfold_valid F V C R (w, s) cache_val delta
    -> (CacheletMap.In (w, s) C)).

(* Well-Formed Way Set Cache *)
(*
Lemma wf_c_preservation_mlc_read : forall sigma
*)

Lemma wf_c_preservation : forall sigma obs sigma' obs',
  wf1 sigma -> wf_c sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf_c sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf_c in *.
  unfold wf1 in *.
  intros.
  injection H2; intros; subst; clear H2.
  inversion H1.
  inversion H15; subst.
  - unfold mlc_read in H33.
    assert (H34 := H33).
    unfold recursive_mlc_read in H33.
    induction (get_hierarchy_tree_height H18).
    discriminate.
    fold recursive_mlc_read in IHn. apply IHn.
    case_eq lambda0; intros. assert (H2' := H2). destruct lambda0 in H33, H2'.
    case_eq (NatMap.find p2 m); intros.
    assert (H3' := H2). destruct (NatMap.find p2 m) in H33, H3'.
    case_eq (cc_hit_read s1 e' l1); intros. assert (H4' := H3).
    destruct (cc_hit_read s1 e' l1) in H33, H4'.

    injection H2'; injection H3'; injection H4'; intros; subst; clear H2' H3' H4'.
    injection H33; intros. subst delta0 d obs0 k.
    

    
    case_eq (NatMap.find lambda k).
    intros. assert (H6' := H6). destruct (NatMap.find lambda k) in H, H6'.

    give_up.
    
  - give_up.
  - give_up.
  - give_up.
  - specialize (H0 k mu rho p lambda (single_level_cache F V C R) F V C R) as H_app.
    assert (forall (w : way_ID) (s : set_ID) (state : enclave_state) (l : memory_address)
          (cache_val : way_set_cache_value) (delta : data_offset),
        cc_unfold (single_level_cache F V C R) state l =
        cc_unfold_valid F V C R (w, s) cache_val delta ->
        CacheletMap.In (elt:=way_set_cache_value) (w, s) C).
    apply H_app.
    reflexivity.
    reflexivity.
    exact H4.
    specialize (H2 w s state l cache_val delta) as H_app2.
    apply H_app2.
    exact H5.
  - specialize (H0 k mu rho p lambda (single_level_cache F V C R) F V C R) as H_app.
    assert (forall (w : way_ID) (s : set_ID) (state : enclave_state) (l : memory_address)
          (cache_val : way_set_cache_value) (delta : data_offset),
        cc_unfold (single_level_cache F V C R) state l =
        cc_unfold_valid F V C R (w, s) cache_val delta ->
        CacheletMap.In (elt:=way_set_cache_value) (w, s) C).
    apply H_app.
    reflexivity.
    reflexivity.
    exact H4.
    specialize (H2 w s state l cache_val delta) as H_app2.
    apply H_app2.
    exact H5.
  - specialize (H0 k mu rho p lambda (single_level_cache F V C R) F V C R) as H_app.
    assert (forall (w : way_ID) (s : set_ID) (state : enclave_state) (l : memory_address)
          (cache_val : way_set_cache_value) (delta : data_offset),
        cc_unfold (single_level_cache F V C R) state l =
        cc_unfold_valid F V C R (w, s) cache_val delta ->
        CacheletMap.In (elt:=way_set_cache_value) (w, s) C).
    apply H_app.
    reflexivity.
    reflexivity.
    exact H4.
    specialize (H2 w s state l cache_val delta) as H_app2.
    apply H_app2.
    exact H5.
  - specialize (H0 k mu rho p lambda (single_level_cache F V C R) F V C R) as H_app.
    assert (forall (w : way_ID) (s : set_ID) (state : enclave_state) (l : memory_address)
          (cache_val : way_set_cache_value) (delta : data_offset),
        cc_unfold (single_level_cache F V C R) state l =
        cc_unfold_valid F V C R (w, s) cache_val delta ->
        CacheletMap.In (elt:=way_set_cache_value) (w, s) C).
    apply H_app.
    reflexivity.
    reflexivity.
    exact H4.
    specialize (H2 w s state l cache_val delta) as H_app2.
    apply H_app2.
    exact H5.
  - subst.
    specialize (H0 k mu rho p lambda (single_level_cache F V C R) F V C R) as H_app.
    assert (forall (w : way_ID) (s : set_ID) (state : enclave_state) (l : memory_address)
          (cache_val : way_set_cache_value) (delta : data_offset),
        cc_unfold (single_level_cache F V C R) state l =
        cc_unfold_valid F V C R (w, s) cache_val delta ->
        CacheletMap.In (elt:=way_set_cache_value) (w, s) C).
    apply H_app.
    reflexivity.
    reflexivity.
    exact H4.
    specialize (H2 w s state l cache_val delta) as H_app2.
    apply H_app2.
    exact H5.
Admitted.

(* First Well-Formed Condition *)
Lemma wf1_preservation : forall sigma obs sigma' obs',
  wf1 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf1 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf1 in *.
  intros.
  injection H1; intros; subst; clear H1.
  inversion H0.
  inversion H14; subst.
  - give_up.
    (*
    unfold mlc_read in H33; unfold recursive_mlc_read in H33.
    destruct (get_hierarchy_tree_height H18).
    discriminate.
    case_eq lambda0; intros; subst.
    case_eq (NatMap.find p2 m); intros; destruct (NatMap.find p2 m) in H33.
    case_eq (cc_hit_read s0 e' l0); intros; destruct (cc_hit_read s0 e' l0) in H33.
    unfold cc_hit_read in H5.
    case_eq (cc_unfold s0 e' l0); intros.
    give_up.
    *)
    (*
    give_up.

    unfold cc_unfold in H5.
    destruct s0; destruct l0.
    unfold block_to_set_and_tag in H5. subst.




    case_eq n0.
    case_eq lambda0.
    case_eq (NatMap.find p2 m).
    case_eq (cc_hit_read s e' l0).
    injection H33. injection H1. intros.
    destruct s0. subst.
    case_eq (Nat.eqb p1 p2). intros.
    apply cmp_to_eq in H4. subst.
    apply (NatMapFacts.add_mapsto_iff m p2 lambda (single_level_cache c1 v w s0) (single_level_cache F V C R)) in H2.
    destruct H2. destruct H2. injection H4. intros. subst.
    case_eq (OrderedPair.eqb 
    case_eq (Nat.eqb lambda p2). intros.
    apply cmp_to_eq in H4. subst.
    destruct H2. injection H4. intros. subst.
    give_up.
    intros. apply cmp_to_uneq in H4.
    give_up.
    
    give_up.
    intros. apply cmp_to_uneq in H4.
    
    give_up.
    destruct (get_cache_hierarchy_parent (cache_node p2) H18).
    discriminate.
    discriminate.
    discriminate.
    destruct l0.
    destruct (NatMap.find b m2). subst.
    give_up.
    discriminate.
    destruct lambda0. subst.
    give_up.
    give_up.
    *)
    (* give_up. give_up. give_up. give_up. give_up. give_up. give_up. give_up. *)
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    specialize (H m mu rho p lambda c c0 v w s) as H_app.
    assert (In c c0 -> CacheletMap.In c w).
    apply H_app. reflexivity.
    apply NatMapFacts.find_mapsto_iff. exact H1.
    generalize H3.
    apply (wf1_mlc_alloc r_bar_val e m lambda0 H17 k lambda (single_level_cache c0 v w s)
    (single_level_cache F V C R) c0 v w s F V C R c).
    exact H38.
    exact H1.
    apply NatMapFacts.find_mapsto_iff in H2; exact H2.
    reflexivity.
    reflexivity.
    exact H4.
    apply NatMapFacts.find_mapsto_iff in H2.
    generalize H3.
    assert (mlc_allocation r_bar_val e m lambda0 H17 = Some k ->
    NatMap.find (elt:=single_level_cache_unit) lambda m = None).
    auto.
    apply (wf1_mlc_alloc_none r_bar_val e m lambda0 H17 k lambda) in H4.
    intros.
    rewrite -> H2 in H4.
    discriminate.
    exact H38.
    exact H38.
  - unfold mlc_write in H33; unfold recursive_mlc_write in H33.
    destruct (get_hierarchy_tree_height H18).
    discriminate.
    destruct lambda0. destruct (NatMap.find p2 m).
    destruct (cc_hit_write s e' l0 v). destruct l0.
    injection H33. injection H1. intros.
    rewrite -> H37 in H38. subst.
    give_up.
    destruct (get_cache_hierarchy_parent (cache_node p2) H18).
    give_up.
    discriminate.
    discriminate.
    destruct l0. destruct (NatMap.find b m0). destruct v.
    discriminate.
    injection H33. intros.
    apply (H m m0 r p lambda c F V C R).
    auto. rewrite -> H34; injection H1; intros; rewrite -> H41; exact H2. exact H3.
    discriminate.
  - give_up.
  - apply (H m m0 r p lambda c F V C R).
    auto. rewrite -> H25; injection H1; intros; rewrite -> H36; exact H2. exact H3.
  - apply (H m m0 r p lambda c F V C R).
    auto. rewrite -> H25; injection H1; intros; rewrite -> H35; exact H2. exact H3.
  - apply (H m m0 r p lambda c F V C R).
    auto. rewrite -> H25; injection H1; intros; rewrite -> H37; exact H2. exact H3.
  - apply (H m m0 r p lambda c F V C R).
    auto. rewrite -> H25; injection H1; intros; rewrite -> H36; exact H2. exact H3.
  - apply (H m m0 r p lambda c F V C R).
    auto. rewrite -> H10; injection H1; intros; rewrite -> H19; exact H2. exact H3.
Admitted.


Definition wf4 (sigma: runtime_state): Prop :=
  forall k mu rho pi p epsilon l q e E raw_e,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find p pi = Some (process_value epsilon l q)) ->
  (epsilon = enclave_state_value e E) ->
  (e = enclave_ID_inactive \/ (e = enclave_ID_active raw_e /\ NatMap.find raw_e E <> None)).

Lemma wf4_preservation : forall sigma obs sigma' obs',
  wf4 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf4 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf4 in *.
  intros.
  inversion H0.
  inversion H15.
  subst.
  - give_up.
  - give_up.
  - give_up.
  - give_up.
  - give_up.
  - give_up.
  - give_up.
  - apply (H m m0 r p p1 epsilon l q e E raw_e).
    auto. injection H1. intros. subst. auto.
*)

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

(*
  intros.
  auto.
  (* split. *)
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
*)

(*
  give_up.
  give_up.
Admitted.

(* Ignore this *)
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

*)

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