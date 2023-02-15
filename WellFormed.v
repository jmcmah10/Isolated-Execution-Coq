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

Lemma eq_to_cmp : forall x, x = x -> (x =? x) = true.
Proof.
  intros x.
  induction x.
  simpl. reflexivity.
  simpl. intros. apply IHx. reflexivity.
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

Lemma iff_trans : forall P Q R,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  split.
  intros; apply H0; apply H; exact H1.
  intros; apply H; apply H0; exact H1.
Qed.

Lemma false_implies_anything : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Lemma contrapositive : forall P Q,
  (P <-> Q) -> (~P <-> ~Q).
Proof.
  intros.
  split; intros; intros contra.
  apply H in contra.
  unfold not in H0.
  apply H0 in contra. exact contra.
  apply H in contra.
  unfold not in H0.
  apply H0 in contra. exact contra.
Qed.

(* Well-Formed 1 and 2 *)
Definition wf1 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda c F V C R,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.MapsTo lambda (single_level_cache F V C R) k) ->
  ((In c F) -> (CacheletMap.In c C)).

Fixpoint cachelet_list_from_way_mask (s: set_ID) (W: way_mask): list cachelet_index :=
  match W with
  | nil => nil
  | w :: W' => (w, s) :: (cachelet_list_from_way_mask s W')
  end.
Fixpoint L_to_cachelet_list (L: list (set_ID * way_mask)): list cachelet_index :=
  match L with
  | nil => nil
  | (s, W) :: L' => (cachelet_list_from_way_mask s W) ++ (L_to_cachelet_list L')
  end.
Definition V_range (V: VPT) (e: raw_enclave_ID): option (list cachelet_index) :=
  match (NatMap.find e V) with
  | Some L => Some (L_to_cachelet_list (NatMapProperties.to_list L))
  | None => None
  end.
Definition wf2 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R c e ranV,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k = Some (single_level_cache F V C R)) ->
  (V_range V e = Some ranV) ->
  (In c ranV -> CacheletMap.In c C).

(* V Range Lemmas *)
Lemma v_range_empty_to_list : forall (L: NatMap.t (NatMap.t way_mask)),
  NatMap.Empty L ->
  (NatMapProperties.to_list L = nil).
Proof.
  intros.
  apply  NatMapFacts.is_empty_iff in H.
  unfold NatMap.is_empty in H.
  unfold NatMap.Raw.is_empty in H.
  unfold NatMapProperties.to_list.
  unfold NatMap.elements.
  unfold NatMap.Raw.elements.
  unfold NatMap.this in *.
  destruct (let (this, _) := L in this) in *.
  reflexivity.
  discriminate.
Qed.

(* CC Unfold Lemmas *)
Lemma cc_unfold_psi : forall psi e' l F V C R c vbtd delta,
  cc_unfold psi e' l = cc_unfold_valid F V C R c vbtd delta ->
  psi = single_level_cache F V C R.
Proof.
  intros.
  unfold cc_unfold in H.
  case_eq psi. intros.
  destruct psi.
  injection H0; intros; subst.
  destruct l.
  destruct (block_to_set_and_tag b s).
  destruct (find_way_ID_with_cache_tag e' s0 c1 v w).
  destruct (CacheletMap.find (w0, s0) w).
  injection H; intros; subst.
  reflexivity.
  discriminate.
  discriminate.
Qed.

Lemma cc_unfold_c : forall psi e' l F V C R c vbtd delta,
  cc_unfold psi e' l = cc_unfold_valid F V C R c vbtd delta ->
  CacheletMap.In c C.
Proof.
  intros.
  assert (H0 := H).
  apply cc_unfold_psi in H0.
  destruct c.
  unfold cc_unfold in H.
  subst psi.
  destruct l.
  destruct (block_to_set_and_tag b R).
  destruct (find_way_ID_with_cache_tag e' s0 c V C).
  case_eq (CacheletMap.find (w, s) C). intros.
  assert (CacheletMap.find (w, s) C <> None).
  intros contra. rewrite -> H0 in contra. discriminate.
  apply CacheletMapFacts.in_find_iff in H1.
  exact H1.
  case_eq (CacheletMap.find (w0, s0) C). intros.
  assert (A0 := H0). destruct (CacheletMap.find (w0, s0) C) in H, A0.
  injection H; intros; subst w0 s0.
  rewrite -> H0 in H1. discriminate.
  discriminate.
  intros; destruct (CacheletMap.find (w0, s0) C).
  discriminate.
  discriminate.
  discriminate.
Qed.

(* CC Update Lemmas *)
Lemma cc_update_f : forall psi e' d l0 c0 psi' F V C R F' V' C' R',
  cc_update psi e' d l0 = cc_update_valid c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  F = F'.
Proof.
  intros.
  subst psi psi'.
  unfold cc_update in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l0). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l0) in A0, H.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H0.
  injection H0; intros; subst c v w s.
  destruct c1.
  destruct w0.
  destruct e'.
  destruct (NatMap.find s R).
  destruct (replace p e).
  injection H; intros; subst.
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l0).
  discriminate.
  discriminate.
Qed.

Lemma cc_update_v : forall psi e' d l0 c0 psi' F V C R F' V' C' R',
  cc_update psi e' d l0 = cc_update_valid c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V = V'.
Proof.
  intros.
  subst psi psi'.
  unfold cc_update in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l0). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l0) in A0, H.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H0.
  injection H0; intros; subst c v w s.
  destruct c1.
  destruct w0.
  destruct e'.
  destruct (NatMap.find s R).
  destruct (replace p e).
  injection H; intros; subst.
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l0).
  discriminate.
  discriminate.
Qed.

Lemma cc_update_c : forall psi e' d l0 c0 psi' F V C R F' V' C' R' c,
  cc_update psi e' d l0 = cc_update_valid c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (CacheletMap.In c C <-> CacheletMap.In c C').
Proof.
  intros.
  subst psi psi'.
  unfold cc_update in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l0). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l0) in A0, H.
  assert (H1 := H0).
  apply cc_unfold_psi in H0.
  apply cc_unfold_c in H1.
  injection A0; intros; subst; clear A0.
  injection H0; intros; subst c1 v w s.
  destruct c2.
  destruct w0.
  destruct e'.
  destruct (NatMap.find s R).
  destruct (replace p e).
  injection H; intros; subst.
  destruct c.
  split.
  {
    intros.
    case_eq (eq_cachelet_index (w, s) (n, n0)).
    intros.
    unfold eq_cachelet_index in H3.
    apply cmp_to_eq_and in H3.
    destruct H3.
    subst n n0.
    apply CacheletMapFacts.in_find_iff.
    intros contra.
    assert (PairMap.find (elt:=way_set_cache_value) (w, s)
    (CacheletMap.add (w, s) (valid_bit_tag_and_data valid_bit c1 d) C)
    = Some (valid_bit_tag_and_data valid_bit c1 d)).
    apply CacheletMapFacts.add_eq_o.
    split.
    unfold fst; reflexivity.
    unfold snd; reflexivity.
    assert (Some (valid_bit_tag_and_data valid_bit c1 d) = None).
    rewrite <- contra.
    rewrite <- H3.
    reflexivity.
    discriminate.
    intros.
    apply cmp_to_uneq_and in H3.
    apply CacheletMapFacts.in_find_iff.
    assert (PairMap.find (n, n0) (CacheletMap.add (w, s) (valid_bit_tag_and_data valid_bit c1 d)
    C) = PairMap.find (n, n0) C).
    apply CacheletMapFacts.add_neq_o.
    unfold fst; unfold snd.
    destruct H3.
    intros contra.
    destruct contra; subst.
    unfold not in H3.
    apply H3. reflexivity.
    intros contra.
    destruct contra; subst.
    unfold not in H3.
    apply H3. reflexivity.
    rewrite -> H4.
    apply CacheletMapFacts.in_find_iff.
    exact H2.
  }
  {
    intros.
    case_eq (eq_cachelet_index (w, s) (n, n0)).
    intros.
    unfold eq_cachelet_index in H3.
    apply cmp_to_eq_and in H3.
    destruct H3.
    subst n n0.
    exact H1.
    intros.
    apply cmp_to_uneq_and in H3.
    assert (CacheletMap.find (n, n0) (CacheletMap.add (w, s) (valid_bit_tag_and_data valid_bit c1 d) C)
    = CacheletMap.find (n, n0) C).
    apply CacheletMapFacts.add_neq_o.
    unfold fst; unfold snd.
    intros contra.
    destruct contra; subst.
    destruct H3.
    unfold not in H3; apply H3; reflexivity.
    unfold not in H3; apply H3; reflexivity.
    apply CacheletMapFacts.add_in_iff in H2.
    destruct H2.
    unfold fst in H2; unfold snd in H2.
    destruct H2; subst.
    exact H1.
    exact H2.
  }
  discriminate.
  discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l0).
  discriminate.
  discriminate.
Qed.

(* CC Hit Read Lemmas *)
Lemma cc_hit_read_f : forall psi e' l D delta c0 psi' F V C R F' V' C' R',
  cc_hit_read psi e' l = cc_hit_read_valid D delta c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  F = F'.
Proof.
  intros.
  subst psi psi'.
  unfold cc_hit_read in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H0.
  injection H0; intros; subst c v w s.
  destruct c1.
  destruct w0.
  destruct (NatMap.find s R).
  destruct e'.
  injection H; intros; subst.
  reflexivity.
  discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l).
  discriminate.
  discriminate.
Qed.

Lemma cc_hit_read_v : forall psi e' l D delta c0 psi' F V C R F' V' C' R',
  cc_hit_read psi e' l = cc_hit_read_valid D delta c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V = V'.
Proof.
  intros.
  subst psi psi'.
  unfold cc_hit_read in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H0.
  injection H0; intros; subst c v w s.
  destruct c1.
  destruct w0.
  destruct (NatMap.find s R).
  destruct e'.
  injection H; intros; subst.
  reflexivity.
  discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l).
  discriminate.
  discriminate.
Qed.

Lemma cc_hit_read_c : forall psi e' l D delta c0 psi' F V C R F' V' C' R',
  cc_hit_read psi e' l = cc_hit_read_valid D delta c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  C = C'.
Proof.
  intros.
  subst psi psi'.
  unfold cc_hit_read in H.
  case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
  assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H0.
  injection H0; intros; subst c v w s.
  destruct c1.
  destruct w0.
  destruct (NatMap.find s R).
  destruct e'.
  injection H; intros; subst.
  reflexivity.
  discriminate.
  discriminate.
  intros; destruct (cc_unfold (single_level_cache F V C R) e' l).
  discriminate.
  discriminate.
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
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.

(*
Lemma cachelet_allocation_v : forall n e psi psi' F V C R F' V' C' R' e_index,
  cachelet_allocation n e psi = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (NatMap.In e_index V <-> NatMap.In e_index V').
Proof.
  intros n.
  induction n.
  {
    intros.
    subst psi psi'.
    unfold cachelet_allocation in H.
    unfold recursive_cachelet_allocation in H.
    injection H; intros; subst.
    split.
    intros; exact H0.
    intros; exact H0.
  }
  {
    intros.
    subst.
    unfold cachelet_allocation in H.
    unfold recursive_cachelet_allocation in H.
    fold recursive_cachelet_allocation in H.
    case_eq (way_first_allocation F); intros;
    assert (A0 := H0); destruct (way_first_allocation F) in A0, H.
    destruct c0.
    case_eq (NatMap.find s R); intros;
    assert (A1 := H1); destruct (NatMap.find s R) in A1, H.
    case_eq (NatMap.find e V); intros;
    assert (A2 := H2); destruct (NatMap.find e V) in A2, H.
    case_eq (NatMap.find s r0); intros; 
    assert (A3 := H3); destruct (NatMap.find s r0) in A3, H.
    injection A0; injection A1; injection A2; injection A3; intros; subst; clear A0 A1 A2 A3.
    specialize (IHn e (single_level_cache (remove_CAT (w, s) F) (NatMap.add e (NatMap.add s (w :: w0) r) V) C
    (NatMap.add s (update p w (enclave_ID_active e)) R)) (single_level_cache F' V' C' R')
    (remove_CAT (w, s) F) (NatMap.add e (NatMap.add s (w :: w0) r) V) C
    (NatMap.add s (update p w (enclave_ID_active e)) R) F' V' C' R' e_index).
    assert (NatMap.In e_index (NatMap.add e (NatMap.add s (w :: w0) r) V) <-> NatMap.In e_index V').
    apply IHn. unfold cachelet_allocation. exact H.
    reflexivity. reflexivity.
    apply iff_sym in H4.
    apply (iff_trans (NatMap.In e_index V) (NatMap.In e_index (NatMap.add e (NatMap.add s
    (w :: w0) r) V)) (NatMap.In e_index V')).
    split.
    {
      intros.
      apply NatMapFacts.add_in_iff. right; exact H5.
    }
    {
      intros.
      apply NatMapFacts.add_in_iff in H5. destruct H5.
      subst. assert (NatMap.find e_index V <> None).
      intros contra. rewrite -> H2 in contra. discriminate.
      apply NatMapFacts.in_find_iff in H5. exact H5.
      exact H5.
    }
    apply iff_sym. exact H4.
    discriminate.
    discriminate.
    injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2 A3.
    specialize (IHn e (single_level_cache (remove_CAT (w, s) F) (NatMap.add e (NatMap.add s (w :: nil) r) V) C
    (NatMap.add s (update p w (enclave_ID_active e)) R)) (single_level_cache F' V' C' R')
    (remove_CAT (w, s) F) (NatMap.add e (NatMap.add s (w :: nil) r) V) C
    (NatMap.add s (update p w (enclave_ID_active e)) R) F' V' C' R' e_index).
    assert (NatMap.In e_index (NatMap.add e (NatMap.add s (w :: nil) r) V) <-> NatMap.In e_index V').
    apply IHn. unfold cachelet_allocation. exact H.
    reflexivity. reflexivity.
    apply iff_sym in H4.
    apply (iff_trans (NatMap.In e_index V) (NatMap.In e_index (NatMap.add e (NatMap.add s
    (w :: nil) r) V)) (NatMap.In e_index V')).
    split.
    {
      intros.
      apply NatMapFacts.add_in_iff. right; exact H5.
    }
    {
      intros.
      apply NatMapFacts.add_in_iff in H5. destruct H5.
      subst. assert (NatMap.find e_index V <> None).
      intros contra. rewrite -> H2 in contra. discriminate.
      apply NatMapFacts.in_find_iff in H5. exact H5.
      exact H5.
    }
    apply iff_sym. exact H4.
    discriminate.
    discriminate.
    injection A0; injection A1; intros; subst; clear A0 A1 A2.
    specialize (IHn e (single_level_cache (remove_CAT (w, s) F) (NatMap.add e (NatMap.add s (w :: nil) (NatMap.empty (list way_ID))) V) C
    (NatMap.add s (update p w (enclave_ID_active e)) R)) (single_level_cache F' V' C' R')
    (remove_CAT (w, s) F) (NatMap.add e (NatMap.add s (w :: nil) (NatMap.empty (list way_ID))) V) C
    (NatMap.add s (update p w (enclave_ID_active e)) R) F' V' C' R' e_index).
    assert (NatMap.In e_index (NatMap.add e (NatMap.add s (w :: nil) (NatMap.empty (list way_ID))) V) <-> NatMap.In e_index V').
    apply IHn. unfold cachelet_allocation. exact H.
    reflexivity. reflexivity.
    apply iff_sym in H3.
    apply (iff_trans (NatMap.In e_index V) (NatMap.In e_index (NatMap.add e (NatMap.add s
    (w :: nil) (NatMap.empty (list way_ID))) V)) (NatMap.In e_index V')).
    split.
    {
      intros.
      apply NatMapFacts.add_in_iff. right; exact H4.
    }
    {
      intros.
      apply NatMapFacts.add_in_iff in H4. destruct H4.
      subst.
      intros contra. rewrite -> H2 in contra. discriminate.
      apply NatMapFacts.in_find_iff in H4. exact H4.
      exact H4.
    }
    apply iff_sym. exact H3.
    
  }
*)

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
  left. auto.
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
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.

(* CC Hit Write Lemmas *)
Lemma cc_hit_write_f : forall psi e' l v D c0 psi' F V C R F' V' C' R',
  cc_hit_write psi e' l v = cc_hit_write_valid D c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  F = F'.
Proof.
  intros.
  unfold cc_hit_write in H.
  case_eq (cc_unfold psi e' l). intros.
  assert (A0 := H2). destruct (cc_unfold psi e' l) in A0, H.
  destruct c3.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H2.
  injection H2; intros; subst c v0 w s.
  destruct w0.
  destruct (NatMap.find s1 R).
  destruct v.
  discriminate.
  destruct e'.
  injection H; intros.
  exact H4.
  discriminate.
  discriminate.
  intros; destruct (cc_unfold psi e' l).
  discriminate.
  discriminate.
Qed.

Lemma cc_hit_write_v : forall psi e' l v D c0 psi' F V C R F' V' C' R',
  cc_hit_write psi e' l v = cc_hit_write_valid D c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V = V'.
Proof.
  intros.
  unfold cc_hit_write in H.
  case_eq (cc_unfold psi e' l). intros.
  assert (A0 := H2). destruct (cc_unfold psi e' l) in A0, H.
  destruct c3.
  injection A0; intros; subst; clear A0.
  apply cc_unfold_psi in H2.
  injection H2; intros; subst c v0 w s.
  destruct w0.
  destruct (NatMap.find s1 R).
  destruct v.
  discriminate.
  destruct e'.
  injection H; intros.
  exact H3.
  discriminate.
  discriminate.
  intros; destruct (cc_unfold psi e' l).
  discriminate.
  discriminate.
Qed.

Lemma cc_hit_write_c : forall psi e' l v D c0 psi' F V C R F' V' C' R' c,
  cc_hit_write psi e' l v = cc_hit_write_valid D c0 psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (CacheletMap.In c C <-> CacheletMap.In c C').
Proof.
  intros.
  split.
  {
    intros.
    subst psi psi'.
    destruct c as (w, s).
    unfold cc_hit_write in H.
    case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
    assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
    injection A0; intros; subst; clear A0.
    assert (H1 := H0).
    apply cc_unfold_psi in H0.
    apply cc_unfold_c in H1.
    injection H0; intros; subst c v0 w0 s0.
    destruct c1.
    destruct w1.
    destruct (NatMap.find s0 R).
    destruct v.
    discriminate.
    destruct e'.
    injection H; intros; subst.
    apply CacheletMapFacts.add_in_iff.
    case_eq (eq_cachelet_index (w, s) (w0, s0)); intros.
    unfold eq_cachelet_index in H3.
    apply cmp_to_eq_and in H3.
    destruct H3. subst w0 s0.
    left. unfold fst; unfold snd.
    split. reflexivity. reflexivity.
    right. exact H2.
    discriminate.
    discriminate.
    intros; destruct (cc_unfold (single_level_cache F V C R) e' l).
    discriminate.
    discriminate.
  }
  {
    intros.
    subst psi psi'.
    destruct c as (w, s).
    unfold cc_hit_write in H.
    case_eq (cc_unfold (single_level_cache F V C R) e' l). intros.
    assert (A0 := H0). destruct (cc_unfold (single_level_cache F V C R) e' l) in A0, H.
    injection A0; intros; subst; clear A0.
    assert (H1 := H0).
    apply cc_unfold_psi in H0.
    apply cc_unfold_c in H1.
    injection H0; intros; subst c v0 w0 s0.
    destruct c1.
    destruct w1.
    destruct (NatMap.find s0 R).
    destruct v.
    discriminate.
    destruct e'.
    injection H; intros; subst.
    apply CacheletMapFacts.add_in_iff in H2.
    destruct H2.
    destruct H2.
    unfold fst in H2; unfold snd in H3; subst; exact H1.
    exact H2.
    discriminate.
    discriminate.
    intros; destruct (cc_unfold (single_level_cache F V C R) e' l).
    discriminate.
    discriminate.
  }
Qed.

(* Cachelet Deallocation Lemmas *)
Lemma cachelet_invalidation_c : forall c c' C C',
  cachelet_invalidation C c' = C' ->
  CacheletMap.In c C <-> CacheletMap.In c C'.
Proof.
  intros.
  unfold cachelet_invalidation in H.
  case_eq (CacheletMap.find c' C). intros.
  assert (A0 := H0). destruct (CacheletMap.find c' C) in H, A0.
  destruct w0.
  injection A0; intros; subst w; clear A0.
  split.
  {
    intros.
    rewrite <- H.
    apply CacheletMapFacts.add_in_iff.
    right; exact H1.
  }
  {
    intros.
    rewrite <- H in H1.
    apply CacheletMapFacts.add_in_iff in H1.
    destruct H1.
    destruct H1.
    destruct c; destruct c'.
    unfold fst in H1.
    unfold snd in H2.
    subst n n0.
    assert (CacheletMap.find (w, s) C <> None).
    intros contra. rewrite -> H0 in contra. discriminate.
    apply CacheletMapFacts.in_find_iff in H1.
    exact H1.
    exact H1.
  }
  discriminate.
  intros.
  destruct (CacheletMap.find c' C).
  discriminate.
  subst C'.
  split.
  intros; exact H.
  intros; exact H.
Qed.

Lemma free_cachelets_v : forall W e s F V C R F' V' C' R',
  free_cachelets e s W F V C R = Some (single_level_cache F' V' C' R') ->
  V = V'.
Proof.
  intros W.
  induction W.
  {
    intros.
    unfold free_cachelets in H.
    injection H; intros; subst.
    reflexivity.
  }
  {
    intros.
    unfold free_cachelets in H.
    case_eq (NatMap.find s R). intros.
    assert (A0 := H0). destruct (NatMap.find s R) in H, A0.
    fold free_cachelets in H.
    injection A0; intros; subst p0; clear A0.
    specialize (IHW e s ((a, s) :: F) V (cachelet_invalidation C (a, s))
      (NatMap.add s (update p a (enclave_ID_active e)) R) F' V' C' R') as H_app.
    apply H_app.
    exact H.
    discriminate.
    intros; destruct (NatMap.find s R).
    discriminate.
    discriminate.
  }
Qed.

Lemma cachelet_deallocation_v : forall e psi psi' F V C R F' V' C' R' r,
  cachelet_deallocation e psi = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  NatMap.In r V <-> NatMap.In r V'.
Proof.
  intros.
  unfold cachelet_deallocation in H.
  subst psi psi'.
  case_eq (NatMap.find e V). intros.
  assert (A0 := H0). destruct (NatMap.find e V) in A0, H.
  injection A0; intros; subst; clear A0.
  generalize dependent F;
  generalize dependent V;
  generalize dependent C;
  generalize dependent R;
  generalize dependent F';
  generalize dependent V';
  generalize dependent C';
  generalize dependent R'.
  induction (NatMapProperties.to_list r0).
  {
    intros.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    split.
    {
      intros.
      apply NatMapFacts.add_in_iff.
      right; exact H1.
    }
    {
      intros.
      apply NatMapFacts.add_in_iff in H1.
      destruct H1. subst.
      assert (NatMap.find r V <> None).
      intros contra. rewrite -> H0 in contra. discriminate.
      apply NatMapFacts.in_find_iff in H1.
      exact H1. exact H1.
    }
  }
  {
    intros.
    unfold clear_remapping_list in H.
    fold clear_remapping_list in H.
    destruct a.
    case_eq (free_cachelets e k w F V C R). intros.
    assert (A0 := H1). destruct (free_cachelets e k w F V C R) in H, A0.
    destruct s. destruct s0.
    injection A0; intros; subst; clear A0.
    apply (free_cachelets_v w e k F V C R c v w0 s) in H1. subst v.
    specialize (IHl R' C' V' F' s w0 V H0 c).
    apply IHl. exact H.
    discriminate.
    intros; destruct (free_cachelets e k w F V C R).
    discriminate.
    discriminate.
  }
  discriminate.
  intros; destruct (NatMap.find e V).
  discriminate.
  discriminate.
Qed.

Lemma free_cachelets_c : forall W e s F V C R F' V' C' R' c,
  free_cachelets e s W F V C R = Some (single_level_cache F' V' C' R') ->
  CacheletMap.In c C <-> CacheletMap.In c C'.
Proof.
  intros W.
  induction W.
  {
    intros.
    unfold free_cachelets in H.
    injection H; intros; subst.
    split.
    intros; exact H0.
    intros; exact H0.
  }
  {
    intros.
    unfold free_cachelets in H.
    case_eq (NatMap.find s R). intros.
    assert (A0 := H0). destruct (NatMap.find s R) in H, A0.
    fold free_cachelets in H.
    injection A0; intros; subst p0; clear A0.
    specialize (IHW e s ((a, s) :: F) V (cachelet_invalidation C (a, s))
      (NatMap.add s (update p a (enclave_ID_active e)) R) F' V' C' R' c) as H_app.
    assert (CacheletMap.In c C <-> CacheletMap.In c (cachelet_invalidation C (a, s))).
    apply (cachelet_invalidation_c c (a, s) C (cachelet_invalidation C (a, s))).
    reflexivity.
    apply (iff_trans (CacheletMap.In c C) (CacheletMap.In c (cachelet_invalidation C (a, s))) (CacheletMap.In c C')).
    exact H1.
    apply H_app.
    exact H.
    discriminate.
    intros. destruct (NatMap.find s R).
    discriminate.
    discriminate.
  }
Qed.

Lemma clear_remapping_list_c : forall e l F V C R F' V' C' R' c,
  clear_remapping_list e l F V C R = Some (single_level_cache F' V' C' R') ->
  CacheletMap.In c C <-> CacheletMap.In c C'.
Proof.
  intros e l.
  induction l.
  {
    intros.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    split.
    intros; exact H0.
    intros; exact H0.
  }
  {
    intros.
    unfold clear_remapping_list in H.
    destruct a.
    case_eq (free_cachelets e s w F V C R). intros.
    assert (A0 := H0). destruct (free_cachelets e s w F V C R) in H, A0.
    destruct s1. destruct s0.
    fold clear_remapping_list in H.
    injection A0; intros; subst; clear A0.
    apply (free_cachelets_c w e s F V C R c1 v0 w1 s0 c) in H0.
    specialize (IHl c1 v0 w1 s0 F' V' C' R' c) as H_app.
    apply (iff_trans (CacheletMap.In c C) (CacheletMap.In c w1) (CacheletMap.In c C')).
    exact H0.
    apply H_app.
    exact H.
    discriminate.
    intros.
    destruct (free_cachelets e s w F V C R).
    discriminate.
    discriminate.
  }
Qed.

Lemma cachelet_deallocation_c : forall e psi psi' F V C R F' V' C' R' c,
  cachelet_deallocation e psi = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  CacheletMap.In c C <-> CacheletMap.In c C'.
Proof.
  unfold cachelet_deallocation.
  destruct psi.
  case_eq (NatMap.find e v).
  intros r.
  destruct (NatMapProperties.to_list r).
  {
    intros.
    injection H1; intros; subst c v w s; clear H1; subst psi'.
    unfold clear_remapping_list in H0.
    injection H0; intros; subst.
    split.
    intros; exact H1.
    intros; exact H1.
  }
  {
    intros.
    unfold clear_remapping_list in H0.
    destruct p.
    injection H1; intros; subst c v w s; clear H1; subst psi'.
    case_eq (free_cachelets e k w0 F V C R). intros.
    assert (A0 := H1). destruct (free_cachelets e k w0 F V C R) in H0, A0.
    destruct s0.
    injection A0; intros; subst; clear A0.
    fold clear_remapping_list in H0.
    apply (free_cachelets_c w0 e k F V C R c v w s0 c0) in H1.
    apply (clear_remapping_list_c e l c v w s0 F' V' C' R' c0) in H0.
    apply (iff_trans (CacheletMap.In c0 C) (CacheletMap.In c0 w) (CacheletMap.In c0 C')).
    exact H1.
    exact H0.
    discriminate.
    intros.
    destruct (free_cachelets e k w0 F V C R).
    discriminate.
    discriminate.
  }
  intros.
  discriminate.
Qed.

(* WF2 MLC Read *)
Lemma wf2_mlc_read : forall h_tree lambda k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R' c enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V enc = Some ranV ->
  V_range V' enc = Some ranV' ->
  (In c ranV -> CacheletMap.In c C) ->
  (In c ranV' -> CacheletMap.In c C').
Proof.
  unfold mlc_read.
  intros h_tree lambda.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda;
  generalize dependent h_tree.
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
    apply H8.
    exact H9.
    discriminate.
  }
  {
    intros h_tree lambda IHTREE. intros.
    unfold recursive_mlc_read in H0.
    fold recursive_mlc_read in H0.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H9). destruct (NatMap.find a k) in A0, H0.
    case_eq (cc_hit_read s0 e' l0). intros.
    assert (A1 := H10). destruct (cc_hit_read s0 e' l0) in A1, H0.
    injection H0; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H11 := H10).
    destruct s; destruct s1.
    apply (cc_hit_read_c (single_level_cache c1 v w s) e' l0 D obs1 c0
    (single_level_cache c2 v0 w0 s0) c1 v w s c2 v0 w0 s0) in H10.
    apply (cc_hit_read_v (single_level_cache c1 v w s) e' l0 D obs1 c0
    (single_level_cache c2 v0 w0 s0) c1 v w s c2 v0 w0 s0) in H11.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H3. subst.
        rewrite -> H1 in H9.
        injection H9; intros; subst c1 v0 w0 s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c2 V C s0) k) =
        Some (single_level_cache c2 V C s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H2.
        injection H2; intros; subst c2 V' C' s0.
        apply H7.
        rewrite -> H5 in H6; injection H6; intros; subst.
        exact H8.
      }
      {
        intros. apply cmp_to_uneq in H3.
        assert (NatMap.find index (NatMap.add a (single_level_cache c2 v0 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H3.
        rewrite -> H2 in H4.
        rewrite -> H1 in H4.
        injection H4; intros; subst F' V' C' R'.
        apply H7.
        rewrite -> H5 in H6; injection H6; intros; subst.
        exact H8.
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
    assert (A1 := H11). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H0.
    case_eq (cc_update s0 e' d1 l0). intros.
    assert (A2 := H12). destruct (cc_update s0 e' d1 l0) in A2, H0.
    injection H0; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H3. subst a.
        destruct s.
        assert (H13 := H12).
        destruct s1.
        apply (cc_update_c (single_level_cache c1 v w s) e' D l0 c0 (single_level_cache c2 v0 w0 s0)
        c1 v w s c2 v0 w0 s0 c) in H12.
        apply (cc_update_v (single_level_cache c1 v w s) e' D l0 c0 (single_level_cache c2 v0 w0 s0)
        c1 v w s c2 v0 w0 s0) in H13.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c2 v0 w0 s0) m) =
        Some (single_level_cache c2 v0 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H2.
        rewrite -> H9 in H1.
        injection H1; injection H2; intros; subst.
        apply H12.
        apply H7.
        rewrite -> H5 in H6; injection H6; intros; subst.
        exact H8.
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
          apply (IHl h_tree root_node WFH1 k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' c enc ranV ranV').
          exact WFH.
          unfold mlc_write. exact H11.
          exact H1.
          rewrite <- H2. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H3.
          reflexivity.
          reflexivity.
          exact H5.
          exact H6.
          exact H7.
          exact H8.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in IHTREE. discriminate.
          specialize (WFH3 c1 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst.
          apply (H p0 p l) in IHTREE.
          apply (IHl h_tree (cache_node p) IHTREE k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' c enc ranV ranV').
          exact WFH.
          unfold mlc_write. exact H11.
          exact H1.
          rewrite <- H2. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H3.
          reflexivity.
          reflexivity.
          exact H5.
          exact H6.
          exact H7.
          exact H8.
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

Lemma wf2_mlc_read_none : forall lambda h_tree k e' m0 l0 D obs1 mu k' index psi psi'
  F V C R F' V' C' R' enc,
  well_defined_cache_tree h_tree ->
  mlc_read k e' m0 l0 lambda h_tree = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V enc = None ->
  V_range V' enc = None.
Proof.
  unfold mlc_read.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda;
  generalize dependent h_tree.
  induction l.
  {
    intros h_tree lambda IHTREE; intros.
    unfold mlc_read in H0.
    unfold recursive_mlc_read in H0.
    destruct l0. destruct (NatMap.find b m0).
    injection H0; intros; subst.
    rewrite -> H1 in H2.
    injection H2; intros; subst.
    exact H5.
    discriminate.
  }
  {
    intros h_tree lambda IHTREE; intros.
    unfold mlc_read in H0.
    unfold recursive_mlc_read in H0.
    fold recursive_mlc_read in H0.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H6). destruct (NatMap.find a k) in A0, H0.
    case_eq (cc_hit_read s0 e' l0). intros.
    assert (A1 := H7). destruct (cc_hit_read s0 e' l0) in A1, H0.
    injection H0; injection A0; injection A1; intros; subst; clear A0 A1.
    destruct s; destruct s1.
    apply (cc_hit_read_v (single_level_cache c0 v w s) e' l0 D obs1 c
    (single_level_cache c1 v0 w0 s0) c0 v w s c1 v0 w0 s0) in H7.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H3. subst.
        rewrite -> H1 in H6.
        injection H6; intros; subst c0 v0 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 V w0 s0) k) =
        Some (single_level_cache c1 V w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H2.
        injection H2; intros; subst c1 V' w0 s0.
        exact H5.
      }
      {
        intros. apply cmp_to_uneq in H3.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v0 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H3.
        rewrite -> H2 in H4.
        rewrite -> H1 in H4.
        injection H4; intros; subst F' V' C' R'.
        exact H5.
      }
    }
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_read s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_read k e' m0 l0 l). intros.
    assert (A1 := H8). destruct (recursive_mlc_read k e' m0 l0 l) in A1, H0.
    case_eq (cc_update s0 e' d1 l0). intros.
    assert (A2 := H9). destruct (cc_update s0 e' d1 l0) in A2, H0.
    injection H0; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H3. subst a.
        destruct s. destruct s1.
        apply (cc_update_v (single_level_cache c0 v w s) e' D l0 c (single_level_cache c1 v0 w0 s0)
        c0 v w s c1 v0 w0 s0) in H9.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w0 s0) m) =
        Some (single_level_cache c1 v0 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H3 in H2.
        rewrite -> H6 in H1.
        injection H1; injection H2; intros; subst.
        exact H5.
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
          apply (IHl h_tree root_node WFH1 k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' enc).
          unfold mlc_read. exact WFH.
          exact H8.
          exact H1.
          rewrite <- H2. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H3.
          reflexivity.
          reflexivity.
          exact H5.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in IHTREE. discriminate.
          specialize (WFH3 c0 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst.
          apply (H p0 p l) in IHTREE.
          apply (IHl h_tree (cache_node p) IHTREE k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' enc).
          unfold mlc_read. exact WFH.
          exact H8.
          exact H1.
          rewrite <- H2. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H3.
          reflexivity.
          reflexivity.
          exact H5.
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

(* WF2 MLC Allocation *)

(* WF2 MLC Write *)
Lemma wf2_mlc_write : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index psi psi'
  F V C R F' V' C' R' c enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V enc = Some ranV ->
  V_range V' enc = Some ranV' ->
  (In c ranV -> CacheletMap.In c C) ->
  (In c ranV' -> CacheletMap.In c C').
Proof.
  unfold mlc_write.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda;
  generalize dependent h_tree.
  induction l.
  {
    intros h_tree lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
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
    apply H6.
    exact H7.
    discriminate.
    discriminate.
  }
  {
    intros h_tree lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' c enc ranV ranV' WFH1; intros.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H8). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros.
    assert (A1 := H9). destruct (cc_hit_write s0 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H10 := H9).
    destruct s; destruct s1.
    apply (cc_hit_write_c (single_level_cache c1 v0 w s) e' (address b d1) v D c0
    (single_level_cache c2 v1 w0 s0) c1 v0 w s c2 v1 w0 s0 c) in H9.
    apply (cc_hit_write_v (single_level_cache c1 v0 w s) e' (address b d1) v D c0
    (single_level_cache c2 v1 w0 s0) c1 v0 w s c2 v1 w0 s0) in H10.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H2. subst.
        rewrite -> H0 in H8.
        injection H8; intros; subst c1 v1 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c2 V w0 s0) k) =
        Some (single_level_cache c2 V w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        injection H1; intros; subst c2 V' w0 s0.
        apply H9.
        rewrite -> H4 in H5; injection H5; intros; subst.
        apply H6. exact H7.
      }
      {
        intros. apply cmp_to_uneq in H2.
        assert (NatMap.find index (NatMap.add a (single_level_cache c2 v1 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H2.
        rewrite -> H1 in H3.
        rewrite -> H0 in H3.
        injection H3; intros; subst F' V' C' R'.
        apply H6.
        rewrite -> H4 in H5; injection H5; intros; subst.
        exact H7.
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
    assert (A1 := H10). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H.
    case_eq (cc_update s0 e' d0 l0). intros.
    assert (A2 := H11). destruct (cc_update s0 e' d0 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H2. subst a.
        destruct s.
        assert (H12 := H11).
        destruct s1.
        apply (cc_update_c (single_level_cache c1 v0 w s) e' D l0 c0 (single_level_cache c2 v1 w0 s0)
        c1 v0 w s c2 v1 w0 s0 c) in H11.
        apply (cc_update_v (single_level_cache c1 v0 w s) e' D l0 c0 (single_level_cache c2 v1 w0 s0)
        c1 v0 w s c2 v1 w0 s0) in H12.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c2 v1 w0 s0) m1) =
        Some (single_level_cache c2 v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        rewrite -> H8 in H0.
        injection H0; injection H1; intros; subst.
        apply H11.
        apply H6.
        rewrite -> H4 in H5; injection H5; intros; subst.
        exact H7.
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
          apply (IHl h_tree root_node WFH1 k e' m0 l0 v D o mu m1 index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' c enc ranV ranV').
          exact WFH.
          unfold mlc_write. exact H10.
          exact H0.
          rewrite <- H1. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H2.
          reflexivity.
          reflexivity.
          exact H4.
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
          apply (WFH4 p0 p l) in IHTREE.
          apply (IHl h_tree (cache_node p) IHTREE k e' m0 l0 v D o mu m1 index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R' c enc ranV ranV').
          exact WFH.
          unfold mlc_write. exact H10.
          exact H0.
          rewrite <- H1. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H2.
          reflexivity.
          reflexivity.
          exact H4.
          exact H5.
          exact H6.
          exact H7.
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

Lemma wf2_mlc_write_none : forall lambda h_tree k e' m0 l0 v D obs1 mu k' index psi psi'
  F V C R F' V' C' R' enc,
  well_defined_cache_tree h_tree ->
  mlc_write k e' m0 l0 v lambda h_tree = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V enc = None ->
  V_range V' enc = None.
Proof.
  unfold mlc_write.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda;
  generalize dependent h_tree.
  induction l.
  {
    intros h_tree lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' enc WFH1; intros.
    destruct (get_cache_ID_path lambda h_tree).
    injection IHTREE; intros; subst.
    unfold recursive_mlc_write in H.
    subst. destruct l0.
    destruct (NatMap.find b m0). destruct v.
    discriminate.
    injection H; intros; subst.
    rewrite -> H0 in H1.
    injection H1; intros; subst.
    exact H4.
    discriminate.
    discriminate.
  }
  {
    intros h_tree lambda IHTREE k e' m0 l0 v D obs1 mu k' index psi psi'
    F V C R F' V' C' R' enc WFH1; intros.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H5). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros.
    assert (A1 := H6). destruct (cc_hit_write s0 e' l0 v) in A1, H. destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H7 := H6).
    destruct s; destruct s1.
    apply (cc_hit_write_c (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0 c) in H6.
    apply (cc_hit_write_v (single_level_cache c0 v0 w s) e' (address b d1) v D c
    (single_level_cache c1 v1 w0 s0) c0 v0 w s c1 v1 w0 s0) in H7.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H2. subst.
        rewrite -> H0 in H5.
        injection H5; intros; subst c0 v1 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 V w0 s0) k) =
        Some (single_level_cache c1 V w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        injection H1; intros; subst c1 V' w0 s0.
        exact H4.
      }
      {
        intros. apply cmp_to_uneq in H2.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v1 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H2.
        rewrite -> H1 in H3.
        rewrite -> H0 in H3.
        injection H3; intros; subst F' V' C' R'.
        exact H4.
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
    assert (A1 := H7). destruct (recursive_mlc_write k e' m0 l0 v l) in A1, H.
    case_eq (cc_update s0 e' d0 l0). intros.
    assert (A2 := H8). destruct (cc_update s0 e' d0 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H2. subst a.
        destruct s.
        assert (H9 := H8).
        destruct s1.
        apply (cc_update_c (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0 c) in H8.
        apply (cc_update_v (single_level_cache c0 v0 w s) e' D l0 c (single_level_cache c1 v1 w0 s0)
        c0 v0 w s c1 v1 w0 s0) in H9.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v1 w0 s0) m1) =
        Some (single_level_cache c1 v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        rewrite -> H5 in H0.
        injection H0; injection H1; intros; subst.
        exact H4.
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
          apply (IHl h_tree root_node WFH1 k e' m0 l0 v D o mu m1 index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H7.
          exact H0.
          rewrite <- H1. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H2.
          reflexivity.
          reflexivity.
          exact H4.
        }
        {
          destruct lambda.
          rewrite -> WFH1 in IHTREE. discriminate.
          specialize (WFH3 c0 a (p :: l) IHTREE).
          unfold get_cache_ID_path in IHTREE. discriminate.
          specialize (WFH2 p0 a (p :: l) IHTREE).
          injection WFH2; intros; subst.
          apply (WFH4 p0 p l) in IHTREE.
          apply (IHl h_tree (cache_node p) IHTREE k e' m0 l0 v D o mu m1 index (single_level_cache F V C R)
          (single_level_cache F' V' C' R') F V C R F' V' C' R').
          exact WFH.
          unfold mlc_write. exact H7.
          exact H0.
          rewrite <- H1. apply eq_sym.
          apply NatMapFacts.add_neq_o.
          apply not_eq_sym. exact H2.
          reflexivity.
          reflexivity.
          exact H4.
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

(* WF2 MLC Deallocation *)
Lemma wf2_clear_remapping_list_helper : forall c,
  In c (L_to_cachelet_list (NatMapProperties.to_list (NatMap.empty way_mask))) ->
  False.
Proof.
  intros.
  unfold NatMapProperties.to_list in H.
  unfold NatMap.elements in H.
  unfold NatMap.this in H.
  unfold NatMap.Raw.elements in H.
  unfold NatMap.empty in H.
  unfold NatMap.Raw.empty in H.
  unfold L_to_cachelet_list in H.
  unfold In in H.
  exact H.
Qed.

Lemma wf2_clear_remapping_list : forall r l F V C R F' V' C' R' e ranV ranV' c,
  clear_remapping_list r (NatMapProperties.to_list l) F V C R
  = Some (single_level_cache F' V' C' R') ->
  V_range V e = Some ranV ->
  V_range V' e = Some ranV' ->
  NatMap.find r V = Some l ->
  (In c ranV -> CacheletMap.In c C) ->
  In c ranV' -> CacheletMap.In c C'.
Proof.
  intros r l.
  induction (NatMapProperties.to_list l).
  {
    intros.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    apply H3.
    unfold V_range in *.
    case_eq (NatMap.find e V). intros.
    assert (A0 := H5). destruct (NatMap.find e V) in H0, A0.
    case_eq (NatMap.find e (NatMap.add r (NatMap.empty way_mask) V)). intros.
    assert (A1 := H6).
    assert ((NatMap.find (elt:=remapping_list) e (NatMap.add r (NatMap.empty way_mask) V)) =
    (NatMap.find (elt:=NatMap.t way_mask) e (NatMap.add r (NatMap.empty way_mask) V))).
    reflexivity.
    destruct (NatMap.find (elt:=remapping_list) e (NatMap.add r (NatMap.empty way_mask) V)) in H1, H7.
    destruct (NatMap.find (elt:=NatMap.t way_mask) e (NatMap.add r (NatMap.empty way_mask) V)) in A1, H7.
    injection A0; injection A1; injection H0; injection H1; injection H7; intros; subst; clear A0 A1.
    {
      case_eq (eqb e r).
      {
        intros. apply cmp_to_eq in H8. subst.
        assert (NatMap.find r (NatMap.add r (NatMap.empty way_mask) V) = Some (NatMap.empty way_mask)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H6 in H8.
        injection H8; intros; subst.
        apply wf2_clear_remapping_list_helper in H4.
        apply false_implies_anything.
        exact H4.
      }
      {
        intros. apply cmp_to_uneq in H8.
        assert (NatMap.find e (NatMap.add r (NatMap.empty way_mask) V) = NatMap.find e V).
        apply NatMapFacts.add_neq_o. apply not_eq_sym. exact H8.
        rewrite -> H5 in H9.
        rewrite -> H6 in H9.
        injection H9; intros; subst.
        exact H4.
      }
    }
    discriminate.
    discriminate.
    intros.
    assert ((NatMap.find (elt:=remapping_list) e (NatMap.add r (NatMap.empty way_mask) V)) =
    (NatMap.find (elt:=NatMap.t way_mask) e (NatMap.add r (NatMap.empty way_mask) V))).
    reflexivity.
    destruct (NatMap.find (elt:=remapping_list) e (NatMap.add r (NatMap.empty way_mask) V)) in *.
    destruct (NatMap.find (elt:=NatMap.t way_mask) e (NatMap.add r (NatMap.empty way_mask) V)) in *.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find e V).
    discriminate.
    discriminate.
  }
  {
    intros.
    unfold clear_remapping_list in H.
    fold clear_remapping_list in H.
    destruct a.
    case_eq (free_cachelets r k w F V C R). intros.
    assert (A0 := H5). destruct (free_cachelets r k w F V C R) in A0, H.
    injection A0; intros; subst; clear A0.
    destruct s.
    assert (H6 := H5).
    apply (free_cachelets_v w r k F V C R c0 v w0 s) in H5.
    apply (free_cachelets_c w r k F V C R c0 v w0 s c) in H6.
    subst v.
    apply (IHl0 c0 V w0 s F' V' C' R' e ranV ranV' c).
    exact H. exact H0. exact H1. exact H2.
    intros. apply H6. apply H3. exact H5.
    exact H4.
    discriminate.
    intros; destruct (free_cachelets r k w F V C R).
    discriminate.
    discriminate.
  }
Qed.

Lemma wf2_cachelet_deallocation : forall r psi psi' F V C R F' V' C' R' e ranV ranV' c,
  cachelet_deallocation r psi = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V e = Some ranV ->
  V_range V' e = Some ranV' ->
  (In c ranV -> CacheletMap.In c C) ->
  In c ranV' -> CacheletMap.In c C'.
Proof.
  intros.
  unfold cachelet_deallocation in H.
  subst psi psi'.
  case_eq (NatMap.find r V). intros.
  assert (A0 := H0). destruct (NatMap.find r V) in A0, H.
  injection A0; intros; subst; clear A0.
  apply (wf2_clear_remapping_list r r0 F V C R F' V' C' R' e ranV ranV' c).
  exact H. exact H2. exact H3. exact H0. exact H4. exact H5.
  discriminate.
  intros; destruct (NatMap.find r V).
  discriminate.
  discriminate.
Qed.

Lemma wf2_clear_remapping_list_none : forall r l F V C R F' V' C' R' e,
  clear_remapping_list r (NatMapProperties.to_list l) F V C R
  = Some (single_level_cache F' V' C' R') ->
  e <> r -> V_range V e = None ->
  V_range V' e = None.
Proof.
  intros r l.
  induction (NatMapProperties.to_list l).
  {
    intros.
    unfold clear_remapping_list in H.
    injection H; intros; subst.
    unfold V_range in *.
    case_eq (NatMap.find e V). intros.
    assert (A0 := H2). destruct (NatMap.find e V) in A0, H1.
    discriminate.
    discriminate.
    intros. assert (H3 := H2). destruct (NatMap.find e V) in H1, H2.
    discriminate.
    assert (NatMap.find (elt := remapping_list) e (NatMap.add r (NatMap.empty way_mask) V) =
    NatMap.find e V).
    apply NatMapFacts.add_neq_o. apply not_eq_sym. exact H0.
    destruct (NatMap.find (elt := remapping_list) e (NatMap.add r (NatMap.empty way_mask) V)).
    rewrite -> H3 in H4. discriminate.
    reflexivity.
  }
  {
    intros.
    unfold clear_remapping_list in H.
    fold clear_remapping_list in H.
    destruct a.
    case_eq (free_cachelets r k w F V C R). intros.
    assert (A0 := H2). destruct (free_cachelets r k w F V C R) in A0, H.
    injection A0; intros; subst; clear A0.
    destruct s.
    apply (free_cachelets_v w r k F V C R c v w0 s) in H2.
    subst v.
    apply (IHl0 c V w0 s F' V' C' R' e).
    exact H. exact H0. exact H1.
    discriminate.
    intros; destruct (free_cachelets r k w F V C R).
    discriminate.
    discriminate.
  }
Qed.

Lemma V_range_in : forall V enc ranV,
  V_range V enc = Some ranV -> NatMap.In enc V.
Proof.
  intros.
  unfold V_range in H.
  case_eq (NatMap.find enc V). intros.
  assert (A0 := H0). destruct (NatMap.find enc V) in A0, H.
  injection A0; intros; subst; clear A0.
  assert (NatMap.find enc V <> None).
  intros contra. rewrite -> H0 in contra. discriminate.
  apply NatMapFacts.in_find_iff in H1. exact H1.
  discriminate.
  intros; destruct (NatMap.find enc V).
  discriminate.
  discriminate.
Qed.

Lemma V_range_not_in : forall V enc,
  V_range V enc = None -> ~NatMap.In enc V.
Proof.
  intros.
  unfold V_range in H.
  case_eq (NatMap.find enc V). intros.
  assert (A0 := H0). destruct (NatMap.find enc V) in A0, H.
  injection A0; intros; subst; clear A0. intros contra.
  apply NatMapFacts.in_find_iff in contra.
  rewrite -> H0 in contra. discriminate.
  discriminate.
  intros. assert (H1 := H0).
  destruct (NatMap.find enc V) in H0, H. discriminate.
  intros contra.
  apply NatMapFacts.in_find_iff in contra.
  rewrite -> H1 in contra. unfold not in contra.
  apply contra. reflexivity.
Qed.

(* TODO *)
Lemma wf2_mlc_dealloc : forall lambda h_tree state k k' index psi psi' F V C R F' V' C' R' c enc ranV ranV',
  well_defined_cache_tree h_tree ->
  mlc_deallocation state k lambda h_tree = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V enc = Some ranV ->
  V_range V' enc = Some ranV' ->
  (In c ranV -> CacheletMap.In c C) ->
  (In c ranV' -> CacheletMap.In c C').
Proof.
  unfold mlc_deallocation.
  intros lambda h_tree.
  case_eq (get_cache_ID_path lambda h_tree).
  intros l.
  generalize dependent lambda;
  generalize dependent h_tree.
  induction l.
  {
    intros h_tree lambda IHTREE state k k' index psi psi' F V C R
    F' V' C' R' c enc ranV ranV' WFH; intros.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    injection H; intros; subst k'.
    rewrite -> H0 in H1.
    injection H1; intros; subst psi psi'.
    injection H8; intros; subst F' V' C' R'.
    apply H6.
    rewrite -> H5 in H4; injection H4; intros; subst.
    exact H7.
    discriminate.
  }
  {
    intros h_tree lambda IHTREE state k k' index psi psi' F V C R
    F' V' C' R' c enc ranV ranV' WFH; intros.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    fold recursive_mlc_deallocation in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H8). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_deallocation r s0). intros.
    assert (A1 := H9). destruct (cachelet_deallocation r s0) in A1, H.
    injection A0; injection A1; intros; subst s0 s2; clear A0 A1.
    case_eq (eqb index a).
    {
      intros; apply cmp_to_eq in H10; subst a.
      rewrite -> H8 in H0.
      injection H0; intros; subst s.
      destruct s1.
      case_eq (V_range v enc). intros.


      specialize (IHL (NatMap.add index (single_level_cache c0 v w s) k) k' index
      (single_level_cache c0 v w s) psi' c0 v w s F' V' C' R' c enc l ranV').
      apply IHL.
      unfold mlc_deallocation. exact H.
      apply NatMapFacts.add_eq_o. reflexivity.
      exact H1.
      reflexivity.
      exact H3.
      unfold cachelet_deallocation in H9.
      destruct psi.
      case_eq (NatMap.find r v0). intros.
      assert (A0 := H11). destruct (NatMap.find r v0) in A0, H9.
      injection A0; injection H2; intros; subst; clear A0.
      exact H10. discriminate.
      intros; destruct (NatMap.find r v0).
      discriminate. exact H10.
      exact H5.
      apply (wf2_cachelet_deallocation r psi (single_level_cache c0 v w s) F V C R
      c0 v w s enc ranV l c).
      exact H9. exact H2. reflexivity. exact H4.
      exact H10. exact H6. exact H7.
      intros. destruct psi.
      injection H2; intros; subst c1 v0 w0 s0.
      apply (cachelet_deallocation_v r (single_level_cache F V C R) (single_level_cache c0 v w s)
      F V C R c0 v w s enc) in H9.
      apply V_range_in in H4. apply V_range_not_in in H10.
      apply H9 in H4.
      unfold not in H10.
      apply H10 in H4.
      apply false_implies_anything.
      exact H4.
      reflexivity.
      reflexivity.
    }
    {
      intros; apply cmp_to_uneq in H10.
      specialize (IHL (NatMap.add a s1 k) k' index
      psi psi' F V C R F' V' C' R' c enc ranV ranV').
      apply IHL.
      unfold mlc_deallocation. exact H.
      rewrite <- H0. apply NatMapFacts.add_neq_o.
      apply not_eq_sym. exact H10.
      exact H1.
      exact H2.
      exact H3.
      exact H4.
      exact H5.
      exact H6.
      exact H7.
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
Qed.

Lemma wf2_mlc_dealloc_none : forall L state k k' index psi psi' F V C R F' V' C' R' enc,
  mlc_deallocation state k L = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  V_range V enc = None ->
  V_range V' enc = None.
Proof.
  intros L state.
  induction L.
  {
    intros.
    unfold mlc_deallocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    subst psi psi'.
    injection H; intros; subst k'.
    rewrite -> H0 in H1.
    injection H1; intros; subst.
    exact H4.
    discriminate.
  }
  {
    intros.
    unfold mlc_deallocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    fold recursive_mlc_deallocation in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H5). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_deallocation r s0). intros.
    assert (A1 := H6). destruct (cachelet_deallocation r s0) in A1, H.
    injection A0; injection A1; intros; subst s0 s2; clear A0 A1.
    case_eq (eqb index a).
    {
      intros; apply cmp_to_eq in H7; subst a.
      rewrite -> H5 in H0.
      injection H0; intros; subst s.
      destruct s1.
      case_eq (V_range v enc). intros.
      apply V_range_in in H7.
      apply V_range_not_in in H4.
      unfold not in H4. subst psi.
      apply (cachelet_deallocation_v r (single_level_cache F V C R) (single_level_cache c v w s)
      F V C R c v w s enc) in H6.
      apply H6 in H7.  apply H4 in H7.
      apply false_implies_anything. exact H7.
      reflexivity.
      reflexivity.
      intros.
      apply (IHL (NatMap.add index (single_level_cache c v w s) k) k' index
      (single_level_cache c v w s) psi' c v w s F' V' C' R' enc).
      unfold mlc_deallocation. exact H.
      apply NatMapFacts.add_eq_o. reflexivity.
      exact H1.
      reflexivity.
      exact H3.
      exact H7.
    }
    {
      intros; apply cmp_to_uneq in H7.
      specialize (IHL (NatMap.add a s1 k) k' index
      psi psi' F V C R F' V' C' R' enc).
      apply IHL.
      unfold mlc_deallocation. exact H.
      rewrite <- H0. apply NatMapFacts.add_neq_o.
      apply not_eq_sym. exact H7.
      exact H1.
      exact H2.
      exact H3.
      exact H4.
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
Qed.

Lemma wf_mlc_dealloc_none : forall L state k k' index,
  mlc_deallocation state k L = Some k' ->
  NatMap.find index k = None ->
  NatMap.find index k' = None.
Proof.
  intros L state.
  induction L.
  {
    intros.
    unfold mlc_deallocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    injection H; intros; subst k'.
    exact H0.
    discriminate.
  }
  {
    intros.
    unfold mlc_deallocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    fold recursive_mlc_deallocation in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H1). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_deallocation r s0). intros.
    assert (A1 := H2). destruct (cachelet_deallocation r s0) in A1, H.
    injection A0; injection A1; intros; subst s0 s2; clear A0 A1.
    case_eq (eqb index a).
    {
      intros; apply cmp_to_eq in H3; subst.
      rewrite -> H0 in H1. discriminate.
    }
    {
      intros; apply cmp_to_uneq in H3.
      apply (IHL (NatMap.add a s1 k) k' index).
      unfold mlc_deallocation. exact H.
      rewrite <- H0. apply NatMapFacts.add_neq_o.
      apply not_eq_sym. exact H3.
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
Qed.

(* WF1 MLC Read *)
Lemma wf1_mlc_read : forall L k e' m0 l0 D obs1 mu k' index psi psi' F V C R F' V' C' R' c,
  mlc_read k e' m0 l0 L = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (In c F -> CacheletMap.In c C) -> (In c F' -> CacheletMap.In c C').
Proof.
  intros L.
  induction L.
  {
    intros.
    unfold mlc_read in H.
    unfold recursive_mlc_read in H.
    destruct l0.
    destruct (NatMap.find b m0).
    injection H; intros; subst.
    rewrite -> H0 in H1.
    injection H1; intros; subst.
    apply H4.
    exact H5.
    discriminate.
  }
  {
    intros.
    unfold mlc_read in H.
    unfold recursive_mlc_read in H.
    fold recursive_mlc_read in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H6). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_read s0 e' l0). intros.
    assert (A1 := H7). destruct (cc_hit_read s0 e' l0) in A1, H.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H8 := H7).
    destruct s; destruct s1.
    apply (cc_hit_read_f (single_level_cache c1 v w s) e' l0 D obs1 c0
    (single_level_cache c2 v0 w0 s0) c1 v w s c2 v0 w0 s0) in H7.
    apply (cc_hit_read_c (single_level_cache c1 v w s) e' l0 D obs1 c0
    (single_level_cache c2 v0 w0 s0) c1 v w s c2 v0 w0 s0) in H8.
    subst.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H2. subst.
        rewrite -> H0 in H6.
        injection H6; intros; subst c2 v w0 s.
        assert (NatMap.find index (NatMap.add index (single_level_cache F v0 C s0) k) =
        Some (single_level_cache F v0 C s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        injection H1; intros; subst F' v0 C' s0.
        apply H4.
        exact H5.
      }
      {
        intros. apply cmp_to_uneq in H2.
        assert (NatMap.find index (NatMap.add a (single_level_cache c2 v0 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H2.
        rewrite -> H1 in H3.
        rewrite -> H0 in H3.
        injection H3; intros; subst F' V' C' R'.
        apply H4.
        exact H5.
      }
    }
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_read s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_read k e' m0 l0 L). intros.
    assert (A1 := H8). destruct (recursive_mlc_read k e' m0 l0 L) in A1, H.
    case_eq (cc_update s0 e' d1 l0). intros.
    assert (A2 := H9). destruct (cc_update s0 e' d1 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H2. subst a.
        destruct s.
        assert (H10 := H9).
        destruct s1.
        apply (cc_update_c (single_level_cache c1 v w s) e' D l0 c0 (single_level_cache c2 v0 w0 s0)
        c1 v w s c2 v0 w0 s0 c) in H9.
        apply (cc_update_f (single_level_cache c1 v w s) e' D l0 c0 (single_level_cache c2 v0 w0 s0)
        c1 v w s c2 v0 w0 s0) in H10.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c2 v0 w0 s0) m) =
        Some (single_level_cache c2 v0 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        rewrite -> H6 in H0.
        injection H0; injection H1; intros; subst.
        apply H9.
        apply H4.
        exact H5.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        intros. apply cmp_to_uneq in H2.
        specialize (IHL k e' m0 l0 D obs1 o m index (single_level_cache F V C R)
        (single_level_cache F' V' C' R') F V C R F' V' C' R' c).
        apply IHL.
        unfold mlc_write. exact H8.
        exact H0.
        rewrite <- H1. apply eq_sym.
        apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H2.
        reflexivity.
        reflexivity.
        exact H4.
        exact H5.
      }
    }
    discriminate.
    intros; destruct (cc_update s0 e' d1 l0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 L).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
  }
Qed.

Lemma wf_mlc_read_none : forall L k e' m0 l0 D obs1 mu k' index,
  mlc_read k e' m0 l0 L = mlc_read_valid D obs1 mu k' ->
  NatMap.find index k = None ->
  NatMap.find index k' = None.
Proof.
  intros L.
  induction L.
  {
    intros.
    unfold mlc_read in H.
    unfold recursive_mlc_read in H.
    destruct l0.
    destruct (NatMap.find b m0).
    injection H; intros; subst.
    exact H0.
    discriminate.
  }
  {
    intros.
    unfold mlc_read in H.
    unfold recursive_mlc_read in H.
    fold recursive_mlc_read in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H1). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_read s0 e' l0). intros.
    assert (A1 := H2). destruct (cc_hit_read s0 e' l0) in A1, H.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H3 := H2).
    destruct s; destruct s1.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H4. subst.
        rewrite -> H1 in H0.
        discriminate.
      }
      {
        intros. apply cmp_to_uneq in H4.
        rewrite <- H0.
        apply NatMapFacts.add_neq_o.
        exact H4.
      }
    }
    discriminate.
    intros; destruct (cc_hit_read s0 e' l0).
    discriminate.
    case_eq (recursive_mlc_read k e' m0 l0 L). intros.
    assert (A1 := H3). destruct (recursive_mlc_read k e' m0 l0 L) in A1, H.
    case_eq (cc_update s0 e' d1 l0). intros.
    assert (A2 := H4). destruct (cc_update s0 e' d1 l0) in A2, H.
    injection H; injection A0; injection A1; injection A2; intros; subst; clear A0 A1 A2.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H5. subst a.
        rewrite -> H0 in H1.
        discriminate.
      }
      {
        intros. apply cmp_to_uneq in H5.
        specialize (IHL k e' m0 l0 D obs1 o m index).
        assert (NatMap.find index m = None).
        apply IHL.
        unfold mlc_write; exact H3.
        exact H0.
        rewrite <- H6.
        apply NatMapFacts.add_neq_o.
        apply not_eq_sym.
        exact H5.
      }
    }
    discriminate.
    intros; destruct (cc_update s0 e' d1 l0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (recursive_mlc_read k e' m0 l0 L).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
  }
Qed.

(* WF1 MLC Allocation *)
Lemma wf1_mlc_alloc : forall L n state k k' index psi psi' F V C R F' V' C' R' c,
  mlc_allocation n state k L = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (In c F -> CacheletMap.In c C) -> (In c F' -> CacheletMap.In c C').
Proof.
  intros L.
  induction L.
  {
    intros.
    unfold mlc_allocation in H.
    destruct state. destruct e.
    unfold recursive_mlc_allocation in H.
    injection H; intros; subst k' psi psi'.
    rewrite -> H0 in H1.
    injection H1; intros; subst.
    apply H4; exact H5.
    discriminate.
  }
  {
    intros.
    unfold mlc_allocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_allocation in H.
    fold recursive_mlc_allocation in H.
    case_eq n.
    intros. subst. discriminate.
    intros. subst n.
    case_eq (NatMap.find a k).
    intros. assert (A0 := H6). destruct (NatMap.find a k) in H, A0.
    case_eq (cachelet_allocation n0 r s0).
    intros. assert (A1 := H7). destruct (cachelet_allocation n0 r s0) in H, A1.
    injection A0; injection A1; intros; subst; clear A0 A1.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H2.
        subst.
        destruct s1.
        specialize (IHL l (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add index (single_level_cache c0 v w s0) k) k' index (single_level_cache c0 v w s0)
        (single_level_cache F' V' C' R') c0 v w s0 F' V' C' R' c) as H_app.
        apply H_app; clear H_app.
        unfold mlc_allocation. exact H.
        apply NatMapFacts.add_eq_o. reflexivity.
        exact H1.
        reflexivity.
        reflexivity.
        intros. destruct s. rewrite -> H6 in H0.
        injection H0; intros; subst c1 v0 w0 s; clear H0.
        assert (HF := H7); apply (cachelet_allocation_f n0 r (single_level_cache F V C R) (single_level_cache c0 v w s0)
        F V C R c0 v w s0 c) in HF.
        assert (HC := H7); apply (cachelet_allocation_c n0 r (single_level_cache F V C R) (single_level_cache c0 v w s0)
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
        intros. apply cmp_to_uneq in H2.
        specialize (IHL l (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add a s1 k) k' index (single_level_cache F V C R) (single_level_cache F' V' C' R')
        F V C R F' V' C' R') as H_app.
        apply H_app; clear H_app.
        unfold mlc_allocation. exact H.
        rewrite <- H0. apply NatMapFacts.add_neq_o. exact H2.
        exact H1.
        reflexivity.
        reflexivity.
        exact H4.
        exact H5.
      }
    }
    discriminate.
    intros; destruct (cachelet_allocation n0 r s0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
    discriminate.
  }
Qed.

Lemma wf_mlc_alloc_none : forall L n state k k' index,
  mlc_allocation n state k L = Some k' ->
  NatMap.find index k = None ->
  NatMap.find index k' = None.
Proof.
  intros L.
  induction L.
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
    fold recursive_mlc_allocation in H.
    case_eq n. intros; subst; discriminate.
    intros; subst.
    case_eq (NatMap.find a k).
    intros. assert (H1' := H1). destruct (NatMap.find a k) in H, H1'.
    case_eq (cachelet_allocation n0 r s0).
    intros. assert (H2' := H2). destruct (cachelet_allocation n0 r s0) in H, H2'.
    injection H1'; injection H2'; intros; subst; clear H1' H2'.
    {
      case_eq (eqb index a); intros.
      {
        intros. apply cmp_to_eq in H3.
        subst a.
        destruct s1.
        specialize (IHL l (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add index (single_level_cache c v w s0) k) k' index) as H_app.
        apply H_app; clear H_app.
        unfold mlc_allocation. exact H.
        rewrite -> H0 in H1. discriminate.
      }
      {
        intros. apply cmp_to_uneq in H3.
        destruct s1.
        specialize (IHL l (enclave_state_value (enclave_ID_active r) (NatMap.empty enclave_memory_range_value))
        (NatMap.add a (single_level_cache c v w s0) k) k' index) as H_app.
        apply H_app; clear H_app.
        unfold mlc_allocation. exact H.
        rewrite <- H0.
        apply NatMapFacts.add_neq_o.
        auto.
      }
    }
    discriminate.
    intros; destruct (cachelet_allocation n0 r s0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
    discriminate.
  }
Qed.

(* WF1 MLC Write *)
Lemma wf1_mlc_write : forall L k e' m0 l0 v D obs1 mu k' index psi psi' F V C R F' V' C' R' c,
  mlc_write k e' m0 l0 v L = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (In c F -> CacheletMap.In c C) -> (In c F' -> CacheletMap.In c C').
Proof.
  intros L.
  induction L.
  {
    intros.
    unfold mlc_write in H.
    unfold recursive_mlc_write in H.
    destruct l0.
    destruct (NatMap.find b m0).
    destruct v.
    discriminate.
    injection H; intros; subst D obs1 mu k'.
    rewrite -> H0 in H1.
    subst psi psi'.
    injection H1; intros; subst.
    apply H4; exact H5.
    discriminate.
  }
  {
    intros.
    unfold mlc_write in H.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H6). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros.
    assert (A1 := H7). destruct (cc_hit_write s0 e' l0 v) in A1, H.
    destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    assert (H8 := H7).
    destruct s; destruct s1.
    apply (cc_hit_write_f (single_level_cache c1 v0 w s) e' (address b d1) v D c0
    (single_level_cache c2 v1 w0 s0) c1 v0 w s c2 v1 w0 s0) in H7.
    apply (cc_hit_write_c (single_level_cache c1 v0 w s) e' (address b d1) v D c0
    (single_level_cache c2 v1 w0 s0) c1 v0 w s c2 v1 w0 s0 c) in H8.
    subst c2.
    {
      case_eq (eqb a index).
      {
        intros. apply cmp_to_eq in H2. subst.
        rewrite -> H0 in H6.
        injection H6; intros; subst c1 v0 w s.
        assert (NatMap.find index (NatMap.add index (single_level_cache F v1 w0 s0) k) =
        Some (single_level_cache F v1 w0 s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        injection H1; intros; subst F' v1 w0 s0.
        apply H8.
        apply H4.
        exact H5.
      }
      {
        intros. apply cmp_to_uneq in H2.
        assert (NatMap.find index (NatMap.add a (single_level_cache c1 v1 w0 s0) k) = NatMap.find index k).
        apply NatMapFacts.add_neq_o. exact H2.
        rewrite -> H1 in H3.
        rewrite -> H0 in H3.
        injection H3; intros; subst F' V' C' R'.
        apply H4.
        exact H5.
      }
    }
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    discriminate.
    intros; destruct (cc_hit_write s0 e' l0 v).
    discriminate.
    injection A0; intros; subst s0; clear A0.
    case_eq (recursive_mlc_write k e' m0 l0 v L). intros.
    assert (A0 := H8). destruct (recursive_mlc_write k e' m0 l0 v L) in A0, H.
    case_eq (cc_update s e' d0 l0). intros.
    assert (A1 := H9). destruct (cc_update s e' d0 l0) in A1, H.
    injection A0; injection A1; injection H; intros; subst; clear A0 A1.
    {
      case_eq (eqb index a).
      {
        intros. apply cmp_to_eq in H2. subst a.
        destruct s0.
        assert (H10 := H9).
        destruct s.
        apply (cc_update_c (single_level_cache c2 v1 w0 s) e' d l0 c0 (single_level_cache c1 v0 w s0)
        c2 v1 w0 s c1 v0 w s0 c) in H9.
        apply (cc_update_f (single_level_cache c2 v1 w0 s) e' d l0 c0 (single_level_cache c1 v0 w s0)
        c2 v1 w0 s c1 v0 w s0) in H10.
        subst.
        assert (NatMap.find index (NatMap.add index (single_level_cache c1 v0 w s0) m1) =
        Some (single_level_cache c1 v0 w s0)).
        apply NatMapFacts.add_eq_o. reflexivity.
        rewrite -> H2 in H1.
        rewrite -> H6 in H0.
        injection H0; injection H1; intros; subst.
        apply H9.
        apply H4.
        exact H5.
        reflexivity.
        reflexivity.
        reflexivity.
        reflexivity.
      }
      {
        intros. apply cmp_to_uneq in H2.
        specialize (IHL k e' m0 l0 v d o m m1 index (single_level_cache F V C R)
        (single_level_cache F' V' C' R') F V C R F' V' C' R' c).
        apply IHL.
        unfold mlc_write. exact H8.
        exact H0.
        rewrite <- H1. apply eq_sym.
        apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H2.
        reflexivity.
        reflexivity.
        exact H4.
        exact H5.
      }
    }
    discriminate.
    intros; destruct (cc_update s e' d0 l0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (recursive_mlc_write k e' m0 l0 v L).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
  }
Qed.

Lemma wf_mlc_write_none : forall L k e' m0 l0 v D obs1 mu k' index,
  mlc_write k e' m0 l0 v L = mlc_write_valid D obs1 mu k' ->
  NatMap.find index k = None ->
  NatMap.find index k' = None.
Proof.
  intros L.
  induction L.
  {
    intros.
    unfold mlc_write in H.
    unfold recursive_mlc_write in H.
    destruct l0.
    destruct (NatMap.find b m0).
    destruct v.
    discriminate.
    injection H; intros; subst D obs1 mu k'.
    exact H0.
    discriminate.
  }
  {
    intros.
    unfold mlc_write in H.
    unfold recursive_mlc_write in H.
    fold recursive_mlc_write in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H1). destruct (NatMap.find a k) in A0, H.
    case_eq (cc_hit_write s0 e' l0 v). intros.
    assert (A1 := H2). destruct (cc_hit_write s0 e' l0 v) in A1, H.
    destruct l0.
    injection H; injection A0; injection A1; intros; subst; clear A0 A1.
    destruct s; destruct s1.
    {
      case_eq (eqb a index).
      {
        intros.
        apply cmp_to_eq in H3.
        subst a.
        rewrite -> H0 in H1.
        discriminate.
      }
      {
        intros.
        apply cmp_to_uneq in H3.
        rewrite <- H0.
        apply NatMapFacts.add_neq_o.
        exact H3.
      }
    }
    discriminate.
    intros; destruct (cc_hit_write s0 e' l0 v).
    discriminate.
    injection A0; intros; subst s0; clear A0.
    case_eq (recursive_mlc_write k e' m0 l0 v L). intros.
    assert (A0 := H3). destruct (recursive_mlc_write k e' m0 l0 v L) in A0, H.
    case_eq (cc_update s e' d0 l0). intros.
    assert (A1 := H4). destruct (cc_update s e' d0 l0) in A1, H.
    injection A0; injection A1; injection H; intros; subst; clear A0 A1.
    {
      case_eq (eqb index a).
      {
        intros.
        apply cmp_to_eq in H5; subst a.
        rewrite -> H0 in H1.
        discriminate.
      }
      {
        intros.
        apply cmp_to_uneq in H5.
        specialize (IHL k e' m0 l0 v d o m m1 index).
        assert (NatMap.find index (NatMap.add a s0 m1) = NatMap.find index m1).
        apply NatMapFacts.add_neq_o.
        apply not_eq_sym. exact H5.
        rewrite -> H6.
        apply IHL.
        exact H3.
        exact H0.
      }
    }
    discriminate.
    intros; destruct (cc_update s e' d0 l0).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (recursive_mlc_write k e' m0 l0 v L).
    discriminate.
    discriminate.
    discriminate.
    intros; destruct (NatMap.find a k).
    discriminate.
    discriminate.
  }
Qed.

(* WF1 MLC Deallocation *)
Lemma wf1_free_cachelets : forall w0 r k F V C R c1 v0 w1 s0 r0 c,
  (In c F -> CacheletMap.In c C) ->
  NatMap.find r V = Some r0 ->
  free_cachelets r k w0 F V C R = Some (single_level_cache c1 v0 w1 s0) ->
  In c c1 -> CacheletMap.In c w1.
Proof.
  intros w0.
  induction w0.
  {
    intros.
    unfold free_cachelets in H1.
    injection H1; intros; subst.
    apply H; exact H2.
  }
  {
    intros.
    unfold free_cachelets in H1.
    fold free_cachelets in H1.
    case_eq (NatMap.find k R). intros.
    assert (A0 := H3). destruct (NatMap.find k R) in A0, H1.
    injection A0; intros; subst p0.
    specialize (IHw0 r k ((a, k) :: F) V (cachelet_invalidation C (a, k))
    (NatMap.add k (update p a (enclave_ID_active r)) R) c1 v0 w1 s0 r0 c).
    apply IHw0.
    intros.
    apply (cachelet_invalidation_c c (a, k) C (cachelet_invalidation C (a, k))).
    reflexivity.
    apply H.
    apply in_inv in H4.
    destruct H4.
    subst c.
    give_up.
    exact H4.
    exact H0.
    exact H1.
    exact H2.
    discriminate.
    intros; destruct (NatMap.find k R).
    discriminate.
    discriminate.
  }
Admitted.

Lemma wf1_clear_remapping_list : forall r r0 c0 v w s F V C R c,
  (In c F -> CacheletMap.In c C) ->
  clear_remapping_list r (NatMapProperties.to_list r0) F V C R = Some (single_level_cache c0 v w s) ->
  NatMap.find r V = Some r0 ->
  In c c0 -> CacheletMap.In c w.
Proof.
  intros r r0.
  induction (NatMapProperties.to_list r0).
  {
    intros.
    unfold clear_remapping_list in H0.
    injection H0; intros; subst c0 v w s.
    apply H; exact H2.
  }
  {
    intros.
    unfold clear_remapping_list in H0.
    fold clear_remapping_list in H0.
    destruct a.
    case_eq (free_cachelets r k w0 F V C R). intros.
    assert (A0 := H3). destruct (free_cachelets r k w0 F V C R) in A0, H0.
    injection A0; intros; subst s1.
    destruct s0.
    specialize (IHl c0 v w s c1 v0 w1 s0 c).
    apply IHl.
    intros.
    give_up.
    exact H0.
    apply (free_cachelets_v) in H3. subst. exact H1.
    exact H2.
    discriminate.
    intros; destruct (free_cachelets r k w0 F V C R).
    discriminate.
    discriminate.
  }
Admitted.

Lemma wf1_mlc_dealloc : forall L state k k' index psi psi' F V C R F' V' C' R' c,
  mlc_deallocation state k L = Some k' ->
  NatMap.find index k = Some psi ->
  NatMap.find index k' = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  (In c F -> CacheletMap.In c C) -> (In c F' -> CacheletMap.In c C').
Proof.
  intros L state.
  induction L.
  {
    intros.
    unfold mlc_deallocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    injection H; intros; subst k'.
    rewrite -> H0 in H1.
    injection H1; intros; subst psi psi'.
    injection H6; intros; subst F' V' C' R'.
    apply H4.
    exact H5.
    discriminate.
  }
  {
    intros.
    unfold mlc_deallocation in H.
    destruct state; destruct e.
    unfold recursive_mlc_deallocation in H.
    fold recursive_mlc_deallocation in H.
    case_eq (NatMap.find a k). intros.
    assert (A0 := H6). destruct (NatMap.find a k) in A0, H.
    case_eq (cachelet_deallocation r s0). intros.
    assert (A1 := H7). destruct (cachelet_deallocation r s0) in A1, H.
    injection A0; injection A1; intros; subst s0 s2; clear A0 A1.
    case_eq (eqb index a).
    {
      intros; apply cmp_to_eq in H8; subst a.
      rewrite -> H6 in H0.
      injection H0; intros; subst s.
      destruct s1.
      specialize (IHL (NatMap.add index (single_level_cache c0 v w s) k) k' index
      (single_level_cache c0 v w s) psi' c0 v w s F' V' C' R' c).
      apply IHL.
      unfold mlc_deallocation. exact H.
      apply NatMapFacts.add_eq_o. reflexivity.
      exact H1.
      reflexivity.
      exact H3.
      unfold cachelet_deallocation in H7.
      destruct psi.
      case_eq (NatMap.find r v0). intros.
      assert (A0 := H8). destruct (NatMap.find r v0) in A0, H7.
      injection A0; injection H2; intros; subst; clear A0.
      (* reason about cachelet_deallocation *)
      give_up.
      discriminate.
      intros; destruct (NatMap.find r v0).
      discriminate.
      discriminate.
      exact H5.
    }
    {
      intros; apply cmp_to_uneq in H8.
      specialize (IHL (NatMap.add a s1 k) k' index
      psi psi' F V C R F' V' C' R' c).
      apply IHL.
      unfold mlc_deallocation. exact H.
      rewrite <- H0. apply NatMapFacts.add_neq_o.
      apply not_eq_sym. exact H8.
      exact H1.
      exact H2.
      exact H3.
      exact H4.
      exact H5.
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
Admitted.

(* First Well-Formed Condition *)
Lemma wf1_preservation : forall sigma obs sigma' obs',
  wf1 sigma -> wf2 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf1 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf1 in *.
  intros obs' H WF2; intros.
  injection H1; intros; subst; clear H1.
  inversion H0.
  inversion H14; subst.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    specialize (H m mu rho p lambda c c0 v w s) as H_app.
    assert (In c c0 -> CacheletMap.In c w).
    apply H_app. reflexivity.
    apply NatMapFacts.find_mapsto_iff. exact H1.
    generalize H3.
    apply (wf1_mlc_read L m e' mu l0 D delta obs0 k lambda (single_level_cache c0 v w s)
    (single_level_cache F V C R) c0 v w s F V C R c).
    exact H30.
    exact H1.
    apply NatMapFacts.find_mapsto_iff in H2; exact H2.
    reflexivity.
    reflexivity.
    exact H4.
    apply (wf_mlc_read_none L m e' mu l0 D delta obs0 k lambda) in H1.
    apply NatMapFacts.find_mapsto_iff in H2.
    rewrite -> H2 in H1.
    discriminate.
    exact H30.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    specialize (H m mu rho p lambda c c0 v w s) as H_app.
    assert (In c c0 -> CacheletMap.In c w).
    apply H_app. reflexivity.
    apply NatMapFacts.find_mapsto_iff. exact H1.
    generalize H3.
    apply (wf1_mlc_alloc L r_bar_val e m k lambda (single_level_cache c0 v w s)
    (single_level_cache F V C R) c0 v w s F V C R c).
    exact H36.
    exact H1.
    apply NatMapFacts.find_mapsto_iff in H2; exact H2.
    reflexivity.
    reflexivity.
    exact H4.
    apply NatMapFacts.find_mapsto_iff in H2.
    generalize H3.
    assert (mlc_allocation r_bar_val e m L = Some k -> NatMap.find lambda m = None).
    auto.
    apply (wf_mlc_alloc_none L r_bar_val e m k lambda) in H4.
    intros.
    rewrite -> H2 in H4.
    discriminate.
    exact H36.
    exact H36.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    specialize (H m m0 rho p lambda c c0 v0 w s) as H_app.
    assert (In c c0 -> CacheletMap.In c w).
    apply H_app. reflexivity.
    apply NatMapFacts.find_mapsto_iff. exact H1.
    generalize H3.
    apply (wf1_mlc_write L m e' m0 l0 v D obs1 mu k lambda (single_level_cache c0 v0 w s)
    (single_level_cache F V C R) c0 v0 w s F V C R c).
    exact H30.
    exact H1.
    apply NatMapFacts.find_mapsto_iff in H2; exact H2.
    reflexivity.
    reflexivity.
    exact H4.
    apply (wf_mlc_write_none L m e' m0 l0 v D obs1 mu k lambda) in H1.
    apply NatMapFacts.find_mapsto_iff in H2.
    rewrite -> H2 in H1.
    discriminate.
    exact H30.
  - subst.
    unfold wf2 in WF2.
    specialize (WF2 m m0 rho p lambda F V C R c).
    (* requires wf2 preservation first *)
    give_up.
  - apply (H k mu rho p lambda c F V C R).
    auto.
    apply NatMapFacts.find_mapsto_iff. 
    apply NatMapFacts.find_mapsto_iff in H2.
    rewrite -> H2. reflexivity.
    exact H3.
  - apply (H k mu rho p lambda c F V C R).
    auto.
    apply NatMapFacts.find_mapsto_iff. 
    apply NatMapFacts.find_mapsto_iff in H2.
    rewrite -> H2. reflexivity.
    exact H3.
  - apply (H k mu rho p lambda c F V C R).
    auto.
    apply NatMapFacts.find_mapsto_iff. 
    apply NatMapFacts.find_mapsto_iff in H2.
    rewrite -> H2. reflexivity.
    exact H3.
  - apply (H k mu rho p lambda c F V C R).
    auto.
    apply NatMapFacts.find_mapsto_iff. 
    apply NatMapFacts.find_mapsto_iff in H2.
    rewrite -> H2. reflexivity.
    exact H3.
  - subst.
    apply (H k mu rho p lambda c F V C R).
    auto.
    apply NatMapFacts.find_mapsto_iff. 
    apply NatMapFacts.find_mapsto_iff in H2.
    rewrite -> H2. reflexivity.
    exact H3.
Admitted.

(* Second Well-Formed Condition *)
Lemma wf2_preservation : forall sigma obs sigma' obs',
  wf1 sigma -> wf2 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf2 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf2 in *.
  intros obs' WF1; intros.
  injection H1; intros; subst m1 m2 r0 p0.
  inversion H0.
  inversion H16.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    case_eq (V_range v e); intros.
    specialize (H m mu rho p lambda c0 v w s c e l1) as H_app.
    assert (In c l1 -> CacheletMap.In c w).
    apply H_app. reflexivity.
    exact H33. exact H5.
    apply (wf2_mlc_read L m e' mu l0 D delta obs0 k lambda (single_level_cache c0 v w s)
    (single_level_cache F V C R) c0 v w s F V C R c e l1 ranV).
    exact H32. exact H33. exact H2.
    reflexivity. reflexivity.
    exact H5. exact H3. exact H6. exact H4.
    assert (V_range V e = None).
    apply (wf2_mlc_read_none L m e' mu l0 D delta obs0 k lambda (single_level_cache c0 v w s)
    (single_level_cache F V C R) c0 v w s F V C R e).
    exact H32. exact H33. exact H2. reflexivity. reflexivity. exact H5.
    rewrite -> H6 in H3. discriminate.
    apply (wf_mlc_read_none L m e' mu l0 D delta obs0 k lambda) in H32.
    rewrite -> H32 in H2.
    discriminate. exact H33.
  - subst.
    unfold wf1 in WF1.
    (* requires wf1 preservation first *) 
    give_up.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    case_eq (V_range v0 e); intros.
    specialize (H m m0 rho p lambda c0 v0 w s c e l1) as H_app.
    assert (In c l1 -> CacheletMap.In c w).
    apply H_app. reflexivity.
    exact H33. exact H5.
    apply (wf2_mlc_write L m e' m0 l0 v D obs1 mu k lambda (single_level_cache c0 v0 w s)
    (single_level_cache F V C R) c0 v0 w s F V C R c e l1 ranV).
    exact H32. exact H33. exact H2.
    reflexivity. reflexivity.
    exact H5. exact H3. exact H6. exact H4.
    assert (V_range V e = None).
    apply (wf2_mlc_write_none L m e' m0 l0 v D obs1 mu k lambda (single_level_cache c0 v0 w s)
    (single_level_cache F V C R) c0 v0 w s F V C R).
    exact H32. exact H33. exact H2. reflexivity. reflexivity. exact H5.
    rewrite -> H6 in H3. discriminate.
    apply (wf_mlc_write_none L m e' m0 l0 v D obs1 mu k lambda) in H32.
    rewrite -> H32 in H2.
    discriminate. exact H33.
  - case_eq (NatMap.find lambda m); intros; subst.
    destruct s.
    case_eq (V_range v e); intros.
    specialize (H m m0 rho p lambda c0 v w s c e l0) as H_app.
    assert (In c l0 -> CacheletMap.In c w).
    apply H_app. reflexivity.
    exact H37. exact H5.
    apply (wf2_mlc_dealloc L (enclave_state_value (enclave_ID_active e_raw) mem) m k lambda
    (single_level_cache c0 v w s) (single_level_cache F V C R) c0 v w s F V C R c e l0 ranV).
    exact H33. exact H37. exact H2. reflexivity. reflexivity.
    exact H5. exact H3. exact H6. exact H4.
    apply (wf2_mlc_dealloc_none L (enclave_state_value (enclave_ID_active e_raw) mem) m k lambda
    (single_level_cache c0 v w s) (single_level_cache F V C R) c0 v w s F V C R e) in H5.
    apply V_range_in in H3.
    apply V_range_not_in in H5.
    unfold not in H5.
    apply H5 in H3.
    apply false_implies_anything. exact H3.
    exact H33. exact H37. exact H2. reflexivity. reflexivity.
    apply (wf_mlc_dealloc_none L (enclave_state_value (enclave_ID_active e_raw) mem) m k lambda) in H33.
    rewrite -> H2 in H33. discriminate.
    exact H37.
  - subst. apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3. exact H4.
  - subst. apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3. exact H4.
  - subst. apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3. exact H4.
  - subst. apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3. exact H4.
  - subst. apply (H k mu rho p lambda F V C R c e ranV).
    reflexivity. exact H2. exact H3. exact H4.
Admitted.