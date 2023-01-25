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

Definition wf_c (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda F V C R,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.MapsTo lambda (single_level_cache F V C R) k) ->
  (forall w s, False <-> (CacheletMap.In (w, s) C)).

Definition wf1 (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda c F V C R,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.MapsTo lambda (single_level_cache F V C R) k) ->
  (In c F) -> (CacheletMap.In c C).

(*
Definition wf1_other (sigma: runtime_state): Prop :=
  forall k mu rho pi lambda c F V C R,
  (sigma = runtime_state_value k mu rho pi) ->
  (NatMap.find lambda k) = Some (single_level_cache F V C R) ->
  (In c F) -> (CacheletMap.In c C).
*)

(*
Lemma mlc_allocation_add : forall n e k lambda h_tree k0 k1 x y,
  (recursive_mlc_allocation n e k lambda h_tree) = Some k0 ->
  (recursive_mlc_allocation n e (NatMap.add x y k) lambda h_tree) = Some k1 ->
  (NatMap.add x y k0 = k1)
*)

Lemma wf1_alloc_c : forall n e psi psi' F V C R F' V' C' R',
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
  unfold recursive_cachelet_allocation in H; unfold cachelet_allocation in H.
  

  induction n.
  injection H; intros; subst; auto.
  fold recursive_cachelet_allocation in *.
  case_eq (way_first_allocation F); intros; destruct (way_first_allocation F).
  destruct c0.
  case_eq (NatMap.find s R); intros; destruct (NatMap.find s R).
  case_eq (NatMap.find e V); intros; destruct (NatMap.find e V).
  case_eq (NatMap.find s r0); intros; destruct (NatMap.find s r0).
  injection H0; injection H1; injection H2; injection H3; intros; subst p r w1 c; clear H0 H1 H2.
  apply IHn.
  rewrite <- H.
  (* this is not true :(  *)

  give_up.
  discriminate.
  discriminate.

  give_up.
  discriminate.
  discriminate.

  give_up.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Admitted.

Lemma wf1_alloc_f : forall n e psi psi' F V C R F' V' C' R' c,
  cachelet_allocation n e psi = Some psi' ->
  psi = single_level_cache F V C R ->
  psi' = single_level_cache F' V' C' R' ->
  In c F' -> In c F.
Proof.
  intros.
  unfold cachelet_allocation in H.
  case_eq psi; intros; destruct psi.
  injection H0; intros; subst.
  injection H3; intros; subst c0 v w s; clear H0 H3.
  
  induction n.
  unfold recursive_cachelet_allocation in H.
  injection H; intros; subst; exact H2.
  unfold recursive_cachelet_allocation in H.
  case_eq (way_first_allocation F); intros.
  assert (H1 := H0).
  unfold way_first_allocation in H1.
  unfold cachelet_min_way_ID in H1.
  destruct (way_first_allocation F).
  destruct c1.
  case_eq (NatMap.find s R); intros; destruct (NatMap.find s R).
  case_eq (NatMap.find e V); intros; destruct (NatMap.find e V).
  case_eq (NatMap.find s r0); intros; destruct (NatMap.find s r0).
  injection H0; injection H3; injection H4; injection H5; intros; subst.
  apply IHn.
  rewrite <- H; fold recursive_cachelet_allocation.
  (* this is not true *)

  give_up.
  discriminate.
  discriminate.
  injection H3; injection H4; intros; subst.
  give_up.
  discriminate.
  discriminate.
  give_up.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  destruct (way_first_allocation F).
  discriminate.
  discriminate.
Admitted.

Lemma unfold_lemma : forall s e l F V C R ci wscv delta,
  cc_unfold s e l = cc_unfold_valid F V C R ci wscv delta.
Proof.
  intros.
  unfold cc_unfold.
  case_eq s; intros.
  case_eq l; intros.
  case_eq (block_to_set_and_tag b s0); intros.
  unfold block_to_set_and_tag in H1.
  injection H1; intros.
  case_eq (find_way_ID_with_cache_tag e s1 c0 v w); intros.
  case_eq (CacheletMap.find (w0, s1) w); intros.
  give_up.
Admitted.
  

Lemma wf1_preservation : forall sigma obs sigma' obs',
  wf1 sigma -> <<sigma; obs>> ===> <<sigma'; obs'>> -> wf1 sigma'.
Proof.
  destruct sigma; destruct sigma'.
  unfold wf1 in *.
  intros.
  inversion H0.
  inversion H15.
  - unfold mlc_read in H33; unfold recursive_mlc_read in H33.
    destruct (get_hierarchy_tree_height H18).
    discriminate.
    case_eq lambda0; intros; subst.
    case_eq (NatMap.find p2 m); intros; destruct (NatMap.find p2 m) in H33.
    case_eq (cc_hit_read s0 e' l0); intros; destruct (cc_hit_read s0 e' l0) in H33.
    unfold cc_hit_read in H5.
    case_eq (cc_unfold s0 e' l0); intros.
    give_up.

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
    give_up. give_up. give_up. give_up. give_up. give_up. give_up. give_up.
  - unfold mlc_allocation in H39; destruct e; unfold recursive_mlc_allocation in H39.
    destruct e.
    induction r_bar_val.
    apply (H m m0 r p lambda c F V C R).
    auto. injection H39; injection H1; intros; rewrite -> H44;
    rewrite -> H43; exact H2. exact H3.
    subst. destruct (NatMap.find lambda0 m). destruct (cachelet_allocation a r4 s).
    destruct (get_cache_hierarchy_parent (cache_node lambda0) H18).
    destruct c0. subst.
    (* case_eq (NatMap.mem lambda0 m). intros. *)

    give_up.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
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
