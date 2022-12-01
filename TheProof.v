From Coq Require Import Lia.
Require Import RuntimeDefinitions.
Require Import Semantics.
Require Import WellFormed.

Notation "'<<' sigma ';' obs '>>'" := (state_and_trace sigma obs).

Lemma runtime_state_unfold : forall k mu rho pi k' mu' rho' pi',
  runtime_state_value k' mu' rho' pi' = runtime_state_value k mu rho pi ->
  k = k' /\ mu = mu' /\ rho = rho' /\ pi = pi'.
Proof.
  intros.
  injection H.
  auto.
Qed.

Lemma lemmaA1 : forall sigma obs sigma' obs',
  well_formed sigma -> <<sigma; obs>> ==> <<sigma'; obs'>> -> well_formed sigma'.
Proof.
  intros.
  inversion H0.
  inversion H.
  {
    give_up.
  }
  {
    destruct sigma.
    destruct r1.
    inversion H.
    destruct well_formed.
    destruct sigma.
  }