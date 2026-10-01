(* Additional proof scripts for VALIS formalisation. *)

Require Import Syntax.
Require Import Denotation.
Require Import Operational.
Require Import Provenance.
Require Import Theorems.
Require Import Coq.Logic.FunctionalExtensionality.

Import Denotation.VALIS.
Import Operational.VALIS.
Import Provenance.VALIS.

Module VALIS.

(* Example: prove a trivial property about lfp *)

Lemma lfp_monotone :
  forall R S,
    (forall t, R t = S t) ->
    lfp R R -> lfp S S.
Proof.
  intros R S Heq Hlfp.
  pose proof (functional_extensionality _ _ Heq) as Heqf.
  rewrite Heqf in Hlfp.
  exact Hlfp.
Qed.

(* Future proofs will go here. *)

End VALIS.
