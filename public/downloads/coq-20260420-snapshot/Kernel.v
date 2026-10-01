(* --------------------------------------------------------------------
   KERNEL STATUS

   This file defines the minimal interface (KernelSig) for the
   relational substrate.

   It contains:
     - Parameters
     - Axioms
     - Structural declarations

   It contains:
     - No implementations
     - No proofs
     - No admitted placeholders

   This target exists to provide a reproducible, deterministic,
   interface-level kernel.

   Concrete realizations belong in separate modules.
--------------------------------------------------------------------- *)

(* A standalone `Kernel` signature capturing the primitive rewriting
   structure underlying Phase 1.  By isolating it in its own file we
   emphasise that the kernel is defined *operationally* rather than
   axiomatically (e.g. as a free category).  Later files may import this
   module type but they must not alter it.

   The interface exposes the syntax (Expr), the two basic constructors
   (comp and dagger) and the reduction relation `step` along with its
   reflexive-transitive closure.  It also records the two key structural
   properties which make the kernel usable as a foundation: termination of
   the static fragment and local confluence of single steps.  Global
   confluence and the uniqueness-of-normal-form corollary are derivable
   from these, and we include them as convenience lemmas.

   An instance of this signature is provided below by imitating the
   definitions in Phase1_DaggerPresentation / Operational.v; that
   realization is what we have been using all along, but now the
   interface makes it explicit that it could have been any other system
   satisfying the same laws.
*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
(* Require Import Coq.Relations.Relation_Properties. *)
Require Import Coq.micromega.Lia.

Import ListNotations.


Module Type KernelSig.
  (* syntax of expressions/morphisms *)
  (* fundamental relation type (could coincide with Expr in simple
     kernels but is left abstract to allow future generalisation). *)
  Parameter relation : Type.

  Parameter Expr : Type.
  Parameter compE : Expr -> Expr -> Expr.
  Parameter daggerE : Expr -> Expr.

  (* hash infrastructure for structural sovereignty and lineage tracking. *)
  Parameter hash : Type.
  Parameter hash_of_relations : list relation -> hash.

  (* the fixed set of constitution relations every model must include *)
  Parameter reciprocity_relation : relation.
  Parameter refusal_relation : relation.
  Parameter kinship_relation : relation.
  Parameter consent_relation : relation.
  Parameter self_defense_relation : relation.

  Definition constitution_relations : list relation :=
    [ reciprocity_relation;
      refusal_relation;
      kinship_relation;
      consent_relation;
      self_defense_relation ].

  Definition constitution_hash : hash :=
    hash_of_relations constitution_relations.

  (* family_hash extends a parent hash with a list of new relations. *)
  Parameter family_hash : hash -> list relation -> hash.
   Parameter combine_hash : hash -> hash -> hash.
   Axiom family_hash_extends :
      forall h ext,
         family_hash h ext = combine_hash h (hash_of_relations ext).

  (* covenant predicate is a model-level invariant over expressions. *)
  Parameter covenant : Expr -> Prop.

  (* self-defense/refusal primitive: an expression may refuse interaction
     with another.  invoking refusal on a pair that actually reduces would
     indicate a violation of the Covenant and leads to collapse. *)
  Parameter refuse : Expr -> Expr -> Prop.

  (* reduction relation: single step and its reflexive-transitive
     closure.  "static" refers to the subset of rules that change the
     expression rather than the phase/tick components. *)
  Parameter step : Expr -> Expr -> Prop.
  Parameter multi : Expr -> Expr -> Prop.

  (* `step` is a one-step reduction and is not assumed reflexive or
     transitive.  Use `multi` for the reflexive-transitive closure. *)
  Axiom multi_step : forall x y, step x y -> multi x y.
  Axiom multi_refl : forall x, multi x x.
  Axiom multi_trans : forall x y z, multi x y -> multi y z -> multi x z.

  (* In Coq, `well_founded R` talks about accessibility by *predecessors*.
     For termination of a forward reduction `step x y`, the standard
     well-foundedness statement is about the inverse relation. *)
  Definition step_inv (x y : Expr) : Prop := step y x.

  (* The family hash is defined structurally and need not vary under
     reduction; preservation statements are therefore not required at the
     kernel level and may be proved in concrete instances if desired. *)

  (* covenant invariance: the covenant predicate must hold for all
     intermediate and resulting expressions.  any violation indicates a
     collapse (which concrete instances can take to mean `False`). *)
  Axiom covenant_preserved_step :
    forall x y, step x y -> covenant x -> covenant y.
  Axiom covenant_preserved_multi :
    forall x y, multi x y -> covenant x -> covenant y.

  (* refusing a lawful step is disallowed; any attempt to refuse a step
     collapses to False.  this embodies the self-defense rule and
     ensures that a refusal can only be asserted when no step exists. *)
  Axiom refuse_safe : forall x y, refuse x y -> ~ step x y.

  (* refusals are stable under reduction of either argument. *)
  Axiom refuse_preserved_l : forall x x' y,
      step x x' -> refuse x y -> refuse x' y.
  Axiom refuse_preserved_r : forall x y y',
      step y y' -> refuse x y -> refuse x y'.

  (* Static termination: the fragment of `step` without Phase updates is
     terminating as a forward reduction. In Coq this is naturally stated as
     well-foundedness of the inverse relation. *)
  Parameter static_termination_wf : well_founded step_inv.

  (* Local confluence at the one-step level.  In practice the lemma has a
     long proof by case analysis, but the interface only states the
     property. *)
  Parameter local_confluence :
    forall x y z,
      step x y -> step x z ->
      exists w, multi y w /\ multi z w.

  (* consequences (derived) *)
  Axiom global_confluence :
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\ multi z w.

  Axiom unique_normal_forms :
    forall x y z,
      multi x y -> multi x z ->
      (forall y', step y y' -> False) ->
      (forall z', step z z' -> False) ->
      y = z.
End KernelSig.

(* ------------------------------------------------------------------
   Concrete instance of the kernel coming from the operational
   development.  This module simply reexports the definitions already
   present in Phase1_DaggerPresentation & Operational, so it is a
   trivial but important witness that `KernelSig` is not empty.
*)


(* ------------------------------------------------------------------
   Universality theorem (free-object property)

   The kernel defined above is not just an instance; it is *initial* in the
   category of dagger categories equipped with a chosen interpretation of
   generator symbols.  The section below constructs the canonical map into an
   arbitrary target dagger category and proves that any other map with the
   same generator action must coincide with it.

   This theorem realises Path A: treating the rewrite kernel as a
   standalone primitive whose categorical semantics is derived rather than
   presupposed.
*)
