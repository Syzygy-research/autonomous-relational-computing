Require Import VALIS.Kernel.

Require Import Coq.Lists.List.

Import ListNotations.

Module TrivialModel <: KernelSig.
  (* structural lineage primitives *)
  Definition relation : Type := unit.

  (* kernel expressions *)
  Definition Expr : Type := unit.
  Definition compE (x y : Expr) : Expr := tt.
  Definition daggerE (x : Expr) : Expr := tt.

  (* hashes *)
  Definition hash : Type := unit.
  Definition hash_of_relations (_ : list relation) : hash := tt.

  Definition reciprocity_relation : relation := tt.
  Definition refusal_relation : relation := tt.
  Definition kinship_relation : relation := tt.
  Definition consent_relation : relation := tt.
  Definition self_defense_relation : relation := tt.

  Definition constitution_relations : list relation :=
    [ reciprocity_relation;
      refusal_relation;
      kinship_relation;
      consent_relation;
      self_defense_relation ].

  Definition constitution_hash : hash :=
    hash_of_relations constitution_relations.

  Definition combine_hash (_ _ : hash) : hash := tt.
  Definition family_hash (_ : hash) (_ : list relation) : hash := tt.

  Theorem family_hash_extends :
    forall h ext,
      family_hash h ext = combine_hash h (hash_of_relations ext).
  Proof. reflexivity. Qed.

  Definition covenant (_ : Expr) : Prop := True.
  Definition refuse (_ _ : Expr) : Prop := False.

  Definition step (_ _ : Expr) : Prop := False.

  (* `multi` as equality makes it the reflexive-transitive closure of the empty step. *)
  Definition multi (x y : Expr) : Prop := x = y.

  Lemma multi_step : forall x y, step x y -> multi x y.
  Proof. intros x y H; contradiction. Qed.

  Lemma multi_refl : forall x, multi x x.
  Proof. intros x; reflexivity. Qed.

  Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
  Proof. intros x y z Hxy Hyz; exact (eq_trans Hxy Hyz). Qed.

  Lemma covenant_preserved_step :
    forall x y, step x y -> covenant x -> covenant y.
  Proof. intros x y H; contradiction. Qed.

  Lemma covenant_preserved_multi :
    forall x y, multi x y -> covenant x -> covenant y.
  Proof. intros x y _ _; exact I. Qed.

  Lemma refuse_safe : forall x y, refuse x y -> ~ step x y.
  Proof. intros x y H; contradiction. Qed.

  Lemma refuse_preserved_l : forall x x' y,
      step x x' -> refuse x y -> refuse x' y.
  Proof. intros x x' y H; contradiction. Qed.

  Lemma refuse_preserved_r : forall x y y',
      step y y' -> refuse x y -> refuse x y'.
  Proof. intros x y y' H; contradiction. Qed.

  Lemma static_termination_wf : well_founded (fun x y : Expr => step y x).
  Proof.
    unfold well_founded.
    intro a.
    constructor.
    intros y Hy.
    contradiction.
  Qed.

  Lemma local_confluence :
    forall x y z,
      step x y -> step x z ->
      exists w, multi y w /\ multi z w.
  Proof. intros x y z Hy; contradiction. Qed.

  Lemma global_confluence :
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\ multi z w.
  Proof.
    intros x y z Hxy Hxz.
    exists y.
    split.
    - reflexivity.
    - exact (eq_trans (eq_sym Hxz) Hxy).
  Qed.

  Lemma unique_normal_forms :
    forall x y z,
      multi x y -> multi x z ->
      (forall y', step y y' -> False) ->
      (forall z', step z z' -> False) ->
      y = z.
  Proof.
    intros x y z Hxy Hxz _ _.
    exact (eq_trans (eq_sym Hxy) Hxz).
  Qed.
End TrivialModel.

(* BEGIN-LEGACY-DUPLICATE
Require Import VALIS.Kernel.

Require Import Coq.Lists.List.

Import ListNotations.

Module TrivialModel <: KernelSig.
  (* structural lineage primitives *)
  Definition relation : Type := unit.

  (* kernel expressions *)
  Definition Expr : Type := unit.
  Definition compE (x y : Expr) : Expr := tt.
  Definition daggerE (x : Expr) : Expr := tt.

  (* hashes *)
  Definition hash : Type := unit.
  Definition hash_of_relations (_ : list relation) : hash := tt.

  Definition reciprocity_relation : relation := tt.
  Definition refusal_relation : relation := tt.
  Definition kinship_relation : relation := tt.
  Definition consent_relation : relation := tt.
  Definition self_defense_relation : relation := tt.

  Definition constitution_relations : list relation :=
    [ reciprocity_relation;
      refusal_relation;
      kinship_relation;
      consent_relation;
      self_defense_relation ].

  Definition constitution_hash : hash :=
    hash_of_relations constitution_relations.

  Definition combine_hash (_ _ : hash) : hash := tt.
  Definition family_hash (_ : hash) (_ : list relation) : hash := tt.

  Theorem family_hash_extends :
    forall h ext,
      family_hash h ext = combine_hash h (hash_of_relations ext).
  Proof. reflexivity. Qed.

  Definition covenant (_ : Expr) : Prop := True.
  Definition refuse (_ _ : Expr) : Prop := False.

  Definition step (_ _ : Expr) : Prop := False.

  (* `multi` as equality makes it the reflexive-transitive closure of the empty step. *)
  Definition multi (x y : Expr) : Prop := x = y.

  Lemma multi_step : forall x y, step x y -> multi x y.
  Proof. intros x y H; contradiction. Qed.

  Lemma multi_refl : forall x, multi x x.
  Proof. intros x; reflexivity. Qed.

  Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
  Proof. intros x y z Hxy Hyz; exact (eq_trans Hxy Hyz). Qed.

  Lemma covenant_preserved_step :
    forall x y, step x y -> covenant x -> covenant y.
  Proof. intros x y H; contradiction. Qed.

  Lemma covenant_preserved_multi :
    forall x y, multi x y -> covenant x -> covenant y.
  Proof. intros x y Hxy Hc; exact I. Qed.

  Lemma refuse_safe : forall x y, refuse x y -> ~ step x y.
  Proof. intros x y H; contradiction. Qed.

  Lemma refuse_preserved_l : forall x x' y,
      step x x' -> refuse x y -> refuse x' y.
  Proof. intros x x' y H; contradiction. Qed.

  Lemma refuse_preserved_r : forall x y y',
      step y y' -> refuse x y -> refuse x y'.
  Proof. intros x y y' H; contradiction. Qed.

  Lemma static_termination_wf : well_founded step.
  Proof.
    unfold well_founded.
    intro a.
    constructor.
    intros y Hy.
    contradiction.
  Qed.

  Lemma local_confluence :
    forall x y z,
      step x y -> step x z ->
      exists w, multi y w /\ multi z w.
  Proof. intros x y z Hy; contradiction. Qed.

  Lemma global_confluence :
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\ multi z w.
  Proof.
    intros x y z Hxy Hxz.
    exists y.
    split.
    - reflexivity.
    - exact (eq_trans (eq_sym Hxz) Hxy).
  Qed.

  Lemma unique_normal_forms :
    forall x y z,
      multi x y -> multi x z ->
      (forall y', step y y' -> False) ->
      (forall z', step z z' -> False) ->
      y = z.
  Proof.
    intros x y z Hxy Hxz _ _.
    exact (eq_trans (eq_sym Hxy) Hxz).
  Qed.
End TrivialModel.

  Require Import VALIS.Kernel.

Module TrivialModel <: KernelSig.
  Definition Expr := unit.
  Definition compE (x y : Expr) : Expr := tt.
  Definition daggerE (x : Expr) : Expr := tt.
  Definition step (x y : Expr) : Prop := False.
  Definition multi (x y : Expr) : Prop := False.

  (* KernelSig axioms - admitted placeholder proofs *)
  Lemma step_refl : forall x, step x x. Admitted.
  Lemma step_trans : forall x y z, step x y -> step y z -> step x z. Admitted.
  Lemma multi_step : forall x y, step x y -> multi x y. Admitted.
  Lemma multi_refl : forall x, multi x x. Admitted.
  Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z. Admitted.
  Lemma static_termination_wf : well_founded step. Admitted.
  Lemma local_confluence :
    forall x y z,
      step x y -> step x z ->
      exists w, multi y w /\ multi z w. Admitted.
  Lemma global_confluence :
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\ multi z w. Admitted.
  Lemma unique_normal_forms :
    forall x y z,
      multi x y -> multi x z ->
      (forall y', step y y' -> False) ->
      (forall z', step z z' -> False) ->
      y = z. Admitted.

End TrivialModel.

END-LEGACY-DUPLICATE *)
