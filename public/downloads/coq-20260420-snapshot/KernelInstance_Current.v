Require Import Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Strings.String.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.micromega.Lia.

Require Import VALIS.Kernel.
Require Import VALIS.Syntax.
Require Import VALIS.Operational_StaticFragment.
Require Import VALIS.Operational_StaticNormalize.

Import ListNotations.
Local Open Scope string_scope.

Module KernelInstance_Current <: KernelSig.
  Definition relation : Type := RelationAtom.

  (* For the sealed Phase-1 instance on main, we take expressions to be
     finite lists of relation-atoms. The operational kernel is the deterministic
     static-normalization step over these lists (see Operational_StaticNormalize). *)
  Definition Expr : Type := list relation.

  Definition compE (x y : Expr) : Expr := List.app x y.

  Definition dagger_atom (a : relation) : relation :=
    {| id := id a;
       source := target a;
       target := source a;
       strength := strength a;
       phase := phase a;
       shear := shear a;
       canonical := canonical a |}.

  Definition daggerE (x : Expr) : Expr := List.map dagger_atom x.

  (* ------------------------------------------------------------------ *)
  (* Hash + constitution scaffolding (kept deterministic and minimal).    *)
  (* ------------------------------------------------------------------ *)

  Definition hash : Type := nat.

  Definition hash_of_relations (l : list relation) : hash := List.length l.

  Definition mk_constitution_atom (name : RelId) : relation :=
    {| id := name;
       source := "";
       target := "";
       strength := 0%R;
       phase := 0%R;
       shear := (0%R, 0%R);
       canonical := true |}.

  Definition reciprocity_relation : relation := mk_constitution_atom "reciprocity".
  Definition refusal_relation : relation := mk_constitution_atom "refusal".
  Definition kinship_relation : relation := mk_constitution_atom "kinship".
  Definition consent_relation : relation := mk_constitution_atom "consent".
  Definition self_defense_relation : relation := mk_constitution_atom "self_defense".

  Definition constitution_relations : list relation :=
    [ reciprocity_relation;
      refusal_relation;
      kinship_relation;
      consent_relation;
      self_defense_relation ].

  Definition constitution_hash : hash :=
    hash_of_relations constitution_relations.

  Definition combine_hash (h1 h2 : hash) : hash := h1 + h2.

  Definition family_hash (h : hash) (ext : list relation) : hash :=
    combine_hash h (hash_of_relations ext).

  Theorem family_hash_extends :
    forall h ext,
      family_hash h ext = combine_hash h (hash_of_relations ext).
  Proof. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (* Covenant / refusal are intentionally trivial at the Phase-1 layer.  *)
  (* ------------------------------------------------------------------ *)

  Definition covenant (_ : Expr) : Prop := True.
  Definition refuse (_ _ : Expr) : Prop := False.

  (* ------------------------------------------------------------------ *)
  (* Deterministic Phase-1 kernel step (static normalization).           *)
  (* ------------------------------------------------------------------ *)

  Definition step (x y : Expr) : Prop :=
    Operational_StaticNormalize.det_step_list x = Some y.

  Definition step_inv (x y : Expr) : Prop := step y x.

  (* 1n reflexive-transitive closure, convenient for deterministic proofs.
     KernelSig requires `multi` to be a plain constant, so we define an
     inductive relation and then alias it. *)
  Inductive multi_rel : Expr -> Expr -> Prop :=
  | multi_rel_refl : forall x, multi_rel x x
  | multi_rel_cons : forall x y z, step x y -> multi_rel y z -> multi_rel x z.

  Definition multi : Expr -> Expr -> Prop := multi_rel.

  Lemma multi_step : forall x y, step x y -> multi x y.
  Proof.
    intros x y H.
    unfold multi.
    eapply multi_rel_cons; [exact H | apply multi_rel_refl].
  Qed.

  Lemma multi_refl : forall x, multi x x.
  Proof. intro x; unfold multi; exact (multi_rel_refl x). Qed.

  Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
  Proof.
    intros x y z Hxy Hyz.
    induction Hxy.
    - exact Hyz.
    - unfold multi in *.
      eapply multi_rel_cons; eauto.
  Qed.

  (* covenant invariance: trivial at this layer *)
  Lemma covenant_preserved_step :
    forall x y, step x y -> covenant x -> covenant y.
  Proof. intros x y _ _; exact I. Qed.

  Lemma covenant_preserved_multi :
    forall x y, multi x y -> covenant x -> covenant y.
  Proof. intros x y _ _; exact I. Qed.

  Lemma refuse_safe : forall x y, refuse x y -> ~ step x y.
  Proof. intros x y H; contradiction. Qed.

  Lemma refuse_preserved_l : forall x x' y,
      step x x' -> refuse x y -> refuse x' y.
  Proof. intros x x' y _ H; contradiction. Qed.

  Lemma refuse_preserved_r : forall x y y',
      step y y' -> refuse x y -> refuse x y'.
  Proof. intros x y y' _ H; contradiction. Qed.

  (* ------------------------------------------------------------------ *)
  (* Termination (static fragment).                                      *)
  (* ------------------------------------------------------------------ *)

  Lemma step_det : forall x y z,
      step x y -> step x z -> y = z.
  Proof.
    intros x y z Hy Hz.
    unfold step in *.
    rewrite Hy in Hz.
    inversion Hz.
    reflexivity.
  Qed.

  Lemma step_decreases_measure : forall x y,
      step x y ->
      Operational_StaticFragment.lex_natpair
        (Operational_StaticFragment.measure_list y)
        (Operational_StaticFragment.measure_list x).
  Proof.
    intros x y Hstep.
    unfold step in Hstep.
    pose proof
      (Operational_StaticNormalize.det_step_list_sound
         x y ([] : list (RelId * R)) 0 Hstep)
      as Hstatic.
    pose proof
      (Operational_StaticFragment.step_static_decreases_measure _ _ Hstatic)
      as Hdec.
    cbn in Hdec.
    exact Hdec.
  Qed.

  Definition measured (x y : Expr) : Prop :=
    Operational_StaticFragment.lex_natpair
      (Operational_StaticFragment.measure_list x)
      (Operational_StaticFragment.measure_list y).

  Lemma measured_wf : well_founded measured.
  Proof.
    unfold measured.
    exact
      (wf_inverse_image
         Expr (nat * nat)
         Operational_StaticFragment.lex_natpair
         Operational_StaticFragment.measure_list
         Operational_StaticFragment.wf_lex_natpair).
  Qed.

  Lemma static_termination_wf : well_founded step_inv.
  Proof.
    (* step_inv x y means step y x, and each forward step strictly decreases
       the lexicographic measure on lists. *)
    eapply Operational_StaticFragment.wf_subrelation.
    - exact measured_wf.
    - intros x y Hinv.
      unfold measured.
      unfold step_inv in Hinv.
      (* Hinv : step y x *)
      exact (step_decreases_measure y x Hinv).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Confluence + unique normal forms (deterministic kernel).            *)
  (* ------------------------------------------------------------------ *)

  Lemma local_confluence :
    forall x y z,
      step x y -> step x z ->
      exists w, multi y w /\ multi z w.
  Proof.
    intros x y z Hy Hz.
    assert (y = z) as -> by (eapply step_det; eauto).
    exists z.
    split; apply multi_refl.
  Qed.

  Theorem global_confluence :
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\ multi z w.
  Proof.
    intros x y z Hxy.
    revert z.
    induction Hxy as [x|x x1 y1 Hstep Hmulti IH]; intros z Hxz.
    - exists z.
      split; [exact Hxz | apply multi_refl].
    - inversion Hxz as [x0|x0 z1 z2 Hstep2 Hmulti2]; subst.
      + exists y1.
        split; [apply multi_refl | unfold multi; eapply multi_rel_cons; eauto].
      + assert (z1 = x1) as -> by (eapply step_det; eauto).
        destruct (IH z Hmulti2) as [w [Hyw Hzw]].
        exists w.
        split; assumption.
  Qed.

  Lemma normal_stuck : forall x y,
      (forall y', step x y' -> False) ->
      multi x y ->
      x = y.
  Proof.
    intros x y Hnormal Hxy.
    induction Hxy.
    - reflexivity.
    - exfalso. exact (Hnormal _ H).
  Qed.

  Theorem unique_normal_forms :
    forall x y z,
      multi x y -> multi x z ->
      (forall y', step y y' -> False) ->
      (forall z', step z z' -> False) ->
      y = z.
  Proof.
    intros x y z Hxy Hxz Hyn Hzn.
    destruct (global_confluence x y z Hxy Hxz) as [w [Hyw Hzw]].
    pose proof (normal_stuck y w Hyn Hyw) as ->.
    pose proof (normal_stuck z w Hzn Hzw) as ->.
    reflexivity.
  Qed.

End KernelInstance_Current.
