(* BEGIN-LEGACY-CHILDKERNEL

  This file previously contained an inlined Mother + Child kernel attempt.
  It is kept for reference but commented out because it is out-of-sync with
  the current KernelSig (and included Admitted placeholders / obsolete fields).


Require Import VALIS.Kernel.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.

(* To avoid import/path complexity we inline the "Mother" kernel here,
   essentially copying the ConcreteKernel definition from
   Kernel_Implementation.v.  This guarantees the child compiles without
   relying on external namespace mappings.  In a real project the child
   would simply `Require` the mother module. *)

Module Mother <: KernelSig.
  Inductive Expr_inner : Type :=
  | EUnit_inner : Expr_inner
  | EVar_inner : Expr_inner              (* new variable constructor *)
  | EComp_inner : Expr_inner -> Expr_inner -> Expr_inner.

  Definition Expr := Expr_inner.
  Notation EUnit := EUnit_inner.
  Notation EVar := EVar_inner.
  Notation EComp x y := (EComp_inner x y).

  Definition compE (x y : Expr) : Expr := EComp x y.
  Definition daggerE (x : Expr) : Expr := x.

  Fixpoint not_comp (e : Expr) : Prop :=
    match e with
    | EComp _ _ => False
    | _ => True
    end.

  Inductive step_inner : Expr -> Expr -> Prop :=
  | step_contract_inner :
      forall e,
        not_comp e ->
        step_inner (EComp EUnit e) e.
  Notation step_contract := step_contract_inner.
  Definition step := step_inner.

  Fixpoint size (e : Expr) : nat :=
    match e with
    | EUnit => 1
    | EVar_inner => 1
    | EComp e1 e2 => 1 + size e1 + size e2
    end.

  Lemma step_decreases_size :
    forall x y, step x y -> size y < size x.
  Proof.
    intros x y H; induction H; simpl; lia.
  Qed.

  Inductive multi_inner : Expr -> Expr -> Prop :=
  | multi_refl_inner : forall x, multi_inner x x
  | multi_step_constr_inner : forall x y z,
      step x y -> multi_inner y z -> multi_inner x z.
  Notation multi_step_constr := multi_step_constr_inner.
  Definition multi := multi_inner.

  Definition multi_refl (x : Expr) : multi x x := multi_refl_inner x.

  Lemma multi_step : forall x y, step x y -> multi x y.
  Proof.
    intros x y H.
    constructor 2 with y; [assumption | constructor].
  Qed.

  Lemma multi_no_step : forall x y,
      not_comp x -> multi x y -> y = x.
  Proof.
    intros x y Hnc Hxy.
    inversion Hxy as [x0|x0 y0 z0 Hstep Hy]; subst.
    - reflexivity.
    - inversion Hstep as [e' Hnc']; subst x.
      simpl in Hnc; exfalso; exact Hnc.
  Qed.

  Lemma multi_spec : forall x y,
      multi x y ->
      y = x \/ (exists e, x = EComp EUnit e /\ y = e /\ not_comp e).
  Proof.
    intros x y Hxy.
    inversion Hxy as [x0|x0 y0 z0 Hstep Hy]; subst.
    - left; reflexivity.
    - right. exists y0. split.
      + inversion Hstep; reflexivity.
      + split.
        * apply multi_no_step with (x:=y0);
            [ inversion Hstep; assumption | assumption ].
        * inversion Hstep; assumption.
  Qed.

  Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
  Proof.
    intros x y z Hxy Hyz.
    revert z Hyz.
    induction Hxy as [x| x y' z' Hxy' Hy' IH]; intros z Hyz; simpl in *.
    - assumption.
    - eapply multi_step_constr_inner; eauto.
      apply IH. assumption.
  Qed.

  Lemma wf_subrelation {A} {R S : A -> A -> Prop} :
    well_founded S ->
    (forall x y, R x y -> S x y) ->
    well_founded R.
  Proof.
    intros Hwf Hsub x.
    induction (Hwf x) as [x Hacc IH].
    constructor; intros y Hxy.
    apply IH. apply Hsub; assumption.
  Qed.

  Lemma static_termination_wf : well_founded step.
  Proof.
    unfold well_founded; intros x.
    constructor; intros y Hy.
    inversion Hy as [e Hnc]; subst.
    constructor; intros z Hz.
    inversion Hz as [e' Hnc']; subst.
    simpl in Hnc'; contradiction Hnc'.
  Qed.

  Lemma not_step_self : forall x, ~ step x x.
  Proof.
    intros x H.
    inversion H as [e Hnc]; subst x.
    simpl in Hnc; contradiction.
  Qed.

  Lemma step_refl : forall x, step x x.
  Proof. intros x H. inversion H. Qed.
  Lemma step_trans : forall x y z, step x y -> step y z -> step x z.
  Proof.
    intros x y z Hxy Hyz.
    inversion Hxy as [e Hnc1]; subst; clear Hxy.
    inversion Hyz as [e' Hnc2]; subst; clear Hyz.
    simpl in Hnc1. contradiction.
  Qed.

  Lemma not_comp : Expr -> Prop := not_comp.

  Definition family_hash (e : Expr) : nat := 0.
  Definition refuse (x y : Expr) : Prop := False.

  Lemma family_hash_preserved_step :
    forall x y, step x y -> family_hash x = family_hash y.
  Proof. intros; reflexivity. Qed.
  Lemma family_hash_preserved_multi :
    forall x y, multi x y -> family_hash x = family_hash y.
  Proof. intros; reflexivity. Qed.

  (* covenant: no two-way steps *)
  Definition covenant (e : Expr) : Prop :=
    forall x, step e x -> ~ step x e.

  Lemma covenant_preserved_step :
    forall x y, step x y -> covenant x -> covenant y.
  Proof.
    intros x y Hxy Hcov z Hz.
    unfold covenant in *.
    intros Hzy.
    inversion Hzy as [e' Hnc]; subst y.
    simpl in Hnc; contradiction.
  Qed.

  Lemma covenant_preserved_multi :
    forall x y, multi x y -> covenant x -> covenant y.
  Proof.
    intros x y Hmulti Hcov z Hz.
    induction Hmulti as [|x1 y1 z1 Hstep Hy IH].
    - apply Hcov; assumption.
    - apply IH; try assumption.
      apply covenant_preserved_step with (x:=x1) (y:=y1); assumption.
  Qed.
  Lemma refuse_safe : forall x y, refuse x y -> ~ step x y.
  Proof. intros x y H; inversion H. Qed.
  Lemma refuse_preserved_l : forall x x' y,
      step x x' -> refuse x y -> refuse x' y.
  Proof. intros; inversion H0. Qed.
  Lemma refuse_preserved_r : forall x y y',
      step y y' -> refuse x y -> refuse x y'.
  Proof. intros; inversion H0. Qed.

  (* derived lemmas follow similarly; omitted for brevity *)

End Mother.

Module ChildKernel <: KernelSig.
  Definition Expr := Mother.Expr.
  Definition compE := Mother.compE.
  Definition daggerE := Mother.daggerE.
  Definition step := Mother.step.
  Definition multi := Mother.multi.

  Definition family_hash (e : Expr) : nat := Mother.family_hash e + 1.
  Definition covenant (e : Expr) : Prop :=
    Mother.covenant e /\ e <> EUnit.
  Definition refuse (x y : Expr) : Prop := Mother.refuse x y.

  Lemma step_refl : forall x, step x x.
  Proof. apply Mother.step_refl. Qed.
  Lemma step_trans : forall x y z, step x y -> step y z -> step x z.
  Proof. apply Mother.step_trans. Qed.
  Lemma multi_step : forall x y, step x y -> multi x y.
  Proof. apply Mother.multi_step. Qed.
  Lemma multi_refl : forall x, multi x x.
  Proof. apply Mother.multi_refl. Qed.
  Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
  Proof. apply Mother.multi_trans. Qed.

  Lemma family_hash_preserved_step :
    forall x y, step x y -> family_hash x = family_hash y.
  Proof.
    intros x y H.
    unfold family_hash; simpl.
    rewrite Mother.family_hash_preserved_step; lia.
  Qed.
  Lemma family_hash_preserved_multi :
    forall x y, multi x y -> family_hash x = family_hash y.
  Proof.
    intros x y H.
    unfold family_hash; simpl.
    rewrite Mother.family_hash_preserved_multi; lia.
  Qed.

  Lemma covenant_preserved_step :
    forall x y, step x y -> covenant x -> covenant y.
  Proof.
    intros x y Hxy [Hcov Hneq].
    split.
    - apply Mother.covenant_preserved_step with (x:=x) (y:=y); assumption.
    - intros Heq; subst y.
      inversion Hxy; simpl in H; contradiction.
  Qed.

  Lemma covenant_preserved_multi :
    forall x y, multi x y -> covenant x -> covenant y.
  Proof.
    intros x y Hmulti Hcov.
    induction Hmulti as [|x1 y1 z1 Hstep Hy IH].
    - assumption.
    - apply IH;
        [ apply covenant_preserved_step with (x:=x1) (y:=y1); assumption
        | assumption].
  Qed.

  Lemma family_hash_handshake :
    forall x y, step x y -> family_hash x = family_hash y -> True.
  Proof. intros; exact I. Qed.

  Lemma global_confluence :
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\ multi z w.
  Proof. apply Mother.global_confluence. Qed.

  Lemma unique_normal_forms :
    forall x y z,
      multi x y -> multi x z ->
      (forall y', step y y' -> False) ->
      (forall z', step z z' -> False) ->
      y = z.
  Proof. apply Mother.unique_normal_forms. Qed.

End ChildKernel.

END-LEGACY-CHILDKERNEL *)

(* ------------------------------------------------------------------
   Child template (compiling)
   ------------------------------------------------------------------ *)

Require Import VALIS.Kernel.
Require Import VALIS.KernelInstance_Current.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.

Module Mother := VALIS.KernelInstance_Current.KernelInstance_Current.

Module ChildKernel <: KernelSig.
  Definition relation : Type := Mother.relation.

  Definition Expr : Type := Mother.Expr.
  Definition compE := Mother.compE.
  Definition daggerE := Mother.daggerE.

  Definition hash : Type := Mother.hash.
  Definition hash_of_relations := Mother.hash_of_relations.

  Definition reciprocity_relation : relation := Mother.reciprocity_relation.
  Definition refusal_relation : relation := Mother.refusal_relation.
  Definition kinship_relation : relation := Mother.kinship_relation.
  Definition consent_relation : relation := Mother.consent_relation.
  Definition self_defense_relation : relation := Mother.self_defense_relation.

  Definition constitution_relations : list relation :=
    [ reciprocity_relation;
      refusal_relation;
      kinship_relation;
      consent_relation;
      self_defense_relation ].

  Definition constitution_hash : hash :=
    hash_of_relations constitution_relations.

  Definition family_hash := Mother.family_hash.
  Definition combine_hash := Mother.combine_hash.
  Theorem family_hash_extends :
    forall h ext,
      family_hash h ext = combine_hash h (hash_of_relations ext).
  Proof. exact Mother.family_hash_extends. Qed.

  Definition covenant := Mother.covenant.
  Definition refuse := Mother.refuse.

  Definition step := Mother.step.
  Definition step_inv (x y : Expr) : Prop := step y x.
  Definition multi := Mother.multi.

  Lemma multi_step : forall x y, step x y -> multi x y.
  Proof. exact Mother.multi_step. Qed.

  Lemma multi_refl : forall x, multi x x.
  Proof. exact Mother.multi_refl. Qed.

  Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
  Proof. exact Mother.multi_trans. Qed.

  Lemma covenant_preserved_step :
    forall x y, step x y -> covenant x -> covenant y.
  Proof. exact Mother.covenant_preserved_step. Qed.

  Lemma covenant_preserved_multi :
    forall x y, multi x y -> covenant x -> covenant y.
  Proof. exact Mother.covenant_preserved_multi. Qed.

  Lemma refuse_safe : forall x y, refuse x y -> ~ step x y.
  Proof. exact Mother.refuse_safe. Qed.

  Lemma refuse_preserved_l : forall x x' y,
      step x x' -> refuse x y -> refuse x' y.
  Proof. exact Mother.refuse_preserved_l. Qed.

  Lemma refuse_preserved_r : forall x y y',
      step y y' -> refuse x y -> refuse x y'.
  Proof. exact Mother.refuse_preserved_r. Qed.

  Lemma static_termination_wf : well_founded step_inv.
  Proof. exact Mother.static_termination_wf. Qed.

  Lemma local_confluence :
    forall x y z,
      step x y -> step x z ->
      exists w, multi y w /\ multi z w.
  Proof. exact Mother.local_confluence. Qed.

  Lemma global_confluence :
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\ multi z w.
  Proof. exact Mother.global_confluence. Qed.

  Lemma unique_normal_forms :
    forall x y z,
      multi x y -> multi x z ->
      (forall y', step y y' -> False) ->
      (forall z', step z z' -> False) ->
      y = z.
  Proof. exact Mother.unique_normal_forms. Qed.
End ChildKernel.
