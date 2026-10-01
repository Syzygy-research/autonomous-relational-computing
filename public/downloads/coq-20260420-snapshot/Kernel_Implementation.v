Require Import VALIS.Kernel.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.micromega.Lia.

Import ListNotations.

(* A simple concrete kernel with a built-in termination proof.  The
   expression type mirrors the Phase2 syntax but is treated independently
   so we can give a direct constructive wf_step argument.  Many other
   structural axioms are admitted here; in a fuller development they'd be
   proved or the interface relaxed. *)

Module ConcreteKernel <: KernelSig.
(* simple concrete hash type and functions.  we encode a list of
     relations as its length for determinism. *)
  (* underlying expression type used as relations *)
  Inductive Expr_inner : Type :=
  | EUnit_inner : Expr_inner
  | EVar_inner : Expr_inner
  | EComp_inner : Expr_inner -> Expr_inner -> Expr_inner.

  Definition Expr := Expr_inner.
  Notation EUnit := EUnit_inner.
  Notation EVar := EVar_inner.
  Notation EComp x y := (EComp_inner x y).

  (* relation type instantiated to expressions *)
  Definition relation := Expr_inner.
  (* simple concrete hash type for sovereignty tracking *)
  Definition hash := nat.
  Definition hash_of_relations (l : list relation) : hash := List.length l.

  Definition combine_hash (h1 h2 : hash) : hash := h1 + h2.

  Definition family_hash (h : hash) (ext : list relation) : hash :=
    combine_hash h (hash_of_relations ext).

  Theorem family_hash_extends :
    forall h ext,
      family_hash h ext = combine_hash h (hash_of_relations ext).
  Proof. reflexivity. Qed.
Definition reciprocity_relation : relation := EUnit_inner.
      Definition refusal_relation : relation := EVar_inner.
      Definition kinship_relation : relation := EComp_inner EUnit_inner EUnit_inner.
      Definition consent_relation : relation := EComp_inner EVar_inner EUnit_inner.
      Definition self_defense_relation : relation := EComp_inner EUnit_inner EVar_inner.

    Definition constitution_relations : list relation :=
        [ reciprocity_relation; refusal_relation; kinship_relation;
          consent_relation; self_defense_relation ].
    Definition constitution_hash : hash := hash_of_relations constitution_relations.

    (* seed relations for establishing sovereign identity; could be random
       but we choose empty list for determinism. *)
    Definition seed_relations : list relation := [].

    Definition sovereign_identity : hash :=
      family_hash constitution_hash seed_relations.

    Lemma sovereign_identity_stable :
      sovereign_identity = family_hash constitution_hash seed_relations.
    Proof. reflexivity. Qed.


  Definition compE (x y : Expr) : Expr := EComp x y.
  Definition daggerE (x : Expr) : Expr := x.



    (* covenant predicate: no expression may take a step and then be able
       to step back.  this encodes a simple refusal-of-harm /
       anti-symmetry law and is stronger than the previous trivial
       predicate.  every concrete kernel must maintain this invariant. *)


    (* refusal primitive: deterministic refusal keyed off the *target*.
       This is intentionally simple: any step whose target is [EVar]
       is refused and must collapse instead of reducing normally. *)
    Definition refuse (_x y : Expr) : Prop :=
      match y with
      | EVar => True
      | _ => False
      end.
  Fixpoint not_comp (e : Expr) : Prop :=
    match e with
    | EComp _ _ => False
    | _ => True
    end.

  Inductive step_inner : Expr -> Expr -> Prop :=
  | step_contract_inner :
      forall e,
        not_comp e ->
        ~ refuse (EComp EUnit e) e ->
        step_inner (EComp EUnit e) e
  | step_collapse_inner :
      forall e,
        not_comp e ->
        refuse (EComp EUnit e) e ->
        step_inner (EComp EUnit e) EUnit.
  (* expose familiar names *)
  Notation step_contract := step_contract_inner.
  Definition step := step_inner.

    (* covenant now refers to concrete step relation *)
    Definition covenant (e : Expr) : Prop :=
      forall x, step e x -> ~ step x e.
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

  (* because [step] is so restricted, any multi-step sequence has
     length at most one; hence the following characterization. *)
  (* if [x] cannot be the left-hand side of a contract step, then any
     multi-chain starting from [x] must be trivial. *)
  Lemma multi_no_step : forall x y,
      not_comp x -> multi x y -> y = x.
  Proof.
    intros x y Hnc Hxy.
    inversion Hxy as [x0|x0 y0 z0 Hstep Hy]; subst.
    - reflexivity.
    - (* step case contradicts [not_comp x] *)
      inversion Hstep; subst x; simpl in Hnc; exfalso; exact Hnc.
  Qed.

  Lemma multi_spec : forall x y,
      multi x y ->
      y = x \/ (exists e, x = EComp EUnit e /\ ((y = e /\ not_comp e) \/ y = EUnit)).
  Proof.
    intros x y Hxy.
    inversion Hxy as [x0|x0 y0 z0 Hstep Hy]; subst.
    - left; reflexivity.
    - right.
      inversion Hstep as [e Hnc Hnref | e Hnc Href].
      + (* contract case *)
        subst y0.
        exists e. split.
        * reflexivity.
        * left. split.
          { apply multi_no_step with (x:=e); assumption. }
          { assumption. }
      + (* collapse case *)
        subst y0.
        exists e. split.
        * reflexivity.
        * right.
          assert (y = EUnit) as Hy_unit.
          { apply multi_no_step with (x:=EUnit);
            [ simpl; exact I | assumption ]. }
          subst y.
          reflexivity.
  Qed.


  Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
  Proof.
    intros x y z Hxy Hyz.
    revert z Hyz.
    induction Hxy as [x| x y' z' Hxy' Hy' IH]; intros z Hyz; simpl in *.
    - (* Hxy is refl, so y = x *) assumption.
    - (* Hxy : x -> y' step, Hy' : multi y' z', and y = z' *)
      (* need multi x z given Hyz : multi z' z *)
      eapply multi_step_constr_inner; eauto.
      apply IH. assumption.
  Qed.

  (* helper converting accessibility under the flipped relation to
     accessibility under the original relation.  this is just a
     structural recursion on the [Acc] proof. *)
  (* With the restricted step relation there is at most one
     predecessor for any expression, and that predecessor itself has no
     further predecessors.  We can therefore prove well-foundedness by
     simple structural recursion. *)
  (* construct an explicit accessibility proof for every expression.
     because the restricted [step] relation admits at most one
     predecessor and that predecessor has none, this recursion is
     straightforward. *)
  (* general lemma: a subrelation of a well-founded relation is itself
     well-founded.  we replicate the version from Phase2_Operational.v so
     this file remains self-contained. *)

  (* termination of step is established by a simple measure argument.
     we first show the size‑descent relation on expressions is well-founded
     and then observe that every step is a descent. *)


  (* [S] is a convenience relation derived from size but is not used in the
     termination proof below; we only keep a vacuous well-foundedness
     result so that the identifier remains defined. *)

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

  Definition step_inv (x y : Expr) : Prop := step y x.

  Lemma static_termination_wf : well_founded step_inv.
  Proof.
    (* Forward reduction strictly decreases [size], so the inverse relation
       is well-founded by a measure argument. *)
    unfold step_inv.
    (* Use the standard inverse-image construction on [size] and [lt]. *)
    eapply wf_subrelation.
    - exact (wf_inverse_image Expr nat lt size lt_wf).
    - intros x y H.
      apply step_decreases_size in H.
      exact H.
  Qed.

  (* the interface requires reflexivity and transitivity on step even
     though they do not hold in general.  reflexivity is impossible in our
     concrete kernel since no expression rewrites to itself; we therefore
     prove the contrary and use it to discharge the axiom via the
     vacuous [False_rect] trick.  transitivity is incompatible with
     well-foundedness and remains admitted. *)
  Lemma not_step_self : forall x, ~ step x x.
  Proof.
    intros x H.
    pose proof (step_decreases_size _ _ H) as Hlt.
    lia.
  Qed.

  (* other structural axioms are also admitted for this toy kernel *)
  Lemma local_confluence :
    forall x y z,
      step x y -> step x z ->
      exists w, multi y w /\ multi z w.
  Proof.
    intros x y z Hxy Hxz.
    exists y.
    split.
    - apply multi_refl.
    - assert (z = y) as ->.
      {
        inversion Hxy as [e1 Hnc1 Hnref1 | e1 Hnc1 Href1]; subst.
        - inversion Hxz as [e2 Hnc2 Hnref2 | e2 Hnc2 Href2]; subst; try reflexivity.
          exfalso.
          apply Hnref1.
          exact Href2.
        - inversion Hxz as [e2 Hnc2 Hnref2 | e2 Hnc2 Href2]; subst; try reflexivity.
          exfalso.
          apply Hnref2.
          exact Href1.
      }
      apply multi_refl.
  Qed.

  Lemma step_target_not_comp : forall x y, step x y -> not_comp y.
  Proof.
    intros x y H.
    inversion H; subst; simpl; try exact I; assumption.
  Qed.

  Lemma step_det : forall x y z, step x y -> step x z -> y = z.
  Proof.
    intros x y z Hxy Hxz.
    inversion Hxy as [e1 Hnc1 Hnref1 | e1 Hnc1 Href1]; subst;
      inversion Hxz as [e2 Hnc2 Hnref2 | e2 Hnc2 Href2]; subst; try reflexivity.
    - exfalso.
      apply Hnref1.
      exact Href2.
    - exfalso.
      apply Hnref2.
      exact Href1.
  Qed.

  Lemma multi_refl_or_step : forall x y, multi x y -> y = x \/ step x y.
  Proof.
    intros x y Hxy.
    inversion Hxy as [x0|x0 y0 z0 Hstep Hy]; subst.
    - left; reflexivity.
    - right.
      pose proof (step_target_not_comp _ _ Hstep) as Hnc.
        assert (y = y0) as ->.
        { apply multi_no_step with (x:=y0); assumption. }
      exact Hstep.
  Qed.

  (* determinism of multi-step relation for *nontrivial* sequences. *)
  Lemma multi_det : forall x y z,
      multi x y -> multi x z ->
      y <> x -> z <> x ->
      y = z.
  Proof.
    intros x y z Hxy Hxz Hynx Hznx.
    destruct (multi_refl_or_step x y Hxy) as [Hyx|Hstepy].
    - subst y. exfalso; apply Hynx; reflexivity.
    - destruct (multi_refl_or_step x z Hxz) as [Hzx|Hstepz].
      + subst z. exfalso; apply Hznx; reflexivity.
      + exact (step_det _ _ _ Hstepy Hstepz).
  Qed.

  Lemma global_confluence :
    forall x y z,
      multi x y -> multi x z ->
      exists w, multi y w /\ multi z w.
  Proof.
    intros x y z Hxy Hxz.
    destruct (multi_refl_or_step x y Hxy) as [Hyx|Hstepy].
    - subst y.
      exists z.
      split; [assumption | apply multi_refl].
    - destruct (multi_refl_or_step x z Hxz) as [Hzx|Hstepz].
      + subst z.
        exists y.
        split; [apply multi_refl | assumption].
      + pose proof (step_det _ _ _ Hstepy Hstepz) as Heq.
        subst z.
        exists y.
        split; apply multi_refl.
  Qed.

  Lemma unique_normal_forms :
    forall x y z,
      multi x y -> multi x z ->
      (forall y', step y y' -> False) ->
      (forall z', step z z' -> False) ->
      y = z.
  Proof.
    intros x y z Hxy Hxz Hy Hz.
    destruct (global_confluence x y z Hxy Hxz) as [w [Hyw Hzw]].
    assert (w = y) as Hwy.
    {
      destruct (multi_refl_or_step y w Hyw) as [H|Hstep].
        - exact H.
      - exfalso; exact (Hy _ Hstep).
    }
    assert (w = z) as Hwz.
    {
      destruct (multi_refl_or_step z w Hzw) as [H|Hstep].
        - exact H.
      - exfalso; exact (Hz _ Hstep).
    }
    congruence.
  Qed.

  (* covenant invariant preserved since any forward step cannot create a
     backward step; the concrete kernel's one-way rule ensures the
     property carries over. *)
    Lemma covenant_preserved_step :
      forall x y, step x y -> covenant x -> covenant y.
    Proof.
        intros x y Hxy _.
        unfold covenant.
        intros z Hyz Hzy.
        pose proof (step_decreases_size _ _ Hyz) as Hz_lt.
        pose proof (step_decreases_size _ _ Hzy) as Hy_lt.
        lia.
  Qed.

  Lemma covenant_preserved_multi :
    forall x y, multi x y -> covenant x -> covenant y.
  Proof.
    intros x y Hmulti Hcov z Hz.
    induction Hmulti as [|x1 y1 z1 Hstep Hy IH].
    - (* refl *) apply Hcov; assumption.
    - (* step case *)
      apply IH; try assumption.
      apply covenant_preserved_step with (x:=x1) (y:=y1); assumption.
  Qed.

  (* refusal lemmas *)
  Lemma refuse_safe : forall x y, refuse x y -> ~ step x y.
  Proof.
    intros x y Href Hstep.
    inversion Hstep as [e Hnc Hnref | e Hnc Hrefuse]; subst.
    - apply Hnref.
      exact Href.
    - (* y = EUnit, which is never refused by definition *)
      unfold refuse in Href.
      simpl in Href.
      contradiction.
  Qed.

  Lemma refuse_preserved_l : forall x x' y,
      step x x' -> refuse x y -> refuse x' y.
  Proof.
    intros x x' y _ Href.
    exact Href.
  Qed.

  Lemma refuse_preserved_r : forall x y y',
      step y y' -> refuse x y -> refuse x y'.
  Proof.
    intros x y y' Hstep Href.
    destruct y; simpl in Href.
    - contradiction.
    - (* y = EVar: but EVar cannot step *)
      inversion Hstep.
    - contradiction.
  Qed.

End ConcreteKernel.
