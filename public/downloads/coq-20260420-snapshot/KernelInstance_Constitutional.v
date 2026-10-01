Require Import Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Strings.String.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.

Require Import VALIS.Kernel.
Require Import VALIS.Syntax.
Require Import VALIS.Operational.
Require Import VALIS.Operational_StaticFragment.
Require Import VALIS.Operational_StaticNormalize.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope R_scope.

(*
  A second sealed kernel instance whose covenant/refusal hooks are non-trivial.

  Design:
  - Expressions are lists of relation-atoms.
  - The "constitution" is enforced as a fixed prefix of 5 atoms that must be
    present in any covenant-satisfying expression.
  - The kernel step rewrites ONLY the payload suffix (after the constitution
    prefix) using the deterministic strategy det_step_list.
  - The covenant constrains the payload atoms (canonical orientation + bounded
    strength). If the next deterministic raw step would violate the covenant,
    the step is refused.
*)

Module KernelInstance_Constitutional <: KernelSig.
  Module Op := VALIS.Operational.VALIS.
  Module SF := Operational_StaticFragment.

  Definition relation : Type := RelationAtom.

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
  (* Hash scaffolding (deterministic + minimal).                          *)
  (* ------------------------------------------------------------------ *)

  Definition hash : Type := nat.

  Definition hash_of_relations (l : list relation) : hash := List.length l.

  Definition combine_hash (h1 h2 : hash) : hash := (h1 + h2)%nat.

  Definition family_hash (h : hash) (ext : list relation) : hash :=
    combine_hash h (hash_of_relations ext).

  Theorem family_hash_extends :
    forall h ext,
      family_hash h ext = combine_hash h (hash_of_relations ext).
  Proof. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (* Constitution atoms (fixed prefix).                                   *)
  (* ------------------------------------------------------------------ *)

  Definition mk_constitution_atom (name : RelId) : relation :=
    {| id := name;
       source := "";
       target := "";
       strength := 0;
       phase := 0;
       shear := (0, 0);
       canonical := true |}.

  Definition reciprocity_relation : relation := mk_constitution_atom "reciprocity".
  Definition refusal_relation : relation := mk_constitution_atom "refusal".
  Definition kinship_relation : relation := mk_constitution_atom "kinship".
  Definition consent_relation : relation := mk_constitution_atom "consent".
  Definition self_defense_relation : relation := mk_constitution_atom "self_defense".

  (* Must definitionally match KernelSig.constitution_relations. *)
  Definition constitution_relations : list relation :=
    [ reciprocity_relation;
      refusal_relation;
      kinship_relation;
      consent_relation;
      self_defense_relation ].

  (* Must definitionally match KernelSig.constitution_hash. *)
  Definition constitution_hash : hash :=
    hash_of_relations constitution_relations.

  Definition constitution_ids : list RelId :=
    [ "reciprocity";
      "refusal";
      "kinship";
      "consent";
      "self_defense" ].

  (* ------------------------------------------------------------------ *)
  (* Covenant (enforced, non-trivial).                                    *)
  (* ------------------------------------------------------------------ *)

  Definition strength_ok (a : relation) : Prop :=
    0 <= strength a /\ strength a <= 1.

  Definition id_ok (a : relation) : Prop :=
    ~ In (id a) constitution_ids.

  Definition payload_ok (a : relation) : Prop :=
    canonical a = true /\ id_ok a /\ strength_ok a.

  (* A covenant-holding expression must begin with the fixed constitution prefix,
     and its payload must satisfy the payload constraints. *)
  Definition covenant (x : Expr) : Prop :=
    exists payload,
      x = List.app constitution_relations payload /\
      Forall payload_ok payload.

  (* ------------------------------------------------------------------ *)
  (* Raw deterministic step on payload, then lifted under constitution prefix. *)
  (* ------------------------------------------------------------------ *)

  Definition raw_step (x y : Expr) : Prop :=
    exists payload payload',
      x = List.app constitution_relations payload /\
      y = List.app constitution_relations payload' /\
      Operational_StaticNormalize.det_step_list payload = Some payload'.

  (* Lawful kernel step = raw deterministic step + covenant preserved. *)
  Definition step (x y : Expr) : Prop :=
    raw_step x y /\ covenant x /\ covenant y.

  Definition step_inv (x y : Expr) : Prop := step y x.

  (* 1n reflexive-transitive closure. *)
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

  (* Covenant preservation (step is explicitly restricted). *)
  Lemma covenant_preserved_step :
    forall x y, step x y -> covenant x -> covenant y.
  Proof.
    intros x y Hstep _.
    destruct Hstep as [_ [_ Hcovy]].
    exact Hcovy.
  Qed.

  Lemma covenant_preserved_multi :
    forall x y, multi x y -> covenant x -> covenant y.
  Proof.
    intros x y Hxy Hcov.
    induction Hxy.
    - exact Hcov.
    - apply IHHxy.
      eapply covenant_preserved_step; eauto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Refusal: triggered when the next deterministic raw step would violate covenant. *)
  (* ------------------------------------------------------------------ *)

  Definition refuse (x y : Expr) : Prop :=
    raw_step x y /\ covenant x /\ ~ covenant y.

  Lemma refuse_safe : forall x y, refuse x y -> ~ step x y.
  Proof.
    intros x y Href Hstep.
    destruct Href as [_ [_ Hnot]].
    destruct Hstep as [_ [_ Hcovy]].
    exact (Hnot Hcovy).
  Qed.

  Lemma det_step_list_det : forall l l1 l2,
      Operational_StaticNormalize.det_step_list l = Some l1 ->
      Operational_StaticNormalize.det_step_list l = Some l2 ->
      l1 = l2.
  Proof.
    intros l l1 l2 H1 H2.
    rewrite H1 in H2.
    inversion H2.
    reflexivity.
  Qed.

  Lemma raw_step_det : forall x y z,
      raw_step x y -> raw_step x z -> y = z.
  Proof.
    intros x y z Hy Hz.
    destruct Hy as [p1 [p1' [Hx [Hy Hdet1]]]].
    destruct Hz as [p2 [p2' [Hx2 [Hz Hdet2]]]].
    subst x.
    (* cancel the fixed prefix to equate the payloads *)
    assert (p1 = p2) as -> by (apply (app_inv_head constitution_relations); exact Hx2).
    assert (p1' = p2') as -> by (eapply det_step_list_det; eauto).
    subst y z.
    reflexivity.
  Qed.

  Lemma refuse_preserved_l : forall x x' y,
      step x x' -> refuse x y -> refuse x' y.
  Proof.
    intros x x' y Hstep Href.
    destruct Hstep as [Hraw [Hcovx Hcovx']].
    destruct Href as [Hraw2 [Hcovx2 Hnotcovy]].
    assert (x' = y) as -> by (symmetry; eapply raw_step_det; eauto).
    exfalso.
    exact (Hnotcovy Hcovx').
  Qed.

  Lemma refuse_preserved_r : forall x y y',
      step y y' -> refuse x y -> refuse x y'.
  Proof.
    intros x y y' Hstep Href.
    destruct Hstep as [_ [Hcovy _]].
    destruct Href as [_ [_ Hnotcovy]].
    exfalso.
    exact (Hnotcovy Hcovy).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Termination: inherit the static-fragment measure decrease.           *)
  (* ------------------------------------------------------------------ *)

  Lemma lex_app_left_mono : forall prefix l1 l2,
      SF.lex_natpair (SF.measure_list l1) (SF.measure_list l2) ->
      SF.lex_natpair (SF.measure_list (List.app prefix l1)) (SF.measure_list (List.app prefix l2)).
  Proof.
    induction prefix as [|a prefix IH]; intros l1 l2 H.
    - simpl. exact H.
    - simpl.
      apply SF.lex_cons_mono.
      apply IH.
      exact H.
  Qed.

  Lemma raw_step_decreases_measure_payload : forall l l',
      Operational_StaticNormalize.det_step_list l = Some l' ->
      SF.lex_natpair (SF.measure_list l') (SF.measure_list l).
  Proof.
    intros l l' Hdet.
    pose proof
      (Operational_StaticNormalize.det_step_list_sound
         l l' ([] : list (RelId * R)) 0 Hdet)
      as Hstatic.
    pose proof (SF.step_static_decreases_measure _ _ Hstatic) as Hdec.
    cbn in Hdec.
    exact Hdec.
  Qed.

  Lemma step_decreases_measure : forall x y,
      step x y ->
      SF.lex_natpair (SF.measure_list y) (SF.measure_list x).
  Proof.
    intros x y Hstep.
    destruct Hstep as [Hraw _].
    destruct Hraw as [p [p' [Hx [Hy Hdet]]]].
    subst x y.
    apply lex_app_left_mono.
    apply raw_step_decreases_measure_payload.
    exact Hdet.
  Qed.

  Definition measured (x y : Expr) : Prop :=
    SF.lex_natpair (SF.measure_list x) (SF.measure_list y).

  Lemma measured_wf : well_founded measured.
  Proof.
    unfold measured.
    exact
      (wf_inverse_image
         Expr (nat * nat)
         SF.lex_natpair
         SF.measure_list
         SF.wf_lex_natpair).
  Qed.

  Lemma static_termination_wf : well_founded step_inv.
  Proof.
    eapply SF.wf_subrelation.
    - exact measured_wf.
    - intros x y Hinv.
      unfold measured.
      unfold step_inv in Hinv.
      (* step_inv x y means step y x *)
      exact (step_decreases_measure y x Hinv).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Determinism -> confluence + unique normal forms.                    *)
  (* ------------------------------------------------------------------ *)

  Lemma step_det : forall x y z,
      step x y -> step x z -> y = z.
  Proof.
    intros x y z Hy Hz.
    destruct Hy as [Hyraw _].
    destruct Hz as [Hzraw _].
    eapply raw_step_det; eauto.
  Qed.

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

  (* ------------------------------------------------------------------ *)
  (* A small witness that refusal is genuinely reachable.                 *)
  (* ------------------------------------------------------------------ *)

  Definition a_atom : relation :=
    {| id := "a";
       source := "A";
       target := "B";
       strength := 1;
       phase := 0;
       shear := (0, 0);
       canonical := true |}.

  Definition b_atom : relation :=
    {| id := "b";
       source := "B";
       target := "C";
       strength := 1;
       phase := 0;
       shear := (0, 0);
       canonical := true |}.

  Lemma payload_ok_a : payload_ok a_atom.
  Proof.
    unfold payload_ok, a_atom, id_ok, strength_ok.
    simpl.
    split; [reflexivity|].
    split.
    - intro Hin.
      simpl in Hin.
      destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; discriminate.
    - lra.
  Qed.

  Lemma payload_ok_b : payload_ok b_atom.
  Proof.
    unfold payload_ok, b_atom, id_ok, strength_ok.
    simpl.
    split; [reflexivity|].
    split.
    - intro Hin.
      simpl in Hin.
      destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; discriminate.
    - lra.
  Qed.

  Local Transparent Operational_StaticNormalize.det_step_list.
  Local Transparent Operational_StaticNormalize.composable.

  Example refusal_example :
    exists x y, refuse x y.
  Proof.
    (* payload = [a;b] satisfies payload_ok but composing a and b yields strength 2,
       violating the covenant for the successor. *)
    set (payload := [a_atom; b_atom]).
    set (payload' :=
           [Op.compose_atoms (normalize_atom a_atom) (normalize_atom b_atom)]).
        set (x := List.app constitution_relations payload).
        set (y := List.app constitution_relations payload').
    exists x, y.
    unfold refuse.
    split.
    - (* raw_step x y *)
      unfold raw_step.
      exists payload, payload'.
      split; [reflexivity|].
      split; [reflexivity|].
      unfold payload, payload'.
      (* det_step_list takes the head-compose step on the 2-element payload. *)
      cbn.
      reflexivity.
    - split.
      + (* covenant x *)
        unfold covenant.
        exists payload.
        split; [reflexivity|].
        unfold payload.
        constructor.
        * apply payload_ok_a.
        * constructor.
          { apply payload_ok_b. }
          { constructor. }
      + (* ~ covenant y *)
        intro Hcovy.
        unfold covenant in Hcovy.
        destruct Hcovy as [p [Hy Hp]].
        subst y.
        assert (p = payload').
        { apply (app_inv_head constitution_relations). symmetry. exact Hy. }
        subst p.
        inversion Hp as [|a0 l0 Hpa Hall]; subst.
        inversion Hall as [|]; subst.
        destruct Hpa as [_ [_ [Hlo Hhi]]].
        (* composed strength is 2, so it cannot satisfy <= 1 *)
        cbn in Hhi.
        lra.
  Qed.

End KernelInstance_Constitutional.
