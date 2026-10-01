Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.micromega.Lia.

Require Import VALIS.Syntax.
Require Import VALIS.Operational.

Import ListNotations.

Module Operational_StaticFragment.
  Module Op := VALIS.Operational.VALIS.

  (* Static fragment of the Phase-1 step relation: excludes arbitrary phase/tick
     updates and keeps only the relation-list rewriting rules plus contextual
     closure. *)
  Inductive step_static : Op.State -> Op.State -> Prop :=
  | SSCompose : forall phi0 tick0 a b rest,
      target (normalize_atom a) = source (normalize_atom b) ->
      let a' := normalize_atom a in
      let b' := normalize_atom b in
      let c := Op.compose_atoms a' b' in
      step_static {| Op.E := a :: b :: rest; Op.phi := phi0; Op.tick := tick0 |}
                  {| Op.E := c :: rest; Op.phi := phi0; Op.tick := tick0 |}
  | SSConverse : forall phi0 tick0 a rest,
      canonical a = false ->
      let c := Op.converse a in
      step_static {| Op.E := a :: rest; Op.phi := phi0; Op.tick := tick0 |}
                  {| Op.E := c :: rest; Op.phi := phi0; Op.tick := tick0 |}
  | SSConsLeft : forall (a : RelationAtom) s s',
      step_static s s' ->
      step_static {| Op.E := a :: Op.E s; Op.phi := Op.phi s; Op.tick := Op.tick s |}
                  {| Op.E := a :: Op.E s'; Op.phi := Op.phi s'; Op.tick := Op.tick s' |}
  | SSAppRight : forall (a : RelationAtom) s s',
      step_static s s' ->
      step_static {| Op.E := Op.E s ++ [a]; Op.phi := Op.phi s; Op.tick := Op.tick s |}
                  {| Op.E := Op.E s' ++ [a]; Op.phi := Op.phi s'; Op.tick := Op.tick s' |}.

  Definition multi_step_static := clos_refl_trans Op.State step_static.

  (* Static steps are also Phase-1 steps. *)
  Lemma step_static_in_step : forall s s',
      step_static s s' -> Op.step s s'.
  Proof.
    intros s s' H.
    induction H.
    - (* SSCompose *)
      eapply Op.StepCompose; eauto.
    - (* SSConverse *)
      eapply Op.StepConverse; eauto.
    - (* SSConsLeft *)
      apply Op.StepConsLeft; assumption.
    - (* SSAppRight *)
      apply Op.StepAppRight; assumption.
  Qed.

  (* ================================================================ *)
  (* Termination measure                                               *)
  (* ================================================================ *)

  Fixpoint count_noncanonical (l : list RelationAtom) : nat :=
    match l with
    | [] => 0
    | x :: xs => (if canonical x then 0 else 1) + count_noncanonical xs
    end.

  Definition measure_list (l : list RelationAtom) : nat * nat :=
    (count_noncanonical l, length l).

  Definition measure_state (s : Op.State) : nat * nat :=
    measure_list (Op.E s).

  (* Lexicographic order on (noncanonical-count, length). *)
  Definition lex_natpair : (nat * nat) -> (nat * nat) -> Prop :=
    slexprod nat nat lt lt.

  Lemma wf_lex_natpair : well_founded lex_natpair.
  Proof.
    unfold lex_natpair.
    apply wf_slexprod; apply lt_wf.
  Qed.

  Lemma count_noncanonical_app_single : forall l a,
      count_noncanonical (l ++ [a]) =
      count_noncanonical l + (if canonical a then 0 else 1).
  Proof.
    induction l as [|x xs IH]; intros a; simpl.
    - lia.
    - rewrite IH. lia.
  Qed.

  (* Monotonicity under adding the same left context. *)
  Lemma lex_cons_mono : forall a l1 l2,
      lex_natpair (measure_list l1) (measure_list l2) ->
      lex_natpair (measure_list (a :: l1)) (measure_list (a :: l2)).
  Proof.
    intros a l1 l2 H.
    unfold lex_natpair, measure_list in *.
    simpl.
    inversion H as [x x' y y' Hlt | x y y' Hlt]; subst; clear H.
    - (* primary component decreases *)
      apply left_slex.
      (* add the same 0/1 prefix contribution to both counts *)
      exact (proj1 (Nat.add_lt_mono_l (count_noncanonical l1)
                      (count_noncanonical l2)
                      (if canonical a then 0 else 1)) Hlt).
    - (* primary equal; secondary decreases *)
      apply right_slex.
      exact (proj1 (Nat.succ_lt_mono (length l1) (length l2)) Hlt).
  Qed.

  (* Monotonicity under adding the same single-element right context. *)
  Lemma lex_app_single_mono : forall a l1 l2,
      lex_natpair (measure_list l1) (measure_list l2) ->
      lex_natpair (measure_list (l1 ++ [a])) (measure_list (l2 ++ [a])).
  Proof.
    intros a l1 l2 H.
    unfold lex_natpair, measure_list in *.
    rewrite !count_noncanonical_app_single.
    rewrite !app_length.
    simpl.
    inversion H as [x x' y y' Hlt | x y y' Hlt]; subst; clear H.
    - apply left_slex.
      (* add the same suffix contribution to both counts *)
      exact (proj1 (Nat.add_lt_mono_r (count_noncanonical l1)
                      (count_noncanonical l2)
                      (if canonical a then 0 else 1)) Hlt).
    - apply right_slex.
      (* same first component; length increases equally *)
      exact (proj1 (Nat.add_lt_mono_r (length l1) (length l2) 1) Hlt).
  Qed.

  (* Each static step strictly decreases the lexicographic measure. *)
  Lemma step_static_decreases_measure : forall s s',
      step_static s s' -> lex_natpair (measure_state s') (measure_state s).
  Proof.
    intros s s' H.
    induction H.
    - (* SSCompose *)
      unfold measure_state, measure_list.
      simpl.
      (* after composing, the head is canonical by construction *)
      unfold Op.compose_atoms.
      simpl.
      (* split on canonicity of the two inputs; either noncanonical-count
         drops (if any input was noncanonical) or length drops (otherwise). *)
      destruct (canonical a) eqn:Ha; destruct (canonical b) eqn:Hb; simpl; try (constructor 1; lia).
      + (* both canonical: counts equal, lengths differ *)
        constructor 2.
        simpl.
        lia.
    - (* SSConverse *)
      unfold measure_state, measure_list.
      simpl.
      (* converse produces a canonical atom *)
      unfold Op.converse.
      destruct a; simpl in *.
      (* canonical a = false ensures the count drops by 1 *)
      rewrite H.
      simpl.
      constructor 1.
      lia.
    - (* SSConsLeft *)
      apply lex_cons_mono.
      exact IHstep_static.
    - (* SSAppRight *)
      apply lex_app_single_mono.
      exact IHstep_static.
  Qed.

  (* Well-foundedness of the *inverse* static step: this is the standard
     termination statement for forward reduction chains. *)
  Definition step_static_inv (x y : Op.State) : Prop := step_static y x.

  (* Subrelations of a well-founded relation are well-founded. *)
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

  Theorem wf_step_static : well_founded step_static_inv.
  Proof.
    (* Use inverse-image of lex order under the measure, then include
       [step_static_inv] as a subrelation via strict decrease. *)
    eapply wf_subrelation.
    - (* wf of measured relation *)
      (* Inverse image of lex_natpair along measure_state. *)
      exact (wf_inverse_image Op.State (nat * nat) lex_natpair measure_state wf_lex_natpair).
    - (* inclusion: each inverse-step decreases the measure *)
      intros x y Hxy.
      unfold step_static_inv in Hxy.
      exact (step_static_decreases_measure y x Hxy).
  Qed.

End Operational_StaticFragment.
