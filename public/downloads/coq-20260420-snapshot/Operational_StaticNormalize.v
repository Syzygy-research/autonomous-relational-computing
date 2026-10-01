Require Import Coq.Lists.List.
Require Import Coq.Init.Wf.
Require Import Coq.Reals.Reals.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Strings.String.

Require Import VALIS.Syntax.
Require Import VALIS.Operational.
Require Import Operational_StaticFragment.

Import ListNotations.

Module Operational_StaticNormalize.
  Module Op := VALIS.Operational.VALIS.
  Module SF := Operational_StaticFragment.

  Definition composable (a b : RelationAtom) : bool :=
    if string_dec (target (normalize_atom a)) (source (normalize_atom b))
    then true
    else false.

  Lemma composable_correct : forall a b,
      composable a b = true ->
      target (normalize_atom a) = source (normalize_atom b).
  Proof.
    intros a b H.
    unfold composable in H.
    destruct (string_dec (target (normalize_atom a)) (source (normalize_atom b))) as [Heq|Hneq].
    - exact Heq.
    - discriminate.
  Qed.

  Opaque composable.

  Fixpoint det_step_list (l : list RelationAtom) : option (list RelationAtom) :=
    match l with
    | [] => None
    | a :: rest =>
        if canonical a then
          match rest with
          | [] => None
          | b :: rest2 =>
              if composable a b then
                let c := Op.compose_atoms (normalize_atom a) (normalize_atom b) in
                Some (c :: rest2)
              else
                match det_step_list rest with
                | None => None
                | Some rest' => Some (a :: rest')
                end
          end
        else
          Some (Op.converse a :: rest)
    end.

  Lemma det_step_list_unfold : forall l,
      det_step_list l =
      match l with
      | [] => None
      | a :: rest =>
          if canonical a then
            match rest with
            | [] => None
            | b :: rest2 =>
                if composable a b then
                  let c := Op.compose_atoms (normalize_atom a) (normalize_atom b) in
                  Some (c :: rest2)
                else
                  match det_step_list rest with
                  | None => None
                  | Some rest' => Some (a :: rest')
                  end
            end
          else
            Some (Op.converse a :: rest)
      end.
  Proof.
    destruct l as [|a rest]; reflexivity.
  Qed.

  Opaque det_step_list.

  Definition det_step_state (s : Op.State) : option Op.State :=
    match det_step_list (Op.E s) with
    | None => None
    | Some E' => Some {| Op.E := E'; Op.phi := Op.phi s; Op.tick := Op.tick s |}
    end.

  Lemma det_step_list_sound :
    forall l l' (phi0 : list (RelId * R)) (tick0 : nat),
      det_step_list l = Some l' ->
      SF.step_static
        {| Op.E := l; Op.phi := phi0; Op.tick := tick0 |}
        {| Op.E := l'; Op.phi := phi0; Op.tick := tick0 |}.
  Proof.
    induction l as [|a rest IH]; intros l' phi0 tick0 Hdet.
    - rewrite det_step_list_unfold in Hdet.
      cbn in Hdet.
      discriminate Hdet.
    - rewrite det_step_list_unfold in Hdet.
      cbn in Hdet.
      destruct (canonical a) eqn:Hcan.
      + (* a canonical *)
        destruct rest as [|b rest2].
        * cbn in Hdet.
          discriminate Hdet.
        * cbn in Hdet.
          destruct (composable a b) eqn:Hcomp.
          { cbn in Hdet.
            inversion Hdet; subst.
            apply SF.SSCompose.
            apply (composable_correct a b).
            exact Hcomp.
          }
          { (* Keep the tail call opaque, then destruct it. *)
            destruct (det_step_list (b :: rest2)) as [tail'|] eqn:Htail.
            - cbn in Hdet.
              inversion Hdet; subst.
              eapply (SF.SSConsLeft a
                        {| Op.E := b :: rest2; Op.phi := phi0; Op.tick := tick0 |}
                        {| Op.E := tail'; Op.phi := phi0; Op.tick := tick0 |}).
              apply (IH tail' phi0 tick0).
              reflexivity.
            - cbn in Hdet.
              discriminate Hdet.
          }
      + (* a non-canonical: converse at head *)
        cbn in Hdet.
        inversion Hdet; subst.
        apply SF.SSConverse.
        exact Hcan.
  Qed.

  Lemma det_step_state_sound : forall s s',
      det_step_state s = Some s' ->
      SF.step_static s s'.
  Proof.
    intros [E0 phi0 tick0] s' H.
    unfold det_step_state in H.
    simpl in H.
    destruct (det_step_list E0) as [E1|] eqn:Hl.
    - inversion H; subst; clear H.
      apply (det_step_list_sound E0 E1 phi0 tick0).
      exact Hl.
    - discriminate H.
  Qed.

  (* Use the static-fragment termination proof to define a total normalizer
     for the deterministic strategy above.

     Key idea: avoid recursion on an [Acc] witness (which tends to create
     brittle dependent-match proof obligations). Instead, use well-founded
     induction on the *state* with respect to the inverse static step.
  *)

  Definition normalize_witness (s : Op.State) :
    { s' : Op.State & SF.multi_step_static s s' /\ det_step_state s' = None }.
  Proof.
    refine (
      well_founded_induction
        SF.wf_step_static
        (fun x => { s' : Op.State & SF.multi_step_static x s' /\ det_step_state s' = None })
        _
        s).
    intros x IH.
    destruct (det_step_state x) as [x1|] eqn:Hdet.
    - pose proof (det_step_state_sound x x1 Hdet) as Hstep.
      destruct (IH x1) as [s' [Hms Hnorm]].
      { unfold SF.step_static_inv. exact Hstep. }
      exists s'.
      split.
      + eapply rt_trans.
        * apply rt_step. exact Hstep.
        * exact Hms.
      + exact Hnorm.
    - exists x.
      split.
      + apply rt_refl.
      + exact Hdet.
  Defined.

  Definition normalize_state (s : Op.State) : Op.State :=
    projT1 (normalize_witness s).

  Lemma normalize_state_is_normal : forall s,
      det_step_state (normalize_state s) = None.
  Proof.
    intro s.
    unfold normalize_state.
    destruct (normalize_witness s) as [nf [Hms Hnorm]].
    simpl.
    exact Hnorm.
  Qed.

  Lemma normalize_state_reachable : forall s,
      SF.multi_step_static s (normalize_state s).
  Proof.
    intro s.
    unfold normalize_state.
    destruct (normalize_witness s) as [nf [Hms Hnorm]].
    simpl.
    exact Hms.
  Qed.

End Operational_StaticNormalize.
