Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Import ListNotations.

Require Import VALIS.Syntax.
Require Import VALIS.Operational.

Module Operational_AlgebraicSoundness.
  Module Op := VALIS.Operational.VALIS.

  (* ------------------------------------------------------------------ *)
  (* A minimal algebraic closure for interpreting relation lists.        *)
  (* ------------------------------------------------------------------ *)

  Section WithGen.
    Context (Gen : Type).

    Inductive Expr : Type :=
    | EUnit
    | EGen (g : Gen)
    | EComp (e1 e2 : Expr).

    Record Algebra := {
      carrier : Type;
      op : carrier -> carrier -> carrier;
      unit : carrier;
      gen : Gen -> carrier;
      assoc : forall x y z, op x (op y z) = op (op x y) z;
      unit_l : forall x, op unit x = x;
      unit_r : forall x, op x unit = x
    }.

    Fixpoint eval (alg : Algebra) (e : Expr) : carrier alg :=
      match e with
      | EUnit => unit alg
      | EGen g => gen alg g
      | EComp e1 e2 => op alg (eval alg e1) (eval alg e2)
      end.

    Fixpoint expr_of_list (l : list Gen) : Expr :=
      match l with
      | [] => EUnit
      | a :: rest => EComp (EGen a) (expr_of_list rest)
      end.
  End WithGen.

  Definition Gen := RelationAtom.

  Definition op_opt (x y : option RelationAtom) : option RelationAtom :=
    match x, y with
    | None, r => r
    | r, None => r
    | Some a, Some b => Some (Op.compose_atoms a b)
    end.

  Arguments op_opt _ _ : simpl never.

  Lemma op_opt_assoc : forall x y z,
      op_opt x (op_opt y z) = op_opt (op_opt x y) z.
  Proof.
    intros x y z.
    destruct x as [x|], y as [y|], z as [z|]; unfold op_opt; simpl; try reflexivity.
    f_equal.
    symmetry.
    apply Op.compose_assoc.
  Qed.

  Lemma op_opt_unit_l : forall x, op_opt None x = x.
  Proof. intro x; destruct x; reflexivity. Qed.

  Lemma op_opt_unit_r : forall x, op_opt x None = x.
  Proof. intro x; destruct x; reflexivity. Qed.

  Definition gen_interp (a : Gen) : option RelationAtom :=
    Some (normalize_atom a).

  Definition Alg : Algebra Gen :=
    {| carrier := option RelationAtom;
       op := op_opt;
       unit := None;
       gen := gen_interp;
       assoc := op_opt_assoc;
       unit_l := op_opt_unit_l;
       unit_r := op_opt_unit_r |}.

  Definition interp_list (l : list Gen) : option RelationAtom :=
    eval Gen Alg (expr_of_list Gen l).

  Definition interp_state (s : Op.State) : option RelationAtom :=
    interp_list (Op.E s).

  Lemma normalize_atom_eq_converse : forall a,
      canonical a = false ->
      normalize_atom a = Op.converse a.
  Proof.
    intros a H.
    unfold normalize_atom.
    rewrite H.
    unfold Op.converse.
    destruct a; simpl.
    reflexivity.
  Qed.

  Lemma interp_list_app_single : forall (l : list Gen) (a : Gen),
      interp_list (l ++ [a]) = op_opt (interp_list l) (gen_interp a).
  Proof.
    induction l as [|x xs IH]; intros a; unfold interp_list, Alg in *; cbn.
    - reflexivity.
    - rewrite IH.
      exact (op_opt_assoc (gen_interp x)
               (eval Gen Alg (expr_of_list Gen xs))
               (gen_interp a)).
  Qed.

  Theorem step_preserves_interp_state :
    forall s s',
      Op.step s s' ->
      interp_state s = interp_state s'.
  Proof.
    intros s s' H.
    induction H.
    - (* StepPhase *)
      unfold interp_state, interp_list.
      simpl.
      reflexivity.
    - (* StepCompose *)
      unfold interp_state, interp_list.
      simpl.
      unfold gen_interp.
      rewrite op_opt_assoc.
      simpl.
      reflexivity.
    - (* StepConverse *)
      unfold interp_state, interp_list.
      simpl.
      unfold gen_interp.
      rewrite (normalize_atom_eq_converse a H).
      unfold normalize_atom.
      unfold Op.converse.
      destruct a; simpl.
      reflexivity.
    - (* StepConsLeft *)
      unfold interp_state, interp_list in *.
      simpl.
      unfold gen_interp.
      rewrite IHstep.
      reflexivity.
    - (* StepAppRight *)
      unfold interp_state in IHstep.
      unfold interp_state.
      simpl.
      repeat rewrite interp_list_app_single.
      rewrite IHstep.
      reflexivity.
  Qed.

  Theorem multi_step_preserves_interp_state :
    forall s s',
      Op.multi_step s s' ->
      interp_state s = interp_state s'.
  Proof.
    intros s s' H.
    eapply (clos_refl_trans_ind Op.State Op.step
              (fun x y => interp_state x = interp_state y)).
    - intros x y Hxy.
      apply step_preserves_interp_state.
      exact Hxy.
    - intro x.
      reflexivity.
    - intros x y z _ IHxy _ IHyx.
      rewrite IHxy.
      exact IHyx.
    - exact H.
  Qed.

End Operational_AlgebraicSoundness.
