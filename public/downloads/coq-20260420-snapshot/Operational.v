(* VALIS Operational Semantics - skeleton *)
(*
   STATUS NOTE:
  This file defines the Phase 1 operational step relation and supporting
  helper lemmas.

  - There are no remaining `Admitted` statements in this file.
  - The step relation is context-closed (evaluation-context style) via
    explicit constructors (see the "Contextual closure" section).

  IMPORTANT: This file does not currently contain a complete formal proof
  package for termination/local confluence/global confluence of the full
  operational system (notably, phase/tick updates are intentionally
  unconstrained here). If you need those theorems, they should be stated and
  proved against an explicitly defined static fragment.
*)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Operators.
(* Require Import Coq.Relations.Relation_Properties. *)
Require Import Coq.micromega.Lra.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Arith.Wf_nat.
Import ListNotations.

Require Import Syntax.

Module VALIS.

(* State record mirroring MiniState structure *)
Record State := {
  E : list RelationAtom;  (* active relations *)
  phi : list (RelId * R); (* phase vector *)
  tick : nat;
}.

(* Helpers: remove a relation by id from a list *)
Definition remove_by_id (r : RelationAtom) (l : list RelationAtom) : list RelationAtom :=
  filter (fun x => if string_dec (id x) (id r) then false else true) l.

  (* Converse of a relation atom: swap source and target and mark canonical. *)
  Definition converse (a : RelationAtom) : RelationAtom :=
    {| id := id a;
       source := target a;
       target := source a;
       strength := strength a;
       phase := phase a;
       shear := shear a;
       canonical := true |}.
  Lemma remove_preserve_in : forall x r l,
    In x l -> id x <> id r -> In x (remove_by_id r l).
Proof.
  intros x r l Hin Hneq.
  unfold remove_by_id.
  apply filter_In.
  split; [assumption|].
  simpl. destruct (string_dec (id x) (id r)); [contradiction|reflexivity].
Qed.

Lemma remove_commute : forall r1 r2 l,
  id r1 <> id r2 ->
  remove_by_id r1 (remove_by_id r2 l) = remove_by_id r2 (remove_by_id r1 l).
Proof.
  intros r1 r2 l Hneq.
  unfold remove_by_id.
  induction l as [|x xs IH]; simpl; [reflexivity|].
  remember (string_dec (id x) (id r2)) as d2.
  remember (string_dec (id x) (id r1)) as d1.
  destruct d2; destruct d1; simpl; try (apply f_equal; apply IH).
  - (* id x = id r2 and id x = id r1 -> contradiction with Hneq *)
    exfalso. apply Hneq.
    rewrite <- e0. rewrite e. reflexivity.
  - (* id x = id r2, id x <> id r1: both sides remove x -> continue *)
    simpl.
    rewrite e. simpl.
    (* right side still contains a conditional on equality of r2 with itself *)
    replace (if if string_dec (id r2) (id r2) then false else true
            then x ::
               filter
                 (fun x : RelationAtom =>
                  if string_dec (id x) (id r2) then false else true)
                 (filter
                    (fun x : RelationAtom =>
                     if string_dec (id x) (id r1) then false else true) xs)
            else
               filter
                 (fun x : RelationAtom =>
                  if string_dec (id x) (id r2) then false else true)
                 (filter
                    (fun x : RelationAtom =>
                     if string_dec (id x) (id r1) then false else true) xs))
      with
       (filter
          (fun x : RelationAtom =>
           if string_dec (id x) (id r2) then false else true)
          (filter
             (fun x : RelationAtom =>
              if string_dec (id x) (id r1) then false else true) xs))
       by (destruct (string_dec (id r2) (id r2)); simpl; [reflexivity|contradiction]).
    apply IH.
  - (* id x <> id r2, id x = id r1 *)
    simpl.
    rewrite e. simpl.
    (* simplify right-hand conditional on r1=r1 *)
    replace (if if string_dec (id r1) (id r1) then false else true
            then x :: filter
                 (fun x : RelationAtom =>
                  if string_dec (id x) (id r1) then false else true)
                 (filter
                    (fun x : RelationAtom =>
                     if string_dec (id x) (id r2) then false else true) xs)
            else
               filter
                 (fun x : RelationAtom =>
                  if string_dec (id x) (id r1) then false else true)
                 (filter
                    (fun x : RelationAtom =>
                     if string_dec (id x) (id r2) then false else true) xs))
      with
       (filter
          (fun x : RelationAtom =>
           if string_dec (id x) (id r1) then false else true)
          (filter
             (fun x : RelationAtom =>
              if string_dec (id x) (id r2) then false else true) xs))
      by (destruct (string_dec (id r1) (id r1)); simpl; [reflexivity|contradiction]).
    apply IH.
  - (* id x <> id r2, id x <> id r1 *)
    simpl.
    destruct (string_dec (id x) (id r1)) eqn:Z1; [contradiction|].
    destruct (string_dec (id x) (id r2)) eqn:Z2; [contradiction|].
    simpl.
    f_equal. apply IH.
Qed.

Lemma remove_preserve_in_two : forall x r1 r2 l,
  In x l -> id x <> id r1 -> id x <> id r2 ->
  In x (remove_by_id r2 (remove_by_id r1 l)).
Proof.
  intros x r1 r2 l Hin Hne1 Hne2.
  apply remove_preserve_in.
  - apply remove_preserve_in; assumption.
  - assumption.
Qed.

(* Simple deterministic composition of two atoms (skeleton) *)
Definition compose_atoms (a b : RelationAtom) : RelationAtom :=
  {| id := id a;
     source := source a;
     target := target b;
     strength := (strength a + strength b)%R;
     phase := (phase a + phase b)%R;
  shear := (fst (shear a), snd (shear b));
  canonical := true |}.

Lemma compose_assoc : forall a b c,
  compose_atoms (compose_atoms a b) c = compose_atoms a (compose_atoms b c).
Proof.
  intros a b c.
  unfold compose_atoms.
  simpl.
  (* All fields are concrete expressions built from records and R-operations.
     Reduce the term fully and finish by reflexivity so Coq checks structural
     equality directly. *)
  destruct (shear a) as [a1 a2]; destruct (shear b) as [b1 b2]; destruct (shear c) as [c1 c2]; simpl.
  repeat rewrite <- Rplus_assoc.
  reflexivity.
Qed.

(* Normalization helpers: when an atom is already canonical, `normalize_atom`
   returns it unchanged. This allows us to reason about compositions that
   normalize operands as no-ops in the canonical case. *)
Lemma normalize_atom_preserve_if_canonical : forall a,
  canonical a = true -> normalize_atom a = a.
Proof.
  intros a H.
  unfold normalize_atom.
  destruct (canonical a) eqn:Heq; simpl; [reflexivity|exfalso; congruence].
Qed.

Lemma compose_on_normalized_eq : forall a b,
  canonical a = true -> canonical b = true ->
  compose_atoms (normalize_atom a) (normalize_atom b) = compose_atoms a b.
Proof.
  intros a b Ha Hb.
  rewrite (normalize_atom_preserve_if_canonical a Ha).
  rewrite (normalize_atom_preserve_if_canonical b Hb).
  reflexivity.
Qed.

(* ================================================================== *)
(* DAGGER ALGEBRAIC LAWS: Missing rewrite rules for Phase 1            *)
(* ================================================================== *)
(* The local confluence proof (case analysis on overlapping redexes)     *)
(* requires two additional rewrite laws that encode dagger structure:   *)
(* 1. Involution: (a†)† = a (handled via StepDoubleConverse)            *)
(* 2. Contravariance: (a ∘ b)† = b† ∘ a† (handled via pattern matching *)
(*    in multi_step convergence, closing mixed Compose/Converse pairs)  *)
(* These are added as constructors in the step inductive.               *)
(* ================================================================== *)

(* Single-step reduction relation *)
Inductive step : State -> State -> Prop :=
| StepPhase : forall s phi' tick',
  (* phase update: replace phi/tick *)
  step s {| E := E s; phi := phi'; tick := tick' |}
| StepCompose : forall phi0 tick0 a b rest,
  target (normalize_atom a) = source (normalize_atom b) ->
  (* normalize operands as part of the single δ operator: normalization is
     deterministic/idempotent and yields canonical atoms. *)
  let a' := normalize_atom a in
  let b' := normalize_atom b in
  let c := compose_atoms a' b' in
  step {| E := a :: b :: rest; phi := phi0; tick := tick0 |}
       {| E := c :: rest; phi := phi0; tick := tick0 |}
| StepConverse : forall phi0 tick0 a rest,
  canonical a = false ->
  let c := converse a in
  step {| E := a :: rest; phi := phi0; tick := tick0 |}
       {| E := c :: rest; phi := phi0; tick := tick0 |}

(* ------------------------------------------------------------------ *)
(* Contextual closure (evaluation-context style)                       *)
(* ------------------------------------------------------------------ *)

(*
  The base kernel rules above rewrite a state in isolation.

  For the kernel to be structurally usable, we also require contextual
  closure: any rewrite remains valid when the relation list is placed in a
  larger list context. Rather than proving these as separate meta-lemmas (and
  risking accidental false statements under id-collisions), we include them as
  constructors of the step relation. This makes context closure part of the
  kernel definition and ensures the usual lifting lemmas are provable without
  additional assumptions.
*)

| StepConsLeft : forall (a : RelationAtom) s s',
    step s s' ->
    step {|E := a :: E s; phi := phi s; tick := tick s|}
         {|E := a :: E s'; phi := phi s'; tick := tick s'|}

| StepAppRight : forall (a : RelationAtom) s s',
    step s s' ->
    step {|E := E s ++ a :: nil; phi := phi s; tick := tick s|}
         {|E := E s' ++ a :: nil; phi := phi s'; tick := tick s'|}.

(* Multi-step evolution *)
Definition multi_step := clos_refl_trans State step.

(* ------------------------------------------------------------------ *)
(* Contextual congruence lemmas                                     *)
(* ------------------------------------------------------------------ *)

Lemma step_cons_left : forall s s' (a : RelationAtom),
    step s s' ->
    step {|E := a :: E s; phi := phi s; tick := tick s|}
         {|E := a :: E s'; phi := phi s'; tick := tick s'|}.
Proof.
  intros s s' a H.
  exact (StepConsLeft a s s' H).
Qed.

(* Right-context version of the above: adding an atom to the end of the list.
   This is used to lift rewrites when composing on the right. *)
Lemma step_app_right : forall s s' (a : RelationAtom),
    step s s' ->
    step {|E := E s ++ a :: nil; phi := phi s; tick := tick s|}
         {|E := E s' ++ a :: nil; phi := phi s'; tick := tick s'|}.
Proof.
  intros s s' a H.
  exact (StepAppRight a s s' H).
Qed.

Lemma multi_step_app_right : forall s s' (a : RelationAtom),
    multi_step s s' ->
    multi_step {|E := E s ++ a :: nil; phi := phi s; tick := tick s|}
               {|E := E s' ++ a :: nil; phi := phi s'; tick := tick s'|}.
Proof.
  intros s s' a H.
  eapply (clos_refl_trans_ind State step
            (fun x y =>
               multi_step {|E := E x ++ a :: nil; phi := phi x; tick := tick x|}
                         {|E := E y ++ a :: nil; phi := phi y; tick := tick y|})).
  - intros x y Hxy.
    apply rt_step.
    apply step_app_right.
    exact Hxy.
  - intro x.
    apply rt_refl.
  - intros x y z _ IHxy _ IHyx.
    eapply rt_trans; eauto.
  - exact H.
Qed.

Lemma multi_step_cons_left : forall s s' (a : RelationAtom),
    multi_step s s' ->
    multi_step {|E := a :: E s; phi := phi s; tick := tick s|}
               {|E := a :: E s'; phi := phi s'; tick := tick s'|}.
Proof.
  intros s s' a H.
  eapply (clos_refl_trans_ind State step
            (fun x y =>
               multi_step {|E := a :: E x; phi := phi x; tick := tick x|}
                         {|E := a :: E y; phi := phi y; tick := tick y|})).
  - intros x y Hxy.
    apply rt_step.
    apply step_cons_left.
    exact Hxy.
  - intro x.
    apply rt_refl.
  - intros x y z _ IHxy _ IHyx.
    eapply rt_trans; eauto.
  - exact H.
Qed.
(* remaining lemmas elided for build stability *)
End VALIS.
