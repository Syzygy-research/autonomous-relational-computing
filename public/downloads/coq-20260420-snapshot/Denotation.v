(* VALIS Denotational Semantics - skeleton *)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import Syntax.

Module VALIS.

(* Tick index type *)
Definition Tick := nat.

(* Enriched relation tuple: entity × phase × resonance *)
Record RelTuple := {
  rt_entity : string;
  rt_phase : R;
  rt_resonance : R;
}.

(* A relation family is a function from Tick to list of tuples *)
Definition RelFamily := Tick -> list RelTuple.

(* Denotation mapping of expressions to families.  Details omitted. *)
Parameter denote : Expr -> RelFamily.

(* Mapping from syntactic `RelationAtom` to semantic `RelTuple` used in the
  denotational model. This is a placeholder parameter: when the concrete
  mapping from atoms to tuples is defined, replace this `Parameter` with
  the actual function and prove the preservation lemmas below. *)
(* Concrete mapping from `RelationAtom` to `RelTuple` used in the
   denotational model. We map the syntactic atom identifier and numeric
   parameters into the tuple; this choice guarantees that flipping
   orientation (normalize) does not change the tuple, because `id`,
   `phase`, and `strength` are preserved by normalization. *)
Definition atom_to_tuple (a : RelationAtom) : RelTuple :=
  {| rt_entity := id a; rt_phase := phase a; rt_resonance := strength a |}.

Lemma atom_normalize_preserves_tuple : forall a,
  atom_to_tuple (normalize_atom a) = atom_to_tuple a.
Proof.
  intros a.
  unfold atom_to_tuple, normalize_atom.
  destruct (canonical a); simpl; reflexivity.
Qed.

(* Delta operator: given a family R at tick t, compute new relations.  This
   corresponds to the compute_delta method in the implementation.  Here we give
   a very simple list-based definition that mimics the Python nested loops.

   For readability we treat RelFamily as a function Tick->list RelTuple; the
   operator below ignores the tick parameter and operates pointwise. *)

(* For the skeleton model we implement a simple uniqueness-by-entity
  filter using `fold_right` and use it as the delta output. Using a
  non-recursive fold simplifies reasoning and proof automation. *)
Definition uniq_by_entity (l : list RelTuple) : list RelTuple :=
  fold_right (fun x acc =>
          if existsb (fun y => if string_dec (rt_entity x) (rt_entity y) then true else false) acc
          then acc else x :: acc) [] l.

Definition list_delta (rels : list RelTuple) : list RelTuple := uniq_by_entity rels.

(* Normalize a tuple to canonical representation. In this simpler denotation
   model we treat normalization as the identity on tuples (placeholder for a
   more detailed atom->tuple mapping). We nevertheless prove idempotence and
   show that using `normalize_tuple` inside `delta` is behavior-preserving.
   When an explicit atom->tuple mapping is added, replace this with the
   concrete normalization that flips orientation when necessary. *)
Definition normalize_tuple (r : RelTuple) : RelTuple := r.

Lemma normalize_tuple_idempotent : forall r,
  normalize_tuple (normalize_tuple r) = normalize_tuple r.
Proof. intros; reflexivity. Qed.

Definition list_delta_norm (rels : list RelTuple) : list RelTuple :=
  uniq_by_entity (map normalize_tuple rels).

Lemma list_delta_norm_equiv : forall rels,
  list_delta_norm rels = list_delta rels.
Proof.
  intros rels. unfold list_delta_norm, list_delta.
  induction rels as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Definition delta (R : RelFamily) : RelFamily :=
  fun t => list_delta_norm (R t).

(* fixed point definition: the least fixed point of delta starting from initial
   relation set.  For simplicity we use a naive inductive definition. *)
Inductive lfp (R : RelFamily) : RelFamily -> Prop :=
| lfp_base : lfp R R
| lfp_step : forall S,
    lfp R S ->
    lfp R (delta S)
.

(* Example lemma, provable directly from the list_delta definition. *)
Definition entities_of (l : list RelTuple) := map rt_entity l.

Lemma in_uniq_by_entity_sub : forall l y,
  In y (uniq_by_entity l) -> In y l.
Proof.
  intros l y.
  revert y.
  induction l as [|x xs IH]; simpl; intros y Hy.
  - inversion Hy.
  - destruct (existsb (fun z : RelTuple =>
            if string_dec (rt_entity x) (rt_entity z) then true else false)
            (uniq_by_entity xs)) eqn:He.
    + (* x excluded from result, so membership must come from tail *)
      simpl in Hy. right. apply IH. assumption.
    + (* x included in result *)
      simpl in Hy. destruct Hy as [Heq | Hy'].
      * subst. left. reflexivity.
      * right. apply IH. assumption.
Qed.

Lemma entities_NoDup : forall xs, NoDup (entities_of (uniq_by_entity xs)).
Proof.
  induction xs as [|x xs IH]; simpl.
  - constructor.
  - simpl.
    remember (uniq_by_entity xs) as u eqn:Hu.
    set (pred := fun y => if string_dec (rt_entity x) (rt_entity y) then true else false).
    destruct (existsb pred u) eqn:He.
    + apply IH.
    + apply NoDup_cons.
      * unfold entities_of; simpl. intro Contra.
          apply in_map_iff in Contra.
          destruct Contra as [y [Hin Hz]].
          (* Hz : rt_entity x = rt_entity y; compute pred accordingly *)
          unfold pred.
          assert (existsb pred u = true) as Htrue.
          { apply existsb_exists. exists y. split; [assumption|].
            unfold pred. replace (rt_entity x) with (rt_entity y) by (apply Hz).
            destruct (string_dec (rt_entity y) (rt_entity y)) as [Heq2 | n];
            [ simpl; reflexivity | exfalso; apply n; reflexivity ]. }
          rewrite Htrue in He. discriminate He.
      * apply IH.
  Qed.
Lemma uniq_preserves_no_dup_implies_id : forall l,
  NoDup (entities_of l) -> uniq_by_entity l = l.
Proof.
  intros l H.
  induction l as [|x xs IH]; simpl.
  - reflexivity.
  - simpl in H.
    unfold entities_of in H.
    inversion H as [|e es Hnd Hnotin]; clear H; subst.
    simpl.
    destruct (existsb (fun y : RelTuple =>
                if string_dec (rt_entity x) (rt_entity y) then true else false) (uniq_by_entity xs)) eqn:He.
    + apply existsb_exists in He.
      destruct He as [y [Hin Hp]].
      unfold pred in Hp.
      destruct (string_dec (rt_entity x) (rt_entity y)) as [e|n].
      * exfalso.
        apply Hnd.
        apply in_map_iff. exists y. split; [now symmetry; exact e |].
        apply in_uniq_by_entity_sub. assumption.
      * discriminate Hp.
    + f_equal. apply IH. exact Hnotin.
Qed.

Lemma uniq_by_entity_idempotent : forall xs,
  uniq_by_entity (uniq_by_entity xs) = uniq_by_entity xs.
Proof.
  intros xs.
  apply uniq_preserves_no_dup_implies_id.
  apply entities_NoDup.
Qed.

Lemma list_delta_idempotent : forall xs, list_delta (list_delta xs) = list_delta xs.
Proof. intro xs. unfold list_delta. apply uniq_by_entity_idempotent. Qed.

Lemma list_delta_norm_idempotent : forall xs,
  list_delta_norm (list_delta_norm xs) = list_delta_norm xs.
Proof.
  intros xs.
  (* use equivalence to ordinary delta and its idempotence *)
  rewrite !list_delta_norm_equiv.
  apply list_delta_idempotent.
Qed.

Lemma delta_idempotent : forall R t,
  delta (delta R) t = delta R t.
Proof.
  intros R t.
  unfold delta.
  apply list_delta_norm_idempotent.
Qed.

(* Properties we will prove later *)
Axiom denote_union : forall p q t,
  denote (EUnion p q) t = (denote p t) ++ (denote q t).

(* delta should be idempotent at fixed point (proof given above) *)

End VALIS.
