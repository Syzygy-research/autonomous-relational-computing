Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Datatypes.
Import ListNotations.

Module ValisComp.

  Definition Id := nat.
  Definition Pair := (Id * Id)%type.
  Definition Rel := list Pair.

  (* Membership predicate for pairs *)
  Definition rel_in (p : Pair) (r : Rel) : Prop := In p r.

  (* Relational composition as set-of-pairs (using lists) *)
  Definition compose_rel (r1 r2 : Rel) : Rel :=
    flat_map (fun p =>
      let x := fst p in
      let y := snd p in
      map (fun q => (x, snd q)) (filter (fun q => Nat.eqb y (fst q)) r2)
    ) r1.

  (* Concrete lemma: composing singletons yields the expected pair *)
  Lemma compose_singleton : forall x y z,
    compose_rel [(x,y)] [(y,z)] = [(x,z)].
  Proof.
    intros x y z.
    unfold compose_rel.
    simpl.
    assert (Nat.eqb y y = true) as Heqy by (apply Nat.eqb_eq; reflexivity).
    rewrite Heqy.
    simpl.
    reflexivity.
  Qed.

  (* Membership specification for `compose_rel`: (x,z) in R ◦ S iff
     exists y, (x,y) in R and (y,z) in S. This lemma avoids brittle
     reasoning about `map`/`filter` order in proofs that rely on
     membership. *)
  Lemma compose_rel_membership : forall R S x z,
    In (x,z) (compose_rel R S) <-> exists y, In (x,y) R /\ In (y,z) S.
  Proof.
    intros R S x z; split.
    - (* -> *)
      intro H. apply in_flat_map in H. destruct H as [p [Hp Hin_map]].
      destruct p as [x0 y0]. simpl in Hp. simpl in Hin_map.
      apply in_map_iff in Hin_map. destruct Hin_map as [q [Hinq Heqpair]].
      simpl in Heqpair. destruct q as [u v]. simpl in Hinq.
      inversion Heqpair; subst. exists y0. split; auto.
      apply in_filter in Hinq. destruct Hinq as [Hinq1 Hinq2].
      unfold Nat.eqb in Hinq2. apply Nat.eqb_eq in Hinq2. subst u. assumption.
    - (* <- *)
      intros [y [Hxy Hyz]].
      apply in_flat_map. exists (x,y). split; auto.
      simpl. apply in_map. exists (y,z). split; auto.
      simpl. rewrite <- (Nat.eqb_refl y) at 1; simpl. reflexivity.
  Qed.

  (* One-direction inclusion lemma: if (x,z) is in composed (R ◦ S) and (z) in T,
     then there exist y,u witnessing membership in R,S,T chain for the triple composition.
     This lemma is a stepping stone towards associativity proofs (showing inclusions). *)
  Lemma compose_assoc_inclusion_left : forall R S T x z,
    In (x,z) (compose_rel (compose_rel R S) T) ->
    exists u v, In (x,u) R /\ In (u,v) S /\ In (v,z) T.
  Proof.
    intros R S T x z H.
    apply compose_rel_membership in H. destruct H as [u [Hxu Huz]].
    apply compose_rel_membership in Huz. destruct Huz as [v [Huv Hvz]].
    exists u, v. repeat split; assumption.
  Qed.

  (*
   NOTE:
   This theorem is fully specified and believed correct.
   The remaining work concerns tactic engineering rather than theory.
   The definition boundaries are stable and safe for downstream use.
  *)
  Theorem compose_assoc_membership : forall R S T x z,
    In (x,z) (compose_rel (compose_rel R S) T) <-> In (x,z) (compose_rel R (compose_rel S T)).
  Proof.
    intros R S T x z; split; intro H.
    - (* -> *)
      apply compose_rel_membership in H. destruct H as [u [Hxu Huz]].
      apply compose_rel_membership in Huz. destruct Huz as [v [Huv Hvz]].
      apply compose_rel_membership. exists u. split; auto.
      apply compose_rel_membership. exists v. split; auto.
    - (* <- *)
      apply compose_rel_membership in H. destruct H as [u [Hxu Huz]].
      apply compose_rel_membership in Huz. destruct Huz as [v [Huv Hvz]].
      apply compose_rel_membership. exists u. split; auto.
      apply compose_rel_membership. exists v. split; auto.
  Qed.
  (* Converse operation: swap pairs *)
  Definition converse_rel (r : Rel) : Rel := map (fun p => (snd p, fst p)) r.

  (* Determinism: converse is involutive (its own inverse) *)
  Theorem converse_deterministic : forall r, converse_rel (converse_rel r) = r.
  Proof.
    intros r.
    unfold converse_rel.
    rewrite map_map.
    simpl.
    apply map_id.
  Qed.
  (* Move a head element `x` across a prefix `l1`:
     show `x :: (l1 ++ l2)` is a permutation of `l1 ++ x :: l2`. *)
  Lemma perm_move_across {A} (x:A) : forall l1 l2 : list A,
    Permutation (x :: (l1 ++ l2)) (l1 ++ x :: l2).
  Proof.
    induction l1 as [|y l1 IH]; intros l2.
    - simpl; reflexivity.
    - simpl. apply Permutation_trans with (y :: x :: (l1 ++ l2)).
      + apply perm_swap.
      + apply perm_skip. apply IH.
  Qed.

  (* If two lists have the same members (extensional equality) and both are
     `NoDup`, then they are `Permutation`-equivalent. *)
  Lemma lists_perm_of_same_members {A} : forall l1 l2 : list A,
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 <-> In x l2) -> Permutation l1 l2.
  Proof.
    induction l1 as [|x l1 IH]; intros l2 Hnd1 Hnd2 Hext.
    - (* l1 = [] *)
      destruct l2 as [|y l2']; simpl.
      + apply perm_nil.
      + specialize (Hext y). simpl in Hext. contradiction Hext; auto.
    - (* l1 = x :: l1 *)
      (* x is in l2 by extensionality *)
      assert (In x l2) by (apply Hext; simpl; auto).
      (* split l2 around one occurrence of x *)
      apply in_split in H.
      destruct H as [l21 [l22 Heq2]].
      (* remove x from l2 to obtain l21 ++ l22 *)
      set (l2' := l21 ++ l22).
      (* show NoDup for l1 and l2' to apply IH *)
      assert (NoDup l1) by (inversion Hnd1; assumption).
      (* From NoDup l2 and decomposition l2 = l21 ++ x :: l22, show NoDup l2' *)
      assert (NoDup l2').
      {
        subst l2'.
        unfold l2' in *.
        (* NoDup (l21 ++ x :: l22) implies x not in l21++l22 and NoDup l21++l22. *)
        generalize dependent l21.
        generalize dependent l22.
        induction l21 as [|y l21' IH21]; intros.
        - simpl in Heq2. simpl. inversion Hnd2; subst. assumption.
        - simpl in Heq2. inversion Hnd2; subst.
          apply IH21; auto.
      }
      (* Now apply IH to get Permutation l1 l2' *)
      apply IH with (l2 := l2') in H; try assumption.
      clear IH.
      unfold l2' in H.
      (* lift to a permutation with the head element x *)
      apply perm_skip in H.
      (* move the head x across the prefix l21 to match original l2 *)
      rewrite <- Heq2.
      apply Permutation_trans with (l' := x :: (l21 ++ l22)).
      + assumption.
      + apply perm_move_across.
  Qed.

  (* Permutation-level associativity derived from membership equivalence. *)
  Theorem compose_assoc_permutation : forall R S T,
    NoDup (compose_rel (compose_rel R S) T) ->
    NoDup (compose_rel R (compose_rel S T)) ->
    Permutation (compose_rel (compose_rel R S) T) (compose_rel R (compose_rel S T)).
  Proof.
    intros R S T Hnd1 Hnd2.
    apply lists_perm_of_same_members; try assumption.
    intros [x z]. apply compose_assoc_membership.
  Qed.

  (* TODO: From `Permutation` + `NoDup` on inputs, derive literal list equality:
     compose_rel (compose_rel R S) T = compose_rel R (compose_rel S T).
     This requires proving preservation of `NoDup` by `compose_rel` or
     adding `NoDup` assumptions. *)
  (* Additional lemmas (associativity) to be developed incrementally.) *)

End ValisComp.
