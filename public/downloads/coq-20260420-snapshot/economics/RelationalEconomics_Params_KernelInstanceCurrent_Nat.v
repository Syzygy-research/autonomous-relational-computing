From Coq Require Import List Arith Lia.
From Coq Require Import Strings.String.

Require Import VALIS.Syntax.
Require Import VALIS.KernelInstance_Current.
Require Import VALIS.Operational_StaticFragment.

Require Import economics.RelationalEconomics.

Import ListNotations.

Module RelationalEconomics_Params_KernelInstanceCurrent_Nat.
  Module K := VALIS.KernelInstance_Current.KernelInstance_Current.

  Module NatAmountModel <: AmountModelSig.
    Definition Amount : Type := nat.
    Definition zero : Amount := 0.
    Definition add (a b : Amount) : Amount := a + b.
    Definition leq (a b : Amount) : Prop := a <= b.

    Infix "+" := add.
    Infix "<=" := leq.

    Theorem add_assoc : forall a b c, a + (b + c) = (a + b) + c.
    Proof. intros a b c; unfold add; simpl; apply Nat.add_assoc. Qed.

    Theorem add_comm : forall a b, a + b = b + a.
    Proof. intros a b; unfold add; simpl; apply Nat.add_comm. Qed.

    Theorem add_zero : forall a, a + zero = a.
    Proof. intros a; unfold add, zero; simpl; apply Nat.add_0_r. Qed.

    Theorem leq_refl : forall a, a <= a.
    Proof. intro a; unfold leq; apply Nat.le_refl. Qed.

    Theorem leq_trans : forall a b c, a <= b -> b <= c -> a <= c.
    Proof. intros a b c Hab Hbc; unfold leq in *; eapply Nat.le_trans; eauto. Qed.

    Theorem zero_least : forall a, zero <= a.
    Proof. intro a; unfold leq, zero; apply Nat.le_0_l. Qed.

    Theorem leq_add_mono :
      forall a b c d,
        a <= b ->
        c <= d ->
        (a + c) <= (b + d).
    Proof.
      intros a b c d Hab Hcd.
      unfold leq, add in *.
      exact (Nat.add_le_mono _ _ _ _ Hab Hcd).
    Qed.

    Theorem leq_add_incr_r : forall a b, a <= a + b.
    Proof. intros a b; unfold leq, add; apply Nat.le_add_r. Qed.

    Theorem leq_add_incr_l : forall a b, a <= b + a.
    Proof. intros a b; unfold leq, add; apply Nat.le_add_l. Qed.

    Definition positive (a : Amount) : Prop := 0 < a.
  End NatAmountModel.

  Module P <: RelationalEconomicsParams K NatAmountModel.
    (* Hashes in the sealed kernel instance are natural numbers. *)
    Definition hash_eq_dec : forall h1 h2 : K.hash, {h1 = h2} + {h1 <> h2} :=
      Nat.eq_dec.

    (* Normalization: use the kernel’s canonicalizer on atoms. *)
    Definition normalize (r : K.relation) : K.relation := normalize_atom r.

    (* Complexity: kernel-derived and deterministic.
       IMPORTANT: `measure_list [normalize r]` becomes constant because
       `normalize_atom` forces canonicity and singleton length is always 1.
       Instead, derive complexity from atom data that is stable under
       normalization (string lengths are invariant under swapping src/tgt). *)
    Definition atom_size (a : K.relation) : nat :=
      String.length (id a) + String.length (source a) + String.length (target a).

    Definition delta_complexity (r : K.relation) : NatAmountModel.Amount :=
      S (atom_size (normalize r)).

    Definition min : NatAmountModel.Amount -> NatAmountModel.Amount -> NatAmountModel.Amount :=
      Nat.min.

    (* Compatibility order on hashes (primitive-aligned): `new` extends `old`
       exactly when `new` is a `family_hash old ext` for some extension list.
       In the sealed Phase-1 kernel instance, hashes are `nat` and
       `family_hash h ext = h + length ext`, so this is fully deterministic. *)
    Definition extends (old new : K.hash) : Prop :=
      exists ext : list K.relation,
        new = K.family_hash old ext.

    (* Deterministic minting policy: trivial placeholders for now.
       Step 3’s goal is to make these policy predicates *depend only on*
       kernel-derived data, not external oracles. *)
    Definition relation_settled (r : K.relation) : Prop :=
      normalize r = r.

    Definition respects_constitution (r : K.relation) : Prop :=
      let rid := id (normalize r) in
      ~ In rid (map id K.constitution_relations).

     (* Governance/lineage compatibility (primitive-aligned): a relation is
       lineage-compatible when it is representable as a constitution-hash
       extension via the kernel's `family_hash`. *)
     Definition lineage_compatible (r : K.relation) : Prop :=
      extends K.constitution_hash
            (K.family_hash K.constitution_hash [normalize r]).
    Definition stake_required (r : K.relation) : NatAmountModel.Amount :=
      delta_complexity (normalize r).

    (* Time model: natural numbers. *)
    Definition Time : Type := nat.
    Definition time_le (t1 t2 : Time) : Prop := t1 <= t2.
    Definition add_time (t1 t2 : Time) : Time := t1 + t2.
     (* Primitive-aligned: use a kernel-defined constant as the epoch and lock
       period, avoiding external clocks in the Phase-1 foundation model. *)
     Definition current_time : Time := K.constitution_hash.
     Definition lock_period : Time := K.constitution_hash.

     (* Slashing model (primitive-aligned): a relation hash is invalidated if it
       is not representable as a constitution-hash extension in the kernel's
       `family_hash` sense. *)
     Definition relation_invalidated (h : K.hash) : Prop :=
      ~ extends K.constitution_hash h.

    Definition relation_invalidated_dec :
      forall h : K.hash, {relation_invalidated h} + {~ relation_invalidated h}.
    Proof.
      intro h.
      unfold relation_invalidated.
      (* For the sealed kernel instance, `extends old new` is equivalent to
         `old <= new` because `family_hash old ext = old + length ext` and we
         can always witness any required length using `repeat` on a fixed
         relation atom. *)
      assert (Hext_le : forall old new, extends old new -> old <= new).
      {
        intros old new [ext Heq].
        subst new.
        unfold K.family_hash, K.combine_hash, K.hash_of_relations.
        simpl.
        lia.
      }
      assert (Hle_ext : forall old new, old <= new -> extends old new).
      {
        intros old new Hle.
        set (n := new - old).
        exists (repeat K.reciprocity_relation n).
        unfold K.family_hash, K.combine_hash, K.hash_of_relations.
        rewrite List.repeat_length.
        unfold n.
        lia.
      }
      destruct (le_lt_dec K.constitution_hash h) as [Hle|Hlt].
      - right.
        intro Hnot.
        apply Hnot.
        apply Hle_ext.
        exact Hle.
      - left.
        intro Hext.
        pose proof (Hext_le _ _ Hext) as Hle.
        lia.
    Defined.

    Theorem extends_refl : forall h, extends h h.
    Proof.
      intro h.
      exists [].
      unfold K.family_hash, K.combine_hash, K.hash_of_relations.
      simpl.
      rewrite Nat.add_0_r.
      reflexivity.
    Qed.

    Theorem extends_trans :
      forall h1 h2 h3, extends h1 h2 -> extends h2 h3 -> extends h1 h3.
    Proof.
      intros h1 h2 h3 H12 H23.
      destruct H12 as [ext12 Heq12].
      destruct H23 as [ext23 Heq23].
      subst h2 h3.
      exists (ext12 ++ ext23).
      unfold K.family_hash, K.combine_hash, K.hash_of_relations.
      rewrite app_length.
      rewrite Nat.add_assoc.
      reflexivity.
    Qed.

    Theorem extends_antisym :
      forall h1 h2, extends h1 h2 -> extends h2 h1 -> h1 = h2.
    Proof.
      intros h1 h2 H12 H21.
      destruct H12 as [ext12 Heq12].
      destruct H21 as [ext21 Heq21].
      subst h2.
      unfold K.family_hash, K.combine_hash, K.hash_of_relations in Heq21.
      simpl in Heq21.
      (* Heq21 : h1 = (h1 + length ext12) + length ext21 *)
      rewrite <- Nat.add_assoc in Heq21.
      (* Heq21 : h1 = h1 + (length ext12 + length ext21) *)
      assert (Hsum0 : List.length ext12 + List.length ext21 = 0).
      {
        assert (Hcancel : h1 + (List.length ext12 + List.length ext21) = h1 + 0).
        {
          rewrite Nat.add_0_r.
          symmetry.
          exact Heq21.
        }
        exact (proj1 (Nat.add_cancel_l (List.length ext12 + List.length ext21) 0 h1) Hcancel).
      }
      assert (Hlen12 : List.length ext12 = 0) by lia.
      unfold K.family_hash, K.combine_hash, K.hash_of_relations.
      simpl.
      rewrite Hlen12.
      rewrite Nat.add_0_r.
      reflexivity.
    Qed.
  End P.

  Module Econ := RelationalEconomics K NatAmountModel P.
End RelationalEconomics_Params_KernelInstanceCurrent_Nat.
