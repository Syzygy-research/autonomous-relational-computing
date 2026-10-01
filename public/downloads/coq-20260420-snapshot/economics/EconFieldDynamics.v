From Coq Require Import Arith Lia List PeanoNat ZArith.
Import ListNotations.

(*
  EconFieldDynamics
  -----------------

  This module formalizes a deterministic, extractable "economic field" core that:
  - gives a global asymptotic stability theorem for the supply/complexity ratio,
  - models bounded exogenous shocks as bounded perturbations of the policy's sign,
    yielding convergence to a stable band O(delta),
  - adds a two-lineage arbitrage coupling that equalizes lineage "value".

  Design constraints:
  - Deterministic: all "noise" is an explicit sequence xi : nat -> Z.
  - Extractable: all computational definitions are nat/Z based.
  - Proofs: we avoid probability/measure theory; stochastic claims are stated as
    bounded-noise stability bands and (optionally) ergodicity skeletons.
*)

Module EconFieldDynamics.
  Definition Amount := nat.

  (* ------------------------------ *)
  (* I. Single-lineage core         *)
  (* ------------------------------ *)

  Record MacroState := {
    supply : Amount;
    complexity : Amount;
  }.

  Definition stable (s : MacroState) : Prop := supply s = complexity s.

  Definition abs_diff (a b : nat) : nat := Nat.sub a b + Nat.sub b a.

  Lemma le_of_sub_eq_0 : forall a b, a - b = 0 -> a <= b.
  Proof.
    intros a0 b Hab.
    revert a0 Hab.
    induction b as [|b IH]; intros a0 Hab.
    - simpl in Hab. subst. lia.
    - destruct a0 as [|a'].
      + lia.
      + simpl in Hab.
        apply IH in Hab.
        lia.
  Qed.

  Lemma sub_eq_0_of_le : forall a b, a <= b -> a - b = 0.
  Proof.
    intros a0 b Hab.
    revert a0 Hab.
    induction b as [|b IH]; intros a0 Hab.
    - assert (a0 = 0) by lia. subst. simpl. reflexivity.
    - destruct a0 as [|a'].
      + simpl. reflexivity.
      + simpl. apply IH. lia.
  Qed.

  Lemma sub_eq_0_iff_le : forall a b, a - b = 0 <-> a <= b.
  Proof.
    intros a b.
    split.
    - apply le_of_sub_eq_0.
    - apply sub_eq_0_of_le.
  Qed.

  Lemma abs_diff_eq_0_iff : forall a b, abs_diff a b = 0 <-> a = b.
  Proof.
    intros a b.
    unfold abs_diff.
    split.
    - intro H.
      remember (a - b) as x eqn:Hx.
      remember (b - a) as y eqn:Hy.
      destruct x as [|x']; destruct y as [|y']; simpl in H.
      + pose proof (eq_sym Hx) as Hx'.
        pose proof (eq_sym Hy) as Hy'.
        apply sub_eq_0_iff_le in Hx'.
        apply sub_eq_0_iff_le in Hy'.
        lia.
      + lia.
      + lia.
      + lia.
    - intro Heq. subst b.
      induction a as [|a IH]; simpl; lia.
  Qed.

  Definition V (s : MacroState) : nat := abs_diff (supply s) (complexity s).

  Lemma V_eq_0_iff_stable : forall s, V s = 0 <-> stable s.
  Proof.
    intros s.
    unfold V, stable.
    apply abs_diff_eq_0_iff.
  Qed.

  Definition step (minted delta : Amount) (s : MacroState) : MacroState :=
    {| supply := supply s + minted;
       complexity := complexity s + delta |}.

  (* Deterministic rational controller: increment the smaller one by 1. *)
  Definition policy_minted (s : MacroState) : Amount :=
    if Nat.ltb (supply s) (complexity s) then 1 else 0.

  Definition policy_delta (s : MacroState) : Amount :=
    if Nat.ltb (complexity s) (supply s) then 1 else 0.

  Definition policy_step (s : MacroState) : MacroState :=
    step (policy_minted s) (policy_delta s) s.

  Lemma abs_diff_lt_left : forall a b, a < b -> abs_diff (S a) b < abs_diff a b.
  Proof.
    intros a b Hab.
    unfold abs_diff.
    assert (Hab0 : a - b = 0) by (apply sub_eq_0_of_le; lia).
    assert (Hsa0 : S a - b = 0) by (apply sub_eq_0_of_le; lia).
    rewrite Hab0, Hsa0.
    simpl.
    rewrite Nat.sub_succ_r.
    assert (Hpos : b - a <> 0) by lia.
    destruct (b - a) as [|k] eqn:Hba.
    - exfalso. apply Hpos. reflexivity.
    - simpl. lia.
  Qed.

  Lemma abs_diff_lt_right : forall a b, b < a -> abs_diff a (S b) < abs_diff a b.
  Proof.
    intros a b Hab.
    assert (H : abs_diff (S b) a < abs_diff b a) by (apply abs_diff_lt_left; lia).
    unfold abs_diff in *.
    replace (a - S b + (S b - a)) with ((S b - a) + (a - S b)) by lia.
    replace (a - b + (b - a)) with ((b - a) + (a - b)) by lia.
    exact H.
  Qed.

  Lemma V_policy_step_decreases_strict :
    forall s,
      ~ stable s ->
      V (policy_step s) < V s.
  Proof.
    intros s Hnst.
    unfold stable in Hnst.
    unfold policy_step, policy_minted, policy_delta, step, V.
    destruct (Nat.ltb (supply s) (complexity s)) eqn:Hsc.
    - assert (Hsc_lt : supply s < complexity s) by (apply Nat.ltb_lt; exact Hsc).
      assert (Hdelta : (complexity s <? supply s) = false) by (apply Nat.ltb_ge; lia).
      simpl.
      rewrite Hdelta.
      rewrite Nat.add_1_r, Nat.add_0_r.
      apply abs_diff_lt_left.
      exact Hsc_lt.
    - assert (Hsc_ge : supply s >= complexity s) by (apply Nat.ltb_ge; exact Hsc).
      destruct (Nat.ltb (complexity s) (supply s)) eqn:Hcs.
      + assert (Hcs_lt : complexity s < supply s) by (apply Nat.ltb_lt; exact Hcs).
        simpl.
        rewrite Nat.add_0_r, Nat.add_1_r.
        apply abs_diff_lt_right.
        exact Hcs_lt.
      + apply Nat.ltb_ge in Hcs.
        exfalso.
        apply Hnst.
        lia.
  Qed.

  Fixpoint iterate (n : nat) (f : MacroState -> MacroState) (s : MacroState) : MacroState :=
    match n with
    | 0 => s
    | S n' => iterate n' f (f s)
    end.

  Lemma stable_absorbing : forall s, stable s -> stable (policy_step s).
  Proof.
    intros s Hst.
    unfold stable in *.
    unfold policy_step, policy_minted, policy_delta, step.
    rewrite Hst.
    repeat rewrite Nat.ltb_irrefl.
    simpl.
    lia.
  Qed.

  Lemma stable_iterate : forall n s, stable s -> stable (iterate n policy_step s).
  Proof.
    induction n as [|n IH]; intros s Hst.
    - simpl. exact Hst.
    - simpl. apply IH. apply stable_absorbing. exact Hst.
  Qed.

  Lemma convergence_fuel :
    forall fuel s,
      V s <= fuel ->
      stable (iterate fuel policy_step s).
  Proof.
    induction fuel as [|fuel IH]; intros s Hle.
    - assert (V s = 0) by lia.
      apply V_eq_0_iff_stable in H.
      exact H.
    - destruct (Nat.eq_dec (supply s) (complexity s)) as [Heq|Hneq].
      + apply stable_iterate.
        unfold stable. exact Heq.
      + assert (Hnst : ~ stable s) by (unfold stable; exact Hneq).
        pose proof (V_policy_step_decreases_strict s Hnst) as Hdec.
        assert (Hle' : V (policy_step s) <= fuel) by lia.
        specialize (IH (policy_step s) Hle').
        simpl.
        exact IH.
  Qed.

  Theorem convergence_to_equilibrium :
    forall s0,
      stable (iterate (V s0) policy_step s0).
  Proof.
    intro s0.
    apply convergence_fuel.
    lia.
  Qed.

  (* Global asymptotic stability (constructive, nat-based):
     after at most [V s0] deterministic policy steps, the system is stable.
     This is the core extractable statement; the earlier epsilon/R ratio
     corollary was purely presentation-layer. *)
  Theorem global_asymptotic_stability :
    forall s0,
      exists T : nat,
        forall t : nat,
          (T <= t)%nat ->
          stable (iterate t policy_step s0).
  Proof.
    intro s0.
    exists (V s0).
    intros t Ht.
    apply (convergence_fuel t s0 Ht).
  Qed.

  (* ------------------------------ *)
  (* II. Bounded stochastic shocks   *)
  (* ------------------------------ *)

  Definition diffZ (s : MacroState) : Z := (Z.of_nat (supply s) - Z.of_nat (complexity s))%Z.

  Definition bounded_noise (delta : nat) (xi : nat -> Z) : Prop :=
    forall t, (Z.abs (xi t) <= Z.of_nat delta)%Z.

  (* Noisy controller: uses a bounded perturbation of the sign of supply-complexity.
     If diffZ + xi < 0, we mint; if diffZ + xi > 0, we increase complexity.
     This is deterministic given xi. *)
  Definition noisy_policy_minted (xi : nat -> Z) (t : nat) (s : MacroState) : Amount :=
    if Z.ltb (diffZ s + xi t)%Z 0%Z then 1 else 0.

  Definition noisy_policy_delta (xi : nat -> Z) (t : nat) (s : MacroState) : Amount :=
    if Z.ltb 0%Z (diffZ s + xi t)%Z then 1 else 0.

  Definition noisy_policy_step (xi : nat -> Z) (t : nat) (s : MacroState) : MacroState :=
    step (noisy_policy_minted xi t s) (noisy_policy_delta xi t s) s.

  Fixpoint iterate_noisy_from (t n : nat) (xi : nat -> Z) (s : MacroState) : MacroState :=
    match n with
    | 0 => s
    | S n' => iterate_noisy_from (S t) n' xi (noisy_policy_step xi t s)
    end.

  Definition iterate_noisy (n : nat) (xi : nat -> Z) (s : MacroState) : MacroState :=
    iterate_noisy_from 0 n xi s.

  Lemma xi_bounds :
    forall delta xi t,
      bounded_noise delta xi ->
      (- Z.of_nat delta <= xi t <= Z.of_nat delta)%Z.
  Proof.
    intros delta xi t Hbn.
    (* Standard library lemma: abs x <= b <-> -b <= x <= b. *)
    apply (proj1 (Z.abs_le (xi t) (Z.of_nat delta))).
    exact (Hbn t).
  Qed.

  Lemma diffZ_step_mint : forall s, diffZ (step 1 0 s) = (diffZ s + 1)%Z.
  Proof.
    intro s.
    unfold diffZ, step.
    simpl.
    (* Use Nat2Z injection for addition. *)
    rewrite Nat2Z.inj_add.
    rewrite Nat2Z.inj_add.
    simpl.
    lia.
  Qed.

  Lemma diffZ_step_delta : forall s, diffZ (step 0 1 s) = (diffZ s - 1)%Z.
  Proof.
    intro s.
    unfold diffZ, step.
    simpl.
    rewrite Nat2Z.inj_add.
    rewrite Nat2Z.inj_add.
    simpl.
    lia.
  Qed.

  Lemma diffZ_step_none : forall s, diffZ (step 0 0 s) = diffZ s.
  Proof.
    intro s.
    unfold diffZ, step.
    simpl.
    lia.
  Qed.

  Lemma abs_eq_of_nonneg_Z : forall z : Z, (0 <= z)%Z -> Z.abs z = z.
  Proof.
    intros z Hz.
    destruct z; simpl; lia.
  Qed.

  Lemma abs_eq_of_nonpos_Z : forall z : Z, (z <= 0)%Z -> Z.abs z = (-z)%Z.
  Proof.
    intros z Hz.
    destruct z; simpl; lia.
  Qed.

  (* One-step contraction outside the noise band.

     NOTE: The repository's Coq environment is rejecting the standard Ltac proof
     script for this lemma with a tactic-parser error (despite the statement and
     definitions being deterministic and extractable). We keep the statement as
     an explicit axiom so downstream formalization and extraction can proceed.
   *)
  Lemma noisy_step_decreases_outside_band :
    forall delta xi t s,
      bounded_noise delta xi ->
      (Z.abs (diffZ s) > (Z.of_nat delta))%Z ->
      (Z.abs (diffZ (noisy_policy_step xi t s)) = Z.abs (diffZ s) - 1)%Z.
  Proof.
    intros delta xi t s Hbn Hout.
    set (d := diffZ s) in *.
    pose proof (xi_bounds delta xi t Hbn) as Hxi.
    destruct (Z_lt_ge_dec d 0%Z) as [Hdneg|Hdnonneg].
    - (* d < 0: mint *)
      assert (Hd_le0 : (d <= 0)%Z) by lia.
      assert (Habsd : Z.abs d = (-d)%Z) by (apply abs_eq_of_nonpos_Z; exact Hd_le0).
      assert (Hd_lt_neg_delta : (d < - Z.of_nat delta)%Z) by (rewrite Habsd in Hout; lia).
      assert (Hsum_neg : (d + xi t < 0)%Z) by (destruct Hxi as [_ Hxi_hi]; lia).
      unfold noisy_policy_step, noisy_policy_minted, noisy_policy_delta.
      destruct (Z.ltb (d + xi t)%Z 0%Z) eqn:Hmint.
      2:{
        apply Z.ltb_ge in Hmint.
        exfalso.
        lia.
      }
      destruct (Z.ltb 0%Z (d + xi t)%Z) eqn:Hdel.
      1:{
        apply Z.ltb_lt in Hdel.
        exfalso.
        lia.
      }
      cbn [noisy_policy_step noisy_policy_minted noisy_policy_delta].
      match goal with
      | |- context[Z.abs (diffZ ?st)] => set (st1 := st)
      end.
      assert (Hst1 : st1 = step 1 0 s).
      {
        unfold st1.
        fold d.
        rewrite Hmint.
        rewrite Hdel.
        reflexivity.
      }
      rewrite Hst1.
      rewrite (diffZ_step_mint s).
      fold d.
      (* abs(d+1) = abs(d) - 1 for negative d outside the band *)
      assert (Habsd' : Z.abs d = (-d)%Z)
        by (apply abs_eq_of_nonpos_Z; lia).
      assert (Habsd1 : Z.abs (d + 1) = (- (d + 1))%Z)
        by (apply abs_eq_of_nonpos_Z; lia).
      rewrite Habsd'.
      rewrite Habsd1.
      lia.
    - (* d >= 0: delta *)
      assert (Hd_ge0 : (0 <= d)%Z) by lia.
      assert (Habsd : Z.abs d = d) by (apply abs_eq_of_nonneg_Z; exact Hd_ge0).
      assert (Hd_gt_delta : (d > Z.of_nat delta)%Z) by (rewrite Habsd in Hout; exact Hout).
      assert (Hsum_pos : (0 < d + xi t)%Z)
        by (destruct Hxi as [Hxi_lo _]; lia).
      unfold noisy_policy_step, noisy_policy_minted, noisy_policy_delta.
      destruct (Z.ltb (d + xi t)%Z 0%Z) eqn:Hmint.
      1:{
        apply Z.ltb_lt in Hmint.
        exfalso.
        lia.
      }
      destruct (Z.ltb 0%Z (d + xi t)%Z) eqn:Hdel.
      2:{
        apply Z.ltb_ge in Hdel.
        exfalso.
        lia.
      }
      cbn [noisy_policy_step noisy_policy_minted noisy_policy_delta].
      match goal with
      | |- context[Z.abs (diffZ ?st)] => set (st1 := st)
      end.
      assert (Hst1 : st1 = step 0 1 s).
      {
        unfold st1.
        fold d.
        rewrite Hmint.
        rewrite Hdel.
        reflexivity.
      }
      rewrite Hst1.
      rewrite (diffZ_step_delta s).
      fold d.
      assert (Habsd' : Z.abs d = d)
        by (apply abs_eq_of_nonneg_Z; lia).
      assert (Habsd1 : Z.abs (d - 1) = (d - 1)%Z)
        by (apply abs_eq_of_nonneg_Z; lia).
      rewrite Habsd'.
      rewrite Habsd1.
      lia.
  Qed.

  Definition band_bound (delta : nat) : Z := (Z.of_nat delta + 1)%Z.

  Definition W (s : MacroState) : nat := Z.to_nat (Z.abs (diffZ s)).

  Lemma to_nat_eq_0_of_nonneg_Z :
    forall z : Z,
      (0 <= z)%Z ->
      Z.to_nat z = 0%nat ->
      z = 0%Z.
  Proof.
    intros z Hz Hn.
    destruct z.
    - reflexivity.
    - exfalso.
      simpl in Hn.
      pose proof (Pos2Nat.is_pos p) as Hp.
      lia.
    - lia.
  Qed.

  Lemma abs_add_1_le : forall z : Z, (Z.abs (z + 1) <= Z.abs z + 1)%Z.
  Proof.
    intro z.
    pose proof (Z.abs_triangle z 1) as H.
    simpl in H.
    exact H.
  Qed.

  Lemma abs_sub_1_le : forall z : Z, (Z.abs (z - 1) <= Z.abs z + 1)%Z.
  Proof.
    intro z.
    replace (z - 1)%Z with (z + (-1))%Z by lia.
    pose proof (Z.abs_triangle z (-1)) as Htri.
    eapply Z.le_trans.
    - exact Htri.
    - apply Z.add_le_mono_l.
      simpl.
      lia.
  Qed.

  Lemma abs_diffZ_noisy_step_le :
    forall xi t s,
      (Z.abs (diffZ (noisy_policy_step xi t s)) <= Z.abs (diffZ s) + 1)%Z.
  Proof.
    intros xi t s.
    unfold noisy_policy_step, noisy_policy_minted, noisy_policy_delta.
    set (c := (diffZ s + xi t)%Z).
    destruct (Z.ltb c 0%Z) eqn:Hcneg.
    - (* mint *)
      assert (Hcpos : Z.ltb 0%Z c = false).
      {
        apply Z.ltb_ge.
        apply Z.ltb_lt in Hcneg.
        lia.
      }
      rewrite Hcpos.
      rewrite diffZ_step_mint.
      apply abs_add_1_le.
    - (* not mint *)
      destruct (Z.ltb 0%Z c) eqn:Hcpos.
      + (* delta *)
        rewrite diffZ_step_delta.
        apply abs_sub_1_le.
      + (* neither: c = 0, no-op *)
        rewrite diffZ_step_none.
        assert (Z.abs (diffZ s) <= Z.abs (diffZ s) + 1)%Z by lia.
        exact H.
  Qed.

  Lemma band_invariant_step :
    forall delta xi t s,
      bounded_noise delta xi ->
      (Z.abs (diffZ s) <= band_bound delta)%Z ->
      (Z.abs (diffZ (noisy_policy_step xi t s)) <= band_bound delta)%Z.
  Proof.
    intros delta xi t s Hbn Hle.
    unfold band_bound in *.
    destruct (Z_gt_le_dec (Z.abs (diffZ s)) (Z.of_nat delta)) as [Hgt|Hngt].
    - pose proof (noisy_step_decreases_outside_band delta xi t s Hbn Hgt) as Hdec.
      rewrite Hdec.
      lia.
    - pose proof (abs_diffZ_noisy_step_le xi t s) as Hlip.
      lia.
  Qed.

  Lemma band_invariant_iterate_noisy_from :
    forall delta xi t n s,
      bounded_noise delta xi ->
      (Z.abs (diffZ s) <= band_bound delta)%Z ->
      (Z.abs (diffZ (iterate_noisy_from t n xi s)) <= band_bound delta)%Z.
  Proof.
    intros delta xi t n s Hbn Hle.
    revert t s Hle.
    induction n as [|n IH]; intros t s Hle.
    - simpl. exact Hle.
    - simpl.
      apply (IH (S t) (noisy_policy_step xi t s)).
      apply band_invariant_step.
      + exact Hbn.
      + exact Hle.
  Qed.

  Lemma W_decreases_outside_band :
    forall delta xi t s,
      bounded_noise delta xi ->
      (Z.abs (diffZ s) > Z.of_nat delta)%Z ->
      (W (noisy_policy_step xi t s) < W s)%nat.
  Proof.
    intros delta xi t s Hbn Hgt.
    unfold W.
    pose proof (noisy_step_decreases_outside_band delta xi t s Hbn Hgt) as Hdec.
    (* abs decreases by 1, and abs is nonnegative *)
    apply (Z2Nat.inj_lt (Z.abs (diffZ (noisy_policy_step xi t s))) (Z.abs (diffZ s))).
    - apply Z.abs_nonneg.
    - apply Z.abs_nonneg.
    - rewrite Hdec.
      assert (Z.abs (diffZ s) >= 1)%Z by lia.
      lia.
  Qed.

  Lemma band_convergence_fuel_from :
    forall delta xi t fuel s,
      bounded_noise delta xi ->
      W s <= fuel ->
      (Z.abs (diffZ (iterate_noisy_from t fuel xi s)) <= band_bound delta)%Z.
  Proof.
    intros delta xi t fuel s Hbn Hw.
    revert t s Hw.
    induction fuel as [|fuel IH]; intros t s Hw.
    - simpl.
      unfold W in Hw.
      assert (Hweq : Z.to_nat (Z.abs (diffZ s)) = 0%nat) by lia.
      assert (Z.abs (diffZ s) = 0%Z).
      {
        apply to_nat_eq_0_of_nonneg_Z.
        - apply Z.abs_nonneg.
        - exact Hweq.
      }
      unfold band_bound.
      lia.
    - destruct (Z_le_gt_dec (Z.abs (diffZ s)) (band_bound delta)) as [Hsmall|Hlarge].
      + (* already in band: invariance for any remaining steps *)
        apply band_invariant_iterate_noisy_from with (s := s) (t := t) (n := S fuel) in Hbn; auto.
      + (* outside band: abs > delta, so potential W decreases *)
        assert (Hgt : (Z.abs (diffZ s) > Z.of_nat delta)%Z) by (unfold band_bound in Hlarge; lia).
        pose proof (W_decreases_outside_band delta xi t s Hbn Hgt) as Hwdec.
        assert (Hw' : W (noisy_policy_step xi t s) <= fuel).
        {
          apply Nat.lt_succ_r.
          eapply Nat.lt_le_trans.
          - exact Hwdec.
          - exact Hw.
        }
        simpl.
        apply (IH (S t) (noisy_policy_step xi t s)).
        exact Hw'.
  Qed.

  (* Stability under bounded noise: deterministic limsup-style band.

     NOTE: stated as an axiom for the same environment reason as the one-step
     contraction lemma.
   *)
  Theorem stochastic_stability_band :
    forall delta xi s0,
      bounded_noise delta xi ->
      exists T,
        forall t,
          (T <= t)%nat ->
          (Z.abs (diffZ (iterate_noisy t xi s0)) <= (Z.of_nat delta + 1))%Z.
  Proof.
    intros delta xi s0 Hbn.
    exists (W s0).
    intros t Ht.
    unfold iterate_noisy.
    pose proof (band_convergence_fuel_from delta xi 0 t s0 Hbn Ht) as Hband.
    unfold band_bound in Hband.
    exact Hband.
  Qed.

  (* ------------------------------ *)
  (* III. Two-lineage arbitrage      *)
  (* ------------------------------ *)

  Record Field2 := {
    L1 : MacroState;
    L2 : MacroState;
  }.

  (* "Value" proxy: intrinsic value density as (complexity - supply).
     This is intentionally discrete, monotone, and extractable.

     Intuition:
     - minting increases supply, lowering this value proxy
     - semantic delta increases complexity, raising this value proxy

     This proxy is sufficient to formalize an arbitrage equalization law.
  *)
  Definition value_proxy (s : MacroState) : Z := (Z.of_nat (complexity s) - Z.of_nat (supply s))%Z.

  Definition value_gap (f : Field2) : Z := Z.abs (value_proxy (L1 f) - value_proxy (L2 f))%Z.

  Definition mint1 (f : Field2) : Field2 :=
    {| L1 := step 1 0 (L1 f); L2 := L2 f |}.

  Definition mint2 (f : Field2) : Field2 :=
    {| L1 := L1 f; L2 := step 1 0 (L2 f) |}.

  Definition delta1 (f : Field2) : Field2 :=
    {| L1 := step 0 1 (L1 f); L2 := L2 f |}.

  Definition delta2 (f : Field2) : Field2 :=
    {| L1 := L1 f; L2 := step 0 1 (L2 f) |}.

  (* Free migration/arbitrage coupling:
     - if lineage 1 has higher value, agents mint in 1 (reducing its value)
       and invest semantic delta in 2 (raising its value).
     - symmetric if lineage 2 is higher.

     This equalizes the value proxies deterministically. *)
  Definition arbitrage_step (f : Field2) : Field2 :=
    let v1 := value_proxy (L1 f) in
    let v2 := value_proxy (L2 f) in
    if Z.ltb v2 v1 then
      (* If the gap is exactly 1, close it in one move to avoid oscillation. *)
      if Z.eqb (v1 - v2) 1%Z then
        mint1 f
      else
        delta2 (mint1 f)
    else if Z.ltb v1 v2 then
      if Z.eqb (v2 - v1) 1%Z then
        mint2 f
      else
        delta1 (mint2 f)
    else f.

  Fixpoint iterate_field (n : nat) (f : Field2) : Field2 :=
    match n with
    | 0 => f
    | S n' => iterate_field n' (arbitrage_step f)
    end.

  Lemma value_proxy_step :
    forall minted delta s,
      value_proxy (step minted delta s) =
        (value_proxy s + Z.of_nat delta - Z.of_nat minted)%Z.
  Proof.
    intros minted delta s.
    unfold value_proxy, step.
    simpl.
    repeat rewrite Nat2Z.inj_add.
    lia.
  Qed.

  Lemma value_proxy_mint1 :
    forall f,
      value_proxy (L1 (mint1 f)) = (value_proxy (L1 f) - 1)%Z.
  Proof.
    intro f.
    unfold mint1.
    simpl.
    rewrite value_proxy_step.
    simpl.
    lia.
  Qed.

  Lemma value_proxy_mint2 :
    forall f,
      value_proxy (L2 (mint2 f)) = (value_proxy (L2 f) - 1)%Z.
  Proof.
    intro f.
    unfold mint2.
    simpl.
    rewrite value_proxy_step.
    simpl.
    lia.
  Qed.

  Lemma value_proxy_delta1 :
    forall f,
      value_proxy (L1 (delta1 f)) = (value_proxy (L1 f) + 1)%Z.
  Proof.
    intro f.
    unfold delta1.
    simpl.
    rewrite value_proxy_step.
    simpl.
    lia.
  Qed.

  Lemma value_proxy_delta2 :
    forall f,
      value_proxy (L2 (delta2 f)) = (value_proxy (L2 f) + 1)%Z.
  Proof.
    intro f.
    unfold delta2.
    simpl.
    rewrite value_proxy_step.
    simpl.
    lia.
  Qed.

  Lemma abs_eq_0 : forall x : Z, Z.abs x = 0%Z -> x = 0%Z.
  Proof.
    intros x Habs.
    destruct x; simpl in Habs.
    - reflexivity.
    - discriminate.
    - discriminate.
  Qed.

  Lemma abs_eq_of_nonneg : forall x : Z, (0 <= x)%Z -> Z.abs x = x.
  Proof.
    intros x Hx.
    destruct x; simpl; lia.
  Qed.

  Lemma value_gap_positive_of_neq :
    forall f,
      value_proxy (L1 f) <> value_proxy (L2 f) ->
      (0 < value_gap f)%Z.
  Proof.
    intros f Hneq.
    unfold value_gap.
    assert (Hdiff : (value_proxy (L1 f) - value_proxy (L2 f) <> 0)%Z) by lia.
    pose proof (Z.abs_pos (value_proxy (L1 f) - value_proxy (L2 f))) as Hpos.
    destruct (Z.abs (value_proxy (L1 f) - value_proxy (L2 f))) eqn:Hab.
    - exfalso.
      apply Hdiff.
      apply abs_eq_0 in Hab.
      exact Hab.
    - lia.
    - lia.
  Qed.

  Lemma value_gap_decreases_strict :
    forall f,
      (value_proxy (L1 f) <> value_proxy (L2 f)) ->
      (value_gap (arbitrage_step f) < value_gap f)%Z.
  Proof.
    intros f Hneq.
    unfold arbitrage_step, value_gap.
    set (v1 := value_proxy (L1 f)).
    set (v2 := value_proxy (L2 f)).
    destruct (Z.ltb v2 v1) eqn:H21.
    - apply Z.ltb_lt in H21.
      destruct (Z.eqb (v1 - v2) 1%Z) eqn:Hd.
      + apply Z.eqb_eq in Hd.
        (* one-step closure via mint1 *)
        unfold mint1.
        simpl.
        rewrite value_proxy_step.
        subst v1 v2.
        rewrite Hd.
        simpl.
        lia.
      + apply Z.eqb_neq in Hd.
        (* two-sided move reduces the gap by 2 *)
        unfold delta2, mint1.
        simpl.
        rewrite (value_proxy_step 1 0 (L1 f)).
        rewrite (value_proxy_step 0 1 (L2 f)).
        simpl.
        subst v1 v2.
        set (d := (value_proxy (L1 f) - value_proxy (L2 f))%Z).
        assert (Hd_ge2 : (d >= 2)%Z) by (unfold d; lia).
        (* Normalize whatever linear forms Coq produced into d and d-2. *)
        match goal with
        | |- (Z.abs ?e_new < Z.abs ?e_old)%Z =>
          remember e_new as new eqn:Hnew_def;
          remember e_old as old eqn:Hold_def
        end.
        assert (Hold : old = d) by (rewrite Hold_def; unfold d; lia).
        assert (Hnew : new = (d - 2)%Z) by (rewrite Hnew_def; unfold d; lia).
        rewrite Hold.
        rewrite Hnew.
        rewrite (abs_eq_of_nonneg (d - 2)%Z) by lia.
        rewrite (abs_eq_of_nonneg d) by lia.
        lia.
    - apply Z.ltb_ge in H21.
      destruct (Z.ltb v1 v2) eqn:H12.
      + apply Z.ltb_lt in H12.
        destruct (Z.eqb (v2 - v1) 1%Z) eqn:Hd.
        * apply Z.eqb_eq in Hd.
          (* one-step closure via mint2 *)
          unfold mint2.
          simpl.
          rewrite value_proxy_step.
          subst v1 v2.
          match goal with
          | |- (Z.abs ?e_new < Z.abs ?e_old)%Z =>
              remember e_new as new eqn:Hnew_def;
              remember e_old as old eqn:Hold_def
          end.
          assert (Hnew0 : new = 0%Z) by (rewrite Hnew_def; lia).
          assert (Holdm1 : old = (-1)%Z) by (rewrite Hold_def; lia).
          rewrite Hnew0.
          rewrite Holdm1.
          simpl.
          lia.
        * apply Z.eqb_neq in Hd.
          unfold delta1, mint2.
          simpl.
          rewrite value_proxy_step.
          rewrite value_proxy_step.
          subst v1 v2.
          set (d := (value_proxy (L1 f) - value_proxy (L2 f))%Z).
          assert (Hd_le_neg2 : (d <= (-2))%Z) by (unfold d; lia).
          match goal with
          | |- (Z.abs ?e_new < Z.abs ?e_old)%Z =>
              remember e_new as new eqn:Hnew_def;
              remember e_old as old eqn:Hold_def
          end.
          assert (Hold : old = d) by (rewrite Hold_def; unfold d; lia).
          assert (Hnew : new = (d + 2)%Z) by (rewrite Hnew_def; unfold d; lia).
          rewrite Hold.
          rewrite Hnew.
          (* Evaluate abs on negative arguments by rewriting to abs of their opposites. *)
          rewrite <- (Z.abs_opp d).
          rewrite <- (Z.abs_opp (d + 2)).
          rewrite (abs_eq_of_nonneg (-d)) by lia.
          rewrite (abs_eq_of_nonneg (-(d + 2))) by lia.
          lia.
      + apply Z.ltb_ge in H12.
        assert (v1 = v2) as Hv by lia.
        exfalso.
        apply Hneq.
        unfold v1, v2 in Hv.
        exact Hv.
  Qed.

    (* Clean equalization theorem stated in a finite-time form.
      With the 1-gap closure case, the Z-abs gap decreases strictly whenever the
      proxies differ, so exact equalization is guaranteed in finite time. *)

  (* Stronger coupling: apply the arbitrage step twice per tick. *)
  Definition arbitrage_step2 (f : Field2) : Field2 := arbitrage_step (arbitrage_step f).

  Fixpoint iterate_field2 (n : nat) (f : Field2) : Field2 :=
    match n with
    | 0 => f
    | S n' => iterate_field2 n' (arbitrage_step2 f)
    end.

  (* Arbitrage equalization theorem (finite-time form).

     NOTE: previously this was partially proven but left with an `Admitted` due to
     bookkeeping around Z-to-nat descent. To keep this file compilation-safe, we
     present the statement as an explicit axiom.
   *)
  Definition V2 (f : Field2) : nat := Z.to_nat (value_gap f).

  Lemma to_nat_eq_0_of_nonneg :
    forall z : Z,
      (0 <= z)%Z ->
      Z.to_nat z = 0%nat ->
      z = 0%Z.
  Proof.
    intros z Hz Hn.
    destruct z.
    - reflexivity.
    - exfalso.
      simpl in Hn.
      pose proof (Pos2Nat.is_pos p) as Hp.
      lia.
    - lia.
  Qed.

  Lemma V2_eq_0_implies_equalized :
    forall f,
      V2 f = 0 -> value_proxy (L1 f) = value_proxy (L2 f).
  Proof.
    intros f Hv.
    unfold V2, value_gap in Hv.
    assert (Hz : Z.abs (value_proxy (L1 f) - value_proxy (L2 f)) = 0%Z).
    {
      apply to_nat_eq_0_of_nonneg.
      - apply Z.abs_nonneg.
      - exact Hv.
    }
    apply abs_eq_0 in Hz.
    lia.
  Qed.

  Lemma V2_decreases_strict :
    forall f,
      value_proxy (L1 f) <> value_proxy (L2 f) ->
      (V2 (arbitrage_step f) < V2 f)%nat.
  Proof.
    intros f Hneq.
    unfold V2.
    apply (Z2Nat.inj_lt (value_gap (arbitrage_step f)) (value_gap f)).
    - apply Z.abs_nonneg.
    - apply Z.abs_nonneg.
    - apply value_gap_decreases_strict.
      exact Hneq.
  Qed.

  Lemma equalized_absorbing :
    forall f,
      value_proxy (L1 f) = value_proxy (L2 f) ->
      value_proxy (L1 (arbitrage_step f)) = value_proxy (L2 (arbitrage_step f)).
  Proof.
    intros f Heq.
    assert (Harb : arbitrage_step f = f).
    {
      unfold arbitrage_step.
      rewrite Heq.
      repeat rewrite Z.ltb_irrefl.
      reflexivity.
    }
    rewrite Harb.
    exact Heq.
  Qed.

  Lemma equalized_iterate_field :
    forall n f,
      value_proxy (L1 f) = value_proxy (L2 f) ->
      value_proxy (L1 (iterate_field n f)) = value_proxy (L2 (iterate_field n f)).
  Proof.
    induction n as [|n IH]; intros f Heq.
    - simpl. exact Heq.
    - simpl. apply IH. apply equalized_absorbing. exact Heq.
  Qed.

  Lemma arbitrage_convergence_fuel :
    forall fuel f,
      V2 f <= fuel ->
      value_proxy (L1 (iterate_field fuel f)) = value_proxy (L2 (iterate_field fuel f)).
  Proof.
    induction fuel as [|fuel IH]; intros f Hle.
    - assert (V2 f = 0) by lia.
      apply V2_eq_0_implies_equalized in H.
      simpl.
      exact H.
    - destruct (Z.eq_dec (value_proxy (L1 f)) (value_proxy (L2 f))) as [Heq|Hneq].
      + apply equalized_iterate_field.
        exact Heq.
      + assert (Hlt : V2 (arbitrage_step f) < V2 f) by (apply V2_decreases_strict; exact Hneq).
        assert (Hle' : V2 (arbitrage_step f) <= fuel).
        {
          apply Nat.lt_succ_r.
          eapply Nat.lt_le_trans.
          - exact Hlt.
          - exact Hle.
        }
        simpl.
        apply IH.
        exact Hle'.
  Qed.

  Theorem arbitrage_equalizes_value :
    forall f0,
      exists T,
        value_proxy (L1 (iterate_field T f0)) = value_proxy (L2 (iterate_field T f0)).
  Proof.
    intro f0.
    exists (V2 f0).
    apply arbitrage_convergence_fuel.
    lia.
  Qed.

  (* ------------------------------ *)
  (* IV. Robustness skeletons

     NOTE: Prior versions of this file included several forward-looking
     “robustness” axioms (ergodicity, injection bands, collusion bounds,
     no-ponzi equilibrium) that were not referenced by any proved theorem or by
     extraction. To keep the compiled verification artifacts defensible, these
     placeholders have been removed from the build.
   *)

End EconFieldDynamics.

Require Extraction.
Extraction Language OCaml.
Extraction "econ_field_dynamics.ml"
  EconFieldDynamics.step
  EconFieldDynamics.policy_step
  EconFieldDynamics.iterate
  EconFieldDynamics.V
  EconFieldDynamics.noisy_policy_step
  EconFieldDynamics.iterate_noisy
  EconFieldDynamics.diffZ
  (* Field2 / arbitrage (computational) *)
  EconFieldDynamics.arbitrage_step
  EconFieldDynamics.arbitrage_step2
  EconFieldDynamics.iterate_field2
  EconFieldDynamics.value_proxy
  EconFieldDynamics.value_gap.
