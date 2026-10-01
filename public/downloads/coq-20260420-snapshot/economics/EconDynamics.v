From Coq Require Import List Arith Lia PeanoNat.
Import ListNotations.

(* This file is intentionally nat-based so we can prove convergence
   constructively (bounded, well-founded decrease on a Nat Lyapunov measure)
   and extract runnable OCaml with minimal runtime dependencies. *)

Module EconDynamics.
  Definition Amount := nat.

  Definition Ledger : Type := list Amount.

  Definition total_supply (L : Ledger) : Amount := fold_left Nat.add L 0.

  (* A minimal "complexity" accumulator. For now we keep it independent from
     the ledger so dynamics can model regimes where supply and complexity drift
     differently. *)

  Record EconState := {
    ledger : Ledger;
    total_supply_s : Amount;
    total_complexity_s : Amount;
    stake_price_s : Amount;
  }.

  Definition intrinsic_value (s : EconState) : Amount :=
    Nat.div (total_complexity_s s) (S (total_supply_s s)).

  Definition dynamic_stake_required (s : EconState) : Amount :=
    Nat.div (total_supply_s s) (S (total_complexity_s s)).

  Definition abs_diff (a b : nat) : nat :=
    Nat.sub a b + Nat.sub b a.

  Lemma le_of_sub_eq_0 : forall a b, a - b = 0 -> a <= b.
  Proof.
    intros a0 b Hab.
    revert a0 Hab.
    induction b as [|b IH]; intros a0 Hab.
    - simpl in Hab. subst. lia.
    - destruct a0 as [|a'].
      + lia.
      + simpl in Hab.
        (* (S a') - (S b) = a' - b *)
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

  Definition V (s : EconState) : nat :=
    abs_diff (total_supply_s s) (total_complexity_s s).

  Definition stable (s : EconState) : Prop :=
    total_supply_s s = total_complexity_s s.

  Definition step (minted delta : Amount) (s : EconState) : EconState :=
    let supply' := total_supply_s s + minted in
    let complexity' := total_complexity_s s + delta in
    {| ledger := ledger s;
       total_supply_s := supply';
       total_complexity_s := complexity';
       stake_price_s := dynamic_stake_required
                         {| ledger := ledger s;
                            total_supply_s := supply';
                            total_complexity_s := complexity';
                            stake_price_s := stake_price_s s |} |}.

  (* Deterministic policy: move the smaller of (supply, complexity) upward by 1.
     This is the minimal opposing-gradient controller that equalizes the two
     quantities and admits a simple Lyapunov proof. *)
  Definition policy_minted (s : EconState) : Amount :=
    if Nat.ltb (total_supply_s s) (total_complexity_s s) then 1 else 0.

  Definition policy_delta (s : EconState) : Amount :=
    if Nat.ltb (total_complexity_s s) (total_supply_s s) then 1 else 0.

  Definition policy_step (s : EconState) : EconState :=
    step (policy_minted s) (policy_delta s) s.

  Lemma abs_diff_eq_0_iff : forall a b, abs_diff a b = 0 <-> a = b.
  Proof.
    intros a b.
    unfold abs_diff.
    split.
    - intro H.
      (* nat addition can only be 0 if both summands are 0 *)
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
      (* compute (a-a) by induction on a, since Nat.sub reduces on successors *)
      induction a as [|a IH]; simpl; lia.
  Qed.

  Lemma V_eq_0_iff_stable : forall s, V s = 0 <-> stable s.
  Proof.
    intros s.
    unfold V, stable.
    apply abs_diff_eq_0_iff.
  Qed.

  Lemma abs_diff_lt_left : forall a b, a < b -> abs_diff (S a) b < abs_diff a b.
  Proof.
    intros a b Hab.
    unfold abs_diff.
    assert (Hab0 : a - b = 0).
    { apply sub_eq_0_of_le. lia. }
    assert (Hsa0 : S a - b = 0).
    { apply sub_eq_0_of_le. lia. }
    rewrite Hab0.
    rewrite Hsa0.
    simpl.
    (* b - (a+1) = pred (b-a) *)
    rewrite Nat.sub_succ_r.
    (* a < b implies b-a is a successor *)
    assert (Hpos : b - a <> 0) by lia.
    destruct (b - a) as [|k] eqn:Hba.
    - exfalso. apply Hpos. reflexivity.
    - simpl. lia.
  Qed.

  Lemma abs_diff_lt_right : forall a b, b < a -> abs_diff a (S b) < abs_diff a b.
  Proof.
    intros a b Hab.
    (* abs_diff is symmetric, reduce to abs_diff_lt_left *)
    assert (H : abs_diff (S b) a < abs_diff b a) by (apply abs_diff_lt_left; lia).
    unfold abs_diff in *.
    (* commute the sums to match the goal *)
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
    destruct (Nat.ltb (total_supply_s s) (total_complexity_s s)) eqn:Hsc.
    - (* supply < complexity: minted=1, delta=0 *)
      assert (Hsc_lt : total_supply_s s < total_complexity_s s).
      { apply Nat.ltb_lt. exact Hsc. }
      (* complexity <? supply is false when supply < complexity *)
      assert (Hdelta : (total_complexity_s s <? total_supply_s s) = false).
      { apply Nat.ltb_ge. lia. }
      simpl.
      rewrite Hdelta.
      rewrite Nat.add_1_r.
      rewrite Nat.add_0_r.
      apply abs_diff_lt_left.
      exact Hsc_lt.
    - (* supply >= complexity *)
      assert (Hsc_ge : total_supply_s s >= total_complexity_s s).
      { apply Nat.ltb_ge. exact Hsc. }
      destruct (Nat.ltb (total_complexity_s s) (total_supply_s s)) eqn:Hcs.
      + (* complexity < supply: delta=1 *)
        assert (Hcs_lt : total_complexity_s s < total_supply_s s).
        { apply Nat.ltb_lt. exact Hcs. }
        simpl.
        rewrite Nat.add_0_r.
        rewrite Nat.add_1_r.
        apply abs_diff_lt_right.
        exact Hcs_lt.
      + (* equality, contradict ~stable *)
        apply Nat.ltb_ge in Hcs.
        exfalso.
        apply Hnst.
        lia.
  Qed.

  Lemma V_policy_step_decreases :
    forall s,
      V (policy_step s) <= V s.
  Proof.
    intros s.
    destruct (Nat.eq_dec (total_supply_s s) (total_complexity_s s)) as [Heq|Hneq].
    - (* stable: policy does nothing, so V stays the same *)
      unfold stable.
      assert (Hm : policy_minted s = 0).
      { unfold policy_minted. rewrite Heq. rewrite Nat.ltb_irrefl. reflexivity. }
      assert (Hd : policy_delta s = 0).
      { unfold policy_delta. rewrite Heq. rewrite Nat.ltb_irrefl. reflexivity. }
      unfold policy_step, step, V.
      rewrite Hm. rewrite Hd.
      simpl.
      rewrite Nat.add_0_r.
      rewrite Nat.add_0_r.
      lia.
    - (* not stable: strict decrease implies non-increase *)
      assert (Hnst : ~ stable s) by (unfold stable; exact Hneq).
      pose proof (V_policy_step_decreases_strict s Hnst) as Hlt.
      lia.
  Qed.

  (* Public-facing Lyapunov statement (matches the intended interface). *)
  Theorem lyapunov_decreases : forall s, V (policy_step s) <= V s.
  Proof.
    exact V_policy_step_decreases.
  Qed.

  Fixpoint iterate (n : nat) (f : EconState -> EconState) (s : EconState) : EconState :=
    match n with
    | 0 => s
    | S n' => iterate n' f (f s)
    end.

  Lemma convergence_fuel :
    forall fuel s,
      V s <= fuel ->
      stable (iterate fuel policy_step s).
  Proof.
    induction fuel as [|fuel IH]; intros s HV.
    - assert (V s = 0) by lia.
      apply V_eq_0_iff_stable in H.
      simpl. exact H.
    - destruct (Nat.eq_dec (total_supply_s s) (total_complexity_s s)) as [Heq|Hneq].
      + (* already stable: one policy_step keeps it stable, then IH finishes *)
        simpl.
        assert (Hst1 : stable (policy_step s)).
        { unfold stable, policy_step, policy_minted, policy_delta, step.
          (* both comparisons are false when supply = complexity *)
          assert (Hm : (total_supply_s s <? total_complexity_s s) = false).
          { apply Nat.ltb_ge. lia. }
          assert (Hd : (total_complexity_s s <? total_supply_s s) = false).
          { apply Nat.ltb_ge. lia. }
          rewrite Hm, Hd.
          simpl.
          rewrite Nat.add_0_r.
          rewrite Nat.add_0_r.
          exact Heq.
        }
        assert (HVps : V (policy_step s) <= fuel).
        { apply V_eq_0_iff_stable in Hst1.
          lia.
        }
        apply IH.
        exact HVps.
      + (* not stable: one strict decrease, then apply IH *)
        assert (Hnst : ~ stable s) by (unfold stable; exact Hneq).
        pose proof (V_policy_step_decreases_strict s Hnst) as Hlt.
        assert (HV' : V (policy_step s) <= fuel) by lia.
        simpl.
        apply IH.
        exact HV'.
  Qed.

  Theorem convergence_to_equilibrium :
    forall s0,
      stable (iterate (V s0) policy_step s0).
  Proof.
    intro s0.
    apply convergence_fuel.
    lia.
  Qed.

  Lemma stable_iterate_policy_step :
    forall t s,
      stable s ->
      stable (iterate t policy_step s).
  Proof.
    induction t as [|t IH]; intros s Hst.
    - simpl. exact Hst.
    - simpl.
      apply IH.
      unfold stable, policy_step, policy_minted, policy_delta, step in *.
      (* if supply = complexity, both comparisons are false, so only +0 updates occur *)
      assert (Hm : (total_supply_s s <? total_complexity_s s) = false).
      { apply Nat.ltb_ge. lia. }
      assert (Hd : (total_complexity_s s <? total_supply_s s) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite Hm, Hd.
      simpl.
      rewrite Nat.add_0_r.
      rewrite Nat.add_0_r.
      exact Hst.
  Qed.

  (* ------------------------------------------------------------ *)
  (* Heterogeneous agents (finite-action potential-game equilibrium) *)
  (* ------------------------------------------------------------ *)

  Inductive Action :=
  | Mint
  | Wait.

  Record AgentProfile := {
    identity : nat;
    risk_tolerance : nat;
    capital_budget : Amount;
    productivity : Amount;
    discount_rate : nat;
  }.

  Definition StrategyProfile := list Action.

  Fixpoint set_nth {A : Type} (n : nat) (x : A) (xs : list A) : list A :=
    match n, xs with
    | 0, [] => []
    | 0, _ :: tl => x :: tl
    | S n', [] => []
    | S n', hd :: tl => hd :: set_nth n' x tl
    end.

  Record PotentialGame := {
    pg_utility_agent : AgentProfile -> EconState -> StrategyProfile -> nat;
    pg_potential : EconState -> StrategyProfile -> nat;
    (* Exact-potential condition: if agent i can strictly improve utility by
       unilateral deviation, potential strictly increases. *)
    pg_potential_improves_on_better_response :
      forall (agents : list AgentProfile) (s : EconState) (p : StrategyProfile)
             (i : nat) (a' : Action),
        i < length agents ->
        length p = length agents ->
        pg_utility_agent (nth i agents (nth 0 agents {| identity := 0; risk_tolerance := 0; capital_budget := 0; productivity := 0; discount_rate := 0 |})) s
                          (set_nth i a' p)
        >
        pg_utility_agent (nth i agents (nth 0 agents {| identity := 0; risk_tolerance := 0; capital_budget := 0; productivity := 0; discount_rate := 0 |})) s
                          p
        ->
        pg_potential s (set_nth i a' p) > pg_potential s p;
  }.

  Section WithPotentialGame.
  Context (PG : PotentialGame).

  Let utility_agent := pg_utility_agent PG.
  Let potential := pg_potential PG.
  Let potential_improves_on_better_response := pg_potential_improves_on_better_response PG.

  Definition nash_equilibrium (agents : list AgentProfile) (s : EconState) (p : StrategyProfile) : Prop :=
    length p = length agents /\
    forall i a',
      i < length agents ->
      utility_agent (nth i agents (nth 0 agents {| identity := 0; risk_tolerance := 0; capital_budget := 0; productivity := 0; discount_rate := 0 |})) s
                    (set_nth i a' p)
      <=
      utility_agent (nth i agents (nth 0 agents {| identity := 0; risk_tolerance := 0; capital_budget := 0; productivity := 0; discount_rate := 0 |})) s
                    p.

  Fixpoint all_profiles (n : nat) : list StrategyProfile :=
    match n with
    | 0 => [[]]
    | S n' =>
        (map (fun p => Mint :: p) (all_profiles n'))
        ++
        (map (fun p => Wait :: p) (all_profiles n'))
    end.

  Lemma all_profiles_nonempty : forall n, all_profiles n <> [].
  Proof.
    intro n.
    induction n as [|n' IH].
    - simpl. discriminate.
    - simpl.
      (* left half is nonempty *)
      intro Hc.
      apply app_eq_nil in Hc as [H1 _].
      (* map preserves nonemptiness *)
      destruct (all_profiles n') as [|p ps] eqn:Hall.
        + exfalso. apply IH. reflexivity.
      + simpl in H1. discriminate.
  Qed.

  Lemma all_profiles_length : forall n p, In p (all_profiles n) -> length p = n.
  Proof.
    intros n.
    induction n as [|n' IH]; intros p Hin.
    - simpl in Hin. destruct Hin as [Hin|Hin]; [subst; reflexivity|contradiction].
    - simpl in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin|Hin].
      + apply in_map_iff in Hin.
        destruct Hin as [p0 [Hp0 Hin0]].
        subst. simpl. f_equal. apply IH. exact Hin0.
      + apply in_map_iff in Hin.
        destruct Hin as [p0 [Hp0 Hin0]].
        subst. simpl. f_equal. apply IH. exact Hin0.
  Qed.

  Definition better (s : EconState) (best cand : StrategyProfile) : StrategyProfile :=
    if Nat.leb (potential s best) (potential s cand) then cand else best.

  Definition argmax_profile (s : EconState) (ps : list StrategyProfile) : StrategyProfile :=
    match ps with
    | [] => []
    | p :: rest => fold_left (better s) rest p
    end.

  Lemma better_in : forall s best cand,
      better s best cand = best \/ better s best cand = cand.
  Proof.
    intros s best cand.
    unfold better.
    destruct (Nat.leb (potential s best) (potential s cand)); auto.
  Qed.

  Lemma fold_left_better_in :
    forall s rest init,
      In (fold_left (better s) rest init) (init :: rest).
  Proof.
    intros s rest.
    induction rest as [|x xs IH]; intros init.
    - simpl. left. reflexivity.
    - simpl.
      specialize (IH (better s init x)).
      destruct (better_in s init x) as [Hb|Hb].
      + (* better returns init *)
        rewrite Hb in IH.
        rewrite Hb.
        (* IH: In (fold_left .. xs init) (init :: xs) *)
        simpl.
        destruct IH as [Hin|Hin].
        * left. exact Hin.
        * right. right. exact Hin.
      + (* better returns x *)
        rewrite Hb in IH.
        rewrite Hb.
        (* IH: In (fold_left .. xs x) (x :: xs) *)
        simpl. right. exact IH.
  Qed.

  Lemma argmax_profile_in : forall s ps,
      ps <> [] -> In (argmax_profile s ps) ps.
  Proof.
    intros s ps Hne.
    destruct ps as [|p rest].
    - contradiction.
    - simpl.
      (* fold_left result is always in (p :: rest) *)
      apply fold_left_better_in.
  Qed.

  Lemma better_ge : forall s best cand,
      potential s best <= potential s (better s best cand) /\
      potential s cand <= potential s (better s best cand).
  Proof.
    intros s best cand.
    unfold better.
    destruct (Nat.leb (potential s best) (potential s cand)) eqn:Hleb.
    - apply Nat.leb_le in Hleb.
      split; lia.
    - apply Nat.leb_gt in Hleb.
      split; lia.
  Qed.

  Lemma fold_left_better_acc_le :
    forall s rest acc,
      potential s acc <= potential s (fold_left (better s) rest acc).
  Proof.
    intros s rest.
    induction rest as [|x xs IH]; intros acc.
    - simpl. lia.
    - simpl.
      destruct (better_ge s acc x) as [Hacc _].
      eapply Nat.le_trans.
      + exact Hacc.
      + apply IH.
  Qed.

  Lemma fold_left_better_rest_max :
    forall s rest init q,
      In q rest ->
      potential s q <= potential s (fold_left (better s) rest init).
  Proof.
    intros s rest.
    induction rest as [|x xs IH]; intros init q Hin.
    - contradiction.
    - simpl in Hin.
      destruct Hin as [Hq|Hin].
      + subst q.
        simpl.
        (* q = x: x <= better(init,x) <= fold_left xs (better(init,x)) *)
        destruct (better_ge s init x) as [_ Hx].
        eapply Nat.le_trans.
        * exact Hx.
        * apply fold_left_better_acc_le.
      + (* q in xs *)
        simpl.
        apply (IH (better s init x) q).
        exact Hin.
  Qed.

  Lemma fold_left_better_max :
    forall s rest init q,
      In q (init :: rest) ->
      potential s q <= potential s (fold_left (better s) rest init).
  Proof.
    intros s rest init q Hin.
    destruct Hin as [Hq|Hin].
    - subst q. apply fold_left_better_acc_le.
    - apply fold_left_better_rest_max.
      exact Hin.
  Qed.

  Lemma argmax_profile_max :
    forall s ps q,
      ps <> [] ->
      In q ps ->
      potential s q <= potential s (argmax_profile s ps).
  Proof.
    intros s ps q Hne Hin.
    destruct ps as [|p rest].
    - contradiction.
    - simpl in Hin.
      apply fold_left_better_max.
      exact Hin.
  Qed.

  Lemma all_profiles_complete : forall n p,
      length p = n ->
      In p (all_profiles n).
  Proof.
    intros n.
    induction n as [|n' IH]; intros p Hlen.
    - destruct p; simpl in Hlen; try discriminate.
      simpl. left. reflexivity.
    - destruct p as [|a p']; simpl in Hlen; try discriminate.
      simpl.
      apply in_or_app.
      destruct a.
      + left. apply in_map.
        apply IH. lia.
      + right. apply in_map.
        apply IH. lia.
  Qed.

  Lemma set_nth_length : forall (A : Type) i (x : A) xs,
      i < length xs ->
      length (set_nth i x xs) = length xs.
  Proof.
    intros A i.
    induction i as [|i IH]; intros x xs Hi.
    - destruct xs as [|h tl]; simpl in *.
      + lia.
      + reflexivity.
    - destruct xs as [|h tl]; simpl in *.
      + lia.
      + simpl. f_equal. apply IH. lia.
  Qed.

  Theorem heterogeneous_equilibrium :
    forall agents s,
      agents <> [] ->
      exists p,
        nash_equilibrium agents s p.
  Proof.
    intros agents s Hane.
    set (n := length agents).
    set (ps := all_profiles n).
    set (p := argmax_profile s ps).
    exists p.
    split.
    - (* length p = length agents *)
      assert (Hp_in : In p ps).
      { subst p ps. apply argmax_profile_in. apply all_profiles_nonempty. }
      (* unfold ps/n so all_profiles_length applies directly *)
      unfold ps, n in Hp_in.
      pose proof (all_profiles_length (length agents) p Hp_in) as Hlen.
      exact Hlen.
    - (* no profitable unilateral deviation *)
      intros i a' Hi.
      (* assume strict improvement and derive a contradiction via potential maximality *)
        set (u_dev :=
               utility_agent
                 (nth i agents
                      (nth 0 agents
                           {| identity := 0;
                              risk_tolerance := 0;
                              capital_budget := 0;
                              productivity := 0;
                              discount_rate := 0 |}))
                 s (set_nth i a' p)).
        set (u_cur :=
               utility_agent
                 (nth i agents
                      (nth 0 agents
                           {| identity := 0;
                              risk_tolerance := 0;
                              capital_budget := 0;
                              productivity := 0;
                              discount_rate := 0 |}))
                 s p).
        destruct (le_gt_dec u_dev u_cur) as [Hle|Hgt].
        + exact Hle.
        + exfalso.
      assert (Hps_ne : ps <> []).
      { unfold ps, n. apply all_profiles_nonempty. }
      assert (Hp_in : In p ps).
      { subst p ps. apply argmax_profile_in. exact Hps_ne. }
      assert (Hlenp : length p = n).
      { unfold ps in Hp_in.
        pose proof (all_profiles_length n p Hp_in) as Hlen.
        exact Hlen.
      }
      assert (Hip : i < length p) by lia.
      assert (Hlenp' : length (set_nth i a' p) = n).
      { rewrite (set_nth_length Action i a' p Hip). lia. }
      assert (Hp'_in : In (set_nth i a' p) ps).
      { unfold ps.
        apply all_profiles_complete.
        exact Hlenp'.
      }
        (* potential must increase on a better response *)
        pose proof (potential_improves_on_better_response agents s p i a' Hi Hlenp Hgt) as Hpot.
      (* but p maximizes potential over ps *)
      pose proof (argmax_profile_max s ps (set_nth i a' p) Hps_ne Hp'_in) as Hmax.
          unfold p in Hpot, Hmax.
        apply (Nat.lt_irrefl (potential s (argmax_profile s ps))).
        eapply Nat.lt_le_trans; [exact Hpot | exact Hmax].
  Qed.

  End WithPotentialGame.

  (* ------------------------------------------------------------ *)
  (* Bounded rationality (noise that eventually vanishes)          *)
  (* ------------------------------------------------------------ *)

  Record NoiseModel := {
    nm_perception_noise : nat -> nat;
  }.

  Section WithNoiseModel.
  Context (NM : NoiseModel).

  Let perception_noise := nm_perception_noise NM.

  Definition perceived_intrinsic_value (t : nat) (s : EconState) : nat :=
    intrinsic_value s + perception_noise t.

  Definition diminishing_noise : Prop := exists T, forall t, T <= t -> perception_noise t = 0.

  (* Structural consequence: after noise vanishes, perceived value equals true value. *)
  Lemma perceived_equals_true_after_T :
    forall T,
      (forall t, T <= t -> perception_noise t = 0) ->
      forall t s,
        T <= t ->
        perceived_intrinsic_value t s = intrinsic_value s.
  Proof.
    intros T Hnoise t s Ht.
    unfold perceived_intrinsic_value.
    rewrite (Hnoise t Ht).
    lia.
  Qed.

  (* Under vanishing noise, the system-level convergence result for policy_step
     is unaffected (policy_step is deterministic and does not depend on noise). *)
  Theorem bounded_noise_convergence :
    diminishing_noise ->
    forall s0,
      stable (iterate (V s0) policy_step s0).
  Proof.
    intros _ s0.
    apply convergence_to_equilibrium.
  Qed.

  End WithNoiseModel.
End EconDynamics.

Require Extraction.
Extraction Language OCaml.
Extraction "econ_dynamics.ml"
  EconDynamics.step
  EconDynamics.policy_step
  EconDynamics.V
  EconDynamics.intrinsic_value
  EconDynamics.dynamic_stake_required.
