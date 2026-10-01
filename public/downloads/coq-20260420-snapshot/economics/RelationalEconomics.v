From Coq Require Import List Arith.
Import ListNotations.

Require Import VALIS.Kernel.

Module Type AmountModelSig.
  Parameter Amount : Type.
  Parameter zero : Amount.
  Parameter add : Amount -> Amount -> Amount.
  Parameter leq : Amount -> Amount -> Prop.

  Infix "+" := add.
  Infix "<=" := leq.

  Parameter add_assoc : forall a b c, a + (b + c) = (a + b) + c.
  Parameter add_comm : forall a b, a + b = b + a.
  Parameter add_zero : forall a, a + zero = a.

  Parameter leq_refl : forall a, a <= a.
  Parameter leq_trans : forall a b c, a <= b -> b <= c -> a <= c.
  Parameter zero_least : forall a, zero <= a.

  Parameter leq_add_mono :
    forall a b c d,
      a <= b ->
      c <= d ->
      (a + c) <= (b + d).

  Parameter leq_add_incr_r : forall a b, a <= a + b.
  Parameter leq_add_incr_l : forall a b, a <= b + a.

  Parameter positive : Amount -> Prop.
End AmountModelSig.

Module Type RelationalEconomicsParams (K : KernelSig) (AM : AmountModelSig).
  (* Decidable equality on hashes (economics-layer requirement). *)
  Parameter hash_eq_dec : forall h1 h2 : K.hash, {h1 = h2} + {h1 <> h2}.

  (* Normalization layer (deterministic canonicalization of relations). *)
  Parameter normalize : K.relation -> K.relation.

  (* Complexity / contribution model. *)
  Parameter delta_complexity : K.relation -> AM.Amount.
  Parameter min : AM.Amount -> AM.Amount -> AM.Amount.

  (* Deterministic minting policy predicates. *)
  Parameter relation_settled : K.relation -> Prop.
  Parameter respects_constitution : K.relation -> Prop.
  Parameter lineage_compatible : K.relation -> Prop.
  Parameter stake_required : K.relation -> AM.Amount.

  (* Time model for stake locking. *)
  Parameter Time : Type.
  Parameter time_le : Time -> Time -> Prop.
  Parameter add_time : Time -> Time -> Time.
  Parameter current_time : Time.
  Parameter lock_period : Time.

  (* Slashing model. *)
  Parameter relation_invalidated : K.hash -> Prop.
  Parameter relation_invalidated_dec :
    forall h : K.hash, {relation_invalidated h} + {~ relation_invalidated h}.

  (* “Extends” partial order on hashes (for compatibility). *)
  Parameter extends : K.hash -> K.hash -> Prop.
  Parameter extends_refl : forall h, extends h h.
  Parameter extends_trans :
    forall h1 h2 h3, extends h1 h2 -> extends h2 h3 -> extends h1 h3.
  Parameter extends_antisym :
    forall h1 h2, extends h1 h2 -> extends h2 h1 -> h1 = h2.
End RelationalEconomicsParams.

Module RelationalEconomics (K : KernelSig) (AM : AmountModelSig) (P : RelationalEconomicsParams K AM).
  (* ------------------------------------------------------------ *)
  (* Amount / stake algebra (kept abstract for determinism)        *)
  (* ------------------------------------------------------------ *)

  Definition Amount : Type := AM.Amount.
  Definition zero : Amount := AM.zero.
  Definition add : Amount -> Amount -> Amount := AM.add.
  Definition leq : Amount -> Amount -> Prop := AM.leq.

  Local Infix "+" := add.
  Local Infix "<=" := leq.

  Local Definition add_assoc : forall a b c, a + (b + c) = (a + b) + c := AM.add_assoc.
  Local Definition add_comm : forall a b, a + b = b + a := AM.add_comm.
  Local Definition add_zero : forall a, a + zero = a := AM.add_zero.

  (* ------------------------------------------------------------ *)
  (* Minimal order interface for Amount                            *)
  (* ------------------------------------------------------------ *)

  Local Definition leq_refl := AM.leq_refl.
  Local Definition leq_trans := AM.leq_trans.
  Local Definition zero_least := AM.zero_least.

  (* Monotonicity of addition (enough to support list-sum bounds). *)
  Local Definition leq_add_mono := AM.leq_add_mono.

  (* Addition is inflationary in either argument (minimal order laws needed
     for monotone “sum increases when you add a term” reasoning). *)
  Local Definition leq_add_incr_r := AM.leq_add_incr_r.
  Local Definition leq_add_incr_l := AM.leq_add_incr_l.

  Lemma leq_add_r : forall a b c, a <= b -> (a + c) <= (b + c).
  Proof.
    intros a b c Hab.
    eapply leq_add_mono; [exact Hab | apply leq_refl].
  Qed.

  Lemma leq_add_l : forall a b c, a <= b -> (c + a) <= (c + b).
  Proof.
    intros a b c Hab.
    (* rewrite via commutativity then reuse leq_add_r *)
    rewrite (add_comm c a).
    rewrite (add_comm c b).
    apply leq_add_r.
    exact Hab.
  Qed.

  Definition positive : Amount -> Prop := AM.positive.

  (* ------------------------------------------------------------ *)
  (* Identity (stake-bound, sybil resistance by construction)      *)
  (* ------------------------------------------------------------ *)

  Record Identity := {
    id_hash : K.hash;
    bonded_stake : Amount;
  }.

  (* A derived single-relation hash helper (kernel remains unchanged). *)
  Definition hash_of_relation (r : K.relation) : K.hash :=
    K.hash_of_relations [r].

  (* ------------------------------------------------------------ *)
  (* Ledger and mint-once constraint                               *)
  (* ------------------------------------------------------------ *)

  Record Contribution := {
    contributor : Identity;
    relation_hash : K.hash;
    contribution_weight : Amount;
  }.

  Definition Ledger := list Contribution.

  Definition ledger_no_duplicate_relations (L : Ledger) : Prop :=
    forall c1 c2,
      In c1 L ->
      In c2 L ->
      relation_hash c1 = relation_hash c2 ->
      c1 = c2.

  Definition relation_already_minted (r : K.relation) (L : Ledger) : Prop :=
    exists c,
      In c L /\
      relation_hash c = hash_of_relation r.

  (* ------------------------------------------------------------ *)
  (* Stake-budget accounting (prevents bonded stake reuse)          *)
  (* ------------------------------------------------------------ *)

  Definition hash_eq_dec : forall h1 h2 : K.hash, {h1 = h2} + {h1 <> h2} :=
    P.hash_eq_dec.

  Fixpoint identity_minted (i : Identity) (L : Ledger) : Amount :=
    match L with
    | [] => zero
    | c :: rest =>
        let rest_sum := identity_minted i rest in
        if hash_eq_dec (id_hash (contributor c)) (id_hash i)
        then contribution_weight c + rest_sum
        else rest_sum
    end.

  Definition stake_respected (L : Ledger) : Prop :=
    forall i,
      identity_minted i L <= bonded_stake i.

  Lemma identity_minted_cons_match :
    forall c rest,
      identity_minted (contributor c) (c :: rest) =
        contribution_weight c + identity_minted (contributor c) rest.
  Proof.
    intros c rest.
    simpl.
    destruct (hash_eq_dec (id_hash (contributor c)) (id_hash (contributor c))) as [Heq|Hneq].
    - reflexivity.
    - exfalso. apply Hneq. reflexivity.
  Qed.

  Lemma identity_minted_monotone_cons :
    forall i c rest,
      identity_minted i rest <= identity_minted i (c :: rest).
  Proof.
    intros i c rest.
    simpl.
    destruct (hash_eq_dec (id_hash (contributor c)) (id_hash i)) as [Heq|Hneq].
    - (* increases by contribution_weight c *)
      apply leq_add_incr_l.
    - (* unchanged *)
      apply leq_refl.
  Qed.

  Fixpoint sum_minted (ids : list Identity) (L : Ledger) : Amount :=
    match ids with
    | [] => zero
    | i :: rest => identity_minted i L + sum_minted rest L
    end.

  Lemma sum_minted_monotone_cons :
    forall ids c rest,
      sum_minted ids rest <= sum_minted ids (c :: rest).
  Proof.
    intros ids c rest.
    induction ids as [|i ids' IH].
    - simpl. apply leq_refl.
    - simpl.
      apply leq_add_mono.
      + apply identity_minted_monotone_cons.
      + exact IH.
  Qed.

  Lemma sum_minted_cons_lower_bound :
    forall ids c rest,
      In (contributor c) ids ->
      contribution_weight c + sum_minted ids rest <= sum_minted ids (c :: rest).
  Proof.
    intros ids c rest Hin.
    induction ids as [|i ids' IH].
    - contradiction.
    - simpl in Hin.
      destruct Hin as [Hi|Hin'].
      + subst i.
        (* contributor is at head: pull out its +weight explicitly *)
        cbn [sum_minted].
        rewrite identity_minted_cons_match.
        (* goal: w + (minted_i_rest + sum_rest_rest) <= (w + minted_i_rest) + sum_rest_cons *)
        (* reorder and use monotonicity of tail *)
        rewrite add_assoc.
        apply leq_add_mono.
        * apply leq_refl.
        * (* sum_minted ids' rest <= sum_minted ids' (c::rest) *)
          apply sum_minted_monotone_cons.
      + (* contributor is in tail *)
        (* use IH on tail, then add monotonicity for head term *)
        specialize (IH Hin').
        (* need: minted i rest <= minted i (c::rest) *)
        cbn [sum_minted].
        apply leq_trans with (identity_minted i (c :: rest) + (contribution_weight c + sum_minted ids' rest)).
        * (* w + (minted_i_rest + sum_tail_rest) <= minted_i_cons + (w + sum_tail_rest) *)
          rewrite (add_assoc (contribution_weight c) (identity_minted i rest) (sum_minted ids' rest)).
          (* commute to expose minted_i_rest at the front *)
          rewrite (add_comm (contribution_weight c) (identity_minted i rest)).
          rewrite <- add_assoc.
          apply leq_add_mono.
          { apply identity_minted_monotone_cons. }
          { apply leq_refl. }
        * (* minted_i_cons + (w + sum_tail_rest) <= minted_i_cons + sum_tail_cons *)
          apply leq_add_mono.
          { apply leq_refl. }
          { exact IH. }
  Qed.

  (* This is the structural “mint once” shape from the spec.
     It is provable from ledger_no_duplicate_relations, but we keep it as an
     explicit surface. *)
  Lemma mint_once_per_relation :
    forall r L c1 c2,
      ledger_no_duplicate_relations L ->
      In c1 L ->
      In c2 L ->
      relation_hash c1 = hash_of_relation r ->
      relation_hash c2 = hash_of_relation r ->
      c1 = c2.
  Proof.
    intros r L c1 c2 Hnodup Hin1 Hin2 Hh1 Hh2.
    apply Hnodup; try assumption.
    now rewrite Hh1, Hh2.
  Qed.

  Lemma mint_once_per_relation_safe :
    forall r L,
      ledger_no_duplicate_relations L ->
      relation_already_minted r L ->
      exists c0,
        In c0 L /\
        relation_hash c0 = hash_of_relation r /\
        forall c,
          In c L ->
          relation_hash c = hash_of_relation r ->
          c = c0.
  Proof.
    intros r L Hnodup Hmint.
    destruct Hmint as [c0 [Hc0in Hc0hash]].
    exists c0.
    split; [exact Hc0in|].
    split; [exact Hc0hash|].
    intros c Hcin Hchash.
    (* uniqueness follows directly from the ledger no-duplicate invariant *)
    apply (Hnodup c c0); try assumption.
    now rewrite Hchash, Hc0hash.
  Qed.

  (* ------------------------------------------------------------ *)
  (* Normalization / canonicalization layer                        *)
  (* ------------------------------------------------------------ *)

  Definition normalize : K.relation -> K.relation := P.normalize.

  (* ------------------------------------------------------------ *)
  (* Contribution measure: normalized + stake-capped               *)
  (* ------------------------------------------------------------ *)

  Definition delta_complexity : K.relation -> Amount := P.delta_complexity.
  Definition min : Amount -> Amount -> Amount := P.min.

  Definition contribution_measure (r : K.relation) (i : Identity) : Amount :=
    min (delta_complexity (normalize r)) (bonded_stake i).

  (* ------------------------------------------------------------ *)
  (* Minting constraint (economics-layer, deterministic)           *)
  (* ------------------------------------------------------------ *)

  Definition relation_settled : K.relation -> Prop := P.relation_settled.
  Definition respects_constitution : K.relation -> Prop := P.respects_constitution.
  Definition lineage_compatible : K.relation -> Prop := P.lineage_compatible.

  Definition stake_required : K.relation -> Amount := P.stake_required.

  Definition mint_allowed (r : K.relation) (i : Identity) (L : Ledger) : Prop :=
    relation_settled r /\
    respects_constitution r /\
    lineage_compatible r /\
    ~(relation_already_minted r L) /\
    stake_required r <= bonded_stake i.

  (* ------------------------------------------------------------ *)
  (* Adversary model                                               *)
  (* ------------------------------------------------------------ *)

  Record Adversary := {
    adversary_identities : list Identity;
    adversary_strategy : Ledger -> K.relation;
  }.

  Fixpoint total_stake (ids : list Identity) : Amount :=
    match ids with
    | [] => zero
    | i :: rest => bonded_stake i + total_stake rest
    end.

  Lemma sum_minted_le_total_stake :
    forall ids L,
      (forall i, In i ids -> identity_minted i L <= bonded_stake i) ->
      sum_minted ids L <= total_stake ids.
  Proof.
    intros ids L Hbound.
    induction ids as [|i ids' IH].
    - simpl. apply leq_refl.
    - simpl.
      apply leq_add_mono.
      + apply Hbound. simpl. left. reflexivity.
      + apply IH.
        intros i' Hin.
        apply Hbound. simpl. right. exact Hin.
  Qed.

  Fixpoint total_supply (L : Ledger) : Amount :=
    match L with
    | [] => zero
    | c :: rest => contribution_weight c + total_supply rest
    end.

  (* ------------------------------------------------------------ *)
  (* Ledger-side assumptions needed for the adversarial bound       *)
  (* ------------------------------------------------------------ *)

  Definition ledger_contributors_in_adversary (A : Adversary) (L : Ledger) : Prop :=
    forall c,
      In c L ->
      In (contributor c) (adversary_identities A).

  Definition ledger_weights_bounded_by_stake (L : Ledger) : Prop :=
    forall c,
      In c L ->
      contribution_weight c <= bonded_stake (contributor c).

  (* Total stake is monotone with respect to list inclusion.
     This is the minimal abstraction we need to lift contributor-inclusion
     into a numerical bound without committing to a specific Amount model. *)
  Record AdversaryStakeAssumptions := {
    asa_total_stake_monotone :
      forall ids1 ids2,
        (forall i, In i ids1 -> In i ids2) ->
        total_stake ids1 <= total_stake ids2;
  }.

  Lemma total_supply_leq_total_stake_of_contributors :
    forall L,
      ledger_weights_bounded_by_stake L ->
      total_supply L <= total_stake (map contributor L).
  Proof.
    intros L Hcap.
    induction L as [|c rest IH].
    - simpl. apply zero_least.
    - simpl.
      (* cap head weight by its bonded stake, and apply IH to the tail *)
      assert (Hhead : contribution_weight c <= bonded_stake (contributor c)).
      { apply Hcap. simpl. left. reflexivity. }
      assert (Htail : ledger_weights_bounded_by_stake rest).
      { intros c' Hin.
        apply Hcap.
        simpl. right. exact Hin.
      }
      specialize (IH Htail).
      eapply leq_add_mono; [exact Hhead | exact IH].
  Qed.

  Lemma contributors_subset_of_adversary :
    forall A L,
      ledger_contributors_in_adversary A L ->
      forall i,
        In i (map contributor L) ->
        In i (adversary_identities A).
  Proof.
    intros A L Hsub i Hin.
    apply in_map_iff in Hin.
    destruct Hin as [c [Hci HcIn]].
    (* Hci : contributor c = i *)
    rewrite <- Hci.
    apply Hsub.
    exact HcIn.
  Qed.

  (* ------------------------------------------------------------ *)
  (* Adversarial supply bound (skeleton surface)                    *)
  (* ------------------------------------------------------------ *)

  Section WithAdversaryStakeAssumptions.
  Context (ASA : AdversaryStakeAssumptions).

  Let total_stake_monotone := asa_total_stake_monotone ASA.

  Theorem adversarial_supply_bound :
    forall A L,
      ledger_no_duplicate_relations L ->
      ledger_contributors_in_adversary A L ->
      ledger_weights_bounded_by_stake L ->
      total_supply L <= total_stake (adversary_identities A).
  Proof.
    intros A L Hnodup Hsubset Hcap.
    (* (1) total_supply is bounded by stake of contributors *)
    pose proof (total_supply_leq_total_stake_of_contributors L Hcap) as H1.
    (* (2) contributors are included in the adversary identity set *)
    pose proof (total_stake_monotone (map contributor L) (adversary_identities A)
                  (contributors_subset_of_adversary A L Hsubset)) as H2.
    (* (3) conclude by transitivity *)
    eapply leq_trans; [exact H1 | exact H2].
  Qed.

  End WithAdversaryStakeAssumptions.

  (* Stronger, stake-consumption adversarial bound (prevents stake reuse):
     supply is bounded by bonded stake when stake_respected holds. *)
  Theorem adversarial_supply_bound_stake_respected :
    forall A L,
      stake_respected L ->
      ledger_contributors_in_adversary A L ->
      total_supply L <= total_stake (adversary_identities A).
  Proof.
    intros A L Hstake Hsub.
    (* 1) total_supply L <= sum_minted ids L by induction on L *)
    assert (Hsup_le_sum :
              forall L0,
                ledger_contributors_in_adversary A L0 ->
                total_supply L0 <= sum_minted (adversary_identities A) L0).
    {
      induction L0 as [|c rest IH].
      - intros _. simpl. apply zero_least.
      - intros Hsub0.
        simpl.
        (* IH applies to the tail once we restrict Hsub0 to rest *)
        assert (Hsub_rest : ledger_contributors_in_adversary A rest).
        { intros c' Hin.
          apply Hsub0.
          simpl. right. exact Hin.
        }
        pose proof (IH Hsub_rest) as IHrest.
        apply leq_trans with (contribution_weight c + sum_minted (adversary_identities A) rest).
        + apply leq_add_mono; [apply leq_refl | exact IHrest].
        + apply sum_minted_cons_lower_bound.
          apply Hsub0.
          simpl. left. reflexivity.
    }
    (* 2) sum_minted ids L <= total_stake ids using stake_respected *)
    pose proof (sum_minted_le_total_stake (adversary_identities A) L
                  (fun i _ => Hstake i)) as Hsum_le_stake.
    eapply leq_trans; [apply Hsup_le_sum; exact Hsub | exact Hsum_le_stake].
  Qed.

  (* ------------------------------------------------------------ *)
  (* Stake lock + slashing (placeholders; economics-layer only)     *)
  (* ------------------------------------------------------------ *)

  (* Time is abstract; economics rules are deterministic in terms of the
     parameters below (no external oracle dependence). *)
  Definition Time : Type := P.Time.
  Definition time_le : Time -> Time -> Prop := P.time_le.
  Definition add_time : Time -> Time -> Time := P.add_time.

  Definition current_time : Time := P.current_time.
  Definition lock_period : Time := P.lock_period.

  Record LockedStake := {
    owner : Identity;
    locked_amount : Amount;
    unlock_time : Time;
    locked_relation_hash : K.hash;
  }.

  Record SystemState := {
    ledger : Ledger;
    locks : list LockedStake;
  }.

  (* Mint deterministically creates a lock for the contributed weight. *)
  Definition lock_for_contribution (c : Contribution) : LockedStake :=
    {| owner := contributor c;
       locked_amount := contribution_weight c;
       unlock_time := add_time current_time lock_period;
       locked_relation_hash := relation_hash c |}.

  Definition mint_creates_lock (c : Contribution) (l : LockedStake) : Prop :=
    l = lock_for_contribution c.

  (* A relation (by hash) may later be invalidated; this feeds slashing. *)
  Definition relation_invalidated : K.hash -> Prop := P.relation_invalidated.
  Definition relation_invalidated_dec :
    forall h : K.hash, {relation_invalidated h} + {~ relation_invalidated h} :=
    P.relation_invalidated_dec.

  Definition slash_condition (l : LockedStake) : Prop :=
    relation_invalidated (locked_relation_hash l).

  Definition slash_condition_dec :
    forall l : LockedStake, {slash_condition l} + {~ slash_condition l}.
  Proof.
    intro l.
    unfold slash_condition.
    destruct (relation_invalidated_dec (locked_relation_hash l)) as [H|H].
    - left. exact H.
    - right. exact H.
  Defined.

  Definition keep_lock (l : LockedStake) : bool :=
    if slash_condition_dec l then false else true.

  Fixpoint filter_locks (ls : list LockedStake) : list LockedStake :=
    match ls with
    | [] => []
    | l :: rest =>
        if keep_lock l then l :: filter_locks rest else filter_locks rest
    end.

  Definition apply_slash (s : SystemState) : SystemState :=
    {| ledger := ledger s;
       locks := filter_locks (locks s) |}.

  (* (Optional) unlocking predicate; actual unlock transition can be defined by
     a deterministic time-step function in a higher layer. *)
  Definition lock_matured (now : Time) (l : LockedStake) : Prop :=
    time_le (unlock_time l) now.

  (* ------------------------------------------------------------ *)
  (* Governance upgrade calculus: constitution extension lattice     *)
  (* ------------------------------------------------------------ *)

  Definition extends : K.hash -> K.hash -> Prop := P.extends.

  Definition extends_refl : forall h, extends h h := P.extends_refl.
  Definition extends_trans :
    forall h1 h2 h3, extends h1 h2 -> extends h2 h3 -> extends h1 h3 :=
    P.extends_trans.
  Definition extends_antisym :
    forall h1 h2, extends h1 h2 -> extends h2 h1 -> h1 = h2 :=
    P.extends_antisym.

  Definition compatible (h1 h2 : K.hash) : Prop :=
    extends h1 h2 \/ extends h2 h1.

  Record Upgrade := {
    old_hash : K.hash;
    new_hash : K.hash;
    extension_proof : extends old_hash new_hash;
  }.

  Theorem upgrade_preserves_compatibility :
    forall u,
      compatible (old_hash u) (new_hash u).
  Proof.
    intros u.
    unfold compatible.
    left.
    exact (extension_proof u).
  Qed.

  (* A higher-level invariant-preservation surface (left for later proof). *)
  Theorem upgrade_preserves_ledger_invariants :
    forall u L,
      compatible (old_hash u) (new_hash u) ->
      ledger_no_duplicate_relations L ->
      ledger_no_duplicate_relations L.
  Proof.
    intros u L _ H.
    exact H.
  Qed.

End RelationalEconomics.
