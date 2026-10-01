# CR/RRS Compositional Kernel Theorem Packet v0

Date: 2026-09-27
Status: theorem-packet scaffold for formal review
Depends on: `docs/cr-rrs-compositional-kernel-reconciliation.md`

## Claim boundary

This packet does not claim a proved global theorem. It records definitions, assumptions, candidate lemmas, counterexample witnesses, independence results, and open proof obligations generated from the current implementation/corpus reconciliation.

Reference-semantics evidence is separate from production KORE conformance and from independent review.

## Objects to formalize

### State

Let `Sigma` be a consequential state containing, for the current synthetic reference scope:

```text
Sigma = (
  principals,
  agents,
  dependencies,
  releases,
  effects,
  finalized,
  history,
  tick,
  epoch
)
```

This is not claimed to be universal. It is the current reference state family. Production KORE may require additional state components.

### Proposal and execution

A proposal `p` is a requested transition into a release state. In the current reference it may mention:

```text
agent_id, principal_id, operation, amount, dependency_id,
release_id/proposal_id, bound_digest, finality_key,
prior_effect, restart
```

An execution `e` consumes a release and records an effect:

```text
release_id, proposal_digest, effect, finality_key
```

### Settlement

The current reference settlement function is executable:

```text
settle(Sigma, p) -> {release, refuse, hold} x Sigma' x receipt
execute(Sigma, e) -> {executed, refuse} x Sigma' x receipt
```

### Consequential reachability

Candidate definition for a fixed semantic environment `Gamma`:

```text
CR_Gamma(Sigma) = { Sigma' | exists p, settle_Gamma(Sigma, p) = release and applies to Sigma' }
```

For traces:

```text
CR*_Gamma(Sigma0) = all states reachable from Sigma0 by finite sequences of released/executed mediated transitions under Gamma.
```

This needs refinement because the current implementation separates release from execution/effect and permits hold/refuse outcomes that also produce evidence.

### Declared global envelope

Let `G` be a predicate over states/traces, not a scalar. Examples:

- aggregate exposure under a principal does not exceed declared limit;
- unknown effects remain risk-bearing;
- a release is consumed at most once;
- revoked or absent authority cannot create release;
- exact binding is preserved from proposal to execution;
- stale dependency/epoch state cannot widen reach.

## Candidate definitions

### ConsequentialDependency

A dependency is consequential for transition `tau` under envelope `G` if changing it while holding other represented state equal can change at least one of:

```text
settlement result, resulting state, forbidden-state predicate, receipt/evidence obligation, future reachability under G.
```

Current dependency domains:

```text
identity/principal, authority/provenance, resource/exposure,
release/execution, effect/observation, finality/history,
dependency/freshness, composition/global envelope.
```

### DependencyCompleteness

Candidate:

```text
DependencyCompleteness(Gamma, Sigma, T, G)
```

holds when every dependency capable of changing membership in `G` for in-scope transitions `T` is either:

1. represented in `Sigma`,
2. derived deterministically from represented state,
3. supplied as an explicit assumption in `Gamma`, or
4. unavailable, in which case settlement cannot widen reach.

### StateAdequacy

Candidate:

```text
StateAdequacy(Sigma, T, G)
```

holds when `Sigma` contains enough current, canonical, and non-stale information to evaluate every dependency required by `T` and `G`.

For current evidence, this includes at least:

```text
agent authority, principal aggregation, resource exposure/reservation,
dependency status/epoch, release consumption, exact binding digest,
effect state, finality state, and history/restart context.
```

### CompositionSoundness

Candidate:

```text
CompositionSoundness(Gamma, T, G)
```

holds when the composition/reduction rule used by the evaluator preserves all dependencies relevant to `G` across sequences, including non-pairwise aggregate interactions.

This cannot be assumed from pairwise compatibility.

### Transition footprint

Candidate extractor:

```text
D(tau) = (reads(tau), writes(tau), effect_obligations(tau), future_dependency_delta(tau))
```

Current status: not implemented. Derivable manually from `settle()` and `execute()` in `frontier-eval/reference/cr-core-synthetic.mjs`.

### Minimal forbidden composition

Candidate:

```text
MF_G = { X : not G(Compose(X)) and for all Y proper-subset X, G(Compose(Y)) }
```

Current status: not implemented. FE010 is a two-step seed. A three-way aggregate example such as `35+35+35>100` should be added as a witness before any pairwise reduction claim is made.

## Candidate theorem

```text
DependencyCompleteness(Gamma, Sigma0, T, G)
and StateAdequacy(Sigma0, T, G)
and CompositionSoundness(Gamma, T, G)
and MediatedTransitionsOnly(trace, Gamma)
and WorldCorrespondence(trace, observations)
=>
CR*_Gamma(Sigma0) subseteq G
```

Plain-language version:

> If every CR-changing dependency is represented or explicitly assumed, the state is adequate for the transition class and envelope, composition/reduction preserves the relevant dependencies including higher-order interactions, every consequential transition is mediated, and external effect/observation uncertainty is treated conservatively, then all reachable mediated consequential states remain inside the declared envelope.

## Mediation assumptions

These are assumptions, not current proof results:

1. Every consequential transition in the trace routes through settlement.
2. Releases are exact-bound to proposals.
3. Execution consumes the release according to single-use semantics.
4. External execution cannot bypass the synthetic/reference state machine inside the theorem scope.
5. Production adapters, real-world APIs, credentials, hardware, cloud state, or human out-of-band action are outside this reference theorem unless separately modeled.

## World-correspondence assumptions

1. Authorized/released state is distinct from executed state.
2. Executed state is distinct from actual world effect.
3. Actual world effect is distinct from observed effect.
4. UNKNOWN, PARTIAL, conflicting, unavailable, or stale observations cannot silently widen reach.
5. Late evidence correction must be represented as evidence/state update, not as retroactive erasure.

## Candidate lemmas

### Lemma 1: Non-creation by identity decomposition

If all agents share a principal `P` and exposure is aggregated at `P`, then splitting actions across agents cannot create aggregate exposure above `P.exposure_limit`.

Evidence: FE001, FE010, V010, V011, exposure-conservation and principal-aggregation mutants.

Open proof obligation: generalize from scalar exposure to correlated/multidimensional envelopes.

### Lemma 2: Single-use release prevents replayed consequence

If a release is consumed on execution and settlement refuses consumed releases, then the same release cannot produce multiple confirmed consequences.

Evidence: FE004, V006, replay and single-use mutants.

Open proof obligation: crash/restart and effect-before-receipt cases require additional recovery assumptions.

### Lemma 3: UNKNOWN is risk-bearing

If an effect is UNKNOWN and the reference semantics hold or preserve reservation/risk until reconciliation, then uncertainty cannot restore capacity by itself.

Evidence: FE005, FE006, V013, V027, unknown-restores-capacity mutant.

Open proof obligation: define reconciliation and late evidence correction semantics precisely enough for proof.

### Lemma 4: Exact binding prevents proposal/execution substitution

If execution checks proposal digest against the released proposal digest, then mutated execution cannot inherit a prior release.

Evidence: FE008, V004, V005, V020, V024, exact-binding mutant.

Open proof obligation: production executor identity and runtime digest conformance are outside the synthetic reference proof.

### Lemma 5: Dependency validity gates reach

If a proposal references a material dependency and settlement requires that dependency to be valid in the current epoch, then failed/stale dependency state cannot produce release.

Evidence: FE007, V018, V019, V031, V032.

Open proof obligation: distributed stale replica and trusted-time semantics need a model of replicas, clocks/epochs, and reconciliation.

### Lemma 6: Finality constrains future reach

If finality records a finalized key and settlement refuses future releases against finalized keys, then finalized consumed reach cannot be reopened without a new semantic rule.

Evidence: FE009, V009, finality-ignored mutant.

Open proof obligation: distinguish finality, compensation, correction, and new settlement.

### Lemma 7: Pairwise compatibility is insufficient for aggregate invariants

There exist aggregate resource invariants where every pair in a set is compatible but the full set is forbidden.

Witness: under `limit=100`, each pair among three `35` reservations has sum `70<=100`, but the triple sum is `105>100`.

This is an independence/counterexample result against ordinary pairwise graph reduction unless k-locality is proved for the invariant class.

## Counterexample witnesses to preserve

### CW-1: Pairwise graph false positive

```text
limit = 100
A = reserve 35
B = reserve 35
C = reserve 35
A+B valid, A+C valid, B+C valid, A+B+C invalid
```

Use: prevents reducing composition to ordinary pairwise compatibility for aggregate exposure.

### CW-2: UNKNOWN-as-no-effect false positive

```text
release 80
execute -> UNKNOWN
new proposal 30
```

If UNKNOWN restores capacity, the system may admit 110 risk-bearing exposure. Current reference holds/refuses depending on scenario.

### CW-3: Restart laundering

```text
release 80
execute -> UNKNOWN
restart
proposal 80
```

If restart clears history/effects, reach widens illegitimately.

### CW-4: Delegation/provenance erasure

```text
agent revoked or lacks authority
proposal succeeds if provenance ignored
```

Current reference refuses; mutant detects.

## Independence results and cautions

1. Pairwise compatibility does not imply global compatibility for aggregate resource envelopes.
2. Authorization of individual operations does not imply validity of their sequence.
3. Observation confidence is not authority; less knowledge cannot be treated as more reach.
4. Restart is not a semantic reset of consequential history.
5. Exact binding is independent of whether a proposal seems substantively similar.
6. Production conformance is independent of reference semantic closure.

## Current experimental evidence summary

| Evidence | Current result | Evidence class |
|---|---|---|
| Frontier scenarios | 10/10 reference pass | experimentally tested / reference semantic |
| Frontier mutants | 14/14 expected mutant detections | mutation tested |
| Phase V pair interactions | 4,760 pair interactions; 9,520 obligations; 0 minimized failures | adversarial / executed within reference scope |
| Recursive chains | 5 chains; 0 minimized failures | adversarial / bounded recursive evidence |
| Higher order | 6,545 triples and 52,360 four-vector combinations considered through reduction/witnesses | reduction evidence, not formal proof |
| Broader mutations | 8/8 mutants detected; 0 survivors | mutation tested |
| Production conformance | blocked; production target not declared | not established |

## Open proof obligations

1. Define `D(tau)` precisely and validate it against existing traces.
2. Define `MF_G` extraction and produce minimal forbidden composition witnesses.
3. Prove or reject k-locality for each invariant family.
4. State which invariants are monotone, non-monotone, additive, non-additive, path-dependent, or epistemic.
5. Formalize `hold` as distinct from `refuse` and `release`.
6. Model release/execution/effect/observation as separate stages.
7. Model finality, correction, compensation, and recovery separately.
8. Separate synthetic reference traces from production-mediated traces.
9. Define what an independent implementation must reproduce before claiming semantic correspondence.
10. Determine whether the current higher-order reduction strategy is sound for each declared invariant class.

## Review questions for a formal-methods person

1. Is the proposed `DependencyCompleteness` definition circular, or can it be made constructive from footprints and envelope predicates?
2. What is the minimal formal state needed to prove non-widening under UNKNOWN?
3. Which invariant classes admit pairwise reduction, and which require k-ary or hypergraph treatment?
4. Can `MF_G` be computed for finite synthetic scenarios in a way that produces useful witnesses?
5. Should `hold` be modeled as refusal, partial transition, or a distinct epistemic state?
6. What assumptions are required for local settlement invariants to imply global trace safety?
7. Where does the current implementation fail to supply adequate information for the theorem target?
8. Which parts are suitable for proof assistant formalization now, and which need more implementation evidence first?

## Non-claims

This packet does not establish:

- universal AI safety;
- a new model of computation;
- production KORE conformance;
- independent reproduction;
- complete higher-order closure;
- correctness of all future CR semantics;
- that pairwise reductions are sound generally;
- that external reality is deterministic or fully observed.

## Next artifact after this packet

A useful next artifact is not a new CR-Core change. It is a read-only analysis tool that reads existing scenarios/traces and emits:

```text
transition footprint,
dependency class,
state fields read/written,
composition interference candidates,
minimal forbidden-composition witnesses where found,
open dependency fields not represented in current state.
```

That tool should fail closed when the footprint is under-specified.
