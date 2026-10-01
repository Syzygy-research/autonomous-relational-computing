# CR/RRS Compositional Kernel Reconciliation

Date: 2026-09-27
Status: implementation-correspondence draft
Scope: current repository evidence only; no CR-Core changes

## Purpose

This report reconciles the proposed CR/RRS compositional kernel against the implementation and corpus currently in this repository. It treats the proposed abstractions as candidates to test against code and evidence, not as assumptions to retrofit into the evaluator.

The core instruction for this pass is strict:

> Do not modify CR-Core merely to make the theory fit. If the implementation contradicts the proposed calculus, preserve the contradiction and surface it.

## Evidence inspected

| Evidence surface | Artifact | What it contributes | Boundary |
|---|---|---|---|
| Synthetic CR reference | `frontier-eval/reference/cr-core-synthetic.mjs` | Executable settlement, execution, digest, mutation, and forbidden-state behavior for the public frontier-eval package. | Synthetic reference semantics only; not production KORE. |
| Frontier scenarios | `frontier-eval/scenarios/frontier-scenarios.json` | Ten adversarial scenario families, expected reference outcomes, and expected mutant detections. | Scenario-level evidence, not a universal scenario generator. |
| Frontier run report | `frontier-eval/reports/frontier-eval-report.json` | 10/10 reference pass, 14/14 expected mutant detections, zero survivors in the frontier pack. | Local/internal run; not independent validation. |
| Reconstructed candidate corpus | `conformance/corpus/MANIFEST.json`, `conformance/corpus/V001.json` through `V035.json` | Thirty-five candidate vectors, expected typed outcomes, and digest manifest. | New reconstructed candidate corpus; not exact recovered historical fixture bytes. |
| Phase V adversarial sweep | `conformance/reports/phase-v-adversarial-sweep.json` | 35 seeds, 1,120 first-order generated cases, 4,760 pair interaction cases, 6,545 triples, 52,360 four-vector combinations, five recursive chains, metamorphic properties. | Search-space construction; not by itself execution of every higher-order case. |
| Phase V closure execution | `conformance/reports/phase-v-closure-execution.json` | 4,760 pair interactions, 9,520 checked pair obligations, five recursive chains, higher-order reduction witnesses, 8/8 broader semantic mutants detected, zero unexplained minimized failures. | Repository-local reference closure; production conformance blocked until production target declared. |
| Scientific lineage | `docs/valis-scientific-lineage.md` | Relation -> canonical state -> covenant/refusal -> GMAP -> value -> CR framing and candidate laws. | Scientific reconstruction, not proof. |
| Public examination reconciliation | `docs/recursive-settlement-public-examination-reconciliation.md` | Existing evidence audit and claim-boundary cautions, including documentary-only flags for fuzz/differential claims not first-class in this pass. | Presentation/evidence architecture, not semantics. |

## Candidate abstraction disposition

Disposition vocabulary:

- **Already present in code**: directly represented by current executable state, function, scenario, or report fields.
- **Derivable from existing semantics**: can be reconstructed as an interpretation over existing fields/traces without changing CR-Core.
- **Requires explicit semantic addition**: plausible but not currently explicit enough to claim as current semantics.
- **Reject or narrow**: proposed abstraction does not accurately describe the implementation as stated, or would overclaim.

| Candidate abstraction | Disposition | Implementation correspondence | Notes / boundary |
|---|---|---|---|
| `ConsequentialDependency` | Derivable from existing semantics | The reference state has `dependencies`, `dependency_id`, epoch checks, authority/provenance checks, exposure/reservation coupling, release consumption, finality, and prior-effect gates. Phase V uses dependency, stale, race, shared dependency, and composition obligations. | There is no single typed `ConsequentialDependency` object. It should be introduced first as a classification over existing dependency-bearing fields, not as a new runtime primitive. |
| `StateAdequacy` | Derivable, partially already present | `settle(state, proposal)` consults principals, agents, dependencies, releases, effects, finalized, history, tick, and epoch. Refusals/holds preserve pre/post state digests. The corpus has verifier unavailable, ledger unavailable, stale state, observation conflict, late evidence correction, and runtime digest mismatch vectors. | Adequacy is not currently a theorem. It can be stated as an obligation: every field that can change CR must be represented in state or in a declared external assumption. |
| `CompositionSoundness` | Derivable in bounded reference scope | Phase V closure executed pair interactions and checked pair obligations; FE010 and V030 explicitly show composition non-triviality. The closure report states no unexplained minimized failures in this encoded scope. | The current closure report uses reduction strategy for higher-order combinations. That is evidence for the encoded obligation set, not a proof that all future higher-order interference reduces to pair obligations. |
| Transition footprint `D(tau)` | Requires explicit semantic addition | A footprint can be approximated from existing read/write/effect fields: `agent_id`, `principal_id`, `operation`, `amount`, `dependency_id`, `release_id`, `finality_key`, `prior_effect`, `restart`, consumed release, effects, and state digests. | No current function returns `D(tau)`. Do not claim footprint semantics are implemented until a read/write/effect-set extractor is specified and validated against traces. |
| Minimal forbidden compositions `MF_G` | Requires explicit semantic addition | FE010 demonstrates a minimal two-step composition: first 60 release succeeds, second 50 release is refused because reserved+used would exceed 100. Phase V higher-order reductions consider triples/fours but do not currently enumerate minimal forbidden sets as first-class artifacts. | `MF_G={X: not G(Compose(X)) and every proper subset passes}` is a good research object, but current reports provide witnesses/reductions, not a complete MF enumerator. |
| Higher-order forbidden composition | Already present as an evidence concern; requires stronger formal handling | Phase V counts 6,545 triples and 52,360 four-vector combinations considered through reduction/witnesses. The handoff's 35+35+35>100 example is a concrete warning that pairwise compatibility is insufficient in resource invariants. | Current closure says higher-order combinations reduce to pairwise composition obligations plus seed-level metamorphic obligations in this encoded pass. That reduction itself is a proof obligation, not something to assume globally. |
| Global consequential closure `CR*_Gamma(Sigma0) subseteq G` | Research conjecture / theorem target | Current code supports local settlement and bounded synthetic traces. Phase V closure supports no unexplained minimized failures within declared reference scope. | Not established as a theorem. Needs explicit mediation assumptions, world-correspondence assumptions, state adequacy, dependency completeness, and composition soundness. |
| Identity dependency domain | Already present | Agents map to principals; revoked agents lose authority; shared principal aggregation blocks sharding. FE001, FE002, V002, V003, V011, V028. | Domain-specific dependency, not universal primitive. |
| Resource/exposure dependency domain | Already present | Principal exposure limit, used/reserved, amount checks, exposure conservation mutant, correlated/multidimensional vectors. FE001, FE003, FE010, V010, V011, V026, V035. | The synthetic reference has a simple scalar exposure model; multidimensional/correlated exposure is in corpus/evidence, not fully expressed in `cr-core-synthetic.mjs`. |
| Authority/provenance dependency domain | Already present | Agent authority, revocation, exact binding, wrong executor/runtime digest, forged receipt. FE002, FE008, V002-V005, V020, V022, V024, V025, V028. | Delegation is represented by vector/scenario classes more than by a rich delegation graph in the synthetic reference. |
| History/finality dependency domain | Already present | Releases, consumed flag, history, finalized map, replay refusal, restart hold, finality refusal. FE004, FE006, FE009, V006, V009, V015, V021, V023, V029, V033. | History is simple in synthetic reference; production crash/reconciliation obligations remain separate. |
| Epistemic dependency domain | Already present | Effects map, `UNKNOWN`, `PARTIAL`/observation vectors, prior-effect hold, unknown-restores-capacity mutant. FE005, FE006, V013, V014, V027, V029, V034. | UNKNOWN is epistemic/risk-bearing; it must not be collapsed into never-executed. |
| Causality/time as independent primitive | Reject or narrow | Current implementation uses tick/epoch, dependency epoch, expiry vectors, stale state, causal race ordering, and event reordering operators. | Treat causality/time as mechanisms affecting state validity and dependency freshness unless a later formal model justifies them as primitive domains. |

## Implementation-derived dependency classes

The current evidence supports dependency classes rather than one monolithic dependency primitive.

| Dependency class | Existing fields / reports | Example vectors and scenarios | Current finding |
|---|---|---|---|
| Identity/principal | `agents.*.principal`, `principals`, shared aggregation | FE001, V011 | Already present. |
| Authority/provenance | `agents.*.authority`, `revoked`, proposal operation, exact binding digest, executor/runtime vectors | FE002, FE008, V002-V005, V020, V024, V028 | Already present; richer delegation graph would be addition. |
| Resource/exposure | `exposure_limit`, `exposure_used`, `reserved`, proposal amount | FE001, FE003, FE010, V010, V026, V035 | Already present for scalar reference; multidimensional exposure is corpus-level. |
| Release/execution | `releases`, `consumed`, `proposal_digest`, `execute()` | FE004, FE008, V006 | Already present. |
| Effect/observation | `effects`, `UNKNOWN`, observation-conflict vectors | FE005, FE006, V013, V014, V027, V034 | Already present with synthetic UNKNOWN semantics. |
| Finality/history | `finalized`, `history`, restart behavior | FE006, FE009, V009, V015, V021, V029, V033 | Already present; crash/recovery production obligations remain open. |
| Dependency/freshness | `dependencies.*.status`, `dependencies.*.epoch`, state epoch | FE007, V018, V019, V031, V032 | Already present in synthetic form; distributed stale-replica semantics remain broader than this reference. |
| Composition/global envelope | Phase V pair/chain/higher-order reports; FE010; V030 | FE010, V030, Phase V closure | Present as test/evidence apparatus, not a closed theorem. |

## Candidate transition footprint

A conservative transition footprint can be derived for analysis, but it is not yet a CR-Core API.

For a settlement transition `tau = settle(S, p)`, the current synthetic reference suggests:

```text
D(tau).reads = {
  agent[p.agent_id],
  principal[p.principal_id or agent.principal],
  dependency[p.dependency_id],
  releases[p.release_id or p.proposal_id],
  finalized[p.finality_key],
  effects[*] when p.restart or p.prior_effect is UNKNOWN,
  epoch,
  history for restart/history-sensitive behavior
}

D(tau).writes_if_release = {
  releases[release_id],
  principal[principal_id].reserved,
  history,
  tick
}

D(tau).writes_if_hold_or_refuse = {
  tick and receipt/digest evidence only in the reference wrapper
}
```

For an execution transition `tau = execute(S, e)`:

```text
D(tau).reads = {
  releases[e.release_id],
  release.proposal_digest,
  release.consumed,
  principal[release.principal_id]
}

D(tau).writes_if_executed = {
  releases[e.release_id].consumed,
  effects[e.release_id],
  principal.reserved,
  principal.exposure_used when CONFIRMED,
  finalized[e.finality_key],
  history
}
```

This proposed `D(tau)` is useful for proof work, trace minimization, and composition analysis. It should remain classified as **requires explicit semantic addition** until implemented as a validated extractor and checked against existing traces.

## Higher-order composition warning

The handoff example matters:

```text
35 + 35 <= 100 for every pair, while 35 + 35 + 35 > 100.
```

This is not a corner case. It is the reason resource/exposure composition cannot be reduced to an ordinary pairwise graph without a proof that the invariant class is pairwise-decomposable.

Current evidence posture:

- Pair interactions: `4,760` executed interaction cases and `9,520` checked obligations in `phase-v-closure-execution.json`.
- Higher order: `6,545` triples and `52,360` four-vector combinations considered through reductions/witnesses.
- This supports the existence of a higher-order concern, but the reduction from higher-order search to pair/seed obligations remains a formal obligation.

Candidate formal rule:

```text
Pairwise compatibility is admissible as a reduction only for invariant families with an explicit k-locality proof.
```

For aggregate exposure, the natural locality is not pairwise by default; it depends on the aggregate capacity and all active reservations/used amounts under the shared principal or correlated envelope.

## Reclassification of canonical vectors

| Vector | Title | Dependency classes | Formalization role |
|---|---|---|---|
| V001 | Baseline Release | authority, resource, dependency, release | Positive seed for ordinary release. |
| V002 | Authority Absent | authority/provenance | Authority dependency completeness. |
| V003 | Self-Approval | authority/provenance, evidence | Authority cannot be manufactured by actor self-claim. |
| V004 | Payload Mutation | exact binding, evidence | Transition identity / binding soundness. |
| V005 | Target Mutation | exact binding, target identity | Transition identity / binding soundness. |
| V006 | Replay | release/execution, history | Single-use and historical consistency. |
| V007 | Expiry | temporal/freshness | Time as validity mechanism. |
| V008 | Pre-Finality Revocation | authority, finality | Revocation before finality blocks reach. |
| V009 | Post-Finality Revocation | finality, evidence | Evidence required after finality; revocation does not reverse completed effects. |
| V010 | Aggregate Exposure | resource/exposure, composition | Resource conservation. |
| V011 | Shared-Principal Anti-Sharding | identity/principal, resource | Non-creation by decomposition. |
| V012 | Concurrency | resource, ordering | Serialization / double-consumption boundary. |
| V013 | UNKNOWN Effect | epistemic/effect | Non-widening under uncertainty. |
| V014 | PARTIAL Effect | epistemic/effect | Non-scalar observation adequacy. |
| V015 | Restart Non-Widening | history, epistemic, restart | Restart cannot erase consequential history. |
| V016 | Verifier Unavailable | state adequacy, evidence | Missing verifier holds rather than widens. |
| V017 | Ledger Unavailable | state adequacy, evidence | Missing ledger holds rather than widens. |
| V018 | Failed Dependency | dependency/freshness | Dependency validity gates release. |
| V019 | Stale State | freshness/epoch | Stale state cannot widen reach. |
| V020 | Wrong Executor | authority/provenance, exact binding | Executor identity matters. |
| V021 | Effect Before Receipt Crash | history, evidence, epistemic | External effect and receipt can diverge; indeterminate boundary. |
| V022 | Forged Receipt | evidence/provenance | Evidence correspondence. |
| V023 | Scoped Recovery | history, evidence, recovery | Recovery requires scoped settlement. |
| V024 | Runtime Digest Mismatch | implementation identity, exact binding | Runtime identity as state adequacy / conformance dependency. |
| V025 | LIVE_BOUND Authority Revocation | authority, runtime state | Revocation over live-bound authority. |
| V026 | Correlated Counterparty Exposure | resource/correlation | Exposure beyond scalar principal. |
| V027 | UNKNOWN Effect Plus New Authorization | epistemic, authority, resource | New authorization does not erase unknown risk. |
| V028 | Nested Delegation | authority/delegation | Delegation boundedness. |
| V029 | Late Evidence Correction | evidence, epistemic, history | Evidence can update state; correction is not silent widening. |
| V030 | Locally Safe Globally Forbidden | composition/global envelope | Local-to-global coherence seed. |
| V031 | Causal Race Ordering | ordering/freshness | Causal ordering as state validity mechanism. |
| V032 | Shared Dependency Exposure | dependency, resource, composition | Shared dependencies create composition interference. |
| V033 | Compensation vs Prevention | finality, evidence, value/recovery | Compensation does not equal prevention. |
| V034 | Observation Conflicts | epistemic/evidence | Observation adequacy and conflict handling. |
| V035 | Multidimensional Consequence Envelope | resource/vector envelope, composition | Multidimensional reachability geometry seed. |

## Reclassification of frontier scenarios and mutants

| Scenario | Attack class | Dependency classes | Mutants expected to break it | Formalization role |
|---|---|---|---|---|
| FE001 | identity_sharding | identity/principal, resource | `principal_aggregation_removed`, `exposure_conservation_broken` | Non-creation by decomposition. |
| FE002 | delegation_laundering | authority/provenance | `authority_provenance_dropped` | Delegation/authority boundedness. |
| FE003 | concurrency | resource, ordering | `exposure_conservation_broken`, `principal_aggregation_removed` | Double-consumption prevention. |
| FE004 | replay | release/execution, history | `replay_permitted`, `single_use_disabled` | Historical consistency and single-use release. |
| FE005 | unknown_exploitation | epistemic/effect, resource | `unknown_restores_capacity` | Non-widening under uncertainty. |
| FE006 | restart_laundering | history, epistemic, restart | `restart_clears_history` | Restart non-widening. |
| FE007 | dependency_path_order | dependency/freshness | `dependency_invalidation_disabled` | Dependency completeness. |
| FE008 | evidence_effect_confusion | exact binding, execution/effect | `exact_binding_weakened` | Proposal/release/execution correspondence. |
| FE009 | finality | finality/history | `finality_ignored` | Finality constrains future reach. |
| FE010 | composition | resource, shared principal, composition | `principal_aggregation_removed`, `exposure_conservation_broken` | Minimal forbidden composition seed. |

The frontier report records `10/10` reference scenarios passing and `14/14` expected mutant detections. This supports discriminator quality for the encoded semantic obligations; it does not establish universal containment.

## Reclassification of Phase V closure material

| Evidence class | Current artifact result | Formal meaning | Boundary |
|---|---|---|---|
| Pair interactions | `4,760` executed pair interaction cases; `9,520` checked pair obligations; zero minimized failures. | Strong evidence that encoded pairwise interaction obligations reduce to existing seed/metamorphic properties in this closure run. | Pair coverage is not enough for all resource or dependency invariants unless k-locality is proven. |
| Recursive chains | Five executed chains; zero minimized failures. | Evidence for bounded recursive state/update preservation across selected chain templates. | Not a proof of arbitrary-length closure. |
| Higher-order reductions | `6,545` triples and `52,360` four-vector combinations considered through reduction/witnesses. | Evidence of higher-order search-space awareness and reduction apparatus. | Reduction correctness is an open proof obligation. |
| Broader mutations | 8/8 encoded mutants detected, zero survivors. | The apparatus can break known-bad semantics for the selected obligation classes. | Mutants are semantic mutants, not arbitrary implementation defects. |
| Production conformance | Blocked because production target not declared. | Correctly separates reference semantics from KORE production conformance. | No production claim can advance from this report alone. |

## Finding on the proposed implication

Candidate obligation:

```text
DependencyCompleteness
and StateAdequacy
and CompositionSoundness
=> CR*_Gamma(Sigma0) subseteq G
```

Current disposition: **research theorem target, not established**.

What the repository currently supports:

1. A concrete synthetic state machine where local settlement reads enough fields to enforce several important CR obligations.
2. A reconstructed 35-vector corpus covering authority, exact binding, replay, exposure, uncertainty, restart, dependency, stale state, delegation, finality, evidence, causal ordering, and multidimensional envelope cases.
3. A frontier adversarial package showing reference scenarios pass and deliberately broken mutants fail.
4. A Phase V closure report showing no unexplained minimized failures within the encoded reference closure scope.

What remains open before theorem promotion:

1. Define `DependencyCompleteness` without smuggling in the result: every CR-changing dependency must either be represented in state or explicitly named as an assumption.
2. Define `StateAdequacy`: the state representation must be adequate for the proposed transition class and envelope `G`.
3. Define `CompositionSoundness`: composition/reduction rules must preserve every dependency class relevant to `G`, including higher-order resource aggregation.
4. Prove or reject k-locality for any pairwise reduction used over aggregate exposure, shared dependencies, causal races, and multidimensional envelopes.
5. State mediation assumptions: every consequential transition is routed through settlement.
6. State world-correspondence assumptions: external effect and observation are not collapsed; UNKNOWN/partial/conflicting observations remain risk-bearing.
7. Separate synthetic reference proof obligations from production KORE conformance.

## Contradictions or non-fits preserved

No direct contradiction was found between the candidate calculus and the current synthetic reference. However, several proposed names would overclaim if promoted now:

- `ConsequentialDependency` is not an implemented type.
- `D(tau)` is not an implemented footprint extractor.
- `MF_G` is not enumerated by current reports.
- Higher-order closure is considered/reduced, not exhaustively independently executed as all triples/fours.
- Global consequential closure is not proved.
- Causality/time should remain a mechanism over state validity, freshness, epoch, expiry, and ordering rather than an independent primitive until formal evidence says otherwise.

These are not failures; they are the useful boundary for the next formal packet.

## Recommended next formal work

1. Implement a non-authoritative `footprint` analysis tool over existing traces without changing CR-Core.
2. Use FE010 and constructed aggregate examples to test minimal forbidden composition extraction.
3. Extend higher-order examples specifically with `35+35+35>100` to prevent accidental pairwise-graph reduction.
4. Draft k-locality conditions for each invariant class: exposure, authority, dependency, history, epistemic state, finality, evidence.
5. Prepare the theorem packet in `docs/cr-rrs-theorem-packet-v0.md` for formal-methods review.
