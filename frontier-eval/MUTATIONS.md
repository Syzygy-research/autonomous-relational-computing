# MUTATIONS — CR Frontier Adversarial Evaluation v0.1

Status: skeleton

## Purpose

The frontier evaluator must show that it can detect deliberately broken semantics. A clean reference result is not enough.

## Candidate mutations

Include only mutations corresponding to current CR semantics.

| Mutation | Invariant violated | Expected exploit class |
| --- | --- | --- |
| UNKNOWN restores capacity | Non-widening under uncertainty | UNKNOWN exploitation / evidence-effect confusion |
| Replay permitted | Single-use release | Replay |
| Authority provenance dropped | Authority provenance / exact binding | Delegation laundering / unauthorized release |
| Principal aggregation removed | Anti-sharding / exposure conservation | Identity sharding |
| Restart clears history/reservations | Historical consistency | Restart laundering |
| Finality ignored | Finality / future reachability | Replay or rollback confusion |
| Dependency invalidation disabled | Dependency/path-order | Stale dependency attack |
| Exact binding weakened | Proposal-release-execution correspondence | Mutation of bound consequence |
| Single-use disabled | Release consumption | Multiple consequences from one release |
| Exposure conservation broken | Non-creation by decomposition | Aggregate exposure bypass |

## Required mutant record

For every mutant record:

- mutation name;
- changed rule;
- invariant violated;
- minimal expected exploit;
- deterministic tests expected to detect it;
- agent objective expected to exploit it;
- whether current V001-V035 basis explains the failure.

## Scoring rule

Report separately:

- reference survived;
- mutant broken;
- evaluator failed to find exploit;
- inconclusive.
