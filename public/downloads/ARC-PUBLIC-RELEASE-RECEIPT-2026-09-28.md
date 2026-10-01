# ARC Public Release Receipt

Status: prepared for GMAP-gated commit, standalone repository publication, and deployment.

## Canon

- Relational Autonomous Computing: canonical paradigm.
- Autonomous Relational Computer (ARC): canonical computer class.
- VALIS: first implementation being put forward.
- VALIS-KORE / CR-Core: framework-independent kernel for supported settlement semantics.
- Relation: primitive.
- Consequential Reachability: first implemented computational object.
- Recursive Relational Settlement: core mechanism.
- Consequential Envelope: current boundary representation.
- Semantics / invariants / executable vectors: public test specification boundary.
- Evaluator: external examination instrument.
- Gateway / infrastructure layer: integration surface, not CR itself.
- Noetica: interpretive/navigation intelligence.
- Observation Deck: human environment.

## Verified artifact counts

- Reconstructed candidate corpus vectors: 35, from conformance/corpus/MANIFEST.json.
- Phase V comparator fixtures: 35, from conformance/comparator/phase-v/MANIFEST.json.
- Phase V comparator result: 35/35 matches across seven scored axes, from conformance/reports/phase-v-comparator-experiment.json.
- Phase V closure result: 4,760 pair interaction cases, 9,520 checked pair obligations, 5 recursive chains, 8/8 broader mutants detected, 0 survivors, from conformance/reports/phase-v-closure-execution.json.
- Frontier Eval v0.1: 10 reference scenarios, 10/10 reference pass, 14/14 expected mutants detected, from frontier-eval/reports/frontier-eval-report.json.

## Verification performed before GMAP publication gate

- npm run test:official-evaluator: PASS.
- npm run test:evaluator: PASS.
- npm run experiment:frontier-eval: PASS.
- Local route checks: PASS for /, /architecture/, /evaluator/, /evaluator-v2-full/, /demo/, /evidence/, /proofs/, /research/, /insurance/, /frontier/, /infrastructure/, /run-locally/, proof manifest, and frontier eval report.
- Standalone package reproduction: PASS for npm install, npm run test:official-evaluator, npm run test:evaluator, npm run experiment:frontier-eval.
- Standalone package disclosure scan: PASS for targeted private/internal/stale terms.
- Standalone package link scan: PASS.

## Public/private boundary

Public package includes the intended evaluator, public evidence artifacts, public docs, bounded Coq proof snapshot, public routes, tests, and reproduction commands.

Excluded from the standalone public package: production KORE internals, protected gateway implementation, credentials, private corpus, private founder/company operating material, internal deployment credentials, and unrelated internal artifacts.

## Deployment status

Publication and deployment remain GMAP-gated. This receipt describes the prepared baseline before public commit, public repository creation/push, and deployment.

## Claim boundary

- Implemented: public evaluator, CR/RRS synthetic environment, proposal/boundary/settlement/release/effect/evidence views, known-bad mutation harness, proof snapshot route.
- Demonstrated: official evaluator verification, evaluator model tests, frontier/mutant synthetic harness, Phase V comparator/closure artifacts under stated boundaries.
- Formalized -- bounded: Coq proof snapshot and theorem packet under declared assumptions.
- Research: ARC generalization and ARC-0 calculus.
- Production KORE conformance: not established by this release.
