# Recursive Settlement Evaluator Release Receipt

Release date: 2026-09-27

Baseline commit: `225983d0fef8caa19539e73ad546aa5527f0c945`

Release commits:

- `e995bf1` — evaluator release with Coq proof snapshot
- `225983d` — mobile masthead presentation fix

## Public routes

- General landing: `/`
- Evaluator: `/evaluator/`
- Full technical evaluator: `/evaluator-v2-full/`
- Short demo: `/demo/`
- Evidence: `/evidence/`
- Proofs: `/proofs/`
- Run locally: `/run-locally/`
- Insurance/risk path: `/insurance/`
- Frontier path: `/frontier/`
- Infrastructure path: `/infrastructure/`

## Reproduction

```bash
npm install
npm run start:evaluator
npm run test:official-evaluator
npm run test:evaluator
npm run experiment:frontier-eval
```

Expected frontier/mutant result:

```text
FRONTIER_EVAL_REFERENCE_PASS_MUTANTS_DETECTED: scenarios=10 reference_pass=10/10 mutants_detected=14/14
```

## Coq proof boundary

The Coq proof snapshot is included at `/downloads/coq-20260420-snapshot/`.

The sealed kernel scope is recorded in `/downloads/coq-proof-snapshot-manifest.json`.

The broader snapshot also contains exploratory material. Exploratory files are not presented as closed proof.

## Claim boundary

Implemented: public evaluator routes, local launch command, reference evaluator tests, frontier/mutant harness.

Demonstrated: current reference scenarios and known-bad mutants under the declared synthetic evaluation scope.

Formalized-bounded: Coq proof snapshot under the stated sealed-kernel boundary.

Conjectural/open: broader CR/RRS theory, insurance applicability, independent external validation and production mediation completeness.

Production KORE conformance: OPEN.
