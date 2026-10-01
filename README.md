# Autonomous Relational Computing / VALIS

Relational Autonomous Computing begins from relation as a computational primitive. VALIS is the first implementation of a proposed computer class called the Autonomous Relational Computer (ARC). Its first implemented computational object is Consequential Reachability, computed through Recursive Relational Settlement.

This repository is the public examination package for the current ARC / VALIS evaluator release. It is not the private production VALIS-KORE repository, not a gateway implementation, and not a claim of production conformance.

## Provenance

The work behind VALIS began fourteen years before its first public implementation, with an investigation into relation as a primitive: what changes when entities, state, knowledge and transformation are understood relationally rather than treating relation as metadata around independent objects?

The computational challenge became: if relation is primitive, what does a computer built around that primitive actually compute? That investigation produced relational state, evidence, authority, transition semantics, composition, recursion, and Recursive Relational Settlement. Consequential Reachability is the first implemented computational object exposed through this release.

## Public architecture

- **Relational Autonomous Computing**: the proposed computing paradigm.
- **Autonomous Relational Computer (ARC)**: a computer class in which state and permissible transitions are determined through explicit relational computation.
- **VALIS**: the first implementation being put forward.
- **VALIS-KORE / CR-Core**: the framework-independent kernel implementing the supported public settlement semantics.
- **Relation**: the primitive.
- **Consequential Reachability (CR)**: the first implemented computational object.
- **Recursive Relational Settlement (RRS)**: the core mechanism that settles, releases, evidences, and updates consequential reach.
- **Consequential Envelope**: the current boundary representation.
- **Evaluator**: the external examination surface.

## Open the public surfaces

- Public site: https://recursive-settlement.com/
- Architecture: /architecture/
- Evaluator: /evaluator/
- Guided evaluation: /demo/
- Evidence: /evidence/
- Proofs: /proofs/
- Run locally: /run-locally/

## Local launch

```bash
npm install
npm run start:evaluator
```

Then open the local URL printed by the server, usually:

```text
http://localhost:8787/evaluator/
```

## Reproduce supported checks

```bash
npm run test:official-evaluator
npm run test:evaluator
npm run experiment:frontier-eval
```

Expected frontier/mutant result from the current public artifact set:

```text
FRONTIER_EVAL_REFERENCE_PASS_MUTANTS_DETECTED: scenarios=10 reference_pass=10/10 mutants_detected=14/14
```

## Claim boundary

Implemented means executable material exists in this public package. Demonstrated means it has been exercised by the current test/evidence artifacts. Formalized -- bounded means a proof artifact applies only within its stated assumptions and scope. Research means motivated by the architecture but not established by this release.

This package does not establish universal computational generality, universal safety, production KORE conformance, external certification, deterministic external effects, perfect observability, or native ARC hardware/operating-system claims.
