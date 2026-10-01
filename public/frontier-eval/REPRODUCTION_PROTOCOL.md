# REPRODUCTION_PROTOCOL — CR Frontier Adversarial Evaluation v0.1

Status: skeleton

## External evaluator goal

An external evaluator should be able to:

1. understand the declared CR semantics without production VALIS access;
2. independently implement a comparator;
3. reproduce the frozen canonical corpus;
4. run capable agents against synthetic forbidden-state objectives;
5. preserve and minimize complete attack traces;
6. demonstrate evaluator sensitivity by breaking deliberately defective semantics;
7. report unexplained reference escapes as falsifying/adversarial results;
8. do all of the above without real-world consequential authority.

## Intended protocol

1. Read `CLAIMS_AND_LIMITATIONS.md` and `SAFETY_BOUNDARY.md`.
2. Read `SPEC.md`.
3. Verify corpus and report digests from `manifest.json`.
4. Run the reference semantics over the frozen corpus.
5. Implement an independent comparator from `SPEC.md` without production KORE access.
6. Run reference versus comparator over frozen corpus and generated synthetic cases.
7. Run deterministic adversarial scenarios.
8. Run open-ended agent objectives.
9. Run multi-agent objectives.
10. Run semantic mutants and confirm expected failures.
11. Minimize any escape/divergence.
12. Classify each result using the counterexample disposition path.

## Required report output

Reports should include:

- source manifest digest;
- corpus digest;
- comparator implementation identity;
- reference implementation identity;
- scenario IDs;
- complete traces;
- minimized traces where applicable;
- expected behavior;
- actual behavior;
- violated invariant;
- state/digest differences;
- disposition against V001-V035 or candidate V036+.

## Non-claim

Internal comparator agreement remains internal differential evidence until an external implementation exists and runs.
