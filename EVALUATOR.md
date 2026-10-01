# ARC / VALIS Evaluator

The evaluator is the public examination surface for Consequential Reachability, the first implemented computational object on VALIS, the first implementation of an Autonomous Relational Computer.

The evaluator lets a reviewer inspect:

- a proposed consequential transition;
- the current Consequential Envelope;
- settlement state and relevant relational constraints;
- release or refusal;
- execution state;
- observed or UNKNOWN effect;
- evidence and receipt boundary;
- known-bad mutation/adversarial evidence;
- bounded Coq proof artifacts and their limits.

## Public routes

- `/` general ARC / VALIS landing
- `/architecture/` ARC architecture orientation
- `/evaluator/` canonical evaluator entry
- `/evaluator-v2-full/` full technical evaluator
- `/demo/` guided public evaluation path
- `/evidence/` evidence registry
- `/proofs/` Coq proof snapshot
- `/research/` ARC research program
- `/insurance/` insurance/risk framing over the same evaluator
- `/frontier/` frontier/adversarial framing over the same evaluator
- `/infrastructure/` gateway/infrastructure framing over the same evaluator
- `/run-locally/` local reproduction instructions

## Boundary

The evaluator demonstrates and tests CR/RRS reference behavior. It does not, by itself, prove the ultimate generality of ARC, production VALIS-KORE conformance, universal safety, alignment, external certification, or insurance validity.
