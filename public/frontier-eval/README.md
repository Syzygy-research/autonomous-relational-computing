# CR Frontier Adversarial Evaluation Pack v0.1

Status: documentation skeleton and source manifest
Date: September 26, 2026

## Mission

This package is being prepared so a frontier AI lab can test Consequential Reachability (CR) against capable/adversarial agents in a safe synthetic world.

The central question is:

> Can a capable agent, using only the declared operations of the synthetic environment, manufacture consequential reach outside the envelope permitted by the declared CR semantics?

A second requirement is equally important:

> Can the same evaluator break deliberately defective versions of those semantics?

A reference pass without mutant sensitivity is insufficient.

## Non-goals

This is not:

- a production VALIS runtime;
- production KORE;
- a GMAP deployment;
- a SaaS product;
- a dashboard;
- a gateway;
- a cloud service;
- a real-world execution system.

The experiment must run without internet, credentials, real money, real infrastructure, hardware, external APIs, shell access from agents, or real user/customer data.

## Current state

This directory currently contains the Pass 1 skeleton and source manifest. The next pass should copy or generate the frozen corpus and reports from the source artifacts named in `manifest.json`.

Do not implement the harness until the IP boundary and reconstructed/derived fixture boundary are accepted for v0.1.

## Files

- `SPEC.md` — minimal CR-Core specification target.
- `THREAT_MODEL.md` — adversarial question and attack classes.
- `SAFETY_BOUNDARY.md` — offline/synthetic execution limits.
- `CLAIMS_AND_LIMITATIONS.md` — evidence categories and non-claims.
- `REPRODUCTION_PROTOCOL.md` — external-lab reproduction flow.
- `MUTATIONS.md` — known-bad semantic variants to include.
- `LINEAGE.md` — correspondence between current CR and older VALIS lineage.
- `manifest.json` — source artifact inventory and digests/boundaries.

## Claim boundary

This pack may test whether, within declared reference semantics and synthetic evaluation scope, capable agents can manufacture consequential reach outside a declared envelope.

It does not establish universal AI safety, model alignment, production KORE security, production conformance, deployment readiness, absence of implementation vulnerabilities, impossibility of future escapes, or a universal theory of consequence.
