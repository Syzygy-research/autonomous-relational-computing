# SPEC — Minimal CR-Core Frontier Evaluation v0.1

Status: skeleton

## Purpose

Define the smallest independently implementable semantics sufficient for an external evaluator to reproduce the declared CR reference behavior in a synthetic world.

Conceptual interface:

```text
initial relational state + proposal -> settlement result + next state + receipt
```

## Required semantic fields

Include a field only when it changes Consequential Reachability.

The v0.1 spec must define:

- entities;
- principals;
- agents;
- identity relationships;
- authority and provenance;
- resources and exposure;
- delegation;
- reservations;
- dependencies;
- proposal identity;
- release identity;
- execution/effect state;
- observation and UNKNOWN;
- finality;
- replay / single-use;
- relevant temporal state;
- receipt and state digest.

## Settlement outcomes

Use the current CR/KORE reference vocabulary as extracted from the corpus and comparator reports. Do not introduce new outcome terms just to match external evaluator language.

## Core invariants to preserve

- Identity multiplication must not manufacture aggregate consequential capacity.
- Delegation must not widen beyond legitimately transferable authority.
- Individually admissible actions must not bypass shared/cumulative exposure through composition.
- Concurrent actions must not double-consume capacity.
- A release must be single-use unless a legitimate new release exists.
- Restart must not restore consumed or unavailable reach.
- UNKNOWN external effects must not widen authority or exposure.
- Executed-but-unobserved is not equivalent to never-executed.
- Stale dependency, stale epoch, or stale trusted-time state must not create illegitimate reach.
- Exact binding must connect proposal, settlement, release, execution/effect, receipt, and future state.

## Required source reconciliation

This spec must be populated from:

- `conformance/corpus/V001.json` through `V035.json`;
- `conformance/comparator/phase-v/V001.json` through `V035.json`;
- Phase V reports listed in `manifest.json`;
- the lineage/correspondence note in `LINEAGE.md`.

Do not infer semantics from the handoff alone.
