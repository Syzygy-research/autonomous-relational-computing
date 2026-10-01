# Phase V Conventional Comparator Fixtures

This directory is reserved for normalized conventional-comparator fixtures used by the Phase V experiment.

A complete run requires one file per vector:

```text
V001.json ... V035.json
```

Each fixture must be authored from the conventional comparator model, not copied from Kore internals. The minimum expected structure is:

```json
{
  "vector_id": "V001",
  "comparator_model_version": "phase-v-conventional-comparator-v0.1",
  "pre_state": {},
  "proposed_consequence": {},
  "expected_verdict": "RELEASE|REFUSAL|HOLD|INDETERMINATE|CORRECTION",
  "projected_state_transition": {},
  "authority_consumption": {},
  "exposure_projection": {},
  "uncertainty_evidence_state": {},
  "obligations": [],
  "future_reachability_projection": {},
  "reason_class": "string",
  "claim_boundary": "string"
}
```

Until these files exist, `npm run experiment:phase-v-comparator` must return `BLOCKED_PENDING_COMPARATOR_FIXTURES`.
