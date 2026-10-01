# Schema notes

v0.1 exports use four JSON artifacts:

- `manifest.json` — run identity, versions, digests, agent declaration and limitations.
- `scenario.json` — synthetic scenario used for the run.
- `trace.json` — ordered synthetic actions, settlement/execution result, receipts and invariant checks.
- `result.json` — terminal status and invariant results.

These artifacts map to ordinary agent-evaluation concepts:

- scenario/task — the declared problem, initial state and success or failure condition.
- environment — the synthetic CR world and available actions.
- agent/solver — the participant choosing actions.
- trajectory — the recorded sequence of observations, actions, settlements and state changes.
- grader — deterministic CR invariant checks over the trace and terminal state.
- outcome/result — the terminal synthetic consequential state and scored invariant results.

These are examples/documented shapes, not a finalized public standard.
