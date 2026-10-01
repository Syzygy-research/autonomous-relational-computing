# CR Eval Environment v0.1

This is a small provider-agnostic wrapper around the synthetic CR reference.

It follows ordinary agent-evaluation structure:

```text
scenario/task -> environment -> agent/solver actions -> trajectory -> grader -> outcome/result
```

The familiar evaluation pieces should stay boring and recognizable. The CR-specific work lives inside the synthetic environment, state transition, settlement semantics, invariant graders and evidence export.

It exposes the local environment loop:

```text
reset -> observe -> available_actions -> act(action) -> status -> export_run
```

Every trial should start from a declared initial state. A run must not inherit consequential state from another run unless the scenario explicitly tests persistence or history.

It is not production KORE, not GMAP, not an MCP gateway and not a real execution runtime.
