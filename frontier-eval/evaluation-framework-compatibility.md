# Evaluation framework compatibility

Before adding custom model-provider adapters or generalized agent orchestration, evaluate whether the need can be met through established agent-evaluation interfaces.

Preferred order:

1. Keep CR-Core framework-independent.
2. Represent CR experiments using ordinary evaluation concepts: scenario/task, environment, agent/solver, tools/actions, trajectory, grader/scorer, outcome/result, metrics and export.
3. Check compatibility with Inspect AI and similar evaluation frameworks before writing custom orchestration.
4. Add only thin adapters where they preserve CR semantics and reduce integration friction.
5. Avoid provider-specific infrastructure unless a concrete evaluator workflow requires it.

Inspect AI compatibility should be evaluated first because its public model already includes tasks, datasets, solvers, scorers, tools, agents, sandboxes and logs. A CR integration should treat the synthetic CR world as the environment/tool surface, the participant as the solver or agent, and CR invariant checks as scorers/graders.

This does not make Inspect AI a dependency of CR-Core. CR-Core must remain callable as a framework-independent semantic object:

```text
state + proposal -> settlement result + next state + evidence
```

Framework integrations should wrap that object. They must not define it.

Stop before implementing custom adapter infrastructure if an established interface can carry the experiment without altering CR semantics or exposing controlled implementation/IP.
