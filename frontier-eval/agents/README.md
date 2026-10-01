# Agents

The evaluator does not require a model provider.

- `scripted-agent.mjs` replays scenario steps and verifies the environment.
- `custom-agent-template.mjs` shows the minimal adapter shape for a user-supplied intelligence.

In standard evaluation language, this layer is the agent or solver. It receives observations and available actions from the environment, chooses actions, and leaves the evaluator to record the trajectory and grade the outcome.

Provider-specific harnesses, prompts, tool orchestration, memory and retries belong outside CR-Core. The evaluator owns the synthetic world, trajectory, grader and result.

Before implementing a custom model-provider adapter or generalized agent orchestration, evaluate compatibility with Inspect AI and other established agent-evaluation interfaces. Prefer a standards-compatible wrapper when it can carry the scenario/task, environment, solver/agent, tools/actions, trajectory, scorer/grader and result without altering CR semantics or adding unnecessary dependency.

CR-Core must remain framework-independent. Framework integrations should wrap the CR semantic object; they must not define it.

Keep provider API keys outside the repository, traces and exports.
