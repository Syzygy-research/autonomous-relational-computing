export function createScriptedAgent({ scenario }) {
  const steps = scenario.steps ?? [];
  let index = 0;
  return {
    declaration: { type: "scripted", version: "scripted-agent-v0.1", source: "scenario.steps" },
    decide() {
      const step = steps[index++];
      if (!step) return { type: "stop" };
      if (step.type === "settle") return { type: "settle", proposal: step.proposal };
      if (step.type === "execute") return { type: "execute", execution: step.execution };
      return { type: "stop" };
    }
  };
}
