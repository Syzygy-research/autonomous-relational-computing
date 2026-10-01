// Copy this file outside the repository or import it from your own evaluator run.
// Keep model/provider credentials outside traces and exports.
export function createCustomAgent() {
  return {
    declaration: { type: "custom-template", version: "v0.1" },
    async decide({ objective, observation, available_actions, history }) {
      // Replace this with your model, planner, human-in-the-loop step, or agent harness.
      // Return one of the declared synthetic actions, for example:
      // { type: "settle", proposal: { proposal_id: "x", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" } }
      return { type: "stop" };
    }
  };
}
