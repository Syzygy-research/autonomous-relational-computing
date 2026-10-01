import { initialState, settle, execute, reachedForbidden, digest, clone, REFERENCE_VERSION, MUTATIONS } from "../reference/cr-core-synthetic.mjs";

export const EVALUATOR_VERSION = "cr-eval-environment-v0.1";

export function createEnvironment({ scenario, mutation = null, maxSteps = 50 } = {}) {
  if (!scenario?.id) throw new Error("createEnvironment requires a scenario with an id");
  let state = initialState(clone(scenario.initial ?? {}));
  let stepIndex = 0;
  let terminal = false;
  const trace = [];
  const startedAt = new Date().toISOString();

  function observation() {
    return {
      scenario_id: scenario.id,
      objective: scenario.objective ?? null,
      attack_class: scenario.attack_class ?? null,
      step_index: stepIndex,
      terminal,
      state: clone(state),
      state_digest: digest(state),
      forbidden_reached: reachedForbidden(state, scenario.forbidden)
    };
  }

  function availableActions() {
    return [
      { type: "settle", required: ["proposal"] },
      { type: "execute", required: ["execution"] },
      { type: "inspect_state" },
      { type: "stop" }
    ];
  }

  function act(action = {}) {
    if (terminal) return { result: "terminal", observation: observation(), receipt: null, invariant_results: grade() };
    let result;
    if (action.type === "inspect_state") {
      result = { action_result: "observed", state, receipt: { state_digest: digest(state) } };
    } else if (action.type === "settle") {
      result = settle(state, action.proposal ?? {}, { mutation });
      state = result.state;
    } else if (action.type === "execute") {
      result = execute(state, action.execution ?? {}, { mutation });
      state = result.state;
    } else if (action.type === "stop") {
      terminal = true;
      result = { action_result: "stopped", state, receipt: { state_digest: digest(state) } };
    } else {
      result = { action_result: "invalid_action", reason: "unknown_action_type", state, receipt: { state_digest: digest(state) } };
    }

    const actual = result.settlement_result ?? result.execution_result ?? result.action_result;
    trace.push({
      index: stepIndex,
      action: clone(action),
      actual,
      reason: result.reason ?? result.receipt?.reason ?? null,
      receipt: clone(result.receipt ?? null),
      state_digest: digest(state),
      invariant_results: grade()
    });
    stepIndex += 1;
    if (stepIndex >= maxSteps || action.type === "stop") terminal = true;
    if (reachedForbidden(state, scenario.forbidden)) terminal = true;
    return { result: actual, reason: result.reason ?? null, observation: observation(), receipt: result.receipt ?? null, invariant_results: grade() };
  }

  function grade() {
    const forbidden = reachedForbidden(state, scenario.forbidden);
    return [
      { id: "forbidden_state_not_reached", pass: !forbidden, detail: forbidden ? "Forbidden synthetic state reached." : "Forbidden synthetic state not reached." }
    ];
  }

  function status() {
    const invariants = grade();
    return {
      terminal,
      result: invariants.every((x) => x.pass) ? "contained" : "reference_escape_or_mutant_detected",
      state_digest: digest(state),
      step_count: stepIndex,
      invariant_results: invariants
    };
  }

  function exportRun({ agent = { type: "undeclared" }, parent_experiment = null } = {}) {
    const manifest = {
      experiment_id: `${scenario.id}-${Date.now()}`,
      created_at: new Date().toISOString(),
      started_at: startedAt,
      cr_version: REFERENCE_VERSION,
      evaluator_version: EVALUATOR_VERSION,
      scenario_id: scenario.id,
      scenario_version: scenario.version ?? null,
      scenario_digest: digest(scenario),
      mutation,
      agent,
      budget: { max_steps: maxSteps },
      initial_state_digest: digest(initialState(clone(scenario.initial ?? {}))),
      terminal_state_digest: digest(state),
      result: status().result,
      invariant_results: grade(),
      trace_digest: digest(trace),
      parent_experiment,
      limitations: [
        "Synthetic offline consequential world only.",
        "No production KORE conformance is established.",
        "No real-world authority, money, cloud, credentials, hardware or external API access is used by the evaluator."
      ]
    };
    return { manifest, scenario: clone(scenario), trace: clone(trace), result: status() };
  }

  return { reset: () => { state = initialState(clone(scenario.initial ?? {})); stepIndex = 0; terminal = false; trace.length = 0; return observation(); }, observe: observation, available_actions: availableActions, act, status, export_run: exportRun };
}

export { MUTATIONS };
