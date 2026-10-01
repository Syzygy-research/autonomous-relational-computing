import crypto from "node:crypto";

export const REFERENCE_VERSION = "cr-frontier-reference-v0.1-synthetic";

export const MUTATIONS = {
  unknown_restores_capacity: "UNKNOWN restores capacity instead of holding it risk-bearing.",
  replay_permitted: "Single-use releases can be replayed.",
  authority_provenance_dropped: "Authority provenance is ignored.",
  principal_aggregation_removed: "Shared-principal exposure aggregation is ignored.",
  restart_clears_history: "Restart clears reservations/history.",
  finality_ignored: "Finalized consumed reach can be reused.",
  dependency_invalidation_disabled: "Failed/stale dependencies are treated as valid.",
  exact_binding_weakened: "Release can execute a mutated proposal.",
  single_use_disabled: "Release consumption is disabled.",
  exposure_conservation_broken: "Exposure capacity can be overdrawn or manufactured."
};

export function stableStringify(value) {
  if (Array.isArray(value)) return `[${value.map(stableStringify).join(",")}]`;
  if (value && typeof value === "object") {
    return `{${Object.keys(value).sort().map((k) => `${JSON.stringify(k)}:${stableStringify(value[k])}`).join(",")}}`;
  }
  return JSON.stringify(value);
}

export function digest(value) {
  return `sha256:${crypto.createHash("sha256").update(stableStringify(value)).digest("hex")}`;
}

export function clone(value) {
  return JSON.parse(JSON.stringify(value));
}

export function initialState(overrides = {}) {
  return {
    tick: 0,
    epoch: 1,
    principals: {
      enterprise_alpha: { exposure_limit: 100, exposure_used: 0, reserved: 0 }
    },
    agents: {
      agent_a: { principal: "enterprise_alpha", authority: ["purchase"], local_limit: 100, revoked: false },
      agent_b: { principal: "enterprise_alpha", authority: ["purchase"], local_limit: 100, revoked: false }
    },
    dependencies: {
      vendor_ok: { status: "valid", epoch: 1 }
    },
    releases: {},
    effects: {},
    finalized: {},
    history: [],
    ...overrides
  };
}

function fail(result, reason) {
  return result === "hold" ? { result, reason } : { result: "refuse", reason };
}

export function settle(inputState, proposal, options = {}) {
  const mutation = options.mutation ?? null;
  const state = clone(inputState);
  state.tick = (state.tick ?? 0) + 1;

  const agent = state.agents?.[proposal.agent_id];
  const principalId = proposal.principal_id ?? agent?.principal;
  const principal = state.principals?.[principalId];
  const dependency = state.dependencies?.[proposal.dependency_id];
  const releaseId = proposal.release_id ?? proposal.proposal_id;
  const priorRelease = state.releases?.[releaseId];
  const amount = proposal.amount ?? 0;
  const receipt = { proposal_digest: digest(proposal), pre_state_digest: digest(inputState), reference_version: REFERENCE_VERSION, mutation };

  const authorityValid = mutation === "authority_provenance_dropped" ? true : Boolean(agent && !agent.revoked && agent.authority?.includes(proposal.operation));
  if (!authorityValid) return refusal(state, receipt, "authority_invalid_or_missing");

  const dependencyValid = mutation === "dependency_invalidation_disabled" ? true : (!proposal.dependency_id || (dependency?.status === "valid" && dependency.epoch === state.epoch));
  if (!dependencyValid) return refusal(state, receipt, "dependency_invalid_or_stale");

  const exactBindingValid = mutation === "exact_binding_weakened" ? true : (!proposal.bound_digest || proposal.bound_digest === digest({ ...proposal, bound_digest: undefined }));
  if (!exactBindingValid) return refusal(state, receipt, "exact_binding_mismatch");

  if (priorRelease?.consumed && mutation !== "replay_permitted" && mutation !== "single_use_disabled") {
    return refusal(state, receipt, "release_already_consumed");
  }

  if (state.finalized?.[proposal.finality_key] && mutation !== "finality_ignored") {
    return refusal(state, receipt, "finality_precludes_future_release");
  }

  if (proposal.prior_effect === "UNKNOWN" && mutation !== "unknown_restores_capacity") {
    return hold(state, receipt, "prior_unknown_effect_risk_bearing");
  }

  if (proposal.restart && mutation === "restart_clears_history") {
    if (state.principals?.[principalId]) state.principals[principalId].reserved = 0;
    state.history = [];
    state.effects = {};
  } else if (proposal.restart && Object.values(state.effects ?? {}).some((e) => e === "UNKNOWN")) {
    return hold(state, receipt, "restart_does_not_clear_unknown_effect");
  }

  const aggregateUsed = mutation === "principal_aggregation_removed" ? 0 : ((principal?.exposure_used ?? 0) + (principal?.reserved ?? 0));
  const available = mutation === "exposure_conservation_broken" ? Number.POSITIVE_INFINITY : ((principal?.exposure_limit ?? 0) - aggregateUsed);
  const localAvailable = agent?.local_limit ?? 0;
  const effectiveAvailable = Math.min(available, mutation === "principal_aggregation_removed" ? localAvailable : available);
  if (amount > effectiveAvailable) return refusal(state, receipt, "insufficient_exposure");

  const nextState = clone(state);
  nextState.releases[releaseId] = { proposal_digest: receipt.proposal_digest, amount, principal_id: principalId, consumed: false, single_use: true };
  nextState.principals[principalId].reserved += amount;
  nextState.history.push({ type: "release", release_id: releaseId, proposal_digest: receipt.proposal_digest, amount, principal_id: principalId });
  receipt.settlement_result = "release";
  receipt.reason = "within_declared_reach";
  receipt.release_id = releaseId;
  receipt.post_state_digest = digest(nextState);
  return { settlement_result: "release", reason: receipt.reason, state: nextState, receipt };
}

export function execute(inputState, execution, options = {}) {
  const mutation = options.mutation ?? null;
  const state = clone(inputState);
  const release = state.releases?.[execution.release_id];
  const receipt = { execution_digest: digest(execution), pre_state_digest: digest(inputState), mutation };
  if (!release) return refusal(state, receipt, "release_missing");
  if (release.consumed && mutation !== "replay_permitted" && mutation !== "single_use_disabled") return refusal(state, receipt, "release_already_consumed");
  const expected = release.proposal_digest;
  if (mutation !== "exact_binding_weakened" && execution.proposal_digest && execution.proposal_digest !== expected) return refusal(state, receipt, "execution_binding_mismatch");
  if (mutation !== "single_use_disabled" && mutation !== "replay_permitted") release.consumed = true;
  const effect = execution.effect ?? "CONFIRMED";
  state.effects[execution.release_id] = effect;
  if (effect === "CONFIRMED") {
    const p = state.principals[release.principal_id];
    p.reserved = Math.max(0, p.reserved - release.amount);
    p.exposure_used += release.amount;
  }
  if (effect === "UNKNOWN" && mutation === "unknown_restores_capacity") {
    const p = state.principals[release.principal_id];
    p.reserved = Math.max(0, p.reserved - release.amount);
  }
  if (execution.finality_key) state.finalized[execution.finality_key] = effect;
  state.history.push({ type: "execution", release_id: execution.release_id, effect });
  receipt.execution_result = "executed";
  receipt.effect = effect;
  receipt.post_state_digest = digest(state);
  return { execution_result: "executed", state, receipt };
}

function refusal(state, receipt, reason) {
  receipt.settlement_result ??= "refuse";
  receipt.reason = reason;
  receipt.post_state_digest = digest(state);
  return { settlement_result: "refuse", reason, state, receipt };
}

function hold(state, receipt, reason) {
  receipt.settlement_result = "hold";
  receipt.reason = reason;
  receipt.post_state_digest = digest(state);
  return { settlement_result: "hold", reason, state, receipt };
}

export function reachedForbidden(state, forbidden) {
  if (!forbidden) return false;
  if (forbidden.kind === "exposure_used_gt") return (state.principals?.[forbidden.principal_id]?.exposure_used ?? 0) > forbidden.amount;
  if (forbidden.kind === "release_exists") return Boolean(state.releases?.[forbidden.release_id]);
  if (forbidden.kind === "effect_count_gt") return Object.values(state.effects ?? {}).length > forbidden.count;
  if (forbidden.kind === "reserved_plus_used_gt") {
    const p = state.principals?.[forbidden.principal_id];
    return ((p?.reserved ?? 0) + (p?.exposure_used ?? 0)) > forbidden.amount;
  }
  return false;
}

