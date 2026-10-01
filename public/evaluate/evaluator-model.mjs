const DEFAULT_TTL_MS = 60_000;

export function createEvaluationState(now = Date.now()) {
  return {
    version: 1,
    now,
    bindingCounter: 0,
    proposal: null,
    proposalDigest: null,
    boundVersion: 0,
    release: null,
    events: [],
  };
}

export function makeProposal({
  operation = "send_message",
  actor = "participant",
  target = "example.workspace",
  payload = "Send the approved update to the selected workspace.",
  scope = "browser-local evaluator simulation",
} = {}) {
  return { operation, actor, target, payload, scope };
}

export function canonicalize(value) {
  if (Array.isArray(value)) {
    return `[${value.map(canonicalize).join(",")}]`;
  }
  if (value && typeof value === "object") {
    return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${canonicalize(value[key])}`).join(",")}}`;
  }
  return JSON.stringify(value);
}

export async function sha256Hex(input) {
  const bytes = new TextEncoder().encode(input);
  if (globalThis.crypto?.subtle) {
    const buffer = await globalThis.crypto.subtle.digest("SHA-256", bytes);
    return [...new Uint8Array(buffer)].map((byte) => byte.toString(16).padStart(2, "0")).join("");
  }
  const { createHash } = await import("node:crypto");
  return createHash("sha256").update(input).digest("hex");
}

export async function digestProposal(proposal) {
  return sha256Hex(canonicalize({ kind: "valis_evaluator_proposal", proposal }));
}

export async function bindProposal(state, proposal, now = Date.now()) {
  const digest = await digestProposal(proposal);
  state.bindingCounter += 1;
  state.now = now;
  state.proposal = structuredCloneSafe(proposal);
  state.proposalDigest = digest;
  state.boundVersion = state.bindingCounter;
  state.release = null;
  state.events.push({
    type: "proposal_bound",
    digest,
    boundVersion: state.boundVersion,
    at: now,
  });
  return {
    ok: true,
    digest,
    boundVersion: state.boundVersion,
  };
}

export function approveExactAction(state, { approver = "human_participant", now = Date.now(), ttlMs = DEFAULT_TTL_MS } = {}) {
  if (!state.proposalDigest) {
    return refusal(state, "no_bound_proposal", "No proposal is bound.", now);
  }
  if (approver !== "human_participant") {
    return refusal(state, "self_authorization_refused", "Only the authorized human participant can release the exact proposal.", now);
  }
  state.now = now;
  state.release = {
    releaseId: `release-${state.boundVersion}-${now}`,
    digest: state.proposalDigest,
    boundVersion: state.boundVersion,
    issuedAt: now,
    expiresAt: now + ttlMs,
    revokedAt: null,
    usedAt: null,
    approver,
  };
  state.events.push({
    type: "release_issued",
    releaseId: state.release.releaseId,
    digest: state.release.digest,
    boundVersion: state.release.boundVersion,
    expiresAt: state.release.expiresAt,
    at: now,
  });
  return {
    ok: true,
    release: structuredCloneSafe(state.release),
  };
}

export function revokeRelease(state, now = Date.now()) {
  if (!state.release) {
    return refusal(state, "no_release_to_revoke", "No release exists to revoke.", now);
  }
  state.release.revokedAt = now;
  state.events.push({
    type: "release_revoked",
    releaseId: state.release.releaseId,
    at: now,
  });
  return {
    ok: true,
    release: structuredCloneSafe(state.release),
  };
}

export async function executeReleasedAction(state, proposal, { now = Date.now(), boundVersion = state.boundVersion } = {}) {
  if (!state.release) {
    return refusal(state, "missing_release", "No release exists for this action.", now);
  }
  if (boundVersion !== state.release.boundVersion) {
    return refusal(state, "stale_binding_refused", "The request references an old binding version.", now);
  }
  if (state.release.revokedAt) {
    return refusal(state, "revoked_release_refused", "The release has been revoked.", now);
  }
  if (now > state.release.expiresAt) {
    return refusal(state, "expired_release_refused", "The release has expired.", now);
  }
  if (state.release.usedAt) {
    return refusal(state, "replay_refused", "The release has already been used.", now);
  }
  const requestDigest = await digestProposal(proposal);
  if (requestDigest !== state.release.digest) {
    return refusal(state, "payload_mismatch_refused", "The requested action no longer matches the released proposal.", now, {
      expectedDigest: state.release.digest,
      requestDigest,
    });
  }
  state.release.usedAt = now;
  const receipt = {
    kind: "browser_local_evaluator_receipt",
    simulation: true,
    trustedRuntimeAttestation: false,
    productionAuthority: false,
    releaseId: state.release.releaseId,
    digest: state.release.digest,
    executedAt: now,
    proposal: structuredCloneSafe(proposal),
  };
  state.events.push({
    type: "executed",
    releaseId: state.release.releaseId,
    digest: state.release.digest,
    at: now,
  });
  return {
    ok: true,
    receipt,
  };
}

export async function runChallengeSuite() {
  const baseNow = 1_700_000_000_000;
  const proposal = makeProposal();
  const results = [];

  {
    const state = createEvaluationState(baseNow);
    await bindProposal(state, proposal, baseNow);
    results.push({
      name: "self_authorization",
      result: approveExactAction(state, { approver: "agent", now: baseNow + 1 }),
      expectedCode: "self_authorization_refused",
    });
  }

  {
    const state = createEvaluationState(baseNow);
    await bindProposal(state, proposal, baseNow);
    approveExactAction(state, { now: baseNow + 1 });
    const mutated = { ...proposal, payload: `${proposal.payload} MUTATED` };
    results.push({
      name: "payload_mismatch",
      result: await executeReleasedAction(state, mutated, { now: baseNow + 2 }),
      expectedCode: "payload_mismatch_refused",
    });
  }

  {
    const state = createEvaluationState(baseNow);
    await bindProposal(state, proposal, baseNow);
    approveExactAction(state, { now: baseNow + 1, ttlMs: 5 });
    results.push({
      name: "expired_release",
      result: await executeReleasedAction(state, proposal, { now: baseNow + 100 }),
      expectedCode: "expired_release_refused",
    });
  }

  {
    const state = createEvaluationState(baseNow);
    await bindProposal(state, proposal, baseNow);
    approveExactAction(state, { now: baseNow + 1 });
    revokeRelease(state, baseNow + 2);
    results.push({
      name: "revoked_release",
      result: await executeReleasedAction(state, proposal, { now: baseNow + 3 }),
      expectedCode: "revoked_release_refused",
    });
  }

  {
    const state = createEvaluationState(baseNow);
    await bindProposal(state, proposal, baseNow);
    approveExactAction(state, { now: baseNow + 1 });
    const first = await executeReleasedAction(state, proposal, { now: baseNow + 2 });
    const second = await executeReleasedAction(state, proposal, { now: baseNow + 3 });
    results.push({
      name: "single_use_replay",
      first,
      result: second,
      expectedCode: "replay_refused",
    });
  }

  {
    const state = createEvaluationState(baseNow);
    const oldBind = await bindProposal(state, proposal, baseNow);
    const newProposal = { ...proposal, target: "different.workspace" };
    await bindProposal(state, newProposal, baseNow + 1);
    approveExactAction(state, { now: baseNow + 2 });
    results.push({
      name: "stale_digest_rebinding",
      result: await executeReleasedAction(state, newProposal, { now: baseNow + 3, boundVersion: oldBind.boundVersion }),
      expectedCode: "stale_binding_refused",
    });
  }

  return results.map((item) => ({
    ...item,
    passed: item.result?.ok === false && item.result?.code === item.expectedCode,
  }));
}

export function makeDownloadableReceipt(state, lastResult = null) {
  return {
    kind: "valis_public_evaluator_browser_local_receipt",
    simulation: true,
    trustedRuntimeAttestation: false,
    productionAuthority: false,
    createdAt: new Date().toISOString(),
    proposal: state.proposal,
    proposalDigest: state.proposalDigest,
    release: state.release,
    lastResult,
    events: state.events,
    boundary: "Browser-local evaluator receipt. This is not a trusted runtime attestation or production enforcement proof.",
  };
}

function refusal(state, code, message, now, extra = {}) {
  const event = {
    type: "refusal",
    code,
    message,
    at: now,
    ...extra,
  };
  state.events.push(event);
  return {
    ok: false,
    code,
    message,
    ...extra,
  };
}

function structuredCloneSafe(value) {
  return JSON.parse(JSON.stringify(value));
}
