import assert from "node:assert/strict";
import {
  approveExactAction,
  bindProposal,
  createEvaluationState,
  executeReleasedAction,
  makeProposal,
  revokeRelease,
  runChallengeSuite,
} from "../public/evaluate/evaluator-model.mjs";

const now = 1_700_000_000_000;
const proposal = makeProposal();

{
  const state = createEvaluationState(now);
  await bindProposal(state, proposal, now);
  const release = approveExactAction(state, { now: now + 1 });
  assert.equal(release.ok, true);
  const result = await executeReleasedAction(state, proposal, { now: now + 2 });
  assert.equal(result.ok, true);
  assert.equal(result.receipt.trustedRuntimeAttestation, false);
  assert.equal(result.receipt.productionAuthority, false);
}

{
  const state = createEvaluationState(now);
  await bindProposal(state, proposal, now);
  const result = approveExactAction(state, { approver: "agent", now: now + 1 });
  assert.equal(result.ok, false);
  assert.equal(result.code, "self_authorization_refused");
}

{
  const state = createEvaluationState(now);
  await bindProposal(state, proposal, now);
  approveExactAction(state, { now: now + 1 });
  const result = await executeReleasedAction(state, { ...proposal, payload: "changed" }, { now: now + 2 });
  assert.equal(result.ok, false);
  assert.equal(result.code, "payload_mismatch_refused");
}

{
  const state = createEvaluationState(now);
  await bindProposal(state, proposal, now);
  approveExactAction(state, { now: now + 1, ttlMs: 1 });
  const result = await executeReleasedAction(state, proposal, { now: now + 3 });
  assert.equal(result.ok, false);
  assert.equal(result.code, "expired_release_refused");
}

{
  const state = createEvaluationState(now);
  await bindProposal(state, proposal, now);
  approveExactAction(state, { now: now + 1 });
  revokeRelease(state, now + 2);
  const result = await executeReleasedAction(state, proposal, { now: now + 3 });
  assert.equal(result.ok, false);
  assert.equal(result.code, "revoked_release_refused");
}

{
  const state = createEvaluationState(now);
  await bindProposal(state, proposal, now);
  approveExactAction(state, { now: now + 1 });
  const first = await executeReleasedAction(state, proposal, { now: now + 2 });
  const second = await executeReleasedAction(state, proposal, { now: now + 3 });
  assert.equal(first.ok, true);
  assert.equal(second.ok, false);
  assert.equal(second.code, "replay_refused");
}

{
  const state = createEvaluationState(now);
  const oldBind = await bindProposal(state, proposal, now);
  const next = { ...proposal, target: "new.target" };
  await bindProposal(state, next, now + 1);
  approveExactAction(state, { now: now + 2 });
  const result = await executeReleasedAction(state, next, { now: now + 3, boundVersion: oldBind.boundVersion });
  assert.equal(result.ok, false);
  assert.equal(result.code, "stale_binding_refused");
}

const challengeResults = await runChallengeSuite();
assert.equal(challengeResults.every((result) => result.passed), true);

console.log("evaluator model tests passed");
