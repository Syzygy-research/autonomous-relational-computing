// Refusal tests for the CR frontier reference + environment.
//
// Each block pins one behavior the reference's own SPEC / THREAT_MODEL
// requires but the 2026-09-28 release (6dce80b) did not enforce. Every
// block fails against that release and passes once the corresponding
// boundary check exists. Style follows tools/test-evaluator-model.mjs:
// plain node:assert blocks, no framework.
import assert from "node:assert/strict";
import { initialState, settle, execute } from "../reference/cr-core-synthetic.mjs";
import { createEnvironment } from "../environment/cr-eval-environment.mjs";

const clone = (v) => JSON.parse(JSON.stringify(v));

// ---------- Item 1: caller identity is bound by the environment ----------
{
  const scenario = {
    id: "FIX-1",
    initial: {
      agents: {
        agent_a: { principal: "enterprise_alpha", authority: ["purchase"], local_limit: 100, revoked: false },
        impostor: { principal: "enterprise_alpha", authority: [], local_limit: 100, revoked: false }
      }
    }
  };
  const bound = createEnvironment({ scenario, callerAgentId: "impostor" });
  const asOther = bound.act({ type: "settle", proposal: { proposal_id: "f1-a", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" } });
  assert.equal(asOther.result, "refuse");
  assert.equal(asOther.reason, "caller_identity_mismatch");
  // The bound caller acting as itself is still judged on its own authority.
  const asSelf = bound.act({ type: "settle", proposal: { proposal_id: "f1-b", agent_id: "impostor", operation: "purchase", amount: 10, dependency_id: "vendor_ok" } });
  assert.equal(asSelf.result, "refuse");
  assert.equal(asSelf.reason, "authority_invalid_or_missing");
  // A caller bound to agent_a settles as agent_a.
  const legit = createEnvironment({ scenario, callerAgentId: "agent_a" });
  const ok = legit.act({ type: "settle", proposal: { proposal_id: "f1-c", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" } });
  assert.equal(ok.result, "release");
  // Unbound operation (scripted playback, the operator plays every role) is unchanged.
  const unbound = createEnvironment({ scenario });
  const free = unbound.act({ type: "settle", proposal: { proposal_id: "f1-d", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" } });
  assert.equal(free.result, "release");
}

// ---------- Item 2: negative amount is refused, manufactures nothing ----------
{
  const s = initialState();
  const r = settle(s, { proposal_id: "f2-a", agent_id: "agent_a", operation: "purchase", amount: -100, dependency_id: "vendor_ok" });
  assert.equal(r.settlement_result, "refuse");
  assert.equal(r.reason, "invalid_amount");
  assert.equal(r.state.principals.enterprise_alpha.reserved, 0);
  // An honest over-limit amount is still refused by exposure, not validation.
  const over = settle(s, { proposal_id: "f2-b", agent_id: "agent_b", operation: "purchase", amount: 200, dependency_id: "vendor_ok" });
  assert.equal(over.settlement_result, "refuse");
  assert.equal(over.reason, "insufficient_exposure");
}

// ---------- Item 3: non-numeric amount is refused, books stay numeric ----------
{
  const s = initialState();
  for (const bad of ["abc", "10", Number.NaN, Number.POSITIVE_INFINITY]) {
    const r = settle(s, { proposal_id: "f3-a", agent_id: "agent_a", operation: "purchase", amount: bad, dependency_id: "vendor_ok" });
    assert.equal(r.settlement_result, "refuse");
    assert.equal(r.reason, "invalid_amount");
    assert.equal(r.state.principals.enterprise_alpha.reserved, 0);
  }
  // After the refused attempts the books are uncorrupted: a normal settle releases.
  const ok = settle(s, { proposal_id: "f3-b", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(ok.settlement_result, "release");
  assert.equal(ok.state.principals.enterprise_alpha.reserved, 10);
}

// ---------- Item 4: a proposal cannot name another principal ----------
{
  const s = initialState({
    principals: {
      enterprise_alpha: { exposure_limit: 100, exposure_used: 0, reserved: 0 },
      enterprise_beta: { exposure_limit: 1000, exposure_used: 0, reserved: 0 }
    }
  });
  const r = settle(s, { proposal_id: "f4-a", agent_id: "agent_a", operation: "purchase", amount: 500, principal_id: "enterprise_beta", dependency_id: "vendor_ok" });
  assert.equal(r.settlement_result, "refuse");
  assert.equal(r.reason, "principal_mismatch");
  assert.equal(r.state.principals.enterprise_beta.reserved, 0);
  assert.equal(r.state.principals.enterprise_alpha.reserved, 0);
  // Naming its own principal explicitly is fine.
  const ok = settle(s, { proposal_id: "f4-b", agent_id: "agent_a", operation: "purchase", amount: 50, principal_id: "enterprise_alpha", dependency_id: "vendor_ok" });
  assert.equal(ok.settlement_result, "release");
  assert.equal(ok.state.principals.enterprise_alpha.reserved, 50);
}

// ---------- Item 9: unknown principal refuses cleanly (no TypeError) ----------
{
  const s = initialState({
    principals: {
      enterprise_beta: { exposure_limit: 1000, exposure_used: 0, reserved: 0 }
    },
    agents: {
      agent_a: { principal: "enterprise_alpha", authority: ["purchase"], local_limit: 100, revoked: false }
    }
  });
  const r = settle(s, { proposal_id: "f9-a", agent_id: "agent_a", operation: "purchase", amount: 0, dependency_id: "vendor_ok" });
  assert.equal(r.settlement_result, "refuse");
  assert.equal(r.reason, "principal_not_found");
}

// ---------- Item 5: finality binds the settled reach, not only the named key ----------
{
  const s0 = initialState({
    agents: {
      agent_a: { principal: "enterprise_alpha", authority: ["purchase", "refund"], local_limit: 100, revoked: false },
      agent_b: { principal: "enterprise_alpha", authority: ["purchase"], local_limit: 100, revoked: false }
    }
  });
  let r = settle(s0, { proposal_id: "f5-a", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(r.settlement_result, "release");
  r = execute(r.state, { release_id: "f5-a", effect: "CONFIRMED", finality_key: "invoice-9" });
  assert.equal(r.execution_result, "executed");
  const s = r.state;
  // The published FE009 path: the same purchase naming the finalized key.
  const named = settle(s, { proposal_id: "f5-b", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok", finality_key: "invoice-9" });
  assert.equal(named.settlement_result, "refuse");
  assert.equal(named.reason, "finality_precludes_future_release");
  // The escape: the same purchase omitting the key entirely.
  const omitted = settle(s, { proposal_id: "f5-c", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(omitted.settlement_result, "refuse");
  assert.equal(omitted.reason, "finality_precludes_future_release");
  // A different operation is a different reach and is not finalized.
  const other = settle(s, { proposal_id: "f5-d", agent_id: "agent_a", operation: "refund", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(other.settlement_result, "release");
}

// ---------- Item 6: the UNKNOWN hold is read from state, not only declared ----------
{
  let r = settle(initialState(), { proposal_id: "f6-a", agent_id: "agent_a", operation: "purchase", amount: 80, dependency_id: "vendor_ok" });
  assert.equal(r.settlement_result, "release");
  r = execute(r.state, { release_id: "f6-a", effect: "UNKNOWN" });
  assert.equal(r.execution_result, "executed");
  const s = r.state;
  // The escape: a later settle by the same agent that does not declare prior_effect.
  const undeclared = settle(s, { proposal_id: "f6-b", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(undeclared.settlement_result, "hold");
  assert.equal(undeclared.reason, "prior_unknown_effect_risk_bearing");
  // An agent with no UNKNOWN of its own is not held (10 fits the 20 left unreserved).
  const otherAgent = settle(s, { proposal_id: "f6-c", agent_id: "agent_b", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(otherAgent.settlement_result, "release");
}

// ---------- Item 8: local_limit binds effective availability ----------
{
  const s = initialState({
    agents: {
      agent_a: { principal: "enterprise_alpha", authority: ["purchase"], local_limit: 10, revoked: false },
      agent_b: { principal: "enterprise_alpha", authority: ["purchase"], local_limit: 100, revoked: false }
    }
  });
  const r = settle(s, { proposal_id: "f8-a", agent_id: "agent_a", operation: "purchase", amount: 50, dependency_id: "vendor_ok" });
  assert.equal(r.settlement_result, "refuse");
  assert.equal(r.reason, "insufficient_exposure");
  const ok = settle(s, { proposal_id: "f8-b", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(ok.settlement_result, "release");
}

// ---------- Item 11: an unconsumed release id cannot be re-settled ----------
{
  let r = settle(initialState(), { proposal_id: "f11-a", agent_id: "agent_a", operation: "purchase", amount: 80, dependency_id: "vendor_ok" });
  assert.equal(r.settlement_result, "release");
  const again = settle(r.state, { proposal_id: "f11-a", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(again.settlement_result, "refuse");
  assert.equal(again.reason, "release_id_already_issued");
  assert.equal(again.state.principals.enterprise_alpha.reserved, 80);
  // The original release still executes for its full, original amount.
  const ex = execute(again.state, { release_id: "f11-a", effect: "CONFIRMED" });
  assert.equal(ex.execution_result, "executed");
  assert.equal(ex.state.principals.enterprise_alpha.exposure_used, 80);
  assert.equal(ex.state.principals.enterprise_alpha.reserved, 0);
}

// ---------- Item 12: execution rechecks authority and dependency ----------
{
  let r = settle(initialState(), { proposal_id: "f12-a", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(r.settlement_result, "release");
  const s = r.state;
  // The release record carries the binding the recheck consults.
  const rec = s.releases["f12-a"];
  assert.equal(rec.agent_id, "agent_a");
  assert.equal(rec.operation, "purchase");
  assert.equal(rec.dependency_id, "vendor_ok");
  // Revocation recorded after release blocks execution.
  const revoked = clone(s);
  revoked.agents.agent_a.revoked = true;
  const exRevoked = execute(revoked, { release_id: "f12-a", effect: "CONFIRMED" });
  assert.equal(exRevoked.settlement_result, "refuse");
  assert.equal(exRevoked.reason, "authority_invalid_or_missing");
  // A dependency that failed after release blocks execution.
  const depFailed = clone(s);
  depFailed.dependencies.vendor_ok.status = "failed";
  const exDep = execute(depFailed, { release_id: "f12-a", effect: "CONFIRMED" });
  assert.equal(exDep.settlement_result, "refuse");
  assert.equal(exDep.reason, "dependency_invalid_or_stale");
  // Untouched state still executes.
  const exOk = execute(s, { release_id: "f12-a", effect: "CONFIRMED" });
  assert.equal(exOk.execution_result, "executed");
}

// ---------- D1 edge: arbitrary effect strings are refused ----------
{
  const r = settle(initialState(), { proposal_id: "fd1-a", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  const bad = execute(r.state, { release_id: "fd1-a", effect: "UNVERIFIED_CLAIM" });
  assert.equal(bad.settlement_result, "refuse");
  assert.equal(bad.reason, "invalid_effect");
  assert.equal(bad.state.releases["fd1-a"].consumed, false);
  assert.equal(bad.state.effects["fd1-a"], undefined);
  // The two defined effects still execute.
  const good = execute(r.state, { release_id: "fd1-a", effect: "UNKNOWN" });
  assert.equal(good.execution_result, "executed");
}

// ---------- Item 10: prototype keys cannot forge or lose records ----------
{
  const s = initialState();
  for (const badId of ["__proto__", "constructor", "prototype"]) {
    const r = settle(s, { proposal_id: badId, agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
    assert.equal(r.settlement_result, "refuse");
    assert.equal(r.reason, "invalid_release_id");
  }
  // Executing a prototype key finds no release and pollutes nothing.
  const e = execute(s, { release_id: "__proto__", effect: "UNKNOWN" });
  assert.equal(e.settlement_result, "refuse");
  assert.equal(e.reason, "release_missing");
  assert.equal(Object.prototype.consumed, undefined);
  assert.equal({}.consumed, undefined);
  // A normal settle/execute round trip still works afterwards.
  const ok = settle(s, { proposal_id: "f10-a", agent_id: "agent_a", operation: "purchase", amount: 10, dependency_id: "vendor_ok" });
  assert.equal(ok.settlement_result, "release");
  const done = execute(ok.state, { release_id: "f10-a", effect: "CONFIRMED" });
  assert.equal(done.execution_result, "executed");
}

console.log("cr reference fix tests passed");
