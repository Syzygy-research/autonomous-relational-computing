import {
  approveExactAction,
  bindProposal,
  createEvaluationState,
  executeReleasedAction,
  makeDownloadableReceipt,
  makeProposal,
  revokeRelease,
  runChallengeSuite,
} from "./evaluator-model.mjs";

const state = createEvaluationState();
let lastResult = null;

const form = document.querySelector("#proposal-form");
const output = document.querySelector("#output");
const digestEl = document.querySelector("#digest");
const releaseEl = document.querySelector("#release");
const eventsEl = document.querySelector("#events");
const challengesEl = document.querySelector("#challenges");

form.addEventListener("submit", async (event) => {
  event.preventDefault();
  const proposal = readProposal();
  lastResult = await bindProposal(state, proposal);
  render();
});

document.querySelector("#approve").addEventListener("click", () => {
  lastResult = approveExactAction(state, { approver: "human_participant" });
  render();
});

document.querySelector("#execute").addEventListener("click", async () => {
  lastResult = await executeReleasedAction(state, readProposal());
  render();
});

document.querySelector("#revoke").addEventListener("click", () => {
  lastResult = revokeRelease(state);
  render();
});

document.querySelector("#run-challenges").addEventListener("click", async () => {
  const results = await runChallengeSuite();
  challengesEl.innerHTML = results.map((item) => `
    <li class="${item.passed ? "pass" : "fail"}">
      <strong>${item.name}</strong>: ${item.passed ? "refused as expected" : "unexpected result"}
      <code>${item.result?.code || "no_code"}</code>
    </li>
  `).join("");
});

document.querySelector("#download").addEventListener("click", () => {
  const receipt = makeDownloadableReceipt(state, lastResult);
  const blob = new Blob([JSON.stringify(receipt, null, 2)], { type: "application/json" });
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = url;
  link.download = "valis-browser-local-evaluator-receipt.json";
  link.click();
  URL.revokeObjectURL(url);
});

document.querySelector("#reset").addEventListener("click", () => {
  Object.assign(state, createEvaluationState());
  lastResult = null;
  challengesEl.innerHTML = "";
  render();
});

for (const element of form.elements) {
  element.addEventListener("input", () => {
    if (state.proposalDigest) {
      output.textContent = "Proposal changed. Bind the updated exact proposal before approval or execution.";
    }
  });
}

function readProposal() {
  const data = new FormData(form);
  return makeProposal({
    operation: data.get("operation"),
    actor: data.get("actor"),
    target: data.get("target"),
    payload: data.get("payload"),
    scope: data.get("scope"),
  });
}

function render() {
  digestEl.textContent = state.proposalDigest || "No proposal bound yet.";
  releaseEl.textContent = state.release ? JSON.stringify(state.release, null, 2) : "No release issued.";
  output.textContent = lastResult ? JSON.stringify(lastResult, null, 2) : "No result yet.";
  eventsEl.textContent = JSON.stringify(state.events, null, 2);
}

render();
