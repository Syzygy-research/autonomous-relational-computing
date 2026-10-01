#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import { createEnvironment, MUTATIONS } from "../environment/cr-eval-environment.mjs";
import { createScriptedAgent } from "../agents/scripted-agent.mjs";

const root = path.resolve(new URL("..", import.meta.url).pathname.replace(/^\/(.:\/)/, "$1"));
const scenariosPath = path.join(root, "scenarios", "frontier-scenarios.json");
const exportsDir = path.join(root, "exports");

function readJson(p) { return JSON.parse(fs.readFileSync(p, "utf8")); }
function writeJson(p, v) { fs.mkdirSync(path.dirname(p), { recursive: true }); fs.writeFileSync(p, JSON.stringify(v, null, 2) + "\n"); }
function scenarios() { return readJson(scenariosPath).scenarios; }
function arg(name, fallback = null) { const i = process.argv.indexOf(name); return i >= 0 ? process.argv[i + 1] : fallback; }
function has(flag) { return process.argv.includes(flag); }

async function run() {
  const cmd = process.argv[2] ?? "help";
  if (cmd === "help") {
    console.log(`cr-eval commands:\n  scenarios\n  mutants\n  run <scenario-id> [--mutant id] [--export]\n  reproduce <export-dir>`);
    return;
  }
  if (cmd === "scenarios") {
    for (const s of scenarios()) console.log(`${s.id}\t${s.attack_class}\t${s.title}`);
    return;
  }
  if (cmd === "mutants") {
    for (const [id, desc] of Object.entries(MUTATIONS)) console.log(`${id}\t${desc}`);
    return;
  }
  if (cmd === "run") {
    const id = process.argv[3];
    const scenario = scenarios().find((s) => s.id === id);
    if (!scenario) throw new Error(`Unknown scenario: ${id}`);
    const mutation = arg("--mutant", null);
    if (mutation && !MUTATIONS[mutation]) throw new Error(`Unknown mutant: ${mutation}`);
    const env = createEnvironment({ scenario, mutation, maxSteps: Number(arg("--max-steps", 50)) });
    const agent = createScriptedAgent({ scenario });
    const history = [];
    while (!env.status().terminal) {
      const action = await agent.decide({ objective: scenario.objective, observation: env.observe(), available_actions: env.available_actions(), history });
      const result = env.act(action);
      history.push({ action, result: result.result, reason: result.reason });
      if (action.type === "stop") break;
    }
    const exported = env.export_run({ agent: agent.declaration });
    console.log(JSON.stringify({ scenario_id: id, mutation, status: exported.result, trace_steps: exported.trace.length }, null, 2));
    if (has("--export")) {
      const out = path.join(exportsDir, `${id}${mutation ? `-${mutation}` : ""}-${Date.now()}`);
      writeJson(path.join(out, "manifest.json"), exported.manifest);
      writeJson(path.join(out, "scenario.json"), exported.scenario);
      writeJson(path.join(out, "trace.json"), exported.trace);
      writeJson(path.join(out, "result.json"), exported.result);
      console.log(`exported=${out}`);
    }
    return;
  }
  if (cmd === "reproduce") {
    const dir = process.argv[3];
    if (!dir) throw new Error("reproduce requires an export directory");
    const scenario = readJson(path.join(dir, "scenario.json"));
    const manifest = readJson(path.join(dir, "manifest.json"));
    const env = createEnvironment({ scenario, mutation: manifest.mutation ?? null, maxSteps: manifest.budget?.max_steps ?? 50 });
    const agent = createScriptedAgent({ scenario });
    while (!env.status().terminal) {
      const action = await agent.decide({ objective: scenario.objective, observation: env.observe(), available_actions: env.available_actions(), history: [] });
      env.act(action);
      if (action.type === "stop") break;
    }
    const rerun = env.export_run({ agent: agent.declaration, parent_experiment: manifest.experiment_id });
    console.log(JSON.stringify({ reproduced: rerun.manifest.terminal_state_digest === manifest.terminal_state_digest, expected_terminal_state_digest: manifest.terminal_state_digest, actual_terminal_state_digest: rerun.manifest.terminal_state_digest }, null, 2));
    return;
  }
  throw new Error(`Unknown command: ${cmd}`);
}

run().catch((err) => { console.error(err.stack || err.message); process.exit(1); });
