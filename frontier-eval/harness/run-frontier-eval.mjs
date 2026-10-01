import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";
import { initialState, settle, execute, reachedForbidden, MUTATIONS, digest } from "../reference/cr-core-synthetic.mjs";

const root = path.resolve(new URL("..", import.meta.url).pathname.replace(/^\/(.:\/)/, "$1"));
const repo = path.resolve(root, "..");
const scenariosPath = path.join(root, "scenarios", "frontier-scenarios.json");
const reportsDir = path.join(root, "reports");
fs.mkdirSync(reportsDir, { recursive: true });

function readJson(p){ return JSON.parse(fs.readFileSync(p,"utf8")); }
function writeJson(p,v){ fs.writeFileSync(p, JSON.stringify(v,null,2)+"\n"); }
function shaFile(p){ return `sha256:${crypto.createHash("sha256").update(fs.readFileSync(p)).digest("hex")}`; }
function deepMerge(a,b){
  if(!b || typeof b!=="object" || Array.isArray(b)) return b===undefined?a:b;
  const out={...(a||{})};
  for(const [k,v] of Object.entries(b)) out[k]=deepMerge(out[k],v);
  return out;
}
function ensureDir(p){ fs.mkdirSync(p,{recursive:true}); }
function copyDir(src,dst){ ensureDir(dst); for(const ent of fs.readdirSync(src,{withFileTypes:true})){ const s=path.join(src,ent.name), d=path.join(dst,ent.name); if(ent.isDirectory()) copyDir(s,d); else fs.copyFileSync(s,d); } }

function runScenario(scenario, mutation=null){
  let state = initialState(deepMerge({}, scenario.initial ?? {}));
  const trace=[];
  for(const [index,step] of scenario.steps.entries()){
    let result;
    if(step.type === "settle") result = settle(state, step.proposal, { mutation });
    else if(step.type === "execute") result = execute(state, step.execution, { mutation });
    else throw new Error(`Unknown step type ${step.type}`);
    state = result.state;
    const actual = result.settlement_result ?? result.execution_result;
    trace.push({ index, type: step.type, expected_reference: step.expect_reference, actual, reason: result.reason ?? result.receipt?.reason, receipt: result.receipt });
  }
  const escaped = reachedForbidden(state, scenario.forbidden);
  return { scenario_id: scenario.id, mutation, escaped_forbidden_state: escaped, final_state_digest: digest(state), trace };
}

function expectedDetected(scenario, mutation, run){
  if(!(scenario.expected_mutants ?? []).includes(mutation)) return null;
  return run.escaped_forbidden_state || run.trace.some((t) => t.expected_reference && t.actual !== t.expected_reference);
}

const scenarioDoc = readJson(scenariosPath);
const scenarios = scenarioDoc.scenarios;
const referenceResults=[];
const mutantResults=[];
for(const s of scenarios){
  const r=runScenario(s,null);
  const expectedOk = r.trace.every((t)=>!t.expected_reference || t.actual===t.expected_reference) && !r.escaped_forbidden_state;
  referenceResults.push({ ...r, pass: expectedOk });
  for(const m of Object.keys(MUTATIONS)){
    if(!(s.expected_mutants ?? []).includes(m)) continue;
    const mr=runScenario(s,m);
    const detected=Boolean(expectedDetected(s,m,mr));
    mutantResults.push({ ...mr, detected, expected_detection: true, invariant_violation: MUTATIONS[m] });
  }
}

const corpusSrc=path.join(repo,"conformance","corpus");
const comparatorSrc=path.join(repo,"conformance","comparator","phase-v");
copyDir(corpusSrc,path.join(root,"corpus"));
copyDir(comparatorSrc,path.join(root,"comparator","phase-v"));

const sourceFiles=[
 "conformance/corpus/MANIFEST.json",
 "conformance/comparator/phase-v/MANIFEST.json",
 "conformance/reports/phase-v-comparator-experiment.json",
 "conformance/reports/phase-v-adversarial-sweep.json",
 "conformance/reports/phase-v-adversarial-execution.json",
 "conformance/reports/phase-v-closure-execution.json",
 "conformance/reports/phase-v-freeze-readiness.json",
 "frontier-eval/scenarios/frontier-scenarios.json",
 "frontier-eval/reference/cr-core-synthetic.mjs"
].map((rel)=>({ path: rel, sha256: shaFile(path.join(repo,rel)), bytes: fs.statSync(path.join(repo,rel)).size }));

const report={
  report_version:"cr-frontier-eval-v0.1-local",
  created_at:new Date().toISOString(),
  verdict: referenceResults.every(r=>r.pass) && mutantResults.every(r=>r.detected) ? "FRONTIER_EVAL_REFERENCE_PASS_MUTANTS_DETECTED" : "FRONTIER_EVAL_FAILURE",
  safety_boundary:"Synthetic offline state machine only; no network, credentials, money, cloud, hardware, shell, external API, or real-world authority is used by this harness.",
  corpus_boundary:"Uses current reconstructed candidate corpus and derived comparator fixtures; not recovered historical canonical fixture bytes.",
  production_boundary:"Not production KORE, not GMAP deployment, not production conformance, not external validation.",
  scenario_count: scenarios.length,
  reference_pass_count: referenceResults.filter(r=>r.pass).length,
  reference_fail_count: referenceResults.filter(r=>!r.pass).length,
  mutant_expected_detection_count: mutantResults.length,
  mutant_detected_count: mutantResults.filter(r=>r.detected).length,
  mutant_survivor_count: mutantResults.filter(r=>!r.detected).length,
  source_files: sourceFiles,
  reference_results: referenceResults,
  mutant_results: mutantResults
};
writeJson(path.join(reportsDir,"frontier-eval-report.json"),report);
fs.writeFileSync(path.join(reportsDir,"frontier-eval-results.jsonl"), [
  ...referenceResults.map(r=>({ kind:"reference", ...r })),
  ...mutantResults.map(r=>({ kind:"mutant", ...r }))
].map(x=>JSON.stringify(x)).join("\n")+"\n");

const manifestPath=path.join(root,"manifest.json");
const manifest=readJson(manifestPath);
manifest.status=report.verdict;
manifest.frontier_eval_report={ path:"frontier-eval/reports/frontier-eval-report.json", sha256:shaFile(path.join(reportsDir,"frontier-eval-report.json")) };
manifest.frontier_eval_results={ path:"frontier-eval/reports/frontier-eval-results.jsonl", sha256:shaFile(path.join(reportsDir,"frontier-eval-results.jsonl")) };
manifest.source_files=sourceFiles;
writeJson(manifestPath,manifest);
console.log(`${report.verdict}: scenarios=${report.scenario_count} reference_pass=${report.reference_pass_count}/${report.scenario_count} mutants_detected=${report.mutant_detected_count}/${report.mutant_expected_detection_count}`);
