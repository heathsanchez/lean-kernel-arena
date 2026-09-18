import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {spawnSync} from "node:child_process";
import {resolve,dirname} from "node:path";
import {fileURLToPath} from "node:url";

const TARGETS=Object.freeze([
  "init-prelude.ndjson",
  "perf/fueled-chain.ndjson",
  "perf/grind-ring-5.ndjson",
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
  "perf/magma-list-pair-n21.ndjson",
  "perf/magma-list-pair-n7.ndjson",
]);
const CONFIGS=Object.freeze([
  {id:"default-2m",budget:2_000_000,stack:null},
  {id:"stack32-2m",budget:2_000_000,stack:32768},
  {id:"stack32-4m",budget:4_000_000,stack:32768},
  {id:"stack32-8m",budget:8_000_000,stack:32768},
]);

const manifestPath=resolve(process.env.MANIFEST??"_build/tests/manifest.json");
const outPath=resolve(process.env.OUT??"genesis/evidence/seven-unknown-resource-sweep-v1.json");
const root=dirname(manifestPath);
const rows=JSON.parse(readFileSync(manifestPath,"utf8"));
const byName=new Map(rows.map(r=>[r.name,r]));
const worker=fileURLToPath(new URL("./qualify-worker.mjs",import.meta.url));

for(const name of TARGETS){
  if(!byName.has(name))throw new Error("missing target from current corpus: "+name);
  if(byName.get(name).expected!=="ACCEPT")throw new Error("target no longer expected ACCEPT: "+name);
}

function runOne(row,config){
  const args=[];
  if(config.stack!==null)args.push("--stack-size="+config.stack);
  args.push(worker,resolve(root,row.name),String(row.bytes),row.sha256);
  const env={
    ...process.env,
    MATHGRAPH_SEMANTIC_BUDGET:String(config.budget),
    MATHGRAPH_INPUT_BYTE_LIMIT:"20000000",
    MATHGRAPH_RECORD_LIMIT:"400000",
  };
  const t0=Date.now();
  const child=spawnSync(process.execPath,args,{
    encoding:"utf8",
    timeout:120_000,
    maxBuffer:2*1024*1024,
    env,
  });
  let parsed=null;
  const lines=(child.stdout??"").trim().split(/\r?\n/).filter(Boolean);
  if(lines.length===1){
    try{parsed=JSON.parse(lines[0]);}catch{}
  }
  return {
    config:config.id,
    budget:config.budget,
    stack_kb:config.stack,
    wall_ms:Date.now()-t0,
    process_status:child.status,
    signal:child.signal??null,
    process_error:child.error?.message??null,
    status:parsed?.status??null,
    reason:parsed?.reason??null,
    frontier:parsed?.frontier??null,
    steps:parsed?.steps??null,
    elapsed:parsed?.elapsed??null,
    crash:parsed?.crash??null,
    timeout:parsed?.timeout??false,
  };
}

const results=[];
for(const name of TARGETS){
  const row=byName.get(name);
  const attempts=[];
  for(const config of CONFIGS){
    // Always establish the exact default baseline. Thereafter stop at the
    // first ACCEPT: later larger envelopes cannot add causal information.
    if(attempts.some(a=>a.status==="ACCEPT"))break;
    const attempt=runOne(row,config);
    attempts.push(attempt);
    console.log("LEAN_RESIDUAL_SWEEP "+JSON.stringify({name,...attempt}));
    if(attempt.crash||attempt.process_error)throw new Error("resource sweep crashed: "+name);
    // A higher-budget REJECT on an expected-ACCEPT case is a scientific
    // separator, not a harness failure. Stop this target and retain it as a
    // latent wrong-verdict cliff exposed behind the default UNKNOWN boundary.
    if(attempt.status==="REJECT")break;
  }
  results.push({name,expected:row.expected,attempts});
}

const family={
  host_stack:results.filter(r=>["init-prelude.ndjson","perf/grind-ring-5.ndjson"].includes(r.name)),
  fueled_chain:results.filter(r=>r.name==="perf/fueled-chain.ndjson"),
  deep_list:results.filter(r=>r.name.includes("magma-list-deep")),
  pair_countermodel:results.filter(r=>r.name.includes("magma-list-pair")),
};
const closed=results.filter(r=>r.attempts.some(a=>a.status==="ACCEPT"));
const latentWrong=results.filter(r=>r.attempts.some(a=>a.status==="REJECT"));
const open=results.filter(r=>!r.attempts.some(a=>a.status==="ACCEPT")&&!r.attempts.some(a=>a.status==="REJECT"));
const minimal=Object.fromEntries(results.map(r=>{
  const a=r.attempts.find(x=>x.status==="ACCEPT")??null;
  return [r.name,a?{config:a.config,budget:a.budget,stack_kb:a.stack_kb,steps:a.steps,elapsed:a.elapsed}:null];
}));
const report={
  schema:"lean-seven-unknown-resource-sweep-v1",
  claim_boundary:"Diagnostic resource-envelope sweep only; no kernel semantics changed and no Arena promotion is claimed.",
  targets:TARGETS,
  configs:CONFIGS,
  results,
  minimal_accept_envelope:minimal,
  closed_count:closed.length,
  still_open_count:open.length,
  still_open:open.map(r=>r.name),
  latent_wrong_reject_count:latentWrong.length,
  latent_wrong_rejects:latentWrong.map(r=>({
    name:r.name,
    first_reject:r.attempts.find(a=>a.status==="REJECT"),
  })),
  family_summary:Object.fromEntries(Object.entries(family).map(([k,rs])=>[
    k,{count:rs.length,closed:rs.filter(r=>r.attempts.some(a=>a.status==="ACCEPT")).length,
       open:rs.filter(r=>!r.attempts.some(a=>a.status==="ACCEPT")).map(r=>r.name)}
  ])),
  gates:{
    all_seven_present:results.length===7,
    latent_wrong_rejects_are_typed:latentWrong.every(r=>
      r.expected==="ACCEPT"&&r.attempts.find(a=>a.status==="REJECT")?.reason
    ),
    no_crashes:results.every(r=>r.attempts.every(a=>!a.crash&&!a.process_error)),
    baseline_reproduces_unknown:results.every(r=>r.attempts[0]?.status==="UNKNOWN"),
  },
};
mkdirSync(dirname(outPath),{recursive:true});
writeFileSync(outPath,JSON.stringify(report,null,2)+"\n");
console.log("LEAN_SEVEN_UNKNOWN_RESOURCE_SWEEP_RESULT="+JSON.stringify(report));
console.log("PASS_LEAN_SEVEN_UNKNOWN_RESOURCE_SWEEP_V1");
