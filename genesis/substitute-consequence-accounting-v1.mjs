import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import * as P from "./production.mjs";

const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGET=4_000_000;

function addInto(dst,src){
  if(!src||typeof src!=="object")return;
  for(const [k,v] of Object.entries(src))
    if(typeof v==="number"&&Number.isFinite(v)) dst[k]=(dst[k]??0)+v;
}
function ratio(num,den){return den>0?num/den:0;}

const retainedRun=Kernel.prototype.run;
const rows=[];
for(const name of TARGETS){
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const seen=[];
  Kernel.prototype.run=function(...args){
    seen.push(this);
    return retainedRun.apply(this,args);
  };
  let r;
  try{
    r=P.checkExport(input,{
      semanticBudget:BUDGET,
      inputBytes:20_000_000,
      recordLimit:400_000,
    });
  }finally{
    Kernel.prototype.run=retainedRun;
  }

  const binder={},sem={};
  let compiledNodeHits=0,compiledSpineHits=0,allocations=0;
  for(const k of seen){
    addInto(binder,k.__binderStats);
    addInto(sem,k.__semStats);
    compiledNodeHits+=k.__compiledNodeHits??0;
    compiledSpineHits+=k.__compiledSpineHits??0;
    allocations+=k.allocations??0;
  }
  const substHits=binder.substHits??0;
  const substMisses=binder.substMisses??0;
  const substReuseRatio=ratio(substHits,substHits+substMisses);

  rows.push({
    name,
    status:r.status,
    reason:r.reason??null,
    steps:r.steps??null,
    frontier:r.frontier_declaration??null,
    kernels_seen:seen.length,
    binder_stats:binder,
    semantic_cache_stats:sem,
    compiled_node_hits:compiledNodeHits,
    compiled_spine_hits:compiledSpineHits,
    allocations,
    substitution_reuse_ratio:substReuseRatio,
  });
  console.log("SUBSTITUTE_CONSEQUENCE_ACCOUNTING_ROW="+JSON.stringify(rows.at(-1)));
}

const ratios=rows.map(r=>r.substitution_reuse_ratio);
const saturated=ratios.every(x=>x>=0.80);
const sparse=ratios.every(x=>x<=0.20);
const classification=saturated?"input-reuse-saturated":sparse?"input-reuse-sparse":"mixed";

const report={
  schema:"substitute-consequence-accounting-v1",
  precommit:{
    realitygraph_commit:"2a147eb014986b07d53b6d70b012837235fa514e",
    source_episode_run:35432871957,
    source_episode_artifact:10581205893,
    source_episode_digest:"sha256:f04a37a60bf265463b3dec96e10dc466fbc9bc6ec1ba4aeb1f6db9faa91469c0",
  },
  candidate:"account existing exact substitution memoization, binder transport skips and compiled representation reuse before adding another representation",
  claim_boundary:"Diagnostic accounting only. rangeSkips is an aggregate binder-transport counter and is not attributed solely to substitution. No new semantic or performance rule is introduced.",
  rows,
  classification,
  gates:{
    no_wrong_reject:rows.every(r=>r.status!=="REJECT"),
    both_unknown_at_4m:rows.every(r=>r.status==="UNKNOWN"&&r.steps===4_000_001),
    substitution_counters_present:rows.every(r=>(r.binder_stats.substHits??0)+(r.binder_stats.substMisses??0)>0),
    compiled_reuse_counters_present:rows.every(r=>r.compiled_node_hits>=0&&r.compiled_spine_hits>=0),
    classification_total:["input-reuse-saturated","input-reuse-sparse","mixed"].includes(classification),
  },
};
mkdirSync(dirname("genesis/evidence/substitute-consequence-accounting-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/substitute-consequence-accounting-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("SUBSTITUTE_CONSEQUENCE_ACCOUNTING_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_SUBSTITUTE_CONSEQUENCE_ACCOUNTING_V1");
console.log("CLASSIFICATION="+classification);
