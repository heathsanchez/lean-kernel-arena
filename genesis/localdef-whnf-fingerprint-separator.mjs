import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import {checkExport} from "./production.mjs";

const budget=Number(process.env.BUDGET??2_000_000);
await import("./localdef-whnf-fingerprint-layer.mjs");
const p=Kernel.prototype;
const targets=[
  ["init-prelude","ACCEPT"],
  ["perf/grind-ring-5","ACCEPT"],
  ["perf/fueled-chain","ACCEPT"],
  ["perf/shared-subterm","ACCEPT"],
];
const rows=[];
for(const [name,expected] of targets){
  const seen=[],run0=p.run;
  p.run=function(...args){seen.push(this);return run0.apply(this,args);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;
  try{r=checkExport(input,{semanticBudget:budget,inputBytes:20_000_000,recordLimit:400_000});}
  finally{p.run=run0;}
  rows.push({
    name,expected,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
    frontier:r.frontier_declaration??null,
    fallback_attempt_reason:r.fallback_attempt_reason??null,
    fallback_attempt_steps:r.fallback_attempt_steps??null,
    kernels:seen.map(k=>({
      localDefs:k.localDefs===true,steps:k.steps??null,constructed:k.allocations??null,
      fingerprint:k.__localDefFingerprint??null,
    })),
  });
}
const wrong=rows.filter(r=>r.status!=="UNKNOWN"&&r.status!==r.expected).length;
const controlClean=rows.find(r=>r.name==="perf/shared-subterm")?.status==="ACCEPT";
const out={
  experiment:"localdef-whnf-obstruction-fingerprint",budget,wrong,controlClean,rows,
  claim_boundary:"Diagnostic only. Counts structural WHNF/substitution shapes and exact active-context local-definition heads without charging semantic ticks or changing evaluator decisions. No repair is selected by this run.",
};
const path=new URL(`./evidence/localdef-whnf-fingerprint-${budget}.json`,import.meta.url);
mkdirSync(dirname(path.pathname),{recursive:true});
writeFileSync(path,JSON.stringify(out,null,2)+"\n");
console.log("LOCALDEF_WHNF_FINGERPRINT "+JSON.stringify(out));
if(wrong||!controlClean)process.exit(1);
