import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import {checkExport} from "./production.mjs";
await import("./exact-context-whnf-cache-layer.mjs");

const budget=Number(process.env.BUDGET??2_000_000);
const targets=[["init-prelude","ACCEPT"],["perf/grind-ring-5","ACCEPT"],["perf/shared-subterm","ACCEPT"]];
const p=Kernel.prototype,run0=p.run;
const rows=[];
for(const [name,expected] of targets){
  const seen=[];
  p.run=function(...args){seen.push(this);return run0.apply(this,args);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;
  try{r=checkExport(input,{semanticBudget:budget,inputBytes:20_000_000,recordLimit:400_000});}
  finally{p.run=run0;}
  rows.push({name,expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    elapsed_ms:Date.now()-t0,frontier:r.frontier_declaration??null,
    fallback_attempt_reason:r.fallback_attempt_reason??null,fallback_attempt_steps:r.fallback_attempt_steps??null,
    kernels:seen.map(k=>({localDefs:k.localDefs===true,steps:k.steps??null,constructed:k.allocations??null,
      whnfHits:k.__whnfExactHits??0,whnfStores:k.__whnfExactStores??0}))});
}
const wrong=rows.filter(r=>r.status!=="UNKNOWN"&&r.status!==r.expected).length;
const controlClean=rows[2]?.status==="ACCEPT";
const out={experiment:"exact-context-whnf-cache",budget,wrong,controlClean,rows,
  claim_boundary:"Successful WHNF reuse only under exact immutable term identity, exact active local-context entry identities, and exact execution-mode key. Cache resets every run; failures are never cached; checking rules are unchanged."};
const path=new URL(`./evidence/context-whnf-cache-${budget}.json`,import.meta.url);
mkdirSync(dirname(path.pathname),{recursive:true});writeFileSync(path,JSON.stringify(out,null,2)+"\n");
console.log("CONTEXT_WHNF_CACHE_SEPARATOR "+JSON.stringify(out));
if(wrong||!controlClean)process.exit(1);
