import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import {checkExport} from "./production.mjs";

const budget=Number(process.env.BUDGET??2_000_000);
const targets=[
  ["init-prelude","ACCEPT"],
  ["perf/grind-ring-5","ACCEPT"],
  ["perf/fueled-chain","ACCEPT"],
  ["perf/shared-subterm","ACCEPT"],
];

function runSet(label){
  const rows=[];
  for(const [name,expected] of targets){
    const seen=[],run0=Kernel.prototype.run;
    Kernel.prototype.run=function(...args){seen.push(this);return run0.apply(this,args);};
    const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
    const t0=Date.now();let r;
    try{r=checkExport(input,{semanticBudget:budget,inputBytes:20_000_000,recordLimit:400_000});}
    finally{Kernel.prototype.run=run0;}
    rows.push({label,name,expected,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,elapsed_ms:Date.now()-t0,frontier:r.frontier_declaration??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null,
      kernels:seen.map(k=>({localDefs:k.localDefs===true,steps:k.steps??null,
        constructed:k.allocations??null,nativeLocalDef:k.__nativeLocalDefClosureStats??null}))});
  }
  return rows;
}

const baseline=runSet("baseline");
const {installNativeLocalDefClosure}=await import("./native-localdef-closure-layer.mjs");
installNativeLocalDefClosure(true);
const candidate=runSet("candidate");

const byName=rows=>Object.fromEntries(rows.map(r=>[r.name,r]));
const b=byName(baseline),c=byName(candidate);
const deltas=targets.map(([name])=>({
  name,
  status_before:b[name].status,status_after:c[name].status,
  reason_before:b[name].reason,reason_after:c[name].reason,
  steps_before:b[name].steps,steps_after:c[name].steps,
  constructed_before:b[name].constructed,constructed_after:c[name].constructed,
  constructed_delta:(c[name].constructed??0)-(b[name].constructed??0),
  elapsed_delta_ms:c[name].elapsed_ms-b[name].elapsed_ms,
}));
const wrong=candidate.filter(r=>r.status!=="UNKNOWN"&&r.status!==r.expected).length;
const controlClean=c["perf/shared-subterm"]?.status==="ACCEPT";
const fueledParity=(c["perf/fueled-chain"]?.status===b["perf/fueled-chain"]?.status &&
  c["perf/fueled-chain"]?.reason===b["perf/fueled-chain"]?.reason);
const out={experiment:"recurrent-localdef-closure-separator",budget,wrong,controlClean,fueledParity,
  baseline,candidate,deltas,
  claim_boundary:"Causal separator only. The candidate compiles the independently recurrent 3/4-argument LocalDef WHNF application interface into transient closures; 2-arg fueled-style and 5+ spines remain on retained WHNF. No promotion implied."};
const path=new URL(`./evidence/recurrent-localdef-closure-${budget}.json`,import.meta.url);
mkdirSync(dirname(path.pathname),{recursive:true});writeFileSync(path,JSON.stringify(out,null,2)+"\n");
console.log("RECURRENT_LOCALDEF_CLOSURE "+JSON.stringify(out));
if(wrong||!controlClean||!fueledParity)process.exit(1);
