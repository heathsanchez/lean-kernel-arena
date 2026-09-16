import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import {checkExport} from "./production.mjs";
import {installBetaEnvironmentClosures} from "./beta-environment-closure-layer.mjs";

const budget=Number(process.env.BUDGET??2_000_000);
const targets=[["init-prelude","ACCEPT"],["perf/grind-ring-5","ACCEPT"],["perf/shared-subterm","ACCEPT"]];
const p=Kernel.prototype;
installBetaEnvironmentClosures(true);
const rows=[];
for(const [name,expected] of targets){
  const seen=[],run0=p.run;
  p.run=function(...args){seen.push(this);return run0.apply(this,args);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;
  try{r=checkExport(input,{semanticBudget:budget,inputBytes:20_000_000,recordLimit:400_000});}
  finally{p.run=run0;}
  rows.push({name,expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    elapsed_ms:Date.now()-t0,frontier:r.frontier_declaration??null,
    fallback_attempt_reason:r.fallback_attempt_reason??null,fallback_attempt_steps:r.fallback_attempt_steps??null,
    kernels:seen.map(k=>({localDefs:k.localDefs===true,steps:k.steps??null,constructed:k.allocations??null,betaEnv:k.__betaEnvStats??null}))});
}
installBetaEnvironmentClosures(false);
const wrong=rows.filter(r=>r.status!=="UNKNOWN"&&r.status!==r.expected).length;
const controlClean=rows[2]?.status==="ACCEPT";
const out={experiment:"current-production-beta-environment-closure",budget,wrong,controlClean,rows,
  claim_boundary:"Existing transient beta-environment closure mechanism requalified on the current repaired production stack. Closures remain internal to one WHNF request and are materialized back to ordinary immutable terms before retained checking resumes. No stored syntax, inference rule, conversion rule, declaration rule, or external result representation changes."};
const path=new URL(`./evidence/current-beta-closure-${budget}.json`,import.meta.url);
mkdirSync(dirname(path.pathname),{recursive:true});writeFileSync(path,JSON.stringify(out,null,2)+"\n");
console.log("CURRENT_BETA_CLOSURE_SEPARATOR "+JSON.stringify(out));
if(wrong||!controlClean)process.exit(1);
