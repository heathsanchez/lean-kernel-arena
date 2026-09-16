import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {checkExport} from "./production.mjs";
import {Kernel} from "./kernel-base.mjs";

const budget=Number(process.env.BUDGET??2_000_000);
if(!Number.isSafeInteger(budget)||budget<1)throw new Error("invalid BUDGET");

const TARGETS=[
  ["init-prelude","ACCEPT"],
  ["perf/grind-ring-5","ACCEPT"],
  ["perf/shared-subterm","ACCEPT"]
];

const sum=(seen,key,subkey)=>seen.reduce((n,k)=>n+(subkey===undefined?(k[key]??0):(k[key]?.[subkey]??0)),0);
const rows=[];

for(const [name,expected] of TARGETS){
  const seen=[],p=Kernel.prototype,run0=p.run;
  p.run=function(...args){seen.push(this);return run0.apply(this,args);};
  const input=readFileSync(new URL(`../_build/tests/${name}.ndjson`,import.meta.url),"utf8");
  const t0=Date.now();let result;
  try{
    result=checkExport(input,{semanticBudget:budget,inputBytes:20_000_000,recordLimit:400_000});
  }finally{
    p.run=run0;
  }
  const row={
    name,expected,status:result.status,reason:result.reason,
    steps:result.steps??null,constructed:result.constructed??null,
    elapsed_ms:Date.now()-t0,frontier:result.frontier_declaration??null,
    supportHits:sum(seen,"__binderStats","supportHits"),
    supportFallbacks:sum(seen,"__binderStats","supportFallbacks"),
    rangeSkips:sum(seen,"__binderStats","rangeSkips"),
    rangeHits:sum(seen,"__binderStats","rangeHits"),
    rangeMisses:sum(seen,"__binderStats","rangeMisses"),
    supportSeedVisits:sum(seen,"__supportStats","seedVisits"),
    supportMakeKnown:sum(seen,"__supportStats","makeKnown"),
    supportMakeUnknown:sum(seen,"__supportStats","makeUnknown")
  };
  rows.push(row);
  console.log("PRODUCTION_SUPPORT_FRONTIER_ROW "+JSON.stringify({budget,...row}));
}

const wrong=rows.filter(r=>r.status!=="UNKNOWN"&&r.status!==r.expected).length;
const controlClean=rows[2]?.status==="ACCEPT";
const out={
  experiment:"production-support-frontier",budget,wrong,controlClean,rows,
  claim_boundary:"Execution-only measurement of compositional exact loose-variable support consumed by retained binder transport. No typing, conversion, reduction, or declaration rule is changed."
};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync(`genesis/evidence/production-support-frontier-${budget}.json`,JSON.stringify(out,null,2)+"\n");
console.log("PRODUCTION_SUPPORT_FRONTIER "+JSON.stringify(out));
if(wrong||!controlClean)process.exit(1);
