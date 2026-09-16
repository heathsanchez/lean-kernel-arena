import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import {checkExport} from "./production.mjs";

// Current-production separator. Each workflow matrix job is a fresh process, so
// prototype instrumentation cannot leak between candidates. Every candidate
// below reuses only exact immutable syntax identities or an already-retained
// lowerBound consequence; no typing/conversion/reduction law is added.
const candidate=process.env.CANDIDATE??"baseline";
const budget=Number(process.env.BUDGET??2_000_000);
if(!Number.isSafeInteger(budget)||budget<1) throw new Error("invalid BUDGET");

const p=Kernel.prototype;
let prefixInstalled=false;
if(candidate!=="baseline"){
  await import("./recursor-prefix-cache-layer.mjs");
  prefixInstalled=true;
}

if(candidate==="prefix-shortcircuit"){
  const run0=p.run,sub0=p.substitute,lower0=p.lowerBound;
  function ensure(k){
    k.__raceOccurs??=new WeakMap();
    k.__raceAbsent??=new WeakMap();
    k.__raceExact??=new WeakMap();
  }
  function depthMap(weak,root){let m=weak.get(root);if(!m){m=new Map();weak.set(root,m);}return m;}
  function occurs(k,e,d){
    if(!Array.isArray(e))return false;
    ensure(k);const m=depthMap(k.__raceOccurs,e);
    if(m.has(d)){k.__raceStats.occursHits++;return m.get(d);}
    k.__raceStats.occursStores++;
    let out=false;
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":out=false;break;
      case "var":out=e[1]===d;break;
      case "pi":case "lam":out=occurs(k,e[1],d)||occurs(k,e[2],d+1);break;
      case "app":out=occurs(k,e[1],d)||occurs(k,e[2],d);break;
      case "proj":out=occurs(k,e[3],d);break;
      case "let":out=occurs(k,e[1],d)||occurs(k,e[2],d)||occurs(k,e[3],d+1);break;
      default:out=true;
    }
    m.set(d,out);return out;
  }
  function exactMap(k,root,arg){
    let byArg=k.__raceExact.get(root);if(!byArg){byArg=new WeakMap();k.__raceExact.set(root,byArg);}
    let m=byArg.get(arg);if(!m){m=new Map();byArg.set(arg,m);}return m;
  }
  p.run=function(...xs){
    this.__raceOccurs=new WeakMap();this.__raceAbsent=new WeakMap();this.__raceExact=new WeakMap();
    this.__raceStats={queries:0,occursHits:0,occursStores:0,absentHits:0,absentStores:0,dependent:0,exactHits:0,exactStores:0};
    return run0.apply(this,xs);
  };
  p.substitute=function(root,arg,depth=0){
    if(!Array.isArray(root)||!Array.isArray(arg))return sub0.call(this,root,arg,depth);
    ensure(this);this.__raceStats.queries++;
    const absent=depthMap(this.__raceAbsent,root);
    if(absent.has(depth)){this.__raceStats.absentHits++;return absent.get(depth);}
    if(!occurs(this,root,depth)){
      const out=lower0.call(this,root,depth);
      if(out===null)throw new Error("occurrence/lowerBound disagreement");
      absent.set(depth,out);this.__raceStats.absentStores++;return out;
    }
    this.__raceStats.dependent++;
    const ex=exactMap(this,root,arg);
    if(ex.has(depth)){this.__raceStats.exactHits++;return ex.get(depth);}
    const out=sub0.call(this,root,arg,depth);
    ex.set(depth,out);this.__raceStats.exactStores++;return out;
  };
}else if(candidate==="prefix-certified"){
  const run0=p.run,sub0=p.substitute,lower0=p.lowerBound;
  function ensure(k){k.__raceIndep??=new WeakMap();k.__raceExact??=new WeakMap();}
  function indepMap(k,root){let m=k.__raceIndep.get(root);if(!m){m=new Map();k.__raceIndep.set(root,m);}return m;}
  function exactMap(k,root,arg){
    let byArg=k.__raceExact.get(root);if(!byArg){byArg=new WeakMap();k.__raceExact.set(root,byArg);}
    let m=byArg.get(arg);if(!m){m=new Map();byArg.set(arg,m);}return m;
  }
  p.run=function(...xs){
    this.__raceIndep=new WeakMap();this.__raceExact=new WeakMap();
    this.__raceStats={queries:0,independentHits:0,independentStores:0,dependentStores:0,exactHits:0,exactStores:0};
    return run0.apply(this,xs);
  };
  p.substitute=function(root,arg,depth=0){
    if(!Array.isArray(root)||!Array.isArray(arg))return sub0.call(this,root,arg,depth);
    ensure(this);this.__raceStats.queries++;
    const indep=indepMap(this,root);
    if(indep.has(depth)){
      const entry=indep.get(depth);
      if(entry.absent){this.__raceStats.independentHits++;return entry.out;}
    }else{
      const out=lower0.call(this,root,depth);
      if(out!==null){
        indep.set(depth,{absent:true,out});this.__raceStats.independentStores++;return out;
      }
      indep.set(depth,{absent:false});this.__raceStats.dependentStores++;
    }
    const ex=exactMap(this,root,arg);
    if(ex.has(depth)){this.__raceStats.exactHits++;return ex.get(depth);}
    const out=sub0.call(this,root,arg,depth);
    ex.set(depth,out);this.__raceStats.exactStores++;return out;
  };
}else if(candidate!=="baseline"&&candidate!=="recursor-prefix"){
  throw new Error("unknown candidate "+candidate);
}

const TARGETS=[["init-prelude","ACCEPT"],["perf/grind-ring-5","ACCEPT"],["perf/shared-subterm","ACCEPT"]];
function stats(k){return {race:k.__raceStats??null,recPrefixHits:k.__recPrefixHits??0,recPrefixStores:k.__recPrefixStores??0,recPrefixReductions:k.__recPrefixReductions??0};}
const rows=[];
for(const [name,expected] of TARGETS){
  const seen=[],run0=p.run;
  p.run=function(...xs){seen.push(this);return run0.apply(this,xs);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;
  try{r=checkExport(input,{semanticBudget:budget,inputBytes:20_000_000,recordLimit:400_000});}
  finally{p.run=run0;}
  const row={name,expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    elapsed_ms:Date.now()-t0,frontier:r.frontier_declaration??null,
    fallback_attempt_reason:r.fallback_attempt_reason??null,fallback_attempt_steps:r.fallback_attempt_steps??null,
    kernelStats:seen.map(stats)};
  rows.push(row);console.log("PRODUCTION_PREFIX_RACE_ROW "+JSON.stringify({candidate,budget,...row}));
}
const wrong=rows.filter(r=>r.status!=="UNKNOWN"&&r.status!==r.expected).length;
const giantsSolved=rows.slice(0,2).filter(r=>r.status==="ACCEPT").length;
const controlClean=rows[2]?.status==="ACCEPT";
const out={experiment:"production-prefix-substitution-race",candidate,budget,prefixInstalled,wrong,giantsSolved,controlClean,rows,
  claim_boundary:"Exact current-production execution separator. Prefix specialization is keyed by exact recursor rule, universe instantiation and immutable prefix identities. Binder-independent reuse is admitted only after exact occurrence/lowerBound evidence; binder-dependent reuse is keyed by exact immutable root, argument and depth after retained substitution completes. No proof rule changes."};
const path=new URL(`./evidence/production-prefix-${candidate}-${budget}.json`,import.meta.url);
mkdirSync(dirname(path.pathname),{recursive:true});writeFileSync(path,JSON.stringify(out,null,2)+"\n");
console.log("PRODUCTION_PREFIX_RACE "+JSON.stringify(out));
if(wrong||!controlClean)process.exit(1);
