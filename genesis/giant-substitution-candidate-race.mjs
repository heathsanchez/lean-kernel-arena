import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";

const candidate=process.env.CANDIDATE??"baseline";
const budget=Number(process.env.BUDGET??2_000_000);
if(!Number.isSafeInteger(budget)||budget<1)throw new Error("invalid BUDGET");

const p=K.Kernel.prototype;
if(candidate==="exact-identity"){
  const run0=p.run,sub0=p.substitute;
  function slot(k,root,arg){
    k.__raceExact??=new WeakMap();
    let byArg=k.__raceExact.get(root);
    if(!byArg){byArg=new WeakMap();k.__raceExact.set(root,byArg);}
    let byDepth=byArg.get(arg);
    if(!byDepth){byDepth=new Map();byArg.set(arg,byDepth);}
    return byDepth;
  }
  p.run=function(...xs){this.__raceExact=new WeakMap();this.__raceExactHits=0;this.__raceExactStores=0;return run0.apply(this,xs);};
  p.substitute=function(root,arg,depth=0){
    if(!Array.isArray(root)||!Array.isArray(arg))return sub0.call(this,root,arg,depth);
    const m=slot(this,root,arg);
    if(m.has(depth)){this.__raceExactHits++;return m.get(depth);}
    const out=sub0.call(this,root,arg,depth);m.set(depth,out);this.__raceExactStores++;return out;
  };
}else if(candidate==="unused"){
  await import("./unused-substitution-layer.mjs");
}else if(candidate==="fv-mask"){
  await import("./free-variable-mask-substitution-layer.mjs");
}else if(candidate==="dynamic-slot"){
  await import("./compiled-dynamic-slot-layer.mjs");
}else if(candidate==="support-pruned"){
  await import("./compiled-dynamic-slot-layer.mjs");
  await import("./support-pruned-substitution-layer.mjs");
}else if(candidate!=="baseline"){
  throw new Error("unknown candidate "+candidate);
}

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
  ["init-prelude","ACCEPT"],
  ["perf/grind-ring-5","ACCEPT"],
  ["perf/shared-subterm","ACCEPT"]
];

function stats(k){
  return {
    exactHits:k.__raceExactHits??0,exactStores:k.__raceExactStores??0,
    unused:k.__unusedStats??null,fv:k.__fvStats??null,
    slot:k.__slotStats??null,support:k.__supportSubStats??null
  };
}

const rows=[];
for(const [name,expected] of TARGETS){
  const seen=[],run=p.run;
  p.run=function(...xs){seen.push(this);return run.apply(this,xs);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;
  try{r=K.checkExport(input,CAPS,budget);}finally{p.run=run;}
  const row={name,expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    elapsed_ms:Date.now()-t0,frontier:r.frontier_declaration??null,kernelStats:seen.map(stats)};
  rows.push(row);console.log("GIANT_SUBSTITUTION_RACE_ROW "+JSON.stringify({candidate,budget,...row}));
}
const wrong=rows.filter(r=>r.status!=="UNKNOWN"&&r.status!==r.expected).length;
const solved=rows.filter(r=>r.status===r.expected).length;
const giantsSolved=rows.slice(0,2).filter(r=>r.status==="ACCEPT").length;
const controlClean=rows[2]?.status==="ACCEPT";
const out={experiment:"giant-substitution-candidate-race",candidate,budget,wrong,solved,giantsSolved,controlClean,rows,
  claim_boundary:"Execution-only separator. Every candidate either memoizes exact immutable identities or applies an already-existing exact de-Bruijn support consequence. Verdict semantics and the requested semantic budget are unchanged."};
mkdirSync("genesis/evidence",{recursive:true});
const safe=candidate.replace(/[^a-z0-9-]/g,"-");
writeFileSync(`genesis/evidence/giant-substitution-${safe}-${budget}.json`,JSON.stringify(out,null,2)+"\n");
console.log("GIANT_SUBSTITUTION_RACE "+JSON.stringify(out));
if(wrong||!controlClean)process.exit(1);
