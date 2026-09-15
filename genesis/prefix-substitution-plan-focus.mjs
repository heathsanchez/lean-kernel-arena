import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT"],["perf/church-numerals","ACCEPT"],
 ["perf/args-before-unfold","ACCEPT"],["perf/folded-constant-first","ACCEPT"],
 ["perf/repeated-subproblem","ACCEPT"],["perf/discarded-argument-match","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT"],
 ["undecidability/subject-reduction-redex","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"],
 ["undecidability/subject-reduction-reduct","REJECT"]
];

const p=K.Kernel.prototype,run0=p.run,sub0=p.substitute,shift0=p.shift;

function depthMap(k,e){
  k.__substPlans??=new WeakMap();
  let m=k.__substPlans.get(e);
  if(!m){m=new Map();k.__substPlans.set(e,m);}
  return m;
}
function fixed(out){return {dyn:false,out};}
function compilePlan(k,e,d){
  if(!Array.isArray(e))return fixed(e);
  const m=depthMap(k,e);
  if(m.has(d)){k.__planHits=(k.__planHits??0)+1;return m.get(d);}
  k.tick();k.__planStores=(k.__planStores??0)+1;
  let q;
  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":q=fixed(e);break;
    case "var":
      if(e[1]===d) q={dyn:true,kind:"arg",shift:d};
      else if(e[1]>d) q=fixed(k.make("var",e[1]-1));
      else q=fixed(e);
      break;
    case "pi":case "lam":{
      const a=compilePlan(k,e[1],d),b=compilePlan(k,e[2],d+1);
      q=(!a.dyn&&!b.dyn)?fixed(k.make(e[0],a.out,b.out)):{dyn:true,kind:e[0],a,b};
      break;
    }
    case "app":{
      const f=compilePlan(k,e[1],d),a=compilePlan(k,e[2],d);
      q=(!f.dyn&&!a.dyn)?fixed(k.make("app",f.out,a.out)):{dyn:true,kind:"app",f,a};
      break;
    }
    case "proj":{
      const x=compilePlan(k,e[3],d);
      q=!x.dyn?fixed(k.make("proj",e[1],e[2],x.out)):{dyn:true,kind:"proj",name:e[1],idx:e[2],x};
      break;
    }
    case "let":{
      const a=compilePlan(k,e[1],d),v=compilePlan(k,e[2],d),b=compilePlan(k,e[3],d+1);
      q=(!a.dyn&&!v.dyn&&!b.dyn)?fixed(k.make("let",a.out,v.out,b.out)):{dyn:true,kind:"let",a,v,b};
      break;
    }
    default:q={dyn:true,kind:"fallback",root:e,depth:d};break;
  }
  m.set(d,q);return q;
}
function executePlan(k,q,arg){
  if(!q.dyn)return q.out;
  k.tick();k.__planExecNodes=(k.__planExecNodes??0)+1;
  switch(q.kind){
    case "arg":
      if(q.shift===0){k.__zeroShiftPlanHits=(k.__zeroShiftPlanHits??0)+1;return arg;}
      return shift0.call(k,arg,q.shift);
    case "pi":case "lam":return k.make(q.kind,executePlan(k,q.a,arg),executePlan(k,q.b,arg));
    case "app":return k.make("app",executePlan(k,q.f,arg),executePlan(k,q.a,arg));
    case "proj":return k.make("proj",q.name,q.idx,executePlan(k,q.x,arg));
    case "let":return k.make("let",executePlan(k,q.a,arg),executePlan(k,q.v,arg),executePlan(k,q.b,arg));
    case "fallback":return sub0.call(k,q.root,arg,q.depth);
  }
}
p.run=function(...args){this.__substPlans=new WeakMap();return run0.apply(this,args);};
p.substitute=function(root,arg,depth=0){
  if(!Array.isArray(root)||!Array.isArray(arg))return sub0.call(this,root,arg,depth);
  this.__planQueries=(this.__planQueries??0)+1;
  return executePlan(this,compilePlan(this,root,depth),arg);
};

const rows=[];
for(const [name,want] of TARGETS){
  const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  const t0=Date.now();let r;
  try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}
  finally{p.run=old;}
  const sum=q=>seen.reduce((n,k)=>n+(k[q]??0),0);
  const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
    prefixHits:sum("__recPrefixHits"),prefixStores:sum("__recPrefixStores"),
    planQueries:sum("__planQueries"),planHits:sum("__planHits"),planStores:sum("__planStores"),
    planExecNodes:sum("__planExecNodes"),zeroShiftPlanHits:sum("__zeroShiftPlanHits")};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT",protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"prefix-substitution-plan-focus",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
 claim_boundary:"Exact execution compilation of retained de-Bruijn substitution. For each immutable term identity and binder depth, a cached plan precomputes argument-independent branches and index decrements once; each substitution executes only branches that depend on the new argument. Shift-by-zero at an exact binder occurrence returns the immutable argument. All constructors and binder-depth transitions match retained substitution exactly; no typing, conversion, or reduction rule changes."};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/prefix-substitution-plan-focus.json",JSON.stringify(out,null,2)+"\n");
console.log("PREFIX_SUBSTITUTION_PLAN_FOCUS "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
