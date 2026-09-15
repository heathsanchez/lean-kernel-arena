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
const p=K.Kernel.prototype,run0=p.run,shift0=p.shift,sub0=p.substitute;

function maxFree(k,e){
 if(!Array.isArray(e))return -1;
 k.__maxFree??=new WeakMap();
 if(k.__maxFree.has(e)){k.tick();k.__maxFreeHits=(k.__maxFreeHits??0)+1;return k.__maxFree.get(e);}
 k.tick();k.__maxFreeStores=(k.__maxFreeStores??0)+1;
 let m=-1;
 switch(e[0]){
  case "sort":case "const":case "nat":case "strlit":m=-1;break;
  case "var":m=e[1];break;
  case "app":m=Math.max(maxFree(k,e[1]),maxFree(k,e[2]));break;
  case "proj":m=maxFree(k,e[3]);break;
  case "pi":case "lam":{
   const a=maxFree(k,e[1]),b=maxFree(k,e[2]),bo=b<=0?-1:b-1;m=Math.max(a,bo);break;
  }
  case "let":{
   const a=maxFree(k,e[1]),v=maxFree(k,e[2]),b=maxFree(k,e[3]),bo=b<=0?-1:b-1;m=Math.max(a,v,bo);break;
  }
  default:m=Number.MAX_SAFE_INTEGER;
 }
 k.__maxFree.set(e,m);return m;
}
p.run=function(...args){this.__maxFree=new WeakMap();return run0.apply(this,args);};
p.shift=function(e,amount,cut=0){
 if(Array.isArray(e)&&maxFree(this,e)<cut){this.__closedShiftSkips=(this.__closedShiftSkips??0)+1;return e;}
 return shift0.call(this,e,amount,cut);
};
p.substitute=function(e,arg,depth=0){
 if(Array.isArray(e)&&maxFree(this,e)<depth){this.__closedSubstSkips=(this.__closedSubstSkips??0)+1;return e;}
 return sub0.call(this,e,arg,depth);
};

const rows=[];
for(const [name,want] of TARGETS){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}finally{p.run=old;}
 const sum=q=>seen.reduce((n,k)=>n+(k[q]??0),0);
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
  prefixHits:sum("__recPrefixHits"),prefixStores:sum("__recPrefixStores"),
  maxFreeHits:sum("__maxFreeHits"),maxFreeStores:sum("__maxFreeStores"),
  closedSubstSkips:sum("__closedSubstSkips"),closedShiftSkips:sum("__closedShiftSkips")};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT",protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"prefix-closed-subterm-pruning",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
 claim_boundary:"Exact structural execution pruning. maxFree(t) is the greatest free de-Bruijn index of immutable term t, cached by exact identity. If maxFree(t)<depth, substitution at that depth cannot replace or decrement any variable, so it returns t unchanged. If maxFree(t)<cut, shifting at cut cannot affect t and likewise returns t unchanged. All other cases delegate to retained semantics. No typing, conversion, or reduction law changes."};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/prefix-closed-subterm-pruning.json",JSON.stringify(out,null,2)+"\n");
console.log("PREFIX_CLOSED_SUBTERM_PRUNING "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
