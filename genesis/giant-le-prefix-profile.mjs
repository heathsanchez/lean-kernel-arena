import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

const LE='["[\"[]\",\"str\",\"LE\"]","str","le"]';
function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
const p=K.Kernel.prototype,whnf0=p.whnf,run0=p.run;
p.run=function(...xs){
  this.__lePrefix={calls:0,byArity:new Map(),prefix2:new Set(),prefix3:new Set(),full:new Set(),bytes:{prefix2:0,prefix3:0,full:0}};
  return run0.apply(this,xs);
};
p.whnf=function(e){
  const {h,args}=spine(e);
  if(h?.[0]==="const"&&h[1]===LE){
    this.__lePrefix??={calls:0,byArity:new Map(),prefix2:new Set(),prefix3:new Set(),full:new Set(),bytes:{prefix2:0,prefix3:0,full:0}};
    const q=this.__lePrefix;q.calls++;q.byArity.set(args.length,(q.byArity.get(args.length)??0)+1);
    const k2=JSON.stringify([h,...args.slice(0,2)]);q.prefix2.add(k2);q.bytes.prefix2+=k2.length;
    const k3=JSON.stringify([h,...args.slice(0,3)]);q.prefix3.add(k3);q.bytes.prefix3+=k3.length;
    const kf=JSON.stringify([h,...args]);q.full.add(kf);q.bytes.full+=kf.length;
  }
  return whnf0.call(this,e);
};

const seen=[],captureRun=p.run;
p.run=function(...xs){seen.push(this);return captureRun.apply(this,xs);};
const input=readFileSync(new URL("../_build/tests/perf/grind-ring-5.ndjson",import.meta.url),"utf8");
let r;
try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=run0;}
const out={status:r.status,reason:r.reason,steps:r.steps??null,frontier:r.frontier_declaration??null,
  calls:0,byArity:{},uniquePrefix2:0,uniquePrefix3:0,uniqueFull:0};
const p2=new Set(),p3=new Set(),pf=new Set();
for(const k of seen){
  const q=k.__lePrefix;if(!q)continue;
  out.calls+=q.calls;
  for(const [a,n] of q.byArity)out.byArity[a]=(out.byArity[a]??0)+n;
  for(const x of q.prefix2)p2.add(x);for(const x of q.prefix3)p3.add(x);for(const x of q.full)pf.add(x);
}
out.uniquePrefix2=p2.size;out.uniquePrefix3=p3.size;out.uniqueFull=pf.size;
out.samplePrefix2=[...p2].slice(0,5).map(s=>({bytes:s.length,text:s.slice(0,800)}));
console.log("GIANT_LE_PREFIX_PROFILE "+JSON.stringify(out));
