import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype,sub0=p.substitute,run0=p.run,whnf0=p.whnf,seen=[];

function freeMask(k,root){
  if(!Array.isArray(root))return 0n;
  k.__freeMask??=new WeakMap();
  if(k.__freeMask.has(root))return k.__freeMask.get(root);
  const work=[{e:root,post:false}],vals=[];
  while(work.length){
    const f=work.pop(),e=f.e;
    if(k.__freeMask.has(e)){vals.push(k.__freeMask.get(e));continue;}
    if(f.post){
      const take=()=>vals.pop();
      let m=0n;
      if(f.tag==="pi"||f.tag==="lam"){const body=take(),dom=take();m=dom|(body>>1n);}
      else if(f.tag==="app"){const a=take(),fn=take();m=fn|a;}
      else if(f.tag==="proj")m=take();
      else if(f.tag==="let"){const body=take(),val=take(),ty=take();m=ty|val|(body>>1n);}
      k.__freeMask.set(e,m);vals.push(m);continue;
    }
    let m;
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":m=0n;break;
      case "var":m=1n<<BigInt(e[1]);break;
      case "pi":case "lam":
        work.push({e,post:true,tag:e[0]});work.push({e:e[2],post:false});work.push({e:e[1],post:false});continue;
      case "app":
        work.push({e,post:true,tag:"app"});work.push({e:e[2],post:false});work.push({e:e[1],post:false});continue;
      case "proj":
        work.push({e,post:true,tag:"proj"});work.push({e:e[3],post:false});continue;
      case "let":
        work.push({e,post:true,tag:"let"});work.push({e:e[3],post:false});work.push({e:e[2],post:false});work.push({e:e[1],post:false});continue;
      default:m=-1n;break;
    }
    k.__freeMask.set(e,m);vals.push(m);
  }
  return vals.pop();
}
p.run=function(...args){this.__freeMask=new WeakMap();this.__whnfKind=[];this.__subDepth=0;this.__classStats=new Map();seen.push(this);return run0.apply(this,args);};
p.whnf=function(e){this.__whnfKind??=[];this.__whnfKind.push(Array.isArray(e)?e[0]:"primitive");try{return whnf0.call(this,e);}finally{this.__whnfKind.pop();}};
p.substitute=function(root,arg,depth=0){
  const outer=(this.__subDepth??0)===0;this.__subDepth=(this.__subDepth??0)+1;
  let cls=null,before=0;
  if(outer&&depth===0){
    const m=freeMask(this,root);
    cls=m===0n?"closed":(m&1n)===0n?"drop-only":"uses-arg";
    before=this.steps??0;
  }
  try{return sub0.call(this,root,arg,depth);}
  finally{
    this.__subDepth--;
    if(outer&&depth===0){
      const cost=(this.steps??0)-before,site=this.__whnfKind?.at(-1)??"<none>",key=site+":"+cls;
      const q=this.__classStats.get(key)??{site,cls,calls:0,totalCost:0,maxCost:0};
      q.calls++;q.totalCost+=cost;q.maxCost=Math.max(q.maxCost,cost);this.__classStats.set(key,q);
    }
  }
};

const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const t0=Date.now(),r=K.checkExport(input,CAPS,1_000_000);
const classes=[];
for(const k of seen)for(const q of k.__classStats?.values()??[])classes.push({...q,avgCost:q.totalCost/Math.max(1,q.calls)});
classes.sort((a,b)=>b.totalCost-a.totalCost);
const out={experiment:"shared-beta-substitution-dependency-class",result:{status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0},classes};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/shared-beta-substitution-dependency-class.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_BETA_SUBSTITUTION_DEPENDENCY_CLASS "+JSON.stringify(out));
