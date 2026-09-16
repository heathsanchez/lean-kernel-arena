import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function head(e){
  let h=e,n=0;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  if(!Array.isArray(h))return {tag:typeof h,args:n};
  if(h[0]==="const")return {tag:"const",name:h[1],args:n};
  return {tag:h[0],args:n};
}

const p=K.Kernel.prototype,run0=p.run,normal0=p.normal;
p.run=function(...xs){
  this.__rootNorm={depth:0,roots:new WeakMap(),rows:[],repeatRoots:0,uniqueRoots:0};
  return run0.apply(this,xs);
};
p.normal=function(e){
  this.__rootNorm??={depth:0,roots:new WeakMap(),rows:[],repeatRoots:0,uniqueRoots:0};
  const q=this.__rootNorm,isRoot=q.depth===0,start=this.steps,decl=this.currentDeclaration;
  let prior=0;
  if(isRoot&&Array.isArray(e)){
    prior=q.roots.get(e)??0;
    q.roots.set(e,prior+1);
    if(prior)q.repeatRoots++;else q.uniqueRoots++;
  }
  q.depth++;
  try{
    const out=normal0.call(this,e);
    if(isRoot){
      q.rows.push({decl,shape:head(e),outShape:head(out),same:e===out,prior,cost:this.steps-start});
    }
    return out;
  }catch(err){
    if(isRoot)q.rows.push({decl,shape:head(e),same:null,prior,cost:this.steps-start,threw:String(err?.message??err)});
    throw err;
  }finally{q.depth--;}
};
const result0=p.result;
p.result=function(...xs){
  const r=result0.apply(this,xs),q=this.__rootNorm;
  if(q){
    const target=q.rows.filter(x=>typeof x.decl==="string"&&x.decl.includes("isValidChar_UInt32"));
    r.__rootNorm={
      repeatRoots:q.repeatRoots,uniqueRoots:q.uniqueRoots,
      topTarget:target.sort((a,b)=>b.cost-a.cost).slice(0,20),
      targetCalls:target.length,
      targetCost:target.reduce((n,x)=>n+x.cost,0)
    };
  }
  return r;
};

for(const name of ["init-prelude","perf/grind-ring-5"]){
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now(),r=K.checkExport(input,CAPS,2_000_000);
  console.log("NORMAL_ROOT_PROFILE "+JSON.stringify({
    name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    frontier:r.frontier_declaration??null,profile:r.__rootNorm??null,elapsed_ms:Date.now()-t0
  }));
}
