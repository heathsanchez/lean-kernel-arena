import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./recursor-prefix-cache-layer.mjs");
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype,sub0=p.substitute,tick0=p.tick,run0=p.run;
function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {h,args};}
function sig(k,e){
 if(!Array.isArray(e))return {tag:typeof e};
 if(e[0]==="app"){const {h,args}=spine(e);return {tag:"app",head:h?.[0]==="const"?h[1]:h?.[0],kind:h?.[0]==="const"?k.env?.get(h[1])?.kind:null,args:args.length};}
 if(e[0]==="lam"||e[0]==="pi")return {tag:e[0],body:e[2]?.[0],domain:e[1]?.[0]};
 return {tag:e[0],index:e[0]==="var"?e[1]:undefined};
}
function id(k,e){
 if(!Array.isArray(e))return "scalar:"+String(e);
 k.__substProfileIds??=new WeakMap();k.__substProfileNext??=1;
 let x=k.__substProfileIds.get(e);if(x===undefined){x=k.__substProfileNext++;k.__substProfileIds.set(e,x);}return x;
}
p.run=function(...args){
 this.__substProfileIds=new WeakMap();this.__substProfileNext=1;this.__substTopDepth=0;this.__substTopActive=null;this.__substTopRows=[];
 return run0.apply(this,args);
};
p.tick=function(...args){
 if(this.__substTopActive)this.__substTopActive.ticks++;
 return tick0.apply(this,args);
};
p.substitute=function(root,arg,depth=0){
 const top=(this.__substTopDepth??0)===0;
 let rec=null;
 if(top){
  rec={rootId:id(this,root),argId:id(this,arg),depth,ticks:0,root:sig(this,root),arg:sig(this,arg),before:this.steps??0};
  this.__substTopRows??=[];this.__substTopRows.push(rec);this.__substTopActive=rec;
 }
 this.__substTopDepth=(this.__substTopDepth??0)+1;
 try{return sub0.call(this,root,arg,depth);}
 finally{
  this.__substTopDepth--;
  if(top){rec.after=this.steps??0;rec.delta=rec.after-rec.before;this.__substTopActive=null;}
 }
};
const seen=[],oldRun=p.run;p.run=function(...xs){seen.push(this);return oldRun.apply(this,xs);};
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const result=K.checkExport(input,CAPS,1_000_000);p.run=oldRun;
const rows=seen.flatMap(k=>k.__substTopRows??[]);
const byRoot=new Map();
for(const r of rows){
 let x=byRoot.get(r.rootId);if(!x){x={rootId:r.rootId,root:r.root,calls:0,ticks:0,max:0,args:new Set(),depths:new Set()};byRoot.set(r.rootId,x);}
 x.calls++;x.ticks+=r.ticks;x.max=Math.max(x.max,r.ticks);x.args.add(r.argId);x.depths.add(r.depth);
}
const topRoots=[...byRoot.values()].map(x=>({...x,uniqueArgs:x.args.size,depths:[...x.depths],args:undefined})).sort((a,b)=>b.ticks-a.ticks).slice(0,30);
const topCalls=[...rows].sort((a,b)=>b.ticks-a.ticks).slice(0,30);
const out={experiment:"shared-subterm-top-substitution-census",
 result:{status:result.status,reason:result.reason,steps:result.steps,constructed:result.constructed},
 prefixHits:seen.reduce((n,k)=>n+(k.__recPrefixHits??0),0),
 topCallCount:rows.length,topRoots,topCalls};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/shared-subterm-top-substitution-census.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_SUBTERM_TOP_SUBSTITUTION_CENSUS "+JSON.stringify(out));
