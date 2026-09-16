import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./compiled-le-nat-dictionary-layer.mjs";
import "./compiled-nat-class-reduction-layer.mjs";
import "./compiled-constant-decidable-nat-layer.mjs";
import "./compiled-nat-pow-layer.mjs";
import "./compiled-decidable-nat-composition-layer.mjs";
import "./compiled-nat-isvalidchar-consequence-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
function prettyName(s){try{let x=JSON.parse(s),p=[];while(Array.isArray(x)&&x.length===3){p.push(String(x[2]));x=JSON.parse(x[0]);}return p.reverse().join(".");}catch{return String(s);}}
function head(e){let h=e,n=0;while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}return Array.isArray(h)?{tag:h[0],name:h[0]==="const"?prettyName(h[1]):null,args:n}:{tag:typeof h,args:n};}
function sketch(e,d=12){if(!Array.isArray(e))return e;if(d<=0)return["…",e[0]];if(["nat","var","sort","strlit"].includes(e[0]))return e;if(e[0]==="const")return["const",prettyName(e[1]),e[2]??[]];if(e[0]==="proj")return["proj",prettyName(e[1]),e[2],sketch(e[3],d-1)];return[e[0],...e.slice(1).map(x=>sketch(x,d-1))];}

const p=K.Kernel.prototype;
const methods=["validate","shift","substitute","same","whnf","normal","proofType","equal","instantiateDeclaration","infer","getApp","appN","instantiateForalls","splitAllForalls"];
const originals=new Map();
for(const name of methods){if(typeof p[name]!=="function")continue;const orig=p[name];originals.set(name,orig);p[name]=function(...args){
  this.__pc??={stack:[],ticks:{},calls:{},zeroSub:[]}; const q=this.__pc; const active=prettyName(this.currentDeclaration).endsWith("UInt64.ofNatLT");
  if(active)q.calls[name]=(q.calls[name]??0)+1; q.stack.push(active?name:null); try{return orig.apply(this,args);}finally{q.stack.pop();}
};}
const tick0=p.tick;p.tick=function(...args){this.__pc??={stack:[],ticks:{},calls:{},zeroSub:[]};if(prettyName(this.currentDeclaration).endsWith("UInt64.ofNatLT")){const m=this.__pc.stack.at(-1)??"<root>";if(m)this.__pc.ticks[m]=(this.__pc.ticks[m]??0)+1;}return tick0.apply(this,args);};
const eqOrig=originals.get("equal")??p.equal;
// Replace wrapped equal with reject capture while preserving hotspot instrumentation.
const wrappedEqual=p.equal;p.equal=function(a,b,ctx=[]){try{return wrappedEqual.call(this,a,b,ctx);}catch(e){if(e?.status==="REJECT"&&prettyName(this.currentDeclaration).endsWith("Nat.zero_sub")){
  this.__pc??={stack:[],ticks:{},calls:{},zeroSub:[]};this.__pc.zeroSub.push({step:this.steps,reason:e.message,ctxDepth:ctx.length,aHead:head(a),bHead:head(b),a:sketch(a),b:sketch(b)});this.__pc.zeroSub=this.__pc.zeroSub.slice(-10);
}throw e;}};
const run0=p.run;p.run=function(...xs){this.__pc={stack:[],ticks:{},calls:{},zeroSub:[]};return run0.apply(this,xs);};
const result0=p.result;p.result=function(...xs){const r=result0.apply(this,xs);r.__pc=this.__pc??{ticks:{},calls:{},zeroSub:[]};return r;};

for(const [name,path] of [["init-prelude","../_build/tests/init-prelude.ndjson"],["grind-ring-5","../_build/tests/perf/grind-ring-5.ndjson"]]){
 const input=readFileSync(new URL(path,import.meta.url),"utf8");const r=K.checkExport(input,CAPS,2_000_000);const pc=r.__pc??{};
 const hot=Object.entries(pc.ticks??{}).sort((a,b)=>b[1]-a[1]).map(([method,ticks])=>({method,ticks,calls:pc.calls?.[method]??0}));
 console.log("POST_CHAR_FRONTIER_PROFILE "+JSON.stringify({name,status:r.status,reason:r.reason,steps:r.steps??null,frontier:r.frontier_declaration??null,hot,zeroSub:pc.zeroSub??[]}));
}
