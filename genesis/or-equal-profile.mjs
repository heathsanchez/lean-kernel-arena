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

const OR=JSON.stringify(["[]","str","Or"]);
function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {h,args};}
function hd(e){const {h,args}=spine(e);return Array.isArray(h)?{tag:h[0],name:h[0]==="const"?h[1]:null,args:args.length}:{tag:typeof h,args:args.length};}
function isOr(e){const {h,args}=spine(e);return h?.[0]==="const"&&h[1]===OR&&args.length===2;}
function sk(e,d=6){
 if(!Array.isArray(e))return e;
 if(d<=0)return ["…",e[0]];
 if(e[0]==="const")return ["const",e[1],e[2]??[]];
 if(e[0]==="var")return ["v",e[1]];
 if(e[0]==="sort")return ["sort",e[1]];
 if(e[0]==="nat")return ["nat",e[1]];
 if(e[0]==="proj")return ["proj",e[1],e[2],sk(e[3],d-1)];
 return [e[0],...e.slice(1).map(x=>sk(x,d-1))];
}

const p=K.Kernel.prototype,eq0=p.equal,run0=p.run;
p.run=function(...xs){this.__orEq=[];return run0.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
 const target=typeof this.currentDeclaration==="string"&&this.currentDeclaration.includes("isValidChar_UInt32");
 const interesting=target&&(isOr(a)||isOr(b));
 if(!interesting)return eq0.call(this,a,b,ctx);
 const start=this.steps,row={step:start,ctxDepth:ctx.length,aHead:hd(a),bHead:hd(b),aBytes:JSON.stringify(a).length,bBytes:JSON.stringify(b).length,aSk:sk(a),bSk:sk(b)};
 try{
   const out=eq0.call(this,a,b,ctx);
   row.cost=this.steps-start;row.result="ok";this.__orEq.push(row);return out;
 }catch(e){
   row.cost=this.steps-start;row.result=e?.message??String(e);
   row.aPrefix=JSON.stringify(a).slice(0,4000);row.bPrefix=JSON.stringify(b).slice(0,4000);
   this.__orEq.push(row);throw e;
 }
};
const result0=p.result;
p.result=function(...xs){const r=result0.apply(this,xs);r.__orEq=(this.__orEq??[]).sort((a,b)=>b.cost-a.cost).slice(0,12);return r;};

for(const name of ["init-prelude","perf/grind-ring-5"]){
 const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
 const t0=Date.now(),r=K.checkExport(input,CAPS,2_000_000);
 console.log("OR_EQUAL_PROFILE "+JSON.stringify({name,status:r.status,reason:r.reason,steps:r.steps??null,frontier:r.frontier_declaration??null,rows:r.__orEq,elapsed_ms:Date.now()-t0}));
}
