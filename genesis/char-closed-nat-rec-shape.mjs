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
import "./compiled-nat-isvalidchar-consequence-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
const NATREC=N("Nat","rec");
function rawSpine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return{h,args};}
function sk(e,d=5){
 if(!Array.isArray(e))return e;if(d<=0)return ["…",e[0]];
 if(["nat","var","sort","strlit"].includes(e[0]))return e;
 if(e[0]==="const")return ["const",e[1],e[2]??[]];
 if(e[0]==="proj")return ["proj",e[1],e[2],sk(e[3],d-1)];
 return [e[0],...e.slice(1).map(x=>sk(x,d-1))];
}
const p=K.Kernel.prototype,whnf0=p.whnf,run0=p.run;
p.run=function(...xs){this.__closedNatRecShapes=[];return run0.apply(this,xs);};
p.whnf=function(e){
 if(Array.isArray(e)&&e[0]==="app"){
  const {h,args}=rawSpine(e);
  if(h?.[0]==="const"&&h[1]===NATREC&&args.length>=4){
   const major=args[args.length-1];
   if(Array.isArray(major)&&major[0]==="nat"&&String(major[1])==="4294967296"&&this.__closedNatRecShapes.length<8){
    const rd=this.env?.get(NATREC);
    this.__closedNatRecShapes.push({step:this.steps,argsLen:args.length,major:sk(major),
      motive:sk(args[0],7),base:sk(args[1],7),minor:sk(args[2],9),extra:args.slice(3,-1).map(x=>sk(x,5)),
      recMeta:rd?{kind:rd.kind,numParams:rd.numParams,numIndices:rd.numIndices,numMinors:rd.numMinors,induct:rd.induct,rules:rd.rules?.map(r=>({ctor:r.ctor,rhs:sk(r.rhs,6)}))}:null});
   }
  }
 }
 return whnf0.call(this,e);
};
const result0=p.result;
p.result=function(...xs){const r=result0.apply(this,xs);r.__closedNatRecShapes=this.__closedNatRecShapes??[];return r;};
for(const name of ["init-prelude","perf/grind-ring-5"]){
 const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
 const r=K.checkExport(input,CAPS,1_000_000);
 console.log("CHAR_CLOSED_NAT_REC_SHAPE "+JSON.stringify({name,status:r.status,reason:r.reason,steps:r.steps??null,
  frontier:r.frontier_declaration??null,shapes:r.__closedNatRecShapes}));
}
