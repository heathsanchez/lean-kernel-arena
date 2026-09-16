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
function sketch(e,d=16){if(!Array.isArray(e))return e;if(d<=0)return["…",e[0]];if(["nat","var","sort","strlit"].includes(e[0]))return e;if(e[0]==="const")return["const",prettyName(e[1]),e[2]??[]];if(e[0]==="proj")return["proj",prettyName(e[1]),e[2],sketch(e[3],d-1)];return[e[0],...e.slice(1).map(x=>sketch(x,d-1))];}
const p=K.Kernel.prototype,eq0=p.equal,run0=p.run;
p.run=function(...xs){this.__zeroSub=[];return run0.apply(this,xs);};
p.equal=function(a,b,ctx=[]){try{return eq0.call(this,a,b,ctx);}catch(e){if(e?.status==="REJECT"&&prettyName(this.currentDeclaration).endsWith("Nat.zero_sub")){
 this.__zeroSub.push({step:this.steps,reason:e.message,ctxDepth:ctx.length,aHead:head(a),bHead:head(b),a:sketch(a),b:sketch(b)});this.__zeroSub=this.__zeroSub.slice(-12);
}throw e;}};
const result0=p.result;p.result=function(...xs){const r=result0.apply(this,xs);r.__zeroSub=this.__zeroSub??[];return r;};
const input=readFileSync(new URL("../_build/tests/perf/grind-ring-5.ndjson",import.meta.url),"utf8");
const r=K.checkExport(input,CAPS,2_000_000);
console.log("NAT_ZERO_SUB_REJECT_PROFILE "+JSON.stringify({status:r.status,reason:r.reason,steps:r.steps??null,frontier:r.frontier_declaration??null,rows:r.__zeroSub}));
