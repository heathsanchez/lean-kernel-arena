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

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
function prettyName(s){try{let x=JSON.parse(s),p=[];while(Array.isArray(x)&&x.length===3){p.push(String(x[2]));x=JSON.parse(x[0]);}return p.reverse().join(".");}catch{return String(s);}}
function spine(e){const xs=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){xs.push(h[2]);h=h[1];}xs.reverse();return{h,xs};}
function sketch(e,d=8){if(!Array.isArray(e))return e;if(d<=0)return ["…",e[0]];if(["nat","var","sort","strlit"].includes(e[0]))return e;if(e[0]==="const")return ["const",prettyName(e[1]),e[2]??[]];return [e[0],...e.slice(1).map(x=>sketch(x,d-1))];}
const p=K.Kernel.prototype,eq0=p.equal,run0=p.run;
p.run=function(...xs){this.__probe=null;return run0.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
  if(this.__probe===null&&prettyName(this.currentDeclaration).endsWith("Char.ofNatAux")&&Array.isArray(a)&&a[0]==="nat"&&String(a[1])==="4294967296"&&Array.isArray(b)&&b[0]==="proj"){
    const {h,xs}=spine(b[3]);
    if(h?.[0]==="const"&&prettyName(h[1])==="Nat.rec"&&xs.length===4&&xs[3]?.[0]==="nat"){
      const vals=[];
      for(let n=0;n<=5;n++){
        const rec=this.appN(h,[xs[0],xs[1],xs[2],this.make("nat",n)]);
        const pr=this.make("proj",b[1],b[2],rec);
        const s0=this.steps,b0=this.budget;
        this.budget=Math.max(this.budget,this.steps+200000);
        let out;
        try{out=this.normal(pr,ctx);}catch(e){out=["ERR",e?.status??e?.message??String(e)];}
        this.budget=b0;
        vals.push({n,steps:this.steps-s0,out:sketch(out,12)});
      }
      this.__probe={target:sketch(a),projType:prettyName(b[1]),field:b[2],motive:sketch(xs[0],10),base:sketch(xs[1],10),minor:sketch(xs[2],14),vals};
    }
  }
  return eq0.call(this,a,b,ctx);
};
const result0=p.result;p.result=function(...xs){const r=result0.apply(this,xs);r.__probe=this.__probe;return r;};
for(const name of ["init-prelude","perf/grind-ring-5"]){
 const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
 const r=K.checkExport(input,CAPS,1_000_000);
 console.log("CHAR_PROJECTED_RECURRENCE_PROBE "+JSON.stringify({name,status:r.status,reason:r.reason,steps:r.steps??null,frontier:r.frontier_declaration??null,probe:r.__probe}));
}
