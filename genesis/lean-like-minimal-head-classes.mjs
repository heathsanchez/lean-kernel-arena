import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const BUDGET=1_000_000;
const TARGETS=["undecidability/alg-conv-trans-acc-left","undecidability/alg-conv-trans-acc-right","undecidability/subject-reduction-redex","undecidability/alg-conv-trans-acc","undecidability/subject-reduction-reduct"];
const MODES={
  var:new Set(["var"]),
  "def+var":new Set(["const:def","var"]),
  "inductive+var":new Set(["const:inductive","var"]),
  "def+inductive+var":new Set(["const:def","const:inductive","var"]),
  "const+var":new Set(["const:def","const:inductive","const:rec","const:ctor","const:axiom","const:opaque","const:thm","const:quot","const:unknown","var"]),
};
const p=K.Kernel.prototype, retainedEqual=p.equal, retainedWhnf=p.whnf;
const snap=k=>({steps:k.steps,budget:k.budget,frontier:k.conversionFrontier});
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
const fallbackable=e=>e instanceof K.Stop||e instanceof RangeError;
function rawSpine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function cls(k,h){if(!Array.isArray(h))return typeof h;if(h[0]!=="const")return h[0];return "const:"+(k.env.get(h[1])?.kind??"unknown");}
function install(allowed){
  p.equal=retainedEqual;p.whnf=retainedWhnf;
  p.whnf=function(e){
    const out=retainedWhnf.call(this,e);
    if(out!==e||!Array.isArray(e)||e[0]!=="app"||!this.caps.has("proof-irrelevance")||this._proofMajorRepresentative)return out;
    const [rh,rargs]=this.getApp(e); if(rh?.[0]!=="const")return out;
    const rd=this.env.get(rh[1]),ind=rd?.kind==="rec"?this.env.get(rd.induct):null;
    if(rd?.kind!=="rec"||ind?.kind!=="inductive"||ind.isProp!==true)return out;
    const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;if(rargs.length<total)return out;
    const major=rargs[total-1],[mh,margs]=this.getApp(major);if(mh?.[0]!=="const")return out;
    const md=this.env.get(mh[1]);if(md?.kind!=="thm"||!Array.isArray(md.value))return out;
    const s=snap(this);this._proofMajorRepresentative=true;
    try{
      let rep=this.appN(this.instantiateDeclaration(mh,md.value),margs);rep=retainedWhnf.call(this,rep);
      if(this.same(rep,major)){restore(this,s);return out;}
      const xs=rargs.slice();xs[total-1]=rep;const rebuilt=this.appN(rh,xs),reduced=retainedWhnf.call(this,rebuilt);
      if(reduced!==rebuilt){this.__proofMajorHits=(this.__proofMajorHits??0)+1;return reduced;}
      restore(this,s);return out;
    }catch(e){if(!fallbackable(e))throw e;restore(this,s);return out;}finally{this._proofMajorRepresentative=false;}
  };
  p.equal=function(a,b,ctx=[]){
    if(this.same(a,b))return;if(this.localDefs)return retainedEqual.call(this,a,b,ctx);
    let pairs=null,kind="binder";
    if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&(a[0]==="pi"||a[0]==="lam"))
      pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];
    else{
      const sa=rawSpine(a),sb=rawSpine(b);
      if(sa.args.length&&sa.args.length===sb.args.length&&(sa.head===sb.head||this.same(sa.head,sb.head))){
        kind=cls(this,sa.head);if(allowed.has(kind))pairs=sa.args.map((x,i)=>[x,sb.args[i],ctx]);
      }
    }
    if(!pairs)return retainedEqual.call(this,a,b,ctx);
    const s=snap(this);
    try{for(const [x,y,c] of pairs)this.equal(x,y,c);this.__hits??={};this.__hits[kind]=(this.__hits[kind]??0)+1;return;}
    catch(e){if(!fallbackable(e))throw e;restore(this,s);return retainedEqual.call(this,a,b,ctx);}
  };
}
function run(mode,allowed){
  install(allowed);const rows=[];
  for(const name of TARGETS){
    const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
    let r;try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,BUDGET);}finally{p.run=old;}
    const hits={};for(const k of seen)for(const [q,n] of Object.entries(k.__hits??{}))hits[q]=(hits[q]??0)+n;
    rows.push({name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,hits,proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0)});
  }
  p.equal=retainedEqual;p.whnf=retainedWhnf;return {mode,rows};
}
const results=Object.entries(MODES).map(([m,a])=>run(m,a));
const viable=results.filter(x=>x.rows.slice(0,3).every(r=>r.status==="ACCEPT")&&x.rows.slice(3).every(r=>r.status==="REJECT")).map(x=>x.mode);
const summary={experiment:"lean-like-minimal-head-class-profile",viable,results};
const out=new URL("./evidence/lean-like-minimal-head-class-profile.json",import.meta.url);mkdirSync(dirname(out.pathname),{recursive:true});writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("LEAN_LIKE_MINIMAL_HEAD_CLASSES "+JSON.stringify(summary));if(!viable.length)process.exit(1);
