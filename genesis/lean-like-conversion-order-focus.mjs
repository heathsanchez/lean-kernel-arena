// Focused Lean-like conversion-order separator.
//
// Goal: retain the focused creative-conversion win without the broad
// pre-normal wrapper that made the full replay too expensive.
//
// Candidate:
//   1. Before deep normalization, decompose only exact same-head raw
//      applications (flattened spine) and raw Pi/lambda binders.
//   2. Preserve the previously separated proof-major representative rule:
//      a checked theorem body may represent an opaque proof only as the major
//      premise of a recursor over Prop, with proof irrelevance enabled.
//
// Failed pre-normal probes are transactional and delegate to the retained
// converter. No transitive closure or invented middle term is added.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import * as K from "./kernel.mjs";

const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const BUDGET=1_000_000;
const ACCEPT_TARGETS=new Set([
  "undecidability/alg-conv-trans-acc-left",
  "undecidability/alg-conv-trans-acc-right",
  "undecidability/subject-reduction-redex"
]);
const BOUNDARY_TARGETS=new Set([
  "undecidability/alg-conv-trans-acc",
  "undecidability/subject-reduction-reduct"
]);
const TARGETS=[...ACCEPT_TARGETS,...BOUNDARY_TARGETS];

const p=K.Kernel.prototype;
const retainedEqual=p.equal,retainedWhnf=p.whnf;

function snap(k){return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
function fallbackable(e){return e instanceof K.Stop || e instanceof RangeError;}
function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {head:h,args};
}
function sameHead(k,a,b){
  return a===b || (Array.isArray(a)&&Array.isArray(b)&&k.same(a,b));
}

function installCandidate(){
  p.equal=retainedEqual;p.whnf=retainedWhnf;

  // Proof-major representative: semantic scope is deliberately tiny.
  p.whnf=function(e){
    const out=retainedWhnf.call(this,e);
    if(out!==e || !Array.isArray(e) || e[0]!=="app" ||
       !this.caps.has("proof-irrelevance") || this._proofMajorRepresentative)
      return out;

    const [rh,rargs]=this.getApp(e);
    if(rh?.[0]!=="const") return out;
    const rd=this.env.get(rh[1]);
    if(rd?.kind!=="rec") return out;
    const ind=this.env.get(rd.induct);
    if(ind?.kind!=="inductive" || ind.isProp!==true) return out;
    const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
    if(rargs.length<total) return out;

    const major=rargs[total-1];
    const [mh,margs]=this.getApp(major);
    if(mh?.[0]!=="const") return out;
    const md=this.env.get(mh[1]);
    if(md?.kind!=="thm" || !Array.isArray(md.value)) return out;

    const s=snap(this);
    this._proofMajorRepresentative=true;
    try{
      let rep=this.instantiateDeclaration(mh,md.value);
      rep=this.appN(rep,margs);
      rep=retainedWhnf.call(this,rep);
      if(this.same(rep,major)){restore(this,s);return out;}
      const args=rargs.slice();args[total-1]=rep;
      const rebuilt=this.appN(rh,args);
      const reduced=retainedWhnf.call(this,rebuilt);
      if(reduced!==rebuilt){
        this.__proofMajorHits=(this.__proofMajorHits??0)+1;
        return reduced;
      }
      restore(this,s);return out;
    }catch(err){
      if(!fallbackable(err)) throw err;
      restore(this,s);return out;
    }finally{
      this._proofMajorRepresentative=false;
    }
  };

  p.equal=function(a,b,ctx=[]){
    if(this.same(a,b)) return;

    // Avoid changing the specialized local-definition fallback. The creative
    // witnesses are decided in the retained kernel, and this keeps the new
    // schedule orthogonal to that subsystem.
    if(this.localDefs) return retainedEqual.call(this,a,b,ctx);

    let kind=null,pairs=null;
    if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&
       (a[0]==="pi"||a[0]==="lam")){
      kind=a[0];
      pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];
    }else{
      const sa=rawSpine(a),sb=rawSpine(b);
      if(sa.args.length>0&&sa.args.length===sb.args.length&&sameHead(this,sa.head,sb.head)){
        kind="same-head-app";
        pairs=sa.args.map((x,i)=>[x,sb.args[i],ctx]);
      }
    }
    if(!pairs) return retainedEqual.call(this,a,b,ctx);

    const s=snap(this);
    try{
      for(const [x,y,c] of pairs) this.equal(x,y,c);
      this.__leanOrderHits=(this.__leanOrderHits??0)+1;
      if(kind==="same-head-app") this.__leanOrderAppHits=(this.__leanOrderAppHits??0)+1;
      else this.__leanOrderBinderHits=(this.__leanOrderBinderHits??0)+1;
      return;
    }catch(err){
      if(!fallbackable(err)) throw err;
      restore(this,s);
      return retainedEqual.call(this,a,b,ctx);
    }
  };
}
function uninstall(){p.equal=retainedEqual;p.whnf=retainedWhnf;}

function inputFor(name){
  return readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
}
function evaluate(label,candidate){
  candidate?installCandidate():uninstall();
  const rows=[];
  for(const name of TARGETS){
    const seen=[],oldRun=p.run;
    p.run=function(...args){seen.push(this);return oldRun.apply(this,args);};
    let r;
    try{r=K.checkExport(inputFor(name),CAPS,BUDGET);}
    finally{p.run=oldRun;}
    rows.push({name,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,
      leanOrderHits:seen.reduce((n,k)=>n+(k.__leanOrderHits??0),0),
      appHits:seen.reduce((n,k)=>n+(k.__leanOrderAppHits??0),0),
      binderHits:seen.reduce((n,k)=>n+(k.__leanOrderBinderHits??0),0),
      proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0)});
  }
  return {label,rows};
}

const baseline=evaluate("baseline",false);
const candidate=evaluate("candidate",true);
uninstall();

const bmap=new Map(baseline.rows.map(r=>[r.name,r]));
const cmap=new Map(candidate.rows.map(r=>[r.name,r]));
const acceptClosed=[...ACCEPT_TARGETS].every(n=>cmap.get(n)?.status==="ACCEPT");
const boundaryPreserved=[...BOUNDARY_TARGETS].every(n=>
  cmap.get(n)?.status===bmap.get(n)?.status
);
const summary={
  experiment:"lean-like-narrow-conversion-order-focus",
  budget:BUDGET,baseline:baseline.rows,candidate:candidate.rows,
  acceptClosed,boundaryPreserved,
  promotable_focus:acceptClosed&&boundaryPreserved,
  claim_boundary:"Only raw Pi/lambda congruence and exact same-head flattened application congruence are attempted before retained deep normalization. Separately, an already-checked theorem body may represent an opaque proof only as a Prop recursor major under proof irrelevance. Failed probes restore steps, budget, and frontier. The forged trans/reduct boundary must preserve its baseline status."
};
const out=new URL("./evidence/lean-like-conversion-order-focus.json",import.meta.url);
mkdirSync(dirname(out.pathname),{recursive:true});
writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("LEAN_LIKE_CONVERSION_ORDER_FOCUS "+JSON.stringify(summary));
if(!summary.promotable_focus) process.exit(1);
