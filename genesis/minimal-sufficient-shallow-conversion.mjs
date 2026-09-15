import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const BUDGET=1_000_000;
const TARGETS=["perf/shared-subterm","undecidability/alg-conv-trans-acc-left","undecidability/alg-conv-trans-acc-right","undecidability/subject-reduction-redex","undecidability/alg-conv-trans-acc","undecidability/subject-reduction-reduct"];
const p=K.Kernel.prototype, retainedEqual=p.equal, retainedWhnf=p.whnf;

const snap=k=>({steps:k.steps,budget:k.budget,frontier:k.conversionFrontier});
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
const fallbackable=e=>e instanceof K.Stop||e instanceof RangeError;
function rawSpine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function sameHead(k,a,b){return a===b||(Array.isArray(a)&&Array.isArray(b)&&k.same(a,b));}
function headClass(k,h){if(!Array.isArray(h))return typeof h;if(h[0]!=="const")return h[0];return "const:"+(k.env.get(h[1])?.kind??"unknown");}
function defHead(k,t){const h=rawSpine(t).head;return Array.isArray(h)&&h[0]==="const"&&k.env.get(h[1])?.kind==="def"?h:null;}
const ALLOWED=new Set(["var","const:def","const:inductive","const:ctor"]);

function install(){
  p.equal=retainedEqual;p.whnf=retainedWhnf;
  p.whnf=function(e){
    const out=retainedWhnf.call(this,e);
    if(out!==e||!Array.isArray(e)||e[0]!=="app"||!this.caps.has("proof-irrelevance")||this._proofMajorRepresentative)return out;
    const [rh,rargs]=this.getApp(e);if(rh?.[0]!=="const")return out;
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
    }catch(e){if(!fallbackable(e))throw e;restore(this,s);return out;}
    finally{this._proofMajorRepresentative=false;}
  };

  p.equal=function(a,b,ctx=[]){
    if(this.same(a,b))return;
    if(this.localDefs)return retainedEqual.call(this,a,b,ctx);

    let pairs=null,kind=null;
    if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&(a[0]==="pi"||a[0]==="lam")){
      kind="binder";pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];
    }else{
      const sa=rawSpine(a),sb=rawSpine(b);
      if(sa.args.length&&sa.args.length===sb.args.length&&sameHead(this,sa.head,sb.head)){
        const c=headClass(this,sa.head);
        if(ALLOWED.has(c)){kind=c;pairs=sa.args.map((x,i)=>[x,sb.args[i],ctx]);}
      }
    }
    if(pairs){
      const s=snap(this);
      try{
        for(const [x,y,c] of pairs)this.equal(x,y,c);
        this.__shallowCongruence??={};this.__shallowCongruence[kind]=(this.__shallowCongruence[kind]??0)+1;
        return;
      }catch(e){
        if(!fallbackable(e))throw e;
        restore(this,s);
      }
    }

    const ah=defHead(this,a),bh=defHead(this,b);
    if(ah&&bh&&ah[1]!==bh[1]){
      const s=snap(this);
      try{
        const x=retainedWhnf.call(this,a),y=retainedWhnf.call(this,b);
        if(x!==a||y!==b){
          this.__differingDefHits=(this.__differingDefHits??0)+1;
          this.equal(x,y,ctx);
          return;
        }
      }catch(e){
        if(!fallbackable(e))throw e;
      }
      restore(this,s);
    }
    return retainedEqual.call(this,a,b,ctx);
  };
}
function uninstall(){p.equal=retainedEqual;p.whnf=retainedWhnf;}
function run(name,candidate){
  candidate?install():uninstall();
  const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  let r;const t0=Date.now();
  try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,BUDGET);}
  finally{p.run=old;uninstall();}
  const hits={};for(const k of seen)for(const [q,n] of Object.entries(k.__shallowCongruence??{}))hits[q]=(hits[q]??0)+n;
  return {name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,hits,
    differingDefHits:seen.reduce((n,k)=>n+(k.__differingDefHits??0),0),proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0)};
}
const baseline=TARGETS.map(n=>run(n,false)),candidate=TARGETS.map(n=>run(n,true));
const cm=new Map(candidate.map(r=>[r.name,r]));
const sharedClosed=cm.get("perf/shared-subterm")?.status==="ACCEPT";
const creativeClosed=TARGETS.slice(1,4).every(n=>cm.get(n)?.status==="ACCEPT");
const forgedPreserved=TARGETS.slice(4).every(n=>cm.get(n)?.status==="REJECT");
const summary={experiment:"minimal-sufficient-shallow-conversion",budget:BUDGET,baseline,candidate,sharedClosed,creativeClosed,forgedPreserved,
  promotable_focus:sharedClosed&&creativeClosed&&forgedPreserved,
  claim_boundary:"Before retained deep normalization, compare raw binders and same-head applications only for local variables, checked definitions, inductive type formers, and constructors. Distinct checked definition heads receive transactional shallow WHNF. Opaque theorem bodies may represent only Prop recursor majors under proof irrelevance. Any failed speculative path restores semantic steps, budget, and frontier."};
const out=new URL("./evidence/minimal-sufficient-shallow-conversion.json",import.meta.url);mkdirSync(dirname(out.pathname),{recursive:true});writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("MINIMAL_SUFFICIENT_SHALLOW_CONVERSION "+JSON.stringify(summary));if(!summary.promotable_focus)process.exit(1);
