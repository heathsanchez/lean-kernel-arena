// Focused decomposition of the creative-conversion obstruction.
//
// Candidate A: pre-normal structural congruence on app/pi/lam.
// Candidate B: for recursors over Prop only, if the major premise is headed by
// an already-checked theorem declaration, use that theorem's checked body as a
// reducible proof representative. This does NOT make opaque/theorem data
// globally transparent; it is restricted to proof majors and requires the
// existing proof-irrelevance capability.
// Candidate C: A+B.
//
// All speculative equality attempts are transactional.
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
const TARGETS=[
  "undecidability/alg-conv-trans-acc-left",
  "undecidability/alg-conv-trans-acc-right",
  "undecidability/subject-reduction-redex"
];

const p=K.Kernel.prototype;
const retainedEqual=p.equal,retainedWhnf=p.whnf;

function snap(k){return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
function fallbackable(e){return e instanceof K.Stop || e instanceof RangeError;}

function install({prenormal=false,proofMajor=false}){
  p.equal=retainedEqual;p.whnf=retainedWhnf;

  if(proofMajor){
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
        // md.value was independently checked against md.type before the theorem
        // entered env. In a Prop major, proof irrelevance makes it a lawful
        // representative of the opaque theorem proof.
        let rep=this.instantiateDeclaration(mh,md.value);
        rep=this.appN(rep,margs);
        rep=retainedWhnf.call(this,rep);
        if(this.same(rep,major)){
          restore(this,s);return out;
        }
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
  }

  if(prenormal){
    p.equal=function(a,b,ctx=[]){
      if(this.same(a,b)) return;
      if(this._preNormalCongruenceProbe) return retainedEqual.call(this,a,b,ctx);
      if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&
         (a[0]==="app"||a[0]==="pi"||a[0]==="lam")){
        const s=snap(this);
        this._preNormalCongruenceProbe=(this._preNormalCongruenceProbe??0)+1;
        try{
          if(a[0]==="app"){
            // Recursive candidate calls must go through this wrapper, so clear
            // the one-frame marker around each child.
            this._preNormalCongruenceProbe--;
            this.equal(a[1],b[1],ctx);
            this.equal(a[2],b[2],ctx);
            this._preNormalCongruenceProbe++;
          }else{
            this._preNormalCongruenceProbe--;
            this.equal(a[1],b[1],ctx);
            this.equal(a[2],b[2],[...ctx,a[1]]);
            this._preNormalCongruenceProbe++;
          }
          this.__preNormalHits=(this.__preNormalHits??0)+1;
          this._preNormalCongruenceProbe--;
          return;
        }catch(err){
          this._preNormalCongruenceProbe=Math.max(0,(this._preNormalCongruenceProbe??1)-1);
          if(!fallbackable(err)) throw err;
          restore(this,s);
          return retainedEqual.call(this,a,b,ctx);
        }
      }
      return retainedEqual.call(this,a,b,ctx);
    };
  }
}

function inputFor(name){
  return readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
}
function evaluate(label,opts){
  install(opts);
  const rows=[];
  for(const name of TARGETS){
    const input=inputFor(name);
    const seen=[];
    const oldRun=p.run;
    p.run=function(...args){seen.push(this);return oldRun.apply(this,args);};
    const r=K.checkExport(input,CAPS,BUDGET);
    p.run=oldRun;
    rows.push({name,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,
      preNormalHits:seen.reduce((n,k)=>n+(k.__preNormalHits??0),0),
      proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0)});
  }
  return {label,opts,rows};
}

const lanes=[
  evaluate("baseline",{prenormal:false,proofMajor:false}),
  evaluate("prenormal-structural",{prenormal:true,proofMajor:false}),
  evaluate("proof-major-representative",{prenormal:false,proofMajor:true}),
  evaluate("combined",{prenormal:true,proofMajor:true})
];
install({prenormal:false,proofMajor:false});

const summary={
  diagnostic:"creative-conversion-minimal-mechanism-separator",
  budget:BUDGET,lanes,
  leftSolvedBy:lanes.filter(x=>x.rows[0].status==="ACCEPT").map(x=>x.label),
  rightPreservedBy:lanes.filter(x=>x.rows[1].status==="ACCEPT").map(x=>x.label),
  redexSolvedBy:lanes.filter(x=>x.rows[2].status==="ACCEPT").map(x=>x.label),
  claim_boundary:"A is ordinary congruence before deep normalization. B exposes a previously checked theorem body only when it is the major premise of a recursor over a Prop inductive and proof irrelevance is enabled. Neither rule invents a middle term or globally unfolds opaque/theorem declarations."
};
const out=new URL("./evidence/creative-conversion-minimal-mechanism.json",import.meta.url);
mkdirSync(dirname(out.pathname),{recursive:true});
writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("CREATIVE_MINIMAL_MECHANISM "+JSON.stringify(summary));
