import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const BUDGET=1_000_000, APP_CAP=16_000;
const TARGETS=[
 ["perf/church-numerals","ACCEPT"],["perf/discarded-argument-match","ACCEPT"],["perf/discarded-argument","ACCEPT"],
 ["perf/app-lam","ACCEPT"],["perf/repeated-subproblem","ACCEPT"],["perf/beta-ladder","ACCEPT"],
 ["perf/folded-constant-first","ACCEPT"],["perf/irrelevance-before-evaluation","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT"],["undecidability/alg-conv-trans-acc-right","ACCEPT"],
 ["undecidability/subject-reduction-redex","ACCEPT"],["undecidability/alg-conv-trans-acc","REJECT"],
 ["undecidability/subject-reduction-reduct","REJECT"]
];

const p=K.Kernel.prototype, retainedEqual=p.equal, retainedWhnf=p.whnf;
const snap=k=>({steps:k.steps,budget:k.budget,frontier:k.conversionFrontier});
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
const fallbackable=e=>e instanceof K.Stop||e instanceof RangeError;
function rawSpine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function headClass(k,h){if(!Array.isArray(h))return typeof h;if(h[0]!=="const")return h[0];return "const:"+(k.env.get(h[1])?.kind??"unknown");}

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
 }catch(e){if(!fallbackable(e))throw e;restore(this,s);return out;}finally{this._proofMajorRepresentative=false;}
};

p.equal=function(a,b,ctx=[]){
 if(this.same(a,b))return;
 if(this.localDefs)return retainedEqual.call(this,a,b,ctx);

 // Lean-like structural schedule: if both raw heads are already binders,
 // congruence is not speculation. Equality of the binders requires equality
 // of their domains and bodies; do not deep-normalize the whole binder first.
 if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&(a[0]==="pi"||a[0]==="lam")){
   this.__nativeBinderHits=(this.__nativeBinderHits??0)+1;
   this.equal(a[1],b[1],ctx);
   this.equal(a[2],b[2],[...ctx,a[1]]);
   return;
 }

 // Same-head local variables / checked definitions are only a sufficient
 // shortcut. Failure can still be rescued by retained unfolding/irrelevance,
 // so keep only this part transactional and tightly budgeted.
 const sa=rawSpine(a),sb=rawSpine(b);
 if(sa.args.length&&sa.args.length===sb.args.length&&(sa.head===sb.head||this.same(sa.head,sb.head))){
   const kind=headClass(this,sa.head);
   if(kind==="var"||kind==="const:def"){
     const s=snap(this);this.budget=Math.min(s.budget,s.steps+APP_CAP);
     try{
       for(let i=0;i<sa.args.length;i++)this.equal(sa.args[i],sb.args[i],ctx);
       this.budget=s.budget;
       this.__appProbeSuccess=(this.__appProbeSuccess??0)+1;
       this.__appProbeMaxSuccess=Math.max(this.__appProbeMaxSuccess??0,this.steps-s.steps);
       return;
     }catch(e){
       this.budget=s.budget;
       if(!fallbackable(e))throw e;
       this.__appProbeFailure=(this.__appProbeFailure??0)+1;
       this.__appProbeMaxFailure=Math.max(this.__appProbeMaxFailure??0,this.steps-s.steps);
       restore(this,s);
     }
   }
 }
 return retainedEqual.call(this,a,b,ctx);
};

const rows=[];
for(const [name,want] of TARGETS){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;
 try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,BUDGET);}
 finally{p.run=old;}
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
   binderHits:seen.reduce((n,k)=>n+(k.__nativeBinderHits??0),0),
   appProbeSuccess:seen.reduce((n,k)=>n+(k.__appProbeSuccess??0),0),
   appProbeFailure:seen.reduce((n,k)=>n+(k.__appProbeFailure??0),0),
   maxAppSuccess:Math.max(0,...seen.map(k=>k.__appProbeMaxSuccess??0)),
   maxAppFailure:Math.max(0,...seen.map(k=>k.__appProbeMaxFailure??0)),
   proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0)};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
p.equal=retainedEqual;p.whnf=retainedWhnf;
const clean=rows.every(r=>r.status===r.want);
const creativeClean=rows.slice(8).every(r=>r.status===r.want);
const perfClean=rows.slice(0,8).every(r=>r.status===r.want);
const out={experiment:"native-binder-capped-app-conversion",appCap:APP_CAP,clean,creativeClean,perfClean,rows};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/native-binder-capped-app-conversion.json",JSON.stringify(out,null,2)+"\n");
console.log("NATIVE_BINDER_CAPPED_APP_CONVERSION "+JSON.stringify(out));
if(!clean)process.exit(1);
