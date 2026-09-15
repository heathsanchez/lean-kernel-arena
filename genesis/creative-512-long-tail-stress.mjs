import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/church-numerals","ACCEPT"],["perf/app-lam","ACCEPT"],["perf/beta-ladder","ACCEPT"],
 ["perf/repeated-subproblem","ACCEPT"],["perf/folded-constant-first","ACCEPT"],
 ["perf/irrelevance-before-evaluation","ACCEPT"],["perf/discarded-argument","ACCEPT"],
 ["perf/discarded-argument-match","ACCEPT"],["perf/args-before-unfold","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT"],["undecidability/alg-conv-trans-acc-right","ACCEPT"],
 ["undecidability/subject-reduction-redex","ACCEPT"],["undecidability/alg-conv-trans-acc","REJECT"],
 ["undecidability/subject-reduction-reduct","REJECT"]
];
const PI_CAP=512,DEF_CAP=6500,VAR_CAP=15500,BUDGET=1_000_000;
const p=K.Kernel.prototype,baseEqual=p.equal,baseWhnf=p.whnf;
const snap=k=>({steps:k.steps,budget:k.budget,frontier:k.conversionFrontier});
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
const fb=e=>e instanceof K.Stop||e instanceof RangeError;
function spine(e){const xs=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){xs.push(h[2]);h=h[1];}xs.reverse();return {h,xs};}
function cls(k,h){if(!Array.isArray(h))return typeof h;if(h[0]!=="const")return h[0];return "const:"+(k.env.get(h[1])?.kind??"unknown");}

p.whnf=function(e){
 const out=baseWhnf.call(this,e);
 if(out!==e||!Array.isArray(e)||e[0]!=="app"||!this.caps.has("proof-irrelevance")||this._proofMajorRepresentative)return out;
 const [rh,args]=this.getApp(e);if(rh?.[0]!=="const")return out;
 const rd=this.env.get(rh[1]),ind=rd?.kind==="rec"?this.env.get(rd.induct):null;
 if(rd?.kind!=="rec"||ind?.kind!=="inductive"||ind.isProp!==true)return out;
 const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;if(args.length<total)return out;
 const major=args[total-1],[mh,margs]=this.getApp(major);if(mh?.[0]!=="const")return out;
 const md=this.env.get(mh[1]);if(md?.kind!=="thm"||!Array.isArray(md.value))return out;
 const s=snap(this);this._proofMajorRepresentative=true;
 try{
   let rep=this.appN(this.instantiateDeclaration(mh,md.value),margs);rep=baseWhnf.call(this,rep);
   if(this.same(rep,major)){restore(this,s);return out;}
   const ys=args.slice();ys[total-1]=rep;const rebuilt=this.appN(rh,ys),r=baseWhnf.call(this,rebuilt);
   if(r!==rebuilt){this.__proofMajorHits=(this.__proofMajorHits??0)+1;return r;}
   restore(this,s);return out;
 }catch(e){if(!fb(e))throw e;restore(this,s);return out;}
 finally{this._proofMajorRepresentative=false;}
};

p.equal=function(a,b,ctx=[]){
 if(this.same(a,b))return;if(this.localDefs)return baseEqual.call(this,a,b,ctx);
 let pairs=null,cap=0,kind=null;
 if(Array.isArray(a)&&Array.isArray(b)&&a[0]==="pi"&&b[0]==="pi"){
   kind="pi";cap=PI_CAP;pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];
 }else{
   const sa=spine(a),sb=spine(b);
   if(sa.xs.length&&sa.xs.length===sb.xs.length&&(sa.h===sb.h||this.same(sa.h,sb.h))){
     const k=cls(this,sa.h);
     if(k==="const:def"){kind=k;cap=DEF_CAP;pairs=sa.xs.map((x,i)=>[x,sb.xs[i],ctx]);}
     else if(k==="var"){kind=k;cap=VAR_CAP;pairs=sa.xs.map((x,i)=>[x,sb.xs[i],ctx]);}
   }
 }
 if(!pairs)return baseEqual.call(this,a,b,ctx);
 const s=snap(this);this.budget=Math.min(s.budget,s.steps+cap);
 try{
   for(const [x,y,c] of pairs)this.equal(x,y,c);
   this.budget=s.budget;this.__creativeHits??={};this.__creativeHits[kind]=(this.__creativeHits[kind]??0)+1;return;
 }catch(e){
   this.budget=s.budget;if(!fb(e))throw e;
   this.__creativeFails??={};this.__creativeFails[kind]=(this.__creativeFails[kind]??0)+1;
   restore(this,s);return baseEqual.call(this,a,b,ctx);
 }
};

const rows=[];
for(const [name,want] of TARGETS){
 console.log("ROW_START "+JSON.stringify({name,want}));
 const seen=[],oldRun=p.run;p.run=function(...xs){seen.push(this);return oldRun.apply(this,xs);};
 const t0=Date.now();let r;
 try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,BUDGET);}
 finally{p.run=oldRun;}
 const merge=field=>{const o={};for(const k of seen)for(const [q,n] of Object.entries(k[field]??{}))o[q]=(o[q]??0)+n;return o;};
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
   hits:merge("__creativeHits"),fails:merge("__creativeFails"),proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0)};
 rows.push(row);console.log("ROW_DONE "+JSON.stringify(row));
}
p.equal=baseEqual;p.whnf=baseWhnf;
const clean=rows.every(r=>r.status===r.want);
const out={experiment:"creative-512-long-tail-stress",caps:{pi:PI_CAP,def:DEF_CAP,var:VAR_CAP},clean,rows};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/creative-512-long-tail-stress.json",JSON.stringify(out,null,2)+"\n");
console.log("CREATIVE_512_LONG_TAIL_STRESS "+JSON.stringify(out));
if(!clean)process.exit(1);
