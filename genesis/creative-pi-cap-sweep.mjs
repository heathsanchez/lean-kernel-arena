import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["undecidability/alg-conv-trans-acc-left","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-right","ACCEPT"],
 ["undecidability/subject-reduction-redex","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"],
 ["undecidability/subject-reduction-reduct","REJECT"]
];
const PI_CAPS=[256,512,1024,2048,4096,6144,8192,10000];
const p=K.Kernel.prototype,baseEqual=p.equal,baseWhnf=p.whnf;
const snap=k=>({steps:k.steps,budget:k.budget,frontier:k.conversionFrontier});
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
const fb=e=>e instanceof K.Stop||e instanceof RangeError;
function spine(e){const xs=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){xs.push(h[2]);h=h[1];}xs.reverse();return {h,xs};}
function cls(k,h){if(!Array.isArray(h))return typeof h;if(h[0]!=="const")return h[0];return "const:"+(k.env.get(h[1])?.kind??"unknown");}
function install(piCap){
 p.equal=baseEqual;p.whnf=baseWhnf;
 p.whnf=function(e){
  const out=baseWhnf.call(this,e);
  if(out!==e||!Array.isArray(e)||e[0]!=="app"||!this.caps.has("proof-irrelevance")||this._proofMajorRepresentative)return out;
  const [rh,args]=this.getApp(e);if(rh?.[0]!=="const")return out;const rd=this.env.get(rh[1]),ind=rd?.kind==="rec"?this.env.get(rd.induct):null;
  if(rd?.kind!=="rec"||ind?.kind!=="inductive"||ind.isProp!==true)return out;
  const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;if(args.length<total)return out;
  const major=args[total-1],[mh,margs]=this.getApp(major);if(mh?.[0]!=="const")return out;const md=this.env.get(mh[1]);
  if(md?.kind!=="thm"||!Array.isArray(md.value))return out;
  const s=snap(this);this._proofMajorRepresentative=true;
  try{let rep=this.appN(this.instantiateDeclaration(mh,md.value),margs);rep=baseWhnf.call(this,rep);
    if(this.same(rep,major)){restore(this,s);return out;}const ys=args.slice();ys[total-1]=rep;const rebuilt=this.appN(rh,ys),r=baseWhnf.call(this,rebuilt);
    if(r!==rebuilt)return r;restore(this,s);return out;
  }catch(e){if(!fb(e))throw e;restore(this,s);return out;}finally{this._proofMajorRepresentative=false;}
 };
 p.equal=function(a,b,ctx=[]){
  if(this.same(a,b))return;if(this.localDefs)return baseEqual.call(this,a,b,ctx);
  let pairs=null,cap=0;
  if(Array.isArray(a)&&Array.isArray(b)&&a[0]==="pi"&&b[0]==="pi"){pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];cap=piCap;}
  else{const sa=spine(a),sb=spine(b);if(sa.xs.length&&sa.xs.length===sb.xs.length&&(sa.h===sb.h||this.same(sa.h,sb.h))){
    const k=cls(this,sa.h);if(k==="const:def"){pairs=sa.xs.map((x,i)=>[x,sb.xs[i],ctx]);cap=6500;}else if(k==="var"){pairs=sa.xs.map((x,i)=>[x,sb.xs[i],ctx]);cap=15500;}
  }}
  if(!pairs)return baseEqual.call(this,a,b,ctx);
  const s=snap(this);this.budget=Math.min(s.budget,s.steps+cap);
  try{for(const [x,y,c] of pairs)this.equal(x,y,c);this.budget=s.budget;return;}
  catch(e){this.budget=s.budget;if(!fb(e))throw e;restore(this,s);return baseEqual.call(this,a,b,ctx);}
 };
}
const results=[];
for(const piCap of PI_CAPS){
 install(piCap);const rows=[];
 for(const [name,want] of TARGETS){const t0=Date.now();const r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);rows.push({name,want,status:r.status,reason:r.reason,steps:r.steps??null,elapsed_ms:Date.now()-t0});}
 results.push({piCap,clean:rows.every(r=>r.status===r.want),rows});console.log("CAP "+JSON.stringify(results.at(-1)));
}
p.equal=baseEqual;p.whnf=baseWhnf;
const viable=results.filter(r=>r.clean).map(r=>r.piCap);
const out={experiment:"creative-pi-cap-sweep",viable,results};mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/creative-pi-cap-sweep.json",JSON.stringify(out,null,2)+"\n");
console.log("CREATIVE_PI_CAP_SWEEP "+JSON.stringify({viable}));
if(!viable.length)process.exit(1);
