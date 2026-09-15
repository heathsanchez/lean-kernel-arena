import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT"],["perf/folded-constant-first","ACCEPT"],["perf/repeated-subproblem","ACCEPT"],
 ["perf/args-before-unfold","ACCEPT"],["perf/discarded-argument-match","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"],["undecidability/subject-reduction-reduct","REJECT"]
];

const p=K.Kernel.prototype, oldRun=p.run, oldSub=p.substitute, oldWhnf=p.whnf;
const END=Symbol("end");

function ensure(k){
  k.__substCanonWeak??=new WeakMap();
  k.__substCanonRoot??=new Map();
  k.__structSubstCache??=new WeakMap();
}
function rep(k,e){
  if(!Array.isArray(e)) return e;
  ensure(k);
  const hit=k.__substCanonWeak.get(e); if(hit!==undefined)return hit;
  const xs=new Array(e.length);let changed=false;
  for(let i=0;i<e.length;i++){const y=Array.isArray(e[i])?rep(k,e[i]):e[i];xs[i]=y;if(y!==e[i])changed=true;}
  let node=k.__substCanonRoot;
  for(const x of xs){let n=node.get(x);if(!(n instanceof Map)){n=new Map();node.set(x,n);}node=n;}
  let out=node.get(END);
  if(out===undefined){out=changed?xs:e;node.set(END,out);k.__canonNodes=(k.__canonNodes??0)+1;}
  k.__substCanonWeak.set(e,out);k.__substCanonWeak.set(out,out);return out;
}
function cacheMap(k,r,a){
  ensure(k);let byR=k.__structSubstCache.get(r);
  if(!byR){byR=new WeakMap();k.__structSubstCache.set(r,byR);}
  let byD=byR.get(a);if(!byD){byD=new Map();byR.set(a,byD);}return byD;
}
p.run=function(...xs){
  this.__substCanonWeak=new WeakMap();this.__substCanonRoot=new Map();this.__structSubstCache=new WeakMap();
  return oldRun.apply(this,xs);
};
p.substitute=function(root,arg,depth=0){
  if(!Array.isArray(root)||!Array.isArray(arg))return oldSub.call(this,root,arg,depth);
  const rr=rep(this,root),aa=rep(this,arg),m=cacheMap(this,rr,aa);
  this.__structQueries=(this.__structQueries??0)+1;
  if(m.has(depth)){this.__structHits=(this.__structHits??0)+1;return m.get(depth);}
  const out=oldSub.call(this,root,arg,depth);m.set(depth,out);this.__structStores=(this.__structStores??0)+1;return out;
};

function spine(e){const xs=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){xs.push(h[2]);h=h[1];}xs.reverse();return {h,xs};}
function substMany(k,e,args,depth=0,memo=new WeakMap()){
  let byD=memo.get(e);if(!byD){byD=new Map();memo.set(e,byD);}
  if(byD.has(depth)){k.__batchMemoHits=(k.__batchMemoHits??0)+1;return byD.get(depth);}
  k.tick();let out;
  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":out=e;break;
    case "var":{const i=e[1];if(i<depth)out=e;else{const j=i-depth;out=j<args.length?k.shift(args[args.length-1-j],depth):k.make("var",i-args.length);}break;}
    case "pi":case "lam":out=k.make(e[0],substMany(k,e[1],args,depth,memo),substMany(k,e[2],args,depth+1,memo));break;
    case "app":out=k.make("app",substMany(k,e[1],args,depth,memo),substMany(k,e[2],args,depth,memo));break;
    case "proj":out=k.make("proj",e[1],e[2],substMany(k,e[3],args,depth,memo));break;
    case "let":out=k.make("let",substMany(k,e[1],args,depth,memo),substMany(k,e[2],args,depth,memo),substMany(k,e[3],args,depth+1,memo));break;
    default:k.unknown("batch-struct-subst-syntax");
  }
  byD.set(depth,out);return out;
}
p.whnf=function(e){
 if(Array.isArray(e)&&e[0]==="app"){
  const {h:rh,xs:rargs}=spine(e);
  if(Array.isArray(rh)&&rh[0]==="const"){
   const rd=this.env?.get(rh[1]);
   if(rd?.kind==="rec"){
    const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
    if(rargs.length>=total){
     const major=this.whnf(rargs[total-1]),{h:mh,xs:margs}=spine(major);
     const md=Array.isArray(mh)&&mh[0]==="const"?this.env.get(mh[1]):null;
     if(md?.kind==="ctor"&&md.induct===rd.induct&&margs.length===md.numParams+md.numFields){
      let ok=true;for(let i=0;i<rd.numParams;i++)if(!this.same(margs[i],rargs[i])){ok=false;break;}
      if(ok){
       const rule=rd.rules.find(rr=>rr.ctor===md.name);
       if(rule){
        this.need("inductive-reduction");this.need("reduction");
        let rhs=this.instantiateDeclaration(rh,rule.rhs);
        const apply=rargs.slice(0,rd.numParams+1+rd.numMinors).concat(margs.slice(md.numParams));
        let cur=rhs,n=0;while(n<apply.length&&Array.isArray(cur)&&cur[0]==="lam"){cur=cur[2];n++;}
        if(n>=2){
         for(let i=0;i<n;i++)this.tick();
         let out=substMany(this,cur,apply.slice(0,n));
         for(let i=n;i<apply.length;i++)out=this.make("app",out,apply[i]);
         for(const extra of rargs.slice(total))out=this.make("app",out,extra);
         this.__recBatchHits=(this.__recBatchHits??0)+1;
         return this.whnf(out);
        }
       }
      }
     }
    }
   }
  }
 }
 return oldWhnf.call(this,e);
};

const rows=[];
for(const [name,want] of TARGETS){
 const seen=[],r0=p.run;p.run=function(...xs){seen.push(this);return r0.apply(this,xs);};
 const t0=Date.now();let r;try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}finally{p.run=r0;}
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
  structuralQueries:seen.reduce((n,k)=>n+(k.__structQueries??0),0),structuralHits:seen.reduce((n,k)=>n+(k.__structHits??0),0),
  canonNodes:seen.reduce((n,k)=>n+(k.__canonNodes??0),0),recBatchHits:seen.reduce((n,k)=>n+(k.__recBatchHits??0),0),
  batchMemoHits:seen.reduce((n,k)=>n+(k.__batchMemoHits??0),0)};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
p.run=oldRun;p.substitute=oldSub;p.whnf=oldWhnf;
const protectedClean=rows.slice(1).every(r=>r.status===r.want);
const sharedClosed=rows[0]?.status==="ACCEPT";
const out={experiment:"structural-substitution-plus-recursor-batch",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/structural-substitution-plus-recursor-batch.json",JSON.stringify(out,null,2)+"\n");
console.log("STRUCTURAL_SUBSTITUTION_PLUS_RECURSOR_BATCH "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
