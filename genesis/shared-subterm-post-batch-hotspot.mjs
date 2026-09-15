import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[["perf/shared-subterm","ACCEPT"]];
const p=K.Kernel.prototype, retainedWhnf=p.whnf;

function spine(e){const xs=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){xs.push(h[2]);h=h[1];}xs.reverse();return {h,xs};}
function substituteMany(k,e,args,depth=0){
 k.tick();
 switch(e[0]){
  case "sort":case "const":case "nat":case "strlit": return e;
  case "var":{
   const i=e[1]; if(i<depth)return e; const j=i-depth;
   if(j<args.length)return k.shift(args[args.length-1-j],depth);
   return k.make("var",i-args.length);
  }
  case "pi":case "lam": return k.make(e[0],substituteMany(k,e[1],args,depth),substituteMany(k,e[2],args,depth+1));
  case "app": return k.make("app",substituteMany(k,e[1],args,depth),substituteMany(k,e[2],args,depth));
  case "proj": return k.make("proj",e[1],e[2],substituteMany(k,e[3],args,depth));
  case "let": return k.make("let",substituteMany(k,e[1],args,depth),substituteMany(k,e[2],args,depth),substituteMany(k,e[3],args,depth+1));
  default: k.unknown("recursor-batch-substitution-syntax");
 }
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
        let cur=rhs,n=0;
        while(n<apply.length&&Array.isArray(cur)&&cur[0]==="lam"){cur=cur[2];n++;}
        if(n>=2){
         for(let i=0;i<n;i++)this.tick();
         let out=substituteMany(this,cur,apply.slice(0,n));
         for(let i=n;i<apply.length;i++)out=this.make("app",out,apply[i]);
         for(const extra of rargs.slice(total))out=this.make("app",out,extra);
         this.__recBatchHits=(this.__recBatchHits??0)+1;
         this.__recBatchBinders=(this.__recBatchBinders??0)+n;
         return this.whnf(out);
        }
       }
      }
     }
    }
   }
  }
 }
 return retainedWhnf.call(this,e);
};

const methods=["shift","substitute","whnf","same","normal","equal","instantiateDeclaration","infer","getApp","make"];
const profOld=new Map();
for(const name of methods){const orig=p[name];if(typeof orig!=="function")continue;profOld.set(name,orig);p[name]=function(...args){this.__prof??={stack:[],ticks:{},calls:{}};const q=this.__prof;q.calls[name]=(q.calls[name]??0)+1;q.stack.push(name);try{return orig.apply(this,args);}finally{q.stack.pop();}};}
const tick0=p.tick,run0=p.run,allKernels=[];
p.tick=function(...args){this.__prof??={stack:[],ticks:{},calls:{}};const top=this.__prof.stack.at(-1)??"<none>";this.__prof.ticks[top]=(this.__prof.ticks[top]??0)+1;return tick0.apply(this,args);};
p.run=function(...args){allKernels.push(this);return run0.apply(this,args);};
const rows=[];
for(const [name,want] of TARGETS){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}finally{p.run=old;}
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
  recBatchHits:seen.reduce((n,k)=>n+(k.__recBatchHits??0),0),recBatchBinders:seen.reduce((n,k)=>n+(k.__recBatchBinders??0),0)};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
p.whnf=retainedWhnf;
const clean=rows.every(r=>r.status===r.want);
const q=allKernels[0]?.__prof??{ticks:{},calls:{}};
const top=Object.keys(q.ticks).map(op=>({op,ticks:q.ticks[op],calls:q.calls[op]??0,avg:q.ticks[op]/Math.max(1,q.calls[op]??1)})).sort((a,b)=>b.ticks-a.ticks);
const out={experiment:"shared-subterm-post-batch-hotspot",clean,rows,top};mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/shared-subterm-post-batch-hotspot.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_SUBTERM_POST_BATCH_HOTSPOT "+JSON.stringify(out));if(!clean)process.exit(1);
