import {readFileSync} from "node:fs";
import * as K from "../genesis/kernel.mjs";

const [dumpPath]=process.argv.slice(2);
if(!dumpPath) throw new Error("usage: node con-leche-model-residual-v2.mjs DUMP");
const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const dump=readFileSync(dumpPath,"utf8");

function stripComplex(text){
  const out=[];
  for(const line of text.split(/\r?\n/)){
    if(!line.trim()) continue;
    const r=JSON.parse(line);
    if(r.inductive){
      const ts=r.inductive.types??[];
      if(ts.length>1||ts.some(t=>(t?.numNested??0)>0)) continue;
    }
    out.push(line);
  }
  return out.join("\n")+"\n";
}

const events=[];
const orig=K.Kernel.prototype.addSingleInductive;
K.Kernel.prototype.addSingleInductive=function(d){
  try {
    return orig.call(this,d);
  } catch(e) {
    if(e instanceof K.Stop && e.message==="inductive-recursion-metadata"){
      const fields=[];
      let derivedRec=false,derivedReflexive=false;
      for(const c of d.ctors??[]){
        let ct=c.type,indT=d.type,cctx=[];
        for(let i=0;i<d.numParams;i++){
          indT=this.whnf(indT);
          if(indT?.[0]!=="pi"||ct?.[0]!=="pi") break;
          cctx.push(indT[1]); indT=indT[2]; ct=ct[2];
        }
        let ordinal=0;
        while(ct?.[0]==="pi"){
          const raw=ct[1],w=this.whnf(raw);
          const hasRaw=this.hasConst(raw,d.name),hasWhnf=this.hasConst(w,d.name);
          let reflexive=false,spDomains=0,resHead=null;
          if(hasWhnf){
            derivedRec=true;
            const sp=this.splitAllForalls(w);
            spDomains=sp.domains.length;
            reflexive=sp.domains.length>0;
            if(reflexive) derivedReflexive=true;
            const [h]=this.getApp(sp.rest); resHead=h?.[0]==="const"?h[1]:h?.[0]??null;
          }
          fields.push({ctor:c.name,ordinal,rawTag:raw?.[0]??null,whnfTag:w?.[0]??null,
            hasRaw,hasWhnf,reflexive,spDomains,resHead});
          cctx.push(raw); ordinal++; ct=ct[2];
        }
      }
      events.push({name:d.name,metadataIsRec:d.isRec,derivedRec,metadataIsReflexive:d.isReflexive,
        derivedReflexive,numParams:d.numParams,numIndices:d.numIndices,numNested:d.numNested,
        ctorCount:d.ctors?.length??null,fields});
    }
    throw e;
  }
};

const stripped=stripComplex(dump);
const r=K.checkExport(stripped,caps,2_000_000);
console.log("CON_LECHE_MODEL_RESIDUAL_V2 "+JSON.stringify({
  status:r.status,reason:r.reason,frontier_declaration:r.frontier_declaration??null,
  captures:events
}));
