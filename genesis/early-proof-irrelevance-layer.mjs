import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,eq0=p.equal;

function S(k){
  return k.__earlyPIStats??={attempts:0,hits:0,nonProof:0,probeFallbacks:0,typeFallbacks:0};
}

p.equal=function(a,b,ctx=[]){
  if(!this.caps.has("proof-irrelevance")||this.__earlyPIProbe>0)
    return eq0.call(this,a,b,ctx);

  const s=S(this);s.attempts++;
  if(this.same(a,b))return;

  let tx=null,ty=null;
  this.__earlyPIProbe=(this.__earlyPIProbe??0)+1;
  try{
    tx=this.proofType(a,ctx);
    ty=this.proofType(b,ctx);
  }catch(e){
    if(e?.message==="budget-exhausted")throw e;
    if(e?.status===undefined)throw e;
    s.probeFallbacks++;
  }finally{
    this.__earlyPIProbe--;
  }

  if(tx!==null&&ty!==null){
    const oldFrontier=this.conversionFrontier,oldExact=this.__lastExactConversionPair;
    try{
      this.equal(tx,ty,ctx);
      s.hits++;
      return;
    }catch(e){
      if(e?.message==="budget-exhausted")throw e;
      if(e?.status===undefined)throw e;
      this.conversionFrontier=oldFrontier;
      this.__lastExactConversionPair=oldExact;
      s.typeFallbacks++;
    }
  }else s.nonProof++;

  return eq0.call(this,a,b,ctx);
};
