import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,eq0=p.equal;

function S(k){
  return k.__sharedHeadStats??={attempts:0,appAttempts:0,appHits:0,appFallbacks:0,projAttempts:0,projHits:0,projFallbacks:0};
}
function spine(e){
  const args=[]; let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse(); return {h,args};
}
function restore(k,frontier,exact){
  k.conversionFrontier=frontier;
  k.__lastExactConversionPair=exact;
}
function isStop(e){ return e && typeof e.status==="string"; }

p.equal=function(a,b,ctx=[]){
  const s=S(this); s.attempts++;
  if(this.same(a,b)) return;

  if(Array.isArray(a)&&Array.isArray(b)){
    const sa=spine(a),sb=spine(b);
    if(sa.args.length>0 && sa.args.length===sb.args.length && this.same(sa.h,sb.h)){
      s.appAttempts++;
      const oldFrontier=this.conversionFrontier,oldExact=this.__lastExactConversionPair;
      try{
        for(let i=0;i<sa.args.length;i++) this.equal(sa.args[i],sb.args[i],ctx);
        s.appHits++;
        return;
      }catch(e){
        if(!isStop(e)||e.message==="budget-exhausted") throw e;
        s.appFallbacks++;
        restore(this,oldFrontier,oldExact);
      }
    }

    if(a[0]==="proj"&&b[0]==="proj"&&a[1]===b[1]&&a[2]===b[2]){
      s.projAttempts++;
      const oldFrontier=this.conversionFrontier,oldExact=this.__lastExactConversionPair;
      try{
        this.equal(a[3],b[3],ctx);
        s.projHits++;
        return;
      }catch(e){
        if(!isStop(e)||e.message==="budget-exhausted") throw e;
        s.projFallbacks++;
        restore(this,oldFrontier,oldExact);
      }
    }
  }

  return eq0.call(this,a,b,ctx);
};
