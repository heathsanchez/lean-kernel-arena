import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,eq0=p.equal;

function q(k){return k.__lazyPiStats??={attempts:0,hits:0,whnfSame:0,fallbacks:0,failedSpeculations:0};}

p.equal=function(a,b,ctx=[]){
  const s=q(this);s.attempts++;
  if(this.same(a,b))return;
  const x=this.whnf(a),y=this.whnf(b);
  if(this.same(x,y)){s.whnfSame++;return;}

  if(Array.isArray(x)&&Array.isArray(y)&&x[0]==="pi"&&y[0]==="pi"){
    const oldFrontier=this.conversionFrontier,oldExact=this.__lastExactConversionPair;
    try{
      // A Pi is a type former, so head congruence is unconditional. Normalize
      // only the domain that becomes the local context entry; do not normalize
      // the entire codomain tree before descending.
      const dx=this.normal(x[1]),dy=this.normal(y[1]);
      this.equal(dx,dy,ctx);
      this.equal(x[2],y[2],[...ctx,dx]);
      s.hits++;
      return;
    }catch(e){
      if(e?.status===undefined||e?.message==="budget-exhausted")throw e;
      s.failedSpeculations++;
      this.conversionFrontier=oldFrontier;
      this.__lastExactConversionPair=oldExact;
    }
  }

  s.fallbacks++;
  return eq0.call(this,a,b,ctx);
};
