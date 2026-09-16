import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,eq0=p.equal;

function S(k){return k.__exposedHeadStats??={attempts:0,headChanges:0,sameHits:0,appAttempts:0,appHits:0,appFallbacks:0,fallbacks:0};}
function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function isStop(e){return e&&typeof e.status==="string";}
function restore(k,f,x){k.conversionFrontier=f;k.__lastExactConversionPair=x;}

p.equal=function(a,b,ctx=[]){
  const s=S(this);s.attempts++;
  if(this.same(a,b))return;

  const ra=spine(a),rb=spine(b);
  // Existing converter already handles an identical raw head. This layer is
  // only for the important case where reduction exposes a common head.
  if(this.same(ra.h,rb.h))return eq0.call(this,a,b,ctx);

  const x=this.whnf(a),y=this.whnf(b);
  const sx=spine(x),sy=spine(y);
  if(!this.same(sx.h,sy.h)){
    s.fallbacks++;
    return eq0.call(this,a,b,ctx);
  }
  s.headChanges++;
  if(this.same(x,y)){s.sameHits++;return;}

  if(sx.args.length>0&&sx.args.length===sy.args.length){
    s.appAttempts++;
    const oldF=this.conversionFrontier,oldX=this.__lastExactConversionPair;
    try{
      for(let i=0;i<sx.args.length;i++)this.equal(sx.args[i],sy.args[i],ctx);
      s.appHits++;return;
    }catch(e){
      if(!isStop(e)||e.message==="budget-exhausted")throw e;
      s.appFallbacks++;restore(this,oldF,oldX);
    }
  }

  s.fallbacks++;
  return eq0.call(this,a,b,ctx);
};
