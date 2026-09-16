import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,eq0=p.equal;

function S(k){return k.__whnfCongStats??={attempts:0,sameHits:0,appAttempts:0,appHits:0,appFallbacks:0,projHits:0,piHits:0,lamHits:0,fallbacks:0};}
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

  const x=this.whnf(a),y=this.whnf(b);
  if(this.same(x,y)){s.sameHits++;return;}

  if(Array.isArray(x)&&Array.isArray(y)){
    const sx=spine(x),sy=spine(y);
    if(sx.args.length>0&&sx.args.length===sy.args.length&&this.same(sx.h,sy.h)){
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
    if(x[0]==="proj"&&y[0]==="proj"&&x[1]===y[1]&&x[2]===y[2]){
      const oldF=this.conversionFrontier,oldX=this.__lastExactConversionPair;
      try{this.equal(x[3],y[3],ctx);s.projHits++;return;}
      catch(e){if(!isStop(e)||e.message==="budget-exhausted")throw e;restore(this,oldF,oldX);}
    }
    if(x[0]==="pi"&&y[0]==="pi"){
      const oldF=this.conversionFrontier,oldX=this.__lastExactConversionPair;
      try{
        this.equal(x[1],y[1],ctx);
        this.equal(x[2],y[2],[...ctx,x[1]]);
        s.piHits++;return;
      }catch(e){if(!isStop(e)||e.message==="budget-exhausted")throw e;restore(this,oldF,oldX);}
    }
    if(x[0]==="lam"&&y[0]==="lam"){
      const oldF=this.conversionFrontier,oldX=this.__lastExactConversionPair;
      try{
        this.equal(x[1],y[1],ctx);
        this.equal(x[2],y[2],[...ctx,x[1]]);
        s.lamHits++;return;
      }catch(e){if(!isStop(e)||e.message==="budget-exhausted")throw e;restore(this,oldF,oldX);}
    }
  }

  s.fallbacks++;
  return eq0.call(this,a,b,ctx);
};
