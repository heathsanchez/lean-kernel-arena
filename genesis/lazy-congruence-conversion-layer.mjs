import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,eq0=p.equal;

function stats(k){
  k.__lazyConvStats??={attempts:0,headSame:0,app:0,pi:0,lam:0,proj:0,fallbacks:0,whnfSame:0};
  return k.__lazyConvStats;
}

p.equal=function(a,b,ctx=[]){
  const q=stats(this);q.attempts++;
  if(this.same(a,b)){q.headSame++;return;}

  // Conservative head-directed conversion. This proves only congruence cases;
  // anything else falls through to the retained complete/current conversion.
  const x=this.whnf(a),y=this.whnf(b);
  if(this.same(x,y)){q.whnfSame++;return;}

  if(Array.isArray(x)&&Array.isArray(y)&&x[0]===y[0]){
    if(x[0]==="app"){
      q.app++;
      this.equal(x[1],y[1],ctx);
      this.equal(x[2],y[2],ctx);
      return;
    }
    if(x[0]==="pi"){
      q.pi++;
      this.equal(x[1],y[1],ctx);
      this.equal(x[2],y[2],[...ctx,x[1]]);
      return;
    }
    if(x[0]==="lam"){
      q.lam++;
      this.equal(x[1],y[1],ctx);
      this.equal(x[2],y[2],[...ctx,x[1]]);
      return;
    }
    if(x[0]==="proj"&&x[1]===y[1]&&x[2]===y[2]){
      q.proj++;
      this.equal(x[3],y[3],ctx);
      return;
    }
  }

  q.fallbacks++;
  return eq0.call(this,x,y,ctx);
};
