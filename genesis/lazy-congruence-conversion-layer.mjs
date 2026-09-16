import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,eq0=p.equal;

function stats(k){
  k.__lazyConvStats??={attempts:0,headSame:0,app:0,pi:0,lam:0,proj:0,fallbacks:0,whnfSame:0,appFallbacks:0};
  return k.__lazyConvStats;
}
function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function sameRigidHead(k,a,b){
  if(!Array.isArray(a)||!Array.isArray(b)||a[0]!==b[0])return false;
  if(a[0]==="var")return a[1]===b[1];
  if(a[0]==="const"){
    if(!k.same(a,b))return false;
    // Theorems are deliberately cold-transparent, so their applications are
    // not treated as injective neutral spines here.
    return k.env.get(a[1])?.kind!=="thm";
  }
  return false;
}

p.equal=function(a,b,ctx=[]){
  const q=stats(this);q.attempts++;
  if(this.same(a,b)){q.headSame++;return;}

  const x=this.whnf(a),y=this.whnf(b);
  if(this.same(x,y)){q.whnfSame++;return;}

  if(Array.isArray(x)&&Array.isArray(y)&&x[0]===y[0]){
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
    if(x[0]==="app"){
      const sx=spine(x),sy=spine(y);
      if(sx.args.length===sy.args.length&&sameRigidHead(this,sx.h,sy.h)){
        q.app++;
        const oldFrontier=this.conversionFrontier,oldExact=this.__lastExactConversionPair;
        try{
          for(let i=0;i<sx.args.length;i++)this.equal(sx.args[i],sy.args[i],ctx);
          return;
        }catch(e){
          if(e?.status===undefined||e?.message==="budget-exhausted")throw e;
          // Failed argument congruence is not inequality of the whole
          // application: proof irrelevance, eta or cold delta may still solve it.
          q.appFallbacks++;
          this.conversionFrontier=oldFrontier;
          this.__lastExactConversionPair=oldExact;
        }
      }
    }
  }

  q.fallbacks++;
  return eq0.call(this,a,b,ctx);
};
