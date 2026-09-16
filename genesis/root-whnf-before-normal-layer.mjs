import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,eq0=p.equal;

function S(k){return k.__rootWhnfEqStats??={attempts:0,hits:0,changedLeft:0,changedRight:0,fallbacks:0};}

p.equal=function(a,b,ctx=[]){
  const s=S(this);s.attempts++;
  if(this.same(a,b))return;
  const wa=this.whnf(a),wb=this.whnf(b);
  if(wa!==a)s.changedLeft++;
  if(wb!==b)s.changedRight++;
  if(this.same(wa,wb)){s.hits++;return;}
  s.fallbacks++;
  return eq0.call(this,a,b,ctx);
};
