import {Kernel,Stop} from "./kernel-base.mjs";

// Exact directed form of the already-verified Nat zero/offset consequence.
// If one side is syntactically primitive zero/Nat.zero, only weak-head reduce
// the other side.  Equality is discharged iff that retained reduction reaches
// zero.  Failed speculation rolls back completely.  This avoids recursively
// normalizing giant structure that cannot affect the zero head decision.
const p=Kernel.prototype,equal0=p.equal,run0=p.run;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
const ZERO=N("Nat","zero");
function zero(e){
  if(!Array.isArray(e))return false;
  if(e[0]==="nat"){
    try{return BigInt(e[1])===0n;}catch{return false;}
  }
  return e[0]==="const"&&e[1]===ZERO&&(e[2]??[]).length===0;
}

p.run=function(...xs){this.__whnfNatZeroHits=0;return run0.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
  const za=zero(a),zb=zero(b);
  if(!za&&!zb)return equal0.call(this,a,b,ctx);
  if(za&&zb){this.__whnfNatZeroHits=(this.__whnfNatZeroHits??0)+1;return;}
  const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
  try{
    const other=za?b:a,w=this.whnf(other);
    if(zero(w)){
      this.__whnfNatZeroHits=(this.__whnfNatZeroHits??0)+1;
      return;
    }
  }catch(e){
    if(!(e instanceof Stop||e instanceof RangeError))throw e;
  }
  this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
  return equal0.call(this,a,b,ctx);
};
