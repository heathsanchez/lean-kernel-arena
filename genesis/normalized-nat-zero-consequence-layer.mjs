import {Kernel,Stop} from "./kernel-base.mjs";

// Minimal composition consequence.
// The verified Nat offset layer already knows that primitive Nat literal 0 and
// Nat.zero are definitionally equal, but that rule sees operands before the
// retained normalizer.  Giant terms can reveal the pair only after ordinary
// beta/iota/projection reduction.  On an otherwise-rigid rejection, reuse the
// retained normalizer and license exactly the zero/zero case—no subtraction,
// theorem-name, or broader arithmetic rule is introduced.
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

p.run=function(...xs){this.__normalizedNatZeroHits=0;return run0.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
  try{return equal0.call(this,a,b,ctx);}catch(original){
    if(!(original instanceof Stop)||original.status!=="REJECT"||original.message!=="rigid-head-mismatch")throw original;
    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    try{
      const x=this.normal(a),y=this.normal(b);
      if(zero(x)&&zero(y)){
        this.__normalizedNatZeroHits=(this.__normalizedNatZeroHits??0)+1;
        return;
      }
    }catch(_){/* diagnostic recovery must not replace the retained outcome */}
    this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    throw original;
  }
};
