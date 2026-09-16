import {Kernel,Stop} from "./kernel-base.mjs";

// Exact positive congruence recovery for projections.
//
// The retained converter is always tried first. Only if it returns the
// unresolved conversion frontier do we normalize both sides and inspect the
// result. If both are the identical projection operator (same structure name
// and field index), definitional equality of their structure arguments implies
// equality of the projections. The structure arguments are compared by the
// complete retained converter, so proof irrelevance and all other already
// qualified conversion rules remain authoritative.
//
// Failed speculation restores semantic steps, budget and diagnostic frontier.
const p=Kernel.prototype;
const retainedEqual=p.equal;

p.equal=function(a,b,ctx=[]){
  if((this.__projectionRecoveryDepth??0)>16)
    return retainedEqual.call(this,a,b,ctx);

  try{
    return retainedEqual.call(this,a,b,ctx);
  }catch(original){
    if(!(original instanceof Stop)||
       original.status!=="UNKNOWN"||
       original.message!=="conversion-frontier")
      throw original;

    const snap={
      steps:this.steps,
      budget:this.budget,
      frontier:this.conversionFrontier
    };

    let x,y;
    // The retained converter reaches conversion-frontier only after it has
    // already normalized both operands exactly. Reuse that completed work
    // instead of normalizing the same giant terms a second time.
    const witnessed=this.__lastExactConversionPair;
    if(witnessed && witnessed.ctxDepth===ctx.length &&
       Array.isArray(witnessed.left) && Array.isArray(witnessed.right)) {
      x=witnessed.left;
      y=witnessed.right;
      this.__projectionRecoveryWitnessHits=(this.__projectionRecoveryWitnessHits??0)+1;
    } else {
      try{
        x=this.normal(a);
        y=this.normal(b);
      }catch(_){
        this.steps=snap.steps;
        this.budget=snap.budget;
        this.conversionFrontier=snap.frontier;
        throw original;
      }
    }

    if(!Array.isArray(x)||!Array.isArray(y)||
       x[0]!=="proj"||y[0]!=="proj"||
       x[1]!==y[1]||x[2]!==y[2]){
      this.steps=snap.steps;
      this.budget=snap.budget;
      this.conversionFrontier=snap.frontier;
      throw original;
    }

    this.__projectionRecoveryAttempts=(this.__projectionRecoveryAttempts??0)+1;
    this.__projectionRecoveryDepth=(this.__projectionRecoveryDepth??0)+1;
    try{
      this.equal(x[3],y[3],ctx);
      this.__projectionRecoverySuccesses=(this.__projectionRecoverySuccesses??0)+1;
      this.__projectionRecoveryDepth--;
      return;
    }catch(e){
      this.__projectionRecoveryDepth--;
      if(!(e instanceof Stop||e instanceof RangeError)) throw e;
      this.steps=snap.steps;
      this.budget=snap.budget;
      this.conversionFrontier=snap.frontier;
      throw original;
    }
  }
};
