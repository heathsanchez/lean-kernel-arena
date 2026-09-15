import { Kernel, Stop } from "./kernel-base.mjs";

// Retained ordering consequence: proof irrelevance before proof evaluation.
//
// This layer does not add a new equality rule. It only reorders the existing
// proof-irrelevance rule while an already-verified rigid/lazy congruence
// transaction is active. Both raw terms must independently infer to
// proposition-valued types, and those proposition types must themselves be
// definitionally equal. A failed probe restores semantic steps/frontier before
// delegating to the retained converter.

const fallbackEqual = Kernel.prototype.equal;

Kernel.prototype.equal = function(a,b,ctx=[]) {
  if(this.localDefs || !this.caps.has("proof-irrelevance") ||
     ((this._lazyDeltaDepth??0)===0 && (this._rigidTypeSpineDepth??0)===0))
    return fallbackEqual.call(this,a,b,ctx);

  if(this.same(a,b)) return;

  const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
  try {
    const ta=this.proofType(a,ctx),tb=this.proofType(b,ctx);
    if(ta!==null && tb!==null) {
      if(this.same(ta,tb)) return;
      fallbackEqual.call(this,ta,tb,ctx);
      return;
    }
  } catch(e) {
    if(!(e instanceof Stop || e instanceof RangeError)) throw e;
  }

  this.steps=snap.steps;
  this.budget=snap.budget;
  this.conversionFrontier=snap.frontier;
  return fallbackEqual.call(this,a,b,ctx);
};
