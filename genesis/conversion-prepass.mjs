import {Kernel,Stop} from "./kernel-base.mjs";

// Conversion planning is purely opportunistic.  A failed probe delegates to
// the retained converter, so this layer can only avoid work on an equality it
// has independently discharged; it never creates a new inequality verdict.
const retainedEqual=Kernel.prototype.equal;
Kernel.prototype.equal=function(a,b,ctx=[]) {
  if(this.same(a,b)) return;

  if(this.caps.has("proof-irrelevance")) {
    const saved=this.conversionFrontier;
    try {
      const ta=this.proofType(a,ctx),tb=this.proofType(b,ctx);
      if(ta!==null&&tb!==null) {
        retainedEqual.call(this,ta,tb,ctx);
        this.conversionFrontier=saved;
        return;
      }
    } catch(e) {
      if(!(e instanceof Stop)) throw e;
    }
    this.conversionFrontier=saved;
  }

  // Congruence gives a cheap sufficient condition even when the shared head is
  // reducible. Failure is not evidence of inequality (the function may erase
  // its argument), so only success is retained.
  if(a?.[0]==="app"&&b?.[0]==="app"&&this.same(a[1],b[1])) {
    const saved=this.conversionFrontier;
    try {
      this.equal(a[2],b[2],ctx);
      this.conversionFrontier=saved;
      return;
    } catch(e) {
      if(!(e instanceof Stop)) throw e;
    }
    this.conversionFrontier=saved;
  }

  return retainedEqual.call(this,a,b,ctx);
};
