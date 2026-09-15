import { Kernel } from "./kernel-base.mjs";

// Exact successful declaration-instantiation consequence reuse.
//
// Within one kernel run the declaration environment is immutable after each
// declaration is installed. For the identical declaration term and identical
// constant-reference object, a completed instantiation is therefore the same
// pure result. Cache only successful completions; failures are never retained.
//
// This is execution compilation only. It introduces no new typing, reduction,
// conversion, universe, equality, or rejection rule.
const retainedRun = Kernel.prototype.run;
const retainedInstantiateDeclaration = Kernel.prototype.instantiateDeclaration;

Kernel.prototype.run = function(...args) {
  this.__instDeclCache = new WeakMap();
  return retainedRun.apply(this,args);
};

Kernel.prototype.instantiateDeclaration = function(ref,term) {
  this.__instDeclCache ??= new WeakMap();

  if(Array.isArray(term) && Array.isArray(ref)) {
    let byRef = this.__instDeclCache.get(term);
    if(!byRef) {
      byRef = new WeakMap();
      this.__instDeclCache.set(term,byRef);
    }
    if(byRef.has(ref)) return byRef.get(ref);

    const out = retainedInstantiateDeclaration.call(this,ref,term);
    byRef.set(ref,out);
    return out;
  }

  return retainedInstantiateDeclaration.call(this,ref,term);
};
