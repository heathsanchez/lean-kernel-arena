import { Kernel } from "./kernel-base.mjs";

// Retained consequence from the semantic-reuse separator: normalization is a
// deterministic successful consequence of an exact expression under one
// monotonic kernel run. Cache successes only; failures/frontiers are never
// retained. Weak identity keys preserve the exact term, not an approximation.
const oldRun = Kernel.prototype.run;
const oldNormal = Kernel.prototype.normal;

Kernel.prototype.run = function(...args) {
  this._normalCache = new WeakMap();
  return oldRun.apply(this,args);
};

Kernel.prototype.normal = function(e) {
  this._normalCache ??= new WeakMap();
  if(Array.isArray(e) && this._normalCache.has(e)) {
    this.tick();
    return this._normalCache.get(e);
  }
  const out=oldNormal.call(this,e);
  if(Array.isArray(e)) this._normalCache.set(e,out);
  return out;
};
