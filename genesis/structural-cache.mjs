import { Kernel } from "./kernel-base.mjs";

// Exact memoization for the two pure de-Bruijn tree transforms that dominate
// the retained execution residual. Keys are expression/argument object identity
// plus the complete numeric parameters, so no local-context information is
// omitted. Only completed transform results are retained; exceptions are never
// cached. Caches are reset for every Kernel.run.
const oldRun = Kernel.prototype.run;
const oldShift = Kernel.prototype.shift;
const oldSubstitute = Kernel.prototype.substitute;

Kernel.prototype.run = function(...args) {
  this._shiftCache = new WeakMap();
  this._substCache = new WeakMap();
  return oldRun.apply(this,args);
};

Kernel.prototype.shift = function(e,amount,cut=0) {
  let byAmount=this._shiftCache?.get(e);
  if(!byAmount) {
    byAmount=new Map();
    this._shiftCache?.set(e,byAmount);
  }
  const key=`${amount}:${cut}`;
  if(byAmount.has(key)) { this.tick(); return byAmount.get(key); }
  const out=oldShift.call(this,e,amount,cut);
  byAmount.set(key,out);
  return out;
};

Kernel.prototype.substitute = function(e,arg,depth=0) {
  let byExpr=this._substCache?.get(e);
  if(!byExpr) {
    byExpr=new WeakMap();
    this._substCache?.set(e,byExpr);
  }
  let byDepth=byExpr.get(arg);
  if(!byDepth) {
    byDepth=new Map();
    byExpr.set(arg,byDepth);
  }
  if(byDepth.has(depth)) { this.tick(); return byDepth.get(depth); }
  const out=oldSubstitute.call(this,e,arg,depth);
  byDepth.set(depth,out);
  return out;
};
