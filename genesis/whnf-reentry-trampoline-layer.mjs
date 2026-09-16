import {Kernel} from "./kernel-base.mjs";

// Execution-only host-stack repair.
//
// The retained fast WHNF evaluator is still the ordinary path. Its internal
// recursive calls re-enter the public `this.whnf`, traversing every later
// optimization wrapper and eventually the retained evaluator again. On deep
// neutral/projection/recursor spines that grows the JavaScript host stack.
//
// While one retained WHNF call is already active, route only that recursive
// re-entry through the existing fully iterative stack-safe evaluator. Later
// wrappers still run before this layer gets control, so their exact native/
// semantic consequences retain first refusal. No semantic rule is added.
const p=Kernel.prototype,retainedWhnf=p.whnf;

p.whnf=function(term){
  if((this.__retainedWhnfDepth??0)>0){
    const previous=this._fullStackSafe;
    this._fullStackSafe=true;
    try {
      return retainedWhnf.call(this,term);
    } finally {
      this._fullStackSafe=previous;
    }
  }

  this.__retainedWhnfDepth=(this.__retainedWhnfDepth??0)+1;
  try {
    return retainedWhnf.call(this,term);
  } finally {
    this.__retainedWhnfDepth--;
  }
};
