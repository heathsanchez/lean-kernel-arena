import {Kernel} from "./kernel-base.mjs";

// Execution-only host-stack repair.
//
// The retained fast WHNF evaluator is still the ordinary path. Its internal
// recursive calls re-enter the public `this.whnf`, traverse every later
// optimization wrapper, and eventually enter the retained evaluator again.
// Deep neutral/projection/recursor spines therefore grow the JavaScript host
// stack even though an exact iterative WHNF evaluator already exists.
//
// `_fullStackSafe` historically selects both iterative WHNF *and* continuation
// inference. Reusing it naively for WHNF re-entry changed local-definition
// inference mid-check (the fueled-chain counterexample). The inference wrapper
// below masks that switch only while it originated from this WHNF trampoline,
// preserving the exact pre-existing inference route. WHNF calls from inside
// inference still hit the trampoline again and remain stack-safe.
const p=Kernel.prototype,retainedWhnf=p.whnf,retainedInfer=p.infer;

p.infer=function(term,ctx){
  if(this.__whnfReentryStackSafe===true && this._fullStackSafe===true){
    const previous=this._fullStackSafe;
    this._fullStackSafe=false;
    try {
      return retainedInfer.call(this,term,ctx);
    } finally {
      this._fullStackSafe=previous;
    }
  }
  return retainedInfer.call(this,term,ctx);
};

p.whnf=function(term){
  if((this.__retainedWhnfDepth??0)>0){
    const previousFull=this._fullStackSafe;
    const previousOrigin=this.__whnfReentryStackSafe;
    this._fullStackSafe=true;
    this.__whnfReentryStackSafe=true;
    try {
      return retainedWhnf.call(this,term);
    } finally {
      this._fullStackSafe=previousFull;
      this.__whnfReentryStackSafe=previousOrigin;
    }
  }

  this.__retainedWhnfDepth=(this.__retainedWhnfDepth??0)+1;
  try {
    return retainedWhnf.call(this,term);
  } finally {
    this.__retainedWhnfDepth--;
  }
};
