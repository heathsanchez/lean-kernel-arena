import {Kernel} from "./kernel-base.mjs";

// Ablation only.  early-proof-irrelevance.mjs bypasses its eager proofType probe
// whenever __earlyPIProbe > 0.  Keep the flag positive for the whole run; the
// retained base converter still performs ordinary proof irrelevance after WHNF/
// normalization, so this removes an optimization policy, not proof semantics.
const p=Kernel.prototype,run0=p.run;
p.run=function(...xs){
  this.__earlyPIProbe=1;
  try{return run0.apply(this,xs);}
  finally{this.__earlyPIProbe=0;}
};
