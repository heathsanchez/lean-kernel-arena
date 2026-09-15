import { Kernel } from "./kernel-base.mjs";

// Exact application-spine consequence reuse, restricted to LocalDef execution.
// getApp is a pure decomposition of an immutable term. Cache only completed
// results by exact term identity; ordinary retained execution is unchanged.
const retainedRun=Kernel.prototype.run;
const retainedGetApp=Kernel.prototype.getApp;

Kernel.prototype.run=function(...args){
  this.__localDefGetApp=new WeakMap();
  return retainedRun.apply(this,args);
};

Kernel.prototype.getApp=function(e){
  if(this.localDefs!==true || !Array.isArray(e))
    return retainedGetApp.call(this,e);

  this.__localDefGetApp??=new WeakMap();
  if(this.__localDefGetApp.has(e))
    return this.__localDefGetApp.get(e);

  const out=retainedGetApp.call(this,e);
  this.__localDefGetApp.set(e,out);
  return out;
};
