import { Kernel } from "./kernel-base.mjs";

// Retained consequence: preserve exact structural sharing of constructed terms.
// The separator showed that hash-consing alone resolves church-numerals while
// preserving every protected verdict. Keys use child object identity and exact
// scalar values; no semantic equality or context is guessed.
const oldRun = Kernel.prototype.run;
const oldMake = Kernel.prototype.make;

function ensureSharing(kernel) {
  kernel._termCons ??= new Map();
  kernel._termObjectIds ??= new WeakMap();
  kernel._nextTermObjectId ??= 1;
}

Kernel.prototype.run = function(...args) {
  this._termCons = new Map();
  this._termObjectIds = new WeakMap();
  this._nextTermObjectId = 1;
  return oldRun.apply(this,args);
};

function objectId(kernel,x) {
  ensureSharing(kernel);
  let id=kernel._termObjectIds.get(x);
  if(id!==undefined) return id;
  id=kernel._nextTermObjectId++;
  kernel._termObjectIds.set(x,id);
  return id;
}

Kernel.prototype.make = function(...xs) {
  this.tick();
  ensureSharing(this);
  const key=JSON.stringify(xs.map(x=>
    Array.isArray(x)?["array",objectId(this,x)]:[typeof x,x]
  ));
  const old=this._termCons.get(key);
  if(old!==undefined) return old;
  this.allocations++;
  this._termCons.set(key,xs);
  objectId(this,xs);
  return xs;
};
