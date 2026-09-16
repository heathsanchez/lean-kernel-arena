import {Kernel} from "./kernel-base.mjs";

// Exact constructor consequence cache layered above retained hash-consing.
// The first exact argument tuple pays the retained make() cost. Subsequent
// calls with the identical scalar values and child object identities return the
// already-returned canonical node without repaying make's semantic tick.
//
// This changes no syntax, equality, allocation, or reduction semantics.
const p=Kernel.prototype,run0=p.run,make0=p.make;

function ensure(k){
  k.__makeConsequence??=new Map();
  k.__makeIds??=new WeakMap();k.__makeNextId??=1;
  k.__makeConsequenceStats??={hits:0,stores:0};
}
function id(k,x){
  if(x!==null&&(typeof x==="object"||typeof x==="function")){
    let n=k.__makeIds.get(x);
    if(n===undefined){n=k.__makeNextId++;k.__makeIds.set(x,n);}
    return "o"+n;
  }
  return typeof x+":"+String(x);
}
function key(k,xs){
  let s="";
  for(let i=0;i<xs.length;i++)s+=(i?"|":"")+id(k,xs[i]);
  return s;
}
p.run=function(...args){
  this.__makeConsequence=new Map();this.__makeIds=new WeakMap();this.__makeNextId=1;
  this.__makeConsequenceStats={hits:0,stores:0};
  return run0.apply(this,args);
};
p.make=function(...xs){
  ensure(this);
  const q=key(this,xs),old=this.__makeConsequence.get(q);
  if(old!==undefined){this.__makeConsequenceStats.hits++;return old;}
  const out=make0.apply(this,xs);
  this.__makeConsequence.set(q,out);this.__makeConsequenceStats.stores++;
  return out;
};
