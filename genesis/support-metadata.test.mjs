import test from "node:test";
import assert from "node:assert/strict";
import {CAPABILITIES} from "./production.mjs";
import {Kernel} from "./kernel-base.mjs";

function kernel() {
  const k=new Kernel(CAPABILITIES,1_000_000);
  k.steps=0;k.allocations=0;
  return k;
}

const V=n=>["var",n],S=["sort",0];

test("validated support metadata feeds exact binder transport without fallback",()=>{
  const k=kernel(),arg=["nat",7];
  let closed=S;
  for(let i=0;i<512;i++) closed=["app",closed,S];
  const root=["app",closed,V(0)];

  k.validate(root);

  assert.equal(k.__support?.get(closed),0);
  assert.equal(k.__support?.get(root),1);

  const substituted=k.substitute(root,arg);
  assert.deepEqual(substituted,["app",closed,arg]);
  assert.ok(k.__binderStats.supportHits>0);
  assert.equal(k.__binderStats.supportFallbacks,0);
});

test("support metadata never suppresses a binder-dependent substitution",()=>{
  const k=kernel(),dependent=["lam",S,["app",V(0),V(1)]];
  k.validate(dependent);
  assert.equal(k.__support?.get(dependent),1);
  assert.deepEqual(k.substitute(dependent,V(3)),["lam",S,["app",V(0),V(4)]]);
});
