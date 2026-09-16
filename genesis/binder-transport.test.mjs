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

test("production binder transport handles a 20000-deep open spine",()=>{
  const k=kernel(),arg=["nat",7];
  let term=V(0);
  for(let i=0;i<20000;i++) term=["app",term,V(1)];
  let shifted=k.shift(term,2),substituted=k.substitute(term,arg);
  for(let i=0;i<20000;i++) {
    assert.deepEqual(shifted[2],V(3));
    assert.deepEqual(substituted[2],V(0));
    shifted=shifted[1];substituted=substituted[1];
  }
  assert.deepEqual(shifted,V(2));assert.equal(substituted,arg);
});

test("binder cutoffs and substitution arguments remain distinct cache keys",()=>{
  const k=kernel(),term=["lam",S,["app",V(0),V(1)]];
  assert.deepEqual(k.shift(term,2),["lam",S,["app",V(0),V(3)]]);
  assert.equal(k.shift(term,2,1),term);
  assert.deepEqual(k.substitute(term,V(3)),["lam",S,["app",V(0),V(4)]]);
  assert.deepEqual(k.substitute(term,V(5)),["lam",S,["app",V(0),V(6)]]);
  assert.equal(k.substitute(term,V(3),1),term);
});

test("closed deep terms retain identity and completed transforms are reused",()=>{
  const k=kernel();let closed=S;
  for(let i=0;i<20000;i++) closed=["lam",S,closed];
  assert.equal(k.shift(closed,1),closed);
  assert.equal(k.substitute(closed,V(0)),closed);
  const open=["let",S,V(0),["app",V(0),V(1)]],arg=["nat",9];
  const first=k.substitute(open,arg),steps=k.steps;
  assert.deepEqual(first,["let",S,arg,["app",V(0),arg]]);
  assert.equal(k.substitute(open,arg),first);assert.equal(k.steps,steps);
});
