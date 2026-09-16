import test from "node:test";
import assert from "node:assert/strict";
import {CAPABILITIES} from "./production.mjs";
import {Kernel} from "./kernel-base.mjs";

function kernel(){
  const k=new Kernel(CAPABILITIES,5_000_000);
  k.steps=0;k.allocations=0;k.env=new Map();k.params=new Set();
  return k;
}

test("retained WHNF does not recurse through the public wrapper stack",()=>{
  const k=kernel();
  let root=["var",0];
  for(let i=0;i<6000;i++) root=["proj","missing.Structure",0,root];
  const out=k.whnf(root);
  assert.equal(out,root);
  assert.notEqual(k._fullStackSafe,true);
});
