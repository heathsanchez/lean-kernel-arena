import test from "node:test";
import assert from "node:assert/strict";
import {CAPABILITIES} from "./production.mjs";
import {Kernel} from "./kernel-base.mjs";

function kernel(){
  const k=new Kernel(CAPABILITIES,5_000_000);
  k.steps=0;k.allocations=0;k.env=new Map();k.params=new Set();
  return k;
}

test("retained WHNF reentry is stack-safe without leaving full-stack mode enabled",()=>{
  const k=kernel();
  let root=["var",0];
  for(let i=0;i<6000;i++) root=["proj","missing.Structure",0,root];
  const out=k.whnf(root);

  let cur=out;
  for(let i=0;i<6000;i++){
    assert.equal(cur[0],"proj");
    assert.equal(cur[1],"missing.Structure");
    assert.equal(cur[2],0);
    cur=cur[3];
  }
  assert.deepEqual(cur,["var",0]);
  assert.notEqual(k._fullStackSafe,true);
  assert.notEqual(k.__whnfReentryStackSafe,true);
});
