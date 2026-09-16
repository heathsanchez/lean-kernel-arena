import test from "node:test";
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {Kernel} from "./kernel-base.mjs";
import {checkExport,CAPABILITIES} from "./production.mjs";

import {leanName} from "./name-codec.mjs";
const name=leanName;
const nat=["const",name("Nat")];
const pi=(a,b)=>["pi",a,b];
const appN=(head,args)=>args.reduce((fn,arg)=>["app",fn,arg],head);

function declarations() {
  let captured;
  const run=Kernel.prototype.run;
  try {
    Kernel.prototype.run=function(...args){captured=args[2];return run.apply(this,args);};
    const input=readFileSync(new URL("./fixtures/nat-conversion.ndjson",import.meta.url),"utf8");
    assert.equal(checkExport(input).status,"ACCEPT");
  } finally { Kernel.prototype.run=run; }
  return captured;
}

test("ordinary UInt32.size follows its validated definition",()=>{
  const size=name("UInt32","size"),term=["const",size],k=new Kernel(CAPABILITIES);
  const defs=[...declarations(),{kind:"def",name:size,type:nat,value:["nat",0],levelParams:[]}];
  assert.equal(k.run(term,nat,defs).status,"ACCEPT");
  assert.deepEqual(k.whnf(term),k.whnf(["nat",0]));
});

test("axiomatic OfNat dictionaries do not invent a defining equation",()=>{
  const ofNat=name("OfNat","ofNat"),inst=name("instOfNatNat"),k=new Kernel(CAPABILITIES);
  const defs=[...declarations(),
    {kind:"axiom",name:inst,type:pi(nat,nat),levelParams:[]},
    {kind:"axiom",name:ofNat,type:pi(["sort",1],pi(nat,pi(nat,nat))),levelParams:[]}];
  const term=appN(["const",ofNat],[nat,["nat",7],appN(["const",inst],[["nat",7]])]);
  assert.equal(k.run(term,nat,defs).status,"ACCEPT");
  assert.deepEqual(k.whnf(term),term);
});
