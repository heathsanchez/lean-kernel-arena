import assert from "node:assert/strict";
import test from "node:test";

import {Kernel} from "./kernel-base.mjs";
import "./compiled-nat-pow-layer.mjs";

const name=(...parts)=>parts.reduce((prefix,part)=>JSON.stringify([prefix,"str",part]),"[]");
const NAT=name("Nat"), HPOW=name("HPow","hPow"), INST_HPOW=name("instHPow"),
  INST_POW_NAT=name("instPowNat"), INST_NAT_POW_NAT=name("instNatPowNat");

function kernel() {
  const k=new Kernel(["application","declarations","nat-literals","reduction"]);
  k.steps=0;
  k.allocations=0;
  k.env=new Map([[HPOW,{kind:"axiom",name:HPOW}]]);
  return k;
}

function natPow(k,base,exponent,instance=undefined) {
  const nat=k.make("const",NAT);
  const powInstance=instance??k.appN(k.make("const",INST_HPOW),[
    nat,
    nat,
    k.appN(k.make("const",INST_POW_NAT),[nat,k.make("const",INST_NAT_POW_NAT)]),
  ]);
  return k.appN(k.make("const",HPOW),[
    nat,nat,nat,powInstance,k.make("nat",base),k.make("nat",exponent),
  ]);
}

test("Nat power shortcut returns only completed exact powers",()=>{
  const exactCases=[
    [0,0],
    [0,1],
    [0,100000],
    [1,0],
    [1,100000],
    [2,0],
    [2,1],
    [2,52],
  ];

  for(const [base,exponent] of exactCases) {
    const k=kernel(),expression=natPow(k,base,exponent);
    const expected=BigInt(base)**BigInt(exponent);
    assert.deepEqual(k.whnf(expression),["nat",Number(expected)],`${base}^${exponent}`);
    assert.equal(k.__natPowHits,1,`${base}^${exponent} should use the shortcut`);
  }

  for(const [base,exponent] of [[2,53],[2,128],[2,100001]]) {
    const k=kernel(),expression=natPow(k,base,exponent);
    assert.deepEqual(k.whnf(expression),expression,`${base}^${exponent} must fall back`);
    assert.equal(k.__natPowHits,undefined,`${base}^${exponent} must not use a partial result`);
  }
});

test("Nat power shortcut ignores a malformed instance",()=>{
  const k=kernel();
  const malformed=k.appN(k.make("const",INST_HPOW),[
    k.make("const",NAT),
    k.make("const",NAT),
    k.make("const",INST_NAT_POW_NAT),
  ]);
  const expression=natPow(k,2,2,malformed);

  assert.deepEqual(k.whnf(expression),expression);
  assert.equal(k.__natPowHits,undefined);
});
