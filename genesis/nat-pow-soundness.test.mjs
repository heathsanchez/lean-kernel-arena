import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import test from "node:test";

import {Kernel,Stop,checkExport} from "./kernel.mjs";
import "./compiled-nat-pow-layer.mjs";

import {leanName} from "./name-codec.mjs";
const name=leanName;
const constant=(...parts)=>["const",name(...parts)];
const pi=(domain,body)=>["pi",domain,body];
const POW=name("Nat","pow"), ZERO=name("Nat","zero");
const EXPONENT_LIMIT=1<<24;

function kernel(capabilities=["application","declarations","nat-literals","reduction"]) {
  const k=new Kernel(capabilities);
  k.steps=0;
  k.allocations=0;
  k.env=new Map([
    [POW,{kind:"axiom",name:POW,levelParams:[]}],
    [ZERO,{kind:"axiom",name:ZERO,levelParams:[]}],
  ]);
  return k;
}

function primitivePow(k,base,exponent,universes=undefined) {
  const head=universes===undefined?k.make("const",POW):k.make("const",POW,universes);
  return k.appN(head,[base,exponent]);
}

function natLiteral(value) {
  return ["nat",value<=BigInt(Number.MAX_SAFE_INTEGER)?Number(value):value.toString()];
}

test("primitive Nat.pow returns exact bounded natural powers",()=>{
  for(const [base,exponent] of [[0,0],[0,7],[1,256],[2,3],[2,64],[2,128],[2,256]]) {
    const k=kernel();
    const expression=primitivePow(k,["nat",base],["nat",exponent]);
    const expected=BigInt(base)**BigInt(exponent);

    assert.deepEqual(k.whnf(expression),natLiteral(expected),`${base}^${exponent}`);
    assert.equal(k.__natPowHits,1);
  }

  const k=kernel();
  assert.deepEqual(k.whnf(primitivePow(k,["const",ZERO],["nat",9])),["nat",0]);
});

test("primitive Nat.pow falls back outside conservative resource bounds",()=>{
  const oversizedBase="1"+"0".repeat(1300);
  const zeroExponentKernel=kernel();
  assert.deepEqual(
    zeroExponentKernel.whnf(primitivePow(zeroExponentKernel,["nat",oversizedBase],["nat",0])),
    ["nat",1],
  );

  for(const [base,exponent] of [[2,4096],[2,EXPONENT_LIMIT+1],[oversizedBase,1]]) {
    const k=kernel(),expression=primitivePow(k,["nat",base],["nat",exponent]);
    assert.deepEqual(k.whnf(expression),expression,`${base}^${exponent}`);
    assert.equal(k.__natPowHits,undefined);
  }

  const k=kernel(),withUniverse=primitivePow(k,["nat",2],["nat",3],[0]);
  assert.deepEqual(k.whnf(withUniverse),withUniverse);
  assert.equal(k.__natPowHits,undefined);
});

test("primitive Nat.pow ignores invalid direct-method numerals",()=>{
  for(const [base,exponent] of [[-2,2],[Number.MAX_SAFE_INTEGER+1,2],[2,-1]]) {
    const k=kernel(),expression=primitivePow(k,["nat",base],["nat",exponent]);
    assert.deepEqual(k.whnf(expression),expression);
    assert.equal(k.__natPowHits,undefined);
  }
});

test("primitive Nat.pow requires literal and reduction capabilities",()=>{
  for(const capabilities of [
    ["application","declarations","reduction"],
    ["application","declarations","nat-literals"],
  ]) {
    const k=kernel(capabilities),expression=primitivePow(k,["nat",2],["nat",3]);
    assert.throws(()=>k.whnf(expression),error=>
      error instanceof Stop&&error.status==="UNKNOWN"&&error.message.startsWith("missing:"));
  }
});

test("validated axiomatic HPow dictionaries do not imply Nat.pow",()=>{
  const caps=["sort","binders","application","reduction","declarations","universes",
    "inductive-envelope","single-inductives","inductive-reduction","nat-literals","rigid-conversion"];
  let natDeclarations;
  const run0=Kernel.prototype.run;
  try {
    Kernel.prototype.run=function(...args){natDeclarations=args[2];return run0.apply(this,args);};
    const fixture=readFileSync(new URL("./fixtures/nat-conversion.ndjson",import.meta.url),"utf8");
    assert.equal(checkExport(fixture,caps).status,"ACCEPT");
  } finally {
    Kernel.prototype.run=run0;
  }

  const nat=constant("Nat"),sort1=["sort",1];
  const H=name("HPow","hPow"),IH=name("instHPow"),IP=name("instPowNat"),IN=name("instNatPowNat");
  const fake=[
    {kind:"axiom",name:IN,levelParams:[],type:nat},
    {kind:"axiom",name:IP,levelParams:[],type:pi(sort1,pi(nat,nat))},
    {kind:"axiom",name:IH,levelParams:[],type:pi(sort1,pi(sort1,pi(nat,nat)))},
    {kind:"axiom",name:H,levelParams:[],type:pi(sort1,pi(sort1,pi(sort1,pi(nat,pi(nat,pi(nat,nat))))))},
  ];
  const appN=(head,args)=>args.reduce((fn,arg)=>["app",fn,arg],head);
  const dict=appN(["const",IH],[nat,nat,appN(["const",IP],[nat,["const",IN]])]);
  const expression=appN(["const",H],[nat,nat,nat,dict,["nat",2],["nat",3]]);
  const k=new Kernel(caps);

  assert.equal(k.run(expression,nat,[...natDeclarations,...fake]).status,"ACCEPT");
  assert.deepEqual(k.whnf(expression),expression);
  assert.throws(()=>k.equal(expression,["nat",8],[]),error=>error instanceof Stop);
  assert.equal(k.__natPowHits,undefined);
});
