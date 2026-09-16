import test from "node:test";
import assert from "node:assert/strict";
import {Kernel,S,V,Lam,App,NatLit} from "./kernel.mjs";
import {leanName} from "./name-codec.mjs";
import "./native-nat-reduction-layer.mjs";

const CAPS=["application","reduction","declarations","nat-literals"];
const BLE=leanName("Nat","ble");
const BTRUE=["const",leanName("Bool","true")];

function freshKernel(){
  const k=new Kernel(CAPS,100000);
  k.steps=0;
  k.allocations=0;
  k.params=new Set();
  k.env=new Map([[BLE,{kind:"axiom",name:BLE,levelParams:[],type:S(0)}]]);
  k._shiftCache=new WeakMap();
  k._substCache=new WeakMap();
  return k;
}

const direct=App(App(["const",BLE],NatLit(3)),NatLit(5));
const betaExposed=App(
  Lam(S(0),
    App(
      Lam(S(0),App(App(["const",BLE],V(1)),V(0))),
      NatLit(5)
    )
  ),
  NatLit(3)
);

test("native Nat.ble is preserved when multi-beta exposes the primitive",()=>{
  const directKernel=freshKernel();
  const expected=directKernel.whnf(direct);
  assert.deepEqual(expected,BTRUE,"control: the retained native rule reduces direct Nat.ble");

  const betaKernel=freshKernel();
  const actual=betaKernel.whnf(betaExposed);
  assert.deepEqual(actual,expected,"multi-beta must re-enter the same retained native rule");
  assert.equal(betaKernel.__nativeNatHits,1,"the beta-exposed primitive must be reduced natively exactly once");
});
