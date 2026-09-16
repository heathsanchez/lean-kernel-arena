import test from "node:test";
import assert from "node:assert/strict";
import {CAPABILITIES} from "./production.mjs";
import {Kernel} from "./kernel-base.mjs";

async function integration(){
  try { return await import("./native-closure-whnf-layer.mjs"); }
  catch (e) {
    if(e?.code==="ERR_MODULE_NOT_FOUND") return null;
    throw e;
  }
}

function kernel(){
  const k=new Kernel(CAPABILITIES,5_000_000);
  k.steps=0;k.allocations=0;k.env=new Map();k.params=new Set();
  return k;
}

function withLayer(k,fn){
  return fn(k);
}

test("native closure integration crosses a definition boundary into beta without eager substitution",async()=>{
  const mod=await integration();
  assert.ok(mod,"native closure integration layer must exist");
  mod.installNativeClosureWhnf(true);
  try {
    const k=kernel();
    k.env.set("id",{kind:"def",levelParams:[],value:["lam",["sort",0],["var",0]],type:["pi",["sort",0],["sort",0]]});
    let substitutes=0;
    const retainedSubstitute=k.substitute;
    k.substitute=function(...args){substitutes++;return retainedSubstitute.apply(this,args);};
    const out=withLayer(k,x=>x.whnf(["app",["const","id"],["sort",0]]));
    assert.deepEqual(out,["sort",0]);
    assert.equal(substitutes,0,"native closure path must not materialize beta through Kernel.substitute");
    assert.ok((k.__nativeClosureStats?.delta??0)>=1,"definition must be unfolded inside closure execution");
    assert.ok((k.__nativeClosureStats?.beta??0)>=1,"beta must be discharged inside closure execution");
  } finally { mod.installNativeClosureWhnf(false); }
});

test("native closure integration keeps let and beta substitutions deferred together",async()=>{
  const mod=await integration();
  assert.ok(mod,"native closure integration layer must exist");
  mod.installNativeClosureWhnf(true);
  try {
    const k=kernel();
    let substitutes=0;
    const retainedSubstitute=k.substitute;
    k.substitute=function(...args){substitutes++;return retainedSubstitute.apply(this,args);};
    const term=["app",["lam",["sort",0],["let",["sort",0],["var",0],["var",0]]],["sort",0]];
    assert.deepEqual(k.whnf(term),["sort",0]);
    assert.equal(substitutes,0);
    assert.ok((k.__nativeClosureStats?.beta??0)>=1);
    assert.ok((k.__nativeClosureStats?.let??0)>=1);
  } finally { mod.installNativeClosureWhnf(false); }
});

test("native closure integration delegates neutral ordinary terms unchanged",async()=>{
  const mod=await integration();
  assert.ok(mod,"native closure integration layer must exist");
  const k0=kernel(), term=["app",["var",0],["sort",0]];
  const baseline=k0.whnf(term);
  mod.installNativeClosureWhnf(true);
  try {
    const k=kernel();
    const out=k.whnf(term);
    assert.deepEqual(out,baseline);
    assert.equal(k.__nativeClosureStats?.fallback??0,1);
  } finally { mod.installNativeClosureWhnf(false); }
});

test("native closure integration leaves local-definition WHNF on the retained path",async()=>{
  const mod=await integration();
  assert.ok(mod,"native closure integration layer must exist");
  mod.installNativeClosureWhnf(true);
  try {
    const k=kernel();
    k.localDefs=true;
    k._activeCtx=[{__localDef:true,type:["sort",1],value:["pi",["sort",0],["sort",0]]}];
    const out=k.whnf(["var",0]);
    assert.deepEqual(out,["pi",["sort",0],["sort",0]]);
    assert.equal(k.__nativeClosureStats?.bypassLocalDefs??0,1);
  } finally { mod.installNativeClosureWhnf(false); }
});
