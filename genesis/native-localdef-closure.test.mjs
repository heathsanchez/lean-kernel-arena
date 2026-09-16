import test from "node:test";
import assert from "node:assert/strict";
import {CAPABILITIES} from "./production.mjs";
import {Kernel} from "./kernel-base.mjs";

async function candidate(){
  try{return await import("./native-localdef-closure-layer.mjs");}
  catch(e){if(e?.code==="ERR_MODULE_NOT_FOUND")return null;throw e;}
}
function kernel(){
  const k=new Kernel(CAPABILITIES,5_000_000);
  k.steps=0;k.allocations=0;k.env=new Map();k.params=new Set();
  k.localDefs=true;k._activeCtx=[];
  return k;
}
function appN(head,args){let out=head;for(const a of args)out=["app",out,a];return out;}
function lamN(n,body){let out=body;for(let i=0;i<n;i++)out=["lam",["sort",0],out];return out;}

const PI0=["pi",["sort",0],["sort",0]];

test("recurrent 3-arg localdef WHNF spine uses closure beta and preserves outer local definition",async()=>{
  const mod=await candidate();assert.ok(mod,"localdef closure candidate must exist");
  const root=appN(lamN(3,["var",3]),[["sort",0],["sort",0],["sort",0]]);

  const baseline=kernel();
  baseline._activeCtx=[{__localDef:true,type:["sort",1],value:PI0}];
  const expected=baseline.whnf(root);
  assert.deepEqual(expected,PI0);

  mod.installNativeLocalDefClosure(true);
  try{
    const k=kernel();k._activeCtx=[{__localDef:true,type:["sort",1],value:PI0}];
    let substitutes=0;const old=k.substitute;
    k.substitute=function(...xs){substitutes++;return old.apply(this,xs);};
    const out=k.whnf(root);
    assert.deepEqual(out,expected);
    assert.equal(substitutes,0,"selected recurrent spine must not eager-substitute beta bodies");
    assert.equal(k.__nativeLocalDefClosureStats?.selected3,1);
    assert.ok((k.__nativeLocalDefClosureStats?.beta??0)>=3);
  }finally{mod.installNativeLocalDefClosure(false);}
});

test("recurrent 4-arg definition spine crosses delta and beta in the closure machine",async()=>{
  const mod=await candidate();assert.ok(mod,"localdef closure candidate must exist");
  mod.installNativeLocalDefClosure(true);
  try{
    const k=kernel();
    k.env.set("f",{kind:"def",levelParams:[],value:lamN(4,["var",3]),type:["sort",1]});
    let substitutes=0;const old=k.substitute;
    k.substitute=function(...xs){substitutes++;return old.apply(this,xs);};
    const first=["sort",0];
    const out=k.whnf(appN(["const","f"],[first,["sort",0],["sort",0],["sort",0]]));
    assert.deepEqual(out,first);
    assert.equal(substitutes,0);
    assert.equal(k.__nativeLocalDefClosureStats?.selected4,1);
    assert.ok((k.__nativeLocalDefClosureStats?.delta??0)>=1);
    assert.ok((k.__nativeLocalDefClosureStats?.beta??0)>=4);
  }finally{mod.installNativeLocalDefClosure(false);}
});

test("2-arg fueled-style local-definition head stays on retained evaluator",async()=>{
  const mod=await candidate();assert.ok(mod,"localdef closure candidate must exist");
  mod.installNativeLocalDefClosure(true);
  try{
    const k=kernel();
    k._activeCtx=[{__localDef:true,type:["sort",1],value:lamN(2,PI0)}];
    k.__retainedWhnfDepth=1;
    const root=appN(["var",0],[["sort",0],["sort",0]]);
    const out=k.whnf(root);
    assert.deepEqual(out,PI0);
    assert.equal(k.__nativeLocalDefClosureStats?.selected3??0,0);
    assert.equal(k.__nativeLocalDefClosureStats?.selected4??0,0);
    assert.ok((k.__nativeLocalDefClosureStats?.delegatedNonRecurrent??0)>=1);
  }finally{mod.installNativeLocalDefClosure(false);}
});

test("5-arg spines remain outside the minimal recurrent interface",async()=>{
  const mod=await candidate();assert.ok(mod,"localdef closure candidate must exist");
  mod.installNativeLocalDefClosure(true);
  try{
    const k=kernel();
    const root=appN(lamN(5,["var",4]),Array.from({length:5},()=>["sort",0]));
    assert.deepEqual(k.whnf(root),["sort",0]);
    assert.equal(k.__nativeLocalDefClosureStats?.selected3??0,0);
    assert.equal(k.__nativeLocalDefClosureStats?.selected4??0,0);
    assert.ok((k.__nativeLocalDefClosureStats?.delegatedNonRecurrent??0)>=1);
  }finally{mod.installNativeLocalDefClosure(false);}
});
