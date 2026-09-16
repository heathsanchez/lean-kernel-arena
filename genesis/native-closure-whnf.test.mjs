import test from "node:test";
import assert from "node:assert/strict";

async function loadNative(){
  try {
    return await import("./native-closure-whnf.mjs");
  } catch {
    return null;
  }
}

const S=n=>["sort",n];
const V=n=>["var",n];
const Lam=(a,b)=>["lam",a,b];
const App=(f,a)=>["app",f,a];
const Let=(a,v,b)=>["let",a,v,b];

async function api(){
  const m=await loadNative();
  assert.ok(m,"native closure evaluator module must exist");
  for(const name of ["emptyClosureEnv","makeClosure","extendClosureEnv","lookupClosureVar","reifyClosure","nativeWhnf"])
    assert.equal(typeof m[name],name==="emptyClosureEnv"?"object":"function",`missing export ${name}`);
  return m;
}

test("closure environment lookup is persistent and de Bruijn ordered",async()=>{
  const m=await api();
  const a=m.makeClosure(S(10),m.emptyClosureEnv);
  const b=m.makeClosure(S(20),m.emptyClosureEnv);
  const env1=m.extendClosureEnv(m.emptyClosureEnv,a);
  const env2=m.extendClosureEnv(env1,b);
  assert.strictEqual(m.lookupClosureVar(env2,0),b);
  assert.strictEqual(m.lookupClosureVar(env2,1),a);
  assert.equal(m.lookupClosureVar(env2,2),null);
  assert.strictEqual(m.lookupClosureVar(env1,0),a,"extending an environment must not mutate its parent");
});

test("native WHNF performs beta without eager tree substitution",async()=>{
  const m=await api();
  const term=App(Lam(S(0),V(0)),S(7));
  const out=m.nativeWhnf(term);
  assert.deepEqual(m.reifyClosure(out),S(7));
});

test("native WHNF composes nested beta environments in de Bruijn order",async()=>{
  const m=await api();
  const term=App(App(Lam(S(0),Lam(S(0),V(1))),S(7)),S(9));
  const out=m.nativeWhnf(term);
  assert.deepEqual(m.reifyClosure(out),S(7));
});

test("native WHNF reduces lets through the same closure environment",async()=>{
  const m=await api();
  const term=Let(S(0),S(11),V(0));
  const out=m.nativeWhnf(term);
  assert.deepEqual(m.reifyClosure(out),S(11));
});

test("reification shifts a captured free variable under a surviving binder",async()=>{
  const m=await api();
  // (fun x => fun y => x) #0  ==>  fun y => #1
  const term=App(Lam(S(0),Lam(S(0),V(1))),V(0));
  const out=m.nativeWhnf(term);
  assert.deepEqual(m.reifyClosure(out),Lam(S(0),V(1)));
});

test("deep beta chains are evaluated iteratively without host-stack growth",async()=>{
  const m=await api();
  let term=S(3);
  const id=Lam(S(0),V(0));
  for(let i=0;i<20_000;i++) term=App(id,term);
  const out=m.nativeWhnf(term);
  assert.deepEqual(m.reifyClosure(out),S(3));
});
