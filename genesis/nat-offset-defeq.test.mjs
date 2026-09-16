import assert from "node:assert/strict";
import test from "node:test";
import {readFileSync} from "node:fs";
import {Kernel,checkExport,Stop,REJECT} from "./kernel.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./compiled-nat-pow-layer.mjs";

const name=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
const C=(...xs)=>["const",name(...xs)], nat=C("Nat"), zero=C("Nat","zero");
const succ=x=>["app",C("Nat","succ"),x];
const caps=["sort","binders","application","reduction","declarations","universes",
  "inductive-envelope","single-inductives","inductive-reduction","nat-literals","rigid-conversion"];
// The exported N package from tests/tutorial/044_natDef.ndjson, with only N
// renamed to Nat. Capture parser output, then validate it again in each kernel.
let declarations;
const run=Kernel.prototype.run;
try {
  Kernel.prototype.run=function(...args){ declarations=args[2];return run.apply(this,args); };
  assert.equal(checkExport(readFileSync(new URL("./fixtures/nat-conversion.ndjson",import.meta.url),"utf8"),caps).status,"ACCEPT");
} finally { Kernel.prototype.run=run; }
// Lawful addition: fun m n => Nat.rec (fun _ => Nat) m (fun _ ih => Nat.succ ih) n.
const appN=(h,...args)=>args.reduce((f,a)=>["app",f,a],h);
const add={kind:"def",name:name("Nat","add"),levelParams:[],type:["pi",nat,["pi",nat,nat]],
  value:["lam",nat,["lam",nat,appN(["const",name("Nat","rec"),[1]],
    ["lam",nat,nat],["var",1],["lam",nat,["lam",nat,succ(["var",0])]], ["var",0])]]};
const mul={kind:"def",name:name("Nat","mul"),levelParams:[],type:add.type,
  value:["lam",nat,["lam",nat,appN(["const",name("Nat","rec"),[1]],
    ["lam",nat,nat],zero,["lam",nat,["lam",nat,appN(C("Nat","add"),["var",3],["var",0])]], ["var",0])]]};
const pow={kind:"def",name:name("Nat","pow"),levelParams:[],type:add.type,
  value:["lam",nat,["lam",nat,appN(["const",name("Nat","rec"),[1]],
    ["lam",nat,nat],succ(zero),["lam",nat,["lam",nat,appN(C("Nat","mul"),["var",3],["var",0])]], ["var",0])]]};
function kernel(){
  const k=new Kernel(caps,50000);
  const r=k.run(["sort",0],["sort",1],[...declarations,add,mul,pow]);
  assert.equal(r.status,"ACCEPT",JSON.stringify(r));
  return k;
}
function rejects(k,a,b,ctx=[]){assert.throws(()=>k.equal(a,b,ctx),e=>e instanceof Stop&&e.status===REJECT);}

for(const warm of [false,true]) for(const reverse of [false,true]) {
  test(`computed zero equals literal (warm=${warm}, reverse=${reverse})`,()=>{
    const k=kernel();
    const literal=warm?k.normal(appN(C("Nat","add"),["nat",0],["nat",0])):["nat",0];
    const computed=appN(["const",name("Nat","rec"),[1]],
      ["lam",nat,nat],zero,["lam",nat,["lam",nat,succ(["var",0])]], ["nat",0]);
    k.equal(k.infer(computed,[]),nat);
    if(warm) {
      assert.deepEqual(k.normal(literal),["nat",0]);
      assert.deepEqual(k.normal(computed),zero);
    }
    const [a,b]=reverse?[literal,computed]:[computed,literal];
    k.equal(a,b,[]);
    k.equal(a,b,[]);
    rejects(k,computed,["nat",1]);
    rejects(k,["nat",1],computed);
  });
}

test("Nat offset rules retain zero/succ, exact big literals, and symbolic guards",()=>{
  const k=kernel(),big=2n**64n;
  k.equal(zero,["nat",0]);
  k.equal(["nat",1],succ(zero));
  k.equal(succ(["nat",(big-1n).toString()]),["nat",big.toString()]);
  k.equal(["nat",big.toString()],["nat",big.toString()]);
  rejects(k,["nat",0],["nat",1]);
  rejects(k,["nat",1],["nat",0]);
  const before=k.steps;
  rejects(k,["nat",big.toString()],["nat",(big+1n).toString()]);
  rejects(k,["nat",(big+1n).toString()],["nat",big.toString()]);
  assert(k.steps-before<100,"distinct huge literals require bounded work");
  rejects(k,succ(["var",0]),["nat",0],[nat]);
  rejects(k,["nat",0],succ(["var",0]),[nat]);
  rejects(k,succ(["var",0]),succ(["var",1]),[nat,nat]);
});

test("Nat literal capability is required by the offset rule",()=>{
  const k=kernel();
  k.caps.delete("nat-literals");
  assert.throws(()=>k.equal(["nat",0],zero),e=>e instanceof Stop&&e.message==="missing:nat-literals");
});

test("normalization keeps a huge Nat literal compact with a cold and warm cache",()=>{
  const k=kernel(),literal=["nat",(2n**64n).toString()],before=k.steps;
  assert.deepEqual(k.normal(literal),literal);
  assert.deepEqual(k.normal(literal),literal);
  assert(k.steps-before<100,"normalizing a literal must not build its unary expansion");
});

test("normalization preserves huge constructor, beta, and arithmetic results",()=>{
  const k=kernel(),big=2n**64n,literal=["nat",big.toString()];
  for(const expression of [
    succ(["nat",(big-1n).toString()]),
    appN(["lam",nat,["var",0]],literal),
    appN(C("Nat","add"),["nat",(big-1n).toString()],["nat",1]),
  ]) {
    const before=k.steps,normal=k.normal(expression);
    k.equal(normal,literal);
    k.equal(literal,normal);
    assert(k.steps-before<500,"computed huge numerals must remain bounded");
  }
});

test("compact normalization retains validation and capability checks",()=>{
  for(const n of [-1,0.5,"-1","bad"]) {
    const k=new Kernel(caps);
    assert.equal(k.run(["nat",n],nat,declarations).status,"REJECT");
  }
  const k=kernel();k.caps.delete("nat-literals");
  assert.throws(()=>k.normal(["nat",0]),e=>e instanceof Stop&&e.message==="missing:nat-literals");
});

test("Nat WHNF preserves literals, exposing a constructor only for recursor majors",()=>{
  const k=kernel(),literal=["nat",(2n**64n).toString()];
  assert.deepEqual(k.whnf(literal),literal);
  assert.deepEqual(k.whnfMajor(literal),succ(["nat",(2n**64n-1n).toString()]));
  assert.deepEqual(k.whnfMajor(appN(C("Nat","pow"),["nat",2],["nat",64])),succ(["nat",(2n**64n-1n).toString()]));
  assert.deepEqual(k.whnf(["nat",0]),["nat",0]);
  assert.deepEqual(k.whnfMajor(["nat",0]),zero);
});

for(const fullStack of [false,true])test(`Nat.rec reduces computed literal majors (fullStack=${fullStack})`,()=>{
  const k=kernel();k._fullStackSafe=fullStack;
  for(const major of [["nat",0],["nat",2],appN(C("Nat","add"),["nat",1],["nat",1]),appN(C("Nat","pow"),["nat",2],["nat",1])]) {
    const expression=appN(["const",name("Nat","rec"),[1]],
      ["lam",nat,nat],zero,["lam",nat,["lam",nat,succ(["var",0])]],major);
    const expected=major[0]==="nat"&&major[1]===0?["nat",0]:["nat",2];
    k.equal(k.whnf(expression),expected);
    const beta=appN(["lam",nat,["lam",nat,expression]],["nat",0],["nat",0]);
    k.equal(k.whnf(beta),expected);
  }
});

test("literal recursor majors preserve local-definition context",()=>{
  let LocalDefKernel;
  const run=Kernel.prototype.run;
  try {
    Kernel.prototype.run=function(...args){if(this.localDefs)LocalDefKernel=this.constructor;return run.apply(this,args);};
    assert.equal(checkExport(readFileSync(new URL("./fixtures/nat-conversion.ndjson",import.meta.url),"utf8"),caps,1).status,"UNKNOWN");
  } finally {Kernel.prototype.run=run;}
  assert(LocalDefKernel,"the real local-definition fallback must be exercised");
  {
    const k=new LocalDefKernel(caps,50000);
    assert.equal(k.run(["sort",0],["sort",1],[...declarations,add]).status,"ACCEPT");
    const ctx=[{__localDef:true,type:nat,value:appN(C("Nat","add"),["nat",1],["nat",1])}];
    const expression=appN(["const",name("Nat","rec"),[1]],
      ["lam",nat,nat],zero,["lam",nat,["lam",nat,succ(["var",0])]], ["var",0]);
    k.equal(expression,["nat",2],ctx);
    k.withCtx(ctx,()=>assert.deepEqual(k.whnfMajor(["var",0]),succ(["nat",1])));
  }
});
