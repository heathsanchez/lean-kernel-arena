import assert from "node:assert/strict";
import test from "node:test";
import {readFileSync} from "node:fs";
import {Kernel,checkExport} from "./kernel.mjs";
import {leanName} from "./name-codec.mjs";

const N=leanName;
const C=(...xs)=>["const",N(...xs)],V=i=>["var",i];
const appN=(h,...args)=>args.reduce((f,a)=>["app",f,a],h);
const nat=C("Nat"),zero=C("Nat","zero"),succ=x=>appN(C("Nat","succ"),x);
const eq=(a,b)=>appN(["const",N("Eq"),[1]],nat,a,b);
const caps=["sort","binders","application","reduction","declarations","universes","inductive-envelope",
  "single-inductives","theorems","prop-inductives","inductive-reduction","nat-literals","rigid-conversion","rule-k","unit-eta"];
let natDeclarations;
const run0=Kernel.prototype.run;
try{
  Kernel.prototype.run=function(...args){natDeclarations=args[2];return run0.apply(this,args);};
  assert.equal(checkExport(readFileSync(new URL("./fixtures/nat-conversion.ndjson",import.meta.url),"utf8"),caps).status,"ACCEPT");
}finally{Kernel.prototype.run=run0;}
const declarations=[...natDeclarations,...JSON.parse(readFileSync(new URL("./fixtures/recursor-independent.json",import.meta.url),"utf8")).declarations];
declarations.push(
  {kind:"thm",name:N("eqZero"),levelParams:[],type:eq(zero,zero),value:appN(["const",N("Eq","refl"),[1]],nat,zero)},
  {kind:"thm",name:N("eqZeroAgain"),levelParams:[],type:eq(zero,zero),value:C("eqZero")},
);
function kernel(fullStack,omit){
  const k=new Kernel(caps.filter(c=>c!==omit),100000);
  const r=k.run(["sort",0],["sort",1],declarations);
  assert.equal(r.status,"ACCEPT",JSON.stringify(r));
  k._fullStackSafe=fullStack;
  return k;
}
function eqRec(index){
  const motive=["lam",nat,["lam",eq(V(2),V(0)),nat]];
  return appN(["const",N("Eq","rec"),[1,1]],nat,V(1),motive,zero,index,V(0));
}

for(const fullStack of [false,true]){
  test(`Eq.rec rule K reduces a variable major only at its derived index (fullStack=${fullStack})`,()=>{
    const k=kernel(fullStack),ctx=[nat,eq(V(0),V(0))],matching=eqRec(V(1));
    k.equal(k.infer(matching,ctx),nat,ctx);
    assert.deepEqual(k.whnf(matching),zero);
    const mismatch=eqRec(succ(V(1)));
    assert(k.same(k.whnf(mismatch),mismatch),"K must preserve a mismatched endpoint");
  });
  test(`Eq.rec rule K capability remains necessary (fullStack=${fullStack})`,()=>{
    const k=kernel(fullStack,"rule-k"),expression=eqRec(V(1));
    assert(k.same(k.whnf(expression),expression));
  });
  test(`unit eta recursor reduction preserves its capability and shape guards (fullStack=${fullStack})`,()=>{
    const unit=["const",N("PUnit"),[1]],motive=["lam",unit,nat];
    const expression=appN(["const",N("PUnit","rec"),[1,1]],motive,zero,V(0));
    const k=kernel(fullStack);
    k.equal(k.infer(expression,[unit]),nat,[unit]);
    assert.deepEqual(k.whnf(expression),zero);
    const without=kernel(fullStack,"unit-eta");
    assert(without.same(without.whnf(expression),expression));
    const nonunit=appN(["const",N("Nat","rec"),[1]],["lam",nat,nat],zero,["lam",nat,["lam",nat,zero]],V(0));
    assert(k.same(k.whnf(nonunit),nonunit),"unit eta must not rewrite a multi-constructor recursor");
  });
}

for(const fullStack of [false,true])test(`recursor majors unfold validated theorem bodies before rule matching (fullStack=${fullStack})`,()=>{
  const k=kernel(fullStack,"rule-k"),motive=["lam",nat,["lam",eq(zero,V(0)),nat]];
  const expression=appN(["const",N("Eq","rec"),[1,1]],nat,zero,motive,zero,zero,C("eqZeroAgain"));
  k.equal(k.infer(expression,[]),nat);
  const before=k.__theoremMajorUnfolds??0;
  assert.deepEqual(k.whnf(expression),zero);
  assert((k.__theoremMajorUnfolds??0)-before>=2,"both theorem aliases must unfold before constructor matching");
});
