import assert from "node:assert/strict";
import test from "node:test";
import {Kernel,S,V,Pi,Lam,App,quotientType} from "./kernel.mjs";
import {leanName} from "./name-codec.mjs";

const N=leanName;
const U="qu",VLEV="qv",EU="eu",EQ=N("Eq");
const names={type:N("Quot"),ctor:N("Quot","mk"),lift:N("Quot","lift"),ind:N("Quot","ind")};
const caps=["sort","binders","application","reduction","declarations","universes","quotients","rigid-conversion"];
const eq={kind:"axiom",name:EQ,levelParams:[EU],type:Pi(S(["param",EU]),Pi(V(0),Pi(V(1),S(0))))};
const quotientDecls=["type","ctor","lift","ind"].map(kind=>({
  kind:"quot",quotKind:kind,name:names[kind],
  levelParams:kind==="lift"?[U,VLEV]:[U],type:quotientType(kind,kind==="lift"?[U,VLEV]:[U]),
}));
const A=["const","QA"],R=App(["const",EQ,[0]],A),a=["const","qa"];
const baseDecls=[eq,...quotientDecls,
  {kind:"axiom",name:"QA",levelParams:[],type:S(0)},
  {kind:"axiom",name:"qa",levelParams:[],type:A}];
const appN=(head,args)=>args.reduce((fn,arg)=>App(fn,arg),head);
const ident=Lam(A,V(0));

function directKernel(declarations=baseDecls) {
  const k=new Kernel(caps,500000);k.steps=0;k.allocations=0;k.params=new Set();
  k.env=new Map(declarations.map(d=>[d.name,d]));return k;
}
function applyPi(k,type,args) {
  let out=type;
  for(const arg of args){out=k.whnf(out);assert.equal(out[0],"pi");out=k.substitute(out[2],arg);}
  return k.whnf(out);
}

const setup=(()=>{
  const k=directKernel();
  const liftRef=["const",names.lift,[0,0]];
  const liftType=k.instantiateDeclaration(liftRef,quotientDecls[2].type);
  const hType=applyPi(k,liftType,[A,R,A,ident])[1];
  const hValue=Lam(A,Lam(A,Lam(App(App(R,V(1)),V(0)),V(0))));
  const qh={kind:"def",name:"qh",levelParams:[],type:hType,value:hValue};
  const declarations=[...baseDecls,qh];
  const mk=appN(["const",names.ctor,[0]],[A,R,a]);
  const lift=appN(liftRef,[A,R,A,ident,["const","qh"],mk]);
  const quotient=appN(["const",names.type,[0]],[A,R]);
  const motive=Lam(quotient,A),minor=Lam(A,V(0));
  const ind=appN(["const",names.ind,[0]],[A,R,motive,minor,mk]);
  return {declarations,lift,ind,mk};
})();

for(const [label,expression] of [["lift",setup.lift],["ind",setup.ind]]){
  test(`Quot.${label} reduces identically in ordinary and iterative evaluators`,()=>{
    assert.equal(new Kernel(caps,500000).run(expression,A,setup.declarations).status,"ACCEPT");
    for(const mode of ["ordinary","full-stack","scoped-beta"]){
      const k=directKernel(setup.declarations);
      if(mode==="full-stack")k._fullStackSafe=true;
      if(mode==="scoped-beta")k._scopedBetaDepth=1;
      assert.deepEqual(k.whnf(expression),a,mode);
      assert.doesNotThrow(()=>k.equal(expression,a,[]),mode);
    }
    const wrapped=App(App(Lam(A,Lam(A,expression)),a),a);
    const multiBeta=directKernel(setup.declarations);
    assert.deepEqual(multiBeta.whnf(wrapped),a,"multi-beta spine");
    assert.doesNotThrow(()=>multiBeta.equal(wrapped,a,[]),"multi-beta spine");
  });
}

test("iterative quotient reduction preserves exact guards",()=>{
  for(const mode of ["ordinary","full-stack","scoped-beta"]){
    const k=directKernel(setup.declarations);
    if(mode==="full-stack")k._fullStackSafe=true;
    if(mode==="scoped-beta")k._scopedBetaDepth=1;
    const short=appN(["const",names.lift,[0,0]],[A,R,A,ident,["const","qh"]]);
    const wrongMk=appN(["const",names.ctor,[0]],[["const","Other"],R,a]);
    const mismatch=appN(["const",names.lift,[0,0]],[A,R,A,ident,["const","qh"],wrongMk]);
    assert.deepEqual(k.whnf(short),short,`${mode} arity`);
    assert.deepEqual(k.whnf(mismatch),mismatch,`${mode} parameters`);
  }
  const noQuot=directKernel(setup.declarations);noQuot.caps.delete("quotients");
  assert.deepEqual(noQuot.whnf(setup.lift),setup.lift);
});
