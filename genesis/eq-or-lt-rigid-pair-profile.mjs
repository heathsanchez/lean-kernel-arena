import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./lazy-congruence-conversion-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function rawHead(e){
  let h=e,args=0;
  while(Array.isArray(h)&&h[0]==="app"){args++;h=h[1];}
  if(!Array.isArray(h))return {tag:typeof h,args};
  return {tag:h[0],name:h[0]==="const"?h[1]:null,args};
}
function count(e){
  let n=0;const st=[e],seen=new Set();
  while(st.length){const x=st.pop();if(!Array.isArray(x)||seen.has(x))continue;seen.add(x);n++;
    for(let i=1;i<x.length;i++)if(Array.isArray(x[i]))st.push(x[i]);}
  return n;
}
const p=K.Kernel.prototype,eq=p.equal,run0=p.run;
p.run=function(...xs){this.__rigidReject=null;return run0.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
  try{return eq.call(this,a,b,ctx);}
  catch(e){
    if(e instanceof K.Stop&&e.status===K.REJECT&&
       typeof this.currentDeclaration==="string"&&this.currentDeclaration.includes("eq_or_lt_of_le")&&
       this.__rigidReject===null){
      this.__rigidReject={reason:e.message,step:this.steps,ctxDepth:ctx.length,ctx:ctx.slice(),a,b};
    }
    throw e;
  }
};

for(const name of ["init-prelude","perf/grind-ring-5"]){
  const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  let r;try{r=K.checkExport(input,CAPS,500_000);}finally{p.run=old;}
  let q=null;for(const k of seen)if(k.__rigidReject){q=k.__rigidReject;break;}
  const out={name,status:r.status,reason:r.reason,steps:r.steps??null,frontier:r.frontier_declaration??null};
  if(q){
    const owner=seen.find(k=>k.__rigidReject===q);
    let lw=null,rw=null,lt=null,rt=null,whnfError=null,inferError=null;
    if(owner){
      const oldSteps=owner.steps,oldBudget=owner.budget;
      try{
        owner.steps=0;owner.budget=2_000_000;
        lw=owner.whnf(q.a);rw=owner.whnf(q.b);
        try{lt=owner.infer(q.a,q.ctx);rt=owner.infer(q.b,q.ctx);}
        catch(e){inferError=String(e?.message??e);}
      }catch(e){whnfError=String(e?.message??e);}
      finally{owner.steps=oldSteps;owner.budget=oldBudget;}
    }
    Object.assign(out,{capturedStep:q.step,capturedReason:q.reason,ctxDepth:q.ctxDepth,
      leftHead:rawHead(q.a),rightHead:rawHead(q.b),leftNodes:count(q.a),rightNodes:count(q.b),
      leftWhnfHead:lw?rawHead(lw):null,rightWhnfHead:rw?rawHead(rw):null,
      leftWhnf:lw?JSON.stringify(lw).slice(0,7000):null,rightWhnf:rw?JSON.stringify(rw).slice(0,7000):null,
      leftTypeHead:lt?rawHead(lt):null,rightTypeHead:rt?rawHead(rt):null,
      leftType:lt?JSON.stringify(lt).slice(0,7000):null,rightType:rt?JSON.stringify(rt).slice(0,7000):null,
      whnfError,inferError,leftBytes:JSON.stringify(q.a).length,rightBytes:JSON.stringify(q.b).length,
      left:JSON.stringify(q.a).slice(0,7000),right:JSON.stringify(q.b).slice(0,7000)});
  }
  console.log("EQ_OR_LT_RIGID_PAIR "+JSON.stringify(out));
}
