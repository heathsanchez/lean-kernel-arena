import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype, old=p.equal, oldRun=p.run; const seen=[];
function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function desc(k,e){const s=spine(e),h=s.head;let name=null,kind=null;if(Array.isArray(h)&&h[0]==="const"){name=h[1];kind=k.env.get(name)?.kind??"const";}else kind=h?.[0]??typeof h;return {tag:e?.[0],kind,name,args:s.args.length};}
p.run=function(...xs){seen.push(this);return oldRun.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
 if((this._lazyDeltaDepth??0)>0){
   this.__ldPairs??=[]; if(this.__ldPairs.length<5000){
     const da=desc(this,a),db=desc(this,b);
     this.__ldPairs.push({step:this.steps,depth:this._lazyDeltaDepth,ctx:ctx.length,a:da,b:db,
       sameHead:da.name!==null&&da.name===db.name,
       sameTag:Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]});
   }
 }
 return old.call(this,a,b,ctx);
};
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const result=K.checkExport(input,CAPS,1_000_000);p.equal=old;p.run=oldRun;
const pairs=seen.flatMap(k=>k.__ldPairs??[]);
const sameRec=pairs.filter(x=>x.sameHead&&x.a.kind==="rec");
const ctorRec=pairs.filter(x=>(x.a.kind==="ctor"&&x.b.kind==="rec")||(x.a.kind==="rec"&&x.b.kind==="ctor"));
const tail=pairs.slice(-80);
const out={experiment:"shared-subterm-lazy-delta-pair-path",result,pairCount:pairs.length,sameRec,ctorRec,tail};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/shared-subterm-lazy-delta-pair-path.json",JSON.stringify(out,null,2)+"\n");
console.log("LAZY_DELTA_PAIR_PATH "+JSON.stringify({result,pairCount:pairs.length,sameRecCount:sameRec.length,ctorRecCount:ctorRec.length,sameRec:sameRec.slice(0,30),ctorRec:ctorRec.slice(-30),tail}));
