import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT"],
 ["perf/args-before-unfold","ACCEPT"],
 ["perf/folded-constant-first","ACCEPT"],
 ["perf/repeated-subproblem","ACCEPT"],
 ["perf/discarded-argument-match","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"],
 ["undecidability/subject-reduction-reduct","REJECT"]
];
const p=K.Kernel.prototype, retainedEqual=p.equal;
function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function snap(k){return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
function fallbackable(e){return e instanceof K.Stop||e instanceof RangeError;}

p.equal=function(a,b,ctx=[]){
  if((this._lazyDeltaDepth??0)>0){
    const sa=spine(a),sb=spine(b);
    if(sa.args.length&&sa.args.length===sb.args.length&&
       (sa.head===sb.head||this.same(sa.head,sb.head))&&
       Array.isArray(sa.head)&&sa.head[0]==="const"){
      const rd=this.env.get(sa.head[1]);
      if(rd?.kind==="rec"){
        const s=snap(this);
        this.budget=Math.min(s.budget,s.steps+220000);
        try{
          // Recursor applications with the same head need not have equal minors.
          // Specialize both to their concrete majors first. WHNF exposes only
          // the constructor demanded by the recursor, retaining shared subterms.
          const x=this.whnf(a),y=this.whnf(b);
          if((x!==a&&!this.same(x,a))||(y!==b&&!this.same(y,b))){
            this.__recMajorFirstHits=(this.__recMajorFirstHits??0)+1;
            this.__recMajorFirstMax=Math.max(this.__recMajorFirstMax??0,this.steps-s.steps);
            this.budget=s.budget;
            return this.equal(x,y,ctx);
          }
        }catch(e){
          this.budget=s.budget;
          if(!fallbackable(e))throw e;
        }
        this.__recMajorFirstMisses=(this.__recMajorFirstMisses??0)+1;
        restore(this,s);
      }
    }
  }
  return retainedEqual.call(this,a,b,ctx);
};

const rows=[];
for(const [name,want] of TARGETS){
  const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  const t0=Date.now();let r;
  try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}
  finally{p.run=old;}
  const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
    recMajorFirstHits:seen.reduce((n,k)=>n+(k.__recMajorFirstHits??0),0),
    recMajorFirstMisses:seen.reduce((n,k)=>n+(k.__recMajorFirstMisses??0),0),
    maxRecMajorFirst:Math.max(0,...seen.map(k=>k.__recMajorFirstMax??0))};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
p.equal=retainedEqual;
const clean=rows.every(r=>r.status===r.want);
const out={experiment:"same-recursor-major-first",clean,rows};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/same-recursor-major-first.json",JSON.stringify(out,null,2)+"\n");
console.log("SAME_RECURSOR_MAJOR_FIRST "+JSON.stringify(out));
if(!clean)process.exit(1);
