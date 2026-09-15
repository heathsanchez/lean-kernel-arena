import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT"],
 ["perf/args-before-unfold","ACCEPT"],
 ["perf/folded-constant-first","ACCEPT"],
 ["perf/repeated-subproblem","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"],
 ["undecidability/subject-reduction-reduct","REJECT"]
];
const p=K.Kernel.prototype, retainedEqual=p.equal;
function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function kind(k,h){if(!Array.isArray(h)||h[0]!=="const")return h?.[0]??null;return k.env.get(h[1])?.kind??"const";}
function snap(k){return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
function fallbackable(e){return e instanceof K.Stop||e instanceof RangeError;}

p.equal=function(a,b,ctx=[]){
  if((this._lazyDeltaDepth??0)>0){
    const sa=spine(a),sb=spine(b),ka=kind(this,sa.head),kb=kind(this,sb.head);
    let rigid=null,blocked=null,flip=false;
    if(ka==="ctor"&&kb==="rec"){rigid=a;blocked=b;}
    else if(kb==="ctor"&&ka==="rec"){rigid=b;blocked=a;flip=true;}
    if(blocked!==null){
      const s=snap(this);
      // This is not full normalization: ask the retained WHNF engine only for
      // the blocked recursor's weak head, which recursively exposes just enough
      // of its major premise for an iota step.
      this.budget=Math.min(s.budget,s.steps+120000);
      try{
        const reduced=this.whnf(blocked);
        if(reduced!==blocked&&!this.same(reduced,blocked)){
          this.__majorDriveHits=(this.__majorDriveHits??0)+1;
          this.__majorDriveMax=Math.max(this.__majorDriveMax??0,this.steps-s.steps);
          this.budget=s.budget;
          return flip?this.equal(reduced,rigid,ctx):this.equal(rigid,reduced,ctx);
        }
      }catch(e){
        this.budget=s.budget;
        if(!fallbackable(e))throw e;
      }
      this.__majorDriveMisses=(this.__majorDriveMisses??0)+1;
      restore(this,s);
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
    majorDriveHits:seen.reduce((n,k)=>n+(k.__majorDriveHits??0),0),
    majorDriveMisses:seen.reduce((n,k)=>n+(k.__majorDriveMisses??0),0),
    maxMajorDrive:Math.max(0,...seen.map(k=>k.__majorDriveMax??0))};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
p.equal=retainedEqual;
const clean=rows.every(r=>r.status===r.want);
const out={experiment:"shared-subterm-major-spine-drive",clean,rows};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/shared-subterm-major-spine-drive.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_SUBTERM_MAJOR_SPINE_DRIVE "+JSON.stringify(out));
if(!clean)process.exit(1);
