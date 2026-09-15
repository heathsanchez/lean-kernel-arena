import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
import {installBetaEnvironmentClosures} from "./beta-environment-closure-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

const TARGETS=[
 ["perf/shared-subterm","ACCEPT",true],
 ["perf/church-numerals","ACCEPT",false],
 ["perf/args-before-unfold","ACCEPT",false],
 ["perf/folded-constant-first","ACCEPT",false],
 ["perf/repeated-subproblem","ACCEPT",false],
 ["perf/discarded-argument-match","ACCEPT",false],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT",false],
 ["undecidability/alg-conv-trans-acc-right","ACCEPT",false],
 ["undecidability/subject-reduction-redex","ACCEPT",false],
 ["undecidability/alg-conv-trans-acc","REJECT",false],
 ["undecidability/subject-reduction-reduct","REJECT",false]
];

const p=K.Kernel.prototype;
function evaluate(enabled){
  installBetaEnvironmentClosures(enabled);
  const rows=[];
  for(const [name,want,focus] of TARGETS){
    const seen=[],baseRun=p.run;
    p.run=function(...xs){seen.push(this);return baseRun.apply(this,xs);};
    const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
    const t0=Date.now();let r;
    try{r=K.checkExport(input,CAPS,1_000_000);}
    finally{p.run=baseRun;}
    const stats={closureSpines:0,betaReductions:0,envHeadLookups:0,envLookups:0,
      letEnvExtensions:0,materializedVisits:0,reusedClosed:0,reusedNoEnv:0,
      supportHits:0,supportStores:0,fallbacks:0};
    for(const k of seen)for(const q of Object.keys(stats))stats[q]+=k.__betaEnvStats?.[q]??0;
    rows.push({name,want,focus,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
      elapsed_ms:Date.now()-t0,stats});
  }
  return rows;
}

const baseline=evaluate(false),candidate=evaluate(true);
installBetaEnvironmentClosures(false);
const comparisons=TARGETS.map(([name,want,focus],i)=>{
  const b=baseline[i],c=candidate[i];
  return {name,want,focus,before:{status:b.status,reason:b.reason,steps:b.steps,constructed:b.constructed,elapsed_ms:b.elapsed_ms},
    after:{status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed,elapsed_ms:c.elapsed_ms},
    stats:c.stats,
    statusChanged:b.status!==c.status,
    stepDelta:(c.steps??0)-(b.steps??0),
    constructedDelta:(c.constructed??0)-(b.constructed??0)};
});
for(const row of comparisons)console.log("ROW "+JSON.stringify(row));

const shared=comparisons[0];
const protectedChanged=comparisons.slice(1).filter(r=>r.after.status!==r.before.status);
const protectedWrong=comparisons.slice(1).filter(r=>r.after.status!==r.want);
const sharedClosed=shared.after.status==="ACCEPT";
const sharedImproved=sharedClosed ||
  ((shared.after.constructed??Infinity)<(shared.before.constructed??Infinity) &&
   shared.stats.closureSpines>0 && shared.stats.betaReductions>0);
const out={experiment:"beta-environment-closure-separator",budget:1_000_000,
  sharedClosed,sharedImproved,protectedChanged:protectedChanged.length,protectedWrong:protectedWrong.length,
  lawful:protectedChanged.length===0&&protectedWrong.length===0,
  promotable:sharedClosed&&protectedChanged.length===0&&protectedWrong.length===0,
  comparisons,
  claim_boundary:"Execution-only multi-beta WHNF separator. Eliminated lambda binders are retained in a transient de-Bruijn environment; application arguments remain closures until WHNF reaches an ordinary-term boundary. Closed subterms are reused by identity after an accounted support analysis. Closures never enter stored syntax, inference, equality, declarations, or the external result. Any non-target/hard path falls back to the frozen retained WHNF."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/beta-environment-closure-separator.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("BETA_ENVIRONMENT_CLOSURE_SEPARATOR "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
