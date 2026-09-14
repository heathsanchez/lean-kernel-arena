import {writeFileSync,appendFileSync,mkdirSync,readFileSync} from "node:fs";
import {spawnSync} from "node:child_process";
import {fileURLToPath} from "node:url";
import {Stop,Kernel,ACCEPT,REJECT,UNKNOWN,S,V,Pi,Lam,App,Let,checkExport} from "./kernel.mjs";

function growthSuite() {
  const C=(name,term,type,expected=ACCEPT,declarations=[])=>({name,term,type,expected,declarations});
  const id=Lam(S(1),Lam(V(0),V(0)));
  const idTy=Pi(S(1),Pi(V(0),V(1)));
  return [
    C("sort",S(0),S(1)), C("bad-sort",S(1),S(0),REJECT),
    C("identity",Lam(S(0),V(0)),Pi(S(0),S(0))),
    C("unbound",Lam(S(0),V(1)),Pi(S(0),S(0)),REJECT),
    C("dependent-identity",id,idTy),
    C("application",App(Lam(S(1),V(0)),S(0)),S(1)),
    C("bad-argument",App(Lam(S(0),V(0)),S(0)),S(0),REJECT),
    C("nonfunction",App(S(0),S(0)),S(0),REJECT),
    C("beta-type",S(0),App(Lam(S(2),V(0)),S(1))),
    C("let",Let(S(1),S(0),V(0)),S(1)),
    C("bad-let",Let(S(0),S(0),V(0)),S(0),REJECT),
    C("let-type-used",Let(S(1),S(0),Lam(V(0),V(0))),Pi(S(0),S(0))),
    C("constant",["const","p"],["const","P"],ACCEPT,[{kind:"axiom",name:"P",type:S(0)},{kind:"axiom",name:"p",type:["const","P"]}]),
    C("self-reference",S(0),S(1),REJECT,[{kind:"def",name:"x",type:S(1),value:["const","x"]}]),
    C("bad-declaration-type",S(0),S(1),REJECT,[{kind:"axiom",name:"x",type:Lam(S(0),V(0))}]),
    C("delta-type",S(0),["const","T"],ACCEPT,[{kind:"def",name:"T",type:S(2),value:S(1)}]),
  ];
}
function evaluate(caps,cases,budget=50000) {
  const rows=cases.map(c=>({...new Kernel(caps,budget).run(c.term,c.type,c.declarations),name:c.name,expected:c.expected}));
  return {rows,covered:rows.filter(r=>r.status===r.expected).length,
    wrong:rows.filter(r=>r.status!==UNKNOWN && r.status!==r.expected),
    steps:rows.reduce((s,r)=>s+r.steps,0)};
}
function assert(b,message) {if(!b) throw new Error(message);}
function runGrowth(emit=()=>{}) {
  const cases=growthSuite(), available=["sort-direct","sort","binders","application","reduction","declarations"];
  let caps=[],baseline=evaluate(caps,cases),protectedNames=new Set(),history=[];
  const record=row=>{history.push(row);emit(row);};
  record({event:"seed",capabilities:caps,covered:baseline.covered,total:cases.length});
  assert(baseline.rows.every(r=>r.status===UNKNOWN),"seed must decline everything");
  while(baseline.covered<cases.length) {
    const absent=available.filter(c=>!caps.includes(c)), candidates=[];
    // Enumerate single additions, then pairs only if the current language cannot progress.
    for(let width=1;width<=2 && !candidates.length;width++) {
      const proposals=width===1?absent.map(a=>[a]):absent.flatMap((a,i)=>absent.slice(i+1).map(b=>[a,b]));
      for(const added of proposals) {
        const trial=[...caps,...added],r=evaluate(trial,cases);
        if(r.wrong.length || r.covered<=baseline.covered) continue;
        if(r.rows.some(x=>protectedNames.has(x.name)&&x.status!==x.expected)) continue;
        candidates.push({trial,added,r});
      }
    }
    assert(candidates.length,"growth frontier needs a new candidate implementation");
    candidates.sort((a,b)=>b.r.covered-a.r.covered || a.r.steps-b.r.steps || a.added.join().localeCompare(b.added.join()));
    const best=candidates[0],before=baseline.covered;
    const ablated=evaluate(caps,cases);
    assert(ablated.covered===before && best.r.covered>before,"addition has no causal gain");
    caps=best.trial; baseline=best.r;
    protectedNames=new Set(baseline.rows.filter(r=>r.status===r.expected).map(r=>r.name));
    record({event:"grow",added:best.added,covered:baseline.covered,total:cases.length,
      wrong:baseline.wrong.length,ablated_coverage:ablated.covered,steps:baseline.steps});
    // Try all deletions after every growth; no replay regression and no increase in counted work.
    for(const cap of [...caps]) {
      const smaller=caps.filter(x=>x!==cap),r=evaluate(smaller,cases);
      if(r.wrong.length===0 && r.covered===baseline.covered && r.steps<=baseline.steps &&
         r.rows.every(x=>!protectedNames.has(x.name)||x.status===x.expected)) {
        caps=smaller;baseline=r;
        record({event:"dissolve",removed:cap,covered:r.covered,steps:r.steps});
      }
    }
  }
  const heldout=[];
  for(let n=2;n<=25;n++) {
    heldout.push({name:"fresh-sort-"+n,term:S(n),type:S(n+1),expected:ACCEPT,declarations:[]});
    heldout.push({name:"fresh-sort-bad-"+n,term:S(n),type:S(n),expected:REJECT,declarations:[]});
    heldout.push({name:"fresh-id-"+n,term:Lam(S(n),Lam(V(0),V(0))),type:Pi(S(n),Pi(V(0),V(1))),expected:ACCEPT,declarations:[]});
    heldout.push({name:"fresh-capture-"+n,term:App(Lam(S(n+1),Lam(S(n+1),V(1))),S(n)),type:Pi(S(n+1),S(n+1)),expected:ACCEPT,declarations:[]});
  }
  const fresh=evaluate(caps,heldout);
  assert(fresh.covered===heldout.length,"heldout failure: "+JSON.stringify(fresh.rows.filter(r=>r.status!==r.expected)));
  record({event:"heldout",covered:fresh.covered,total:heldout.length,wrong:fresh.wrong.length});
  assert(new Kernel(caps,1).run(S(0),S(1)).status===UNKNOWN,"exhaustion became a verdict");
  const trap=[...cases,{name:"unsupported",term:["quot"],type:S(0),expected:UNKNOWN,declarations:[]}];
  assert(evaluate(caps,trap).rows.at(-1).status===UNKNOWN,"unsupported syntax accepted");
  const allAccept=cases.filter(c=>c.expected===REJECT).length;
  assert(allAccept>0,"test harness would allow accept-all");
  // Actual source mutation replaces the successor rule in both paths.
  const mutSource=Kernel.toString().replaceAll('term[1]+1','term[1]').replaceAll('e[1]+1','e[1]');
  const Mutant=new Function("Stop","ACCEPT","REJECT","UNKNOWN","return ("+mutSource+")")(Stop,ACCEPT,REJECT,UNKNOWN);
  assert(new Mutant(caps).run(S(0),S(1)).status!==ACCEPT,"sort mutation survived");
  // Validate a let-bound type before substituting it through a dependent body.
  const letCase=cases.find(c=>c.name==="let-type-used");
  assert(new Kernel(caps).run(letCase.term,letCase.type).status===ACCEPT,"let context lost its definition");
  record({event:"controls",budget_unknown:true,unsupported_unknown:true,sort_mutant_killed:true,
    accept_all_caught:allAccept,programming_errors_are_not_rejections:true});
  return {status:"PASS",scope:"monomorphic fragment; finite tests, not a complete or proven-sound Lean kernel",
    capabilities:caps,training:cases.length,heldout:heldout.length,history};
}

const target=new URL("./evidence/",import.meta.url);
mkdirSync(target,{recursive:true});
writeFileSync(new URL("events.jsonl",target),"");
const started=Date.now();
const report=runGrowth(row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
for(const name of ["level-index-out-of-order","sparse-name-index"]) {
  const raw=readFileSync(new URL("../tests/"+name+".ndjson",import.meta.url),"utf8");
  const r=checkExport(raw,report.capabilities);
  assert(r.status===ACCEPT,"repository Arena fixture failed: "+name+" "+JSON.stringify(r));
  console.log(JSON.stringify({event:"arena-fixture",name,...r}));
}
// A real exported axiom must have a type. Here the type is a lambda, not a type.
const meta={meta:{format:{version:"3.1.0"}}};
const badAxiom=[
 meta,{"in":1,str:{pre:0,str:"bad"}},{"ie":0,sort:0},{"ie":1,bvar:0},
 {"ie":2,lam:{name:0,type:0,body:1,binderInfo:"default"}},
 {axiom:{name:1,type:2,levelParams:[],isUnsafe:false}}
].map(JSON.stringify).join("\n");
assert(checkExport(badAxiom,report.capabilities).status===REJECT,"non-type axiom accepted");
assert(checkExport(badAxiom,[]).status===UNKNOWN,"empty export checker has hidden capability");
writeFileSync(new URL("retained.json",target),JSON.stringify(report.capabilities)+"\n");
const cli=fileURLToPath(new URL("./check.mjs",import.meta.url));
const state=fileURLToPath(new URL("retained.json",target));
const good=readFileSync(new URL("../tests/sparse-name-index.ndjson",import.meta.url),"utf8");
for(const [label,input,expected] of [["valid",good,0],["invalid",badAxiom,1],["unsupported",JSON.stringify(meta)+"\n"+JSON.stringify({quot:{}}),2]]) {
  const r=spawnSync(process.execPath,[cli,"--state",state],{input,encoding:"utf8",timeout:2000});
  assert(!r.error && r.signal===null && r.status===expected,"CLI contract failed: "+label+" "+JSON.stringify(r));
  const verdict=JSON.parse(r.stdout);
  assert(verdict.status===[ACCEPT,REJECT,UNKNOWN][expected],"stdout verdict mismatch");
}
// Reproduce the old harness error in milliseconds: exit zero with empty stdout is success.
const silent=spawnSync(process.execPath,["-e","process.exit(0)"],{encoding:"utf8",timeout:2000});
assert(silent.status===0 && silent.stdout==="","silent-success control failed");
report.cli_contract="PASS";report.arena_repository_fixtures=2;
report.negative_export="PASS";report.elapsed_ms=Date.now()-started;
report.runtime={node:process.version,platform:process.platform,arch:process.arch};
writeFileSync(new URL("summary.json",target),JSON.stringify(report,null,2)+"\n");
console.log("FAST_GROWTH_PASS "+JSON.stringify({training:report.training,heldout:report.heldout,elapsed_ms:report.elapsed_ms}));
