import {writeFileSync,appendFileSync,mkdirSync,readFileSync} from "node:fs";
import {spawnSync} from "node:child_process";
import {fileURLToPath} from "node:url";
import {levelsEqual,Stop,Kernel,ACCEPT,REJECT,UNKNOWN,S,V,Pi,Lam,App,Let,checkExport} from "./kernel.mjs";

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


function runUniverseTests(emit=()=>{}) {
  const base=["sort","binders","application","reduction","declarations"],caps=[...base,"universes"];
  const u=["param","u"],v=["param","v"],succ=x=>["succ",x],max=(a,b)=>["max",a,b],imax=(a,b)=>["imax",a,b];
  const pairs=[
    ["commutativity",max(u,v),max(v,u),true],
    ["absorption",max(u,succ(u)),succ(u),true],
    ["imax-zero",imax(u,0),0,true],
    ["imax-one",imax(u,1),max(u,1),true],
    ["imax-param",imax(0,u),u,true],
    ["zero-branch-trap",imax(1,u),max(1,u),false],
    ["distinct-parameters",u,v,false],
    ["successor-trap",succ(u),u,false],
    ["nested-imax",imax(u,imax(v,u)),imax(max(u,v),u),true],
    ["empty-name",["param",""],0,false],
  ];
  for(const [name,a,b,expected] of pairs) assert(levelsEqual(a,b)===expected,"level law failed: "+name);
  const judgment={term:S(u),type:S(succ(u))};
  assert(new Kernel(base).run(judgment.term,judgment.type,[],["u"]).status===UNKNOWN,"ablation did not restore universe frontier");
  assert(new Kernel(caps).run(judgment.term,judgment.type,[],["u"]).status===ACCEPT,"polymorphic sort failed");
  assert(new Kernel(caps).run(S(u),S(u),[],["u"]).status===REJECT,"Sort u : Sort u accepted");
  assert(new Kernel(caps).run(S(u),S(succ(u))).status===REJECT,"undeclared universe accepted");
  const declarations=[{name:"poly",kind:"def",levelParams:["u"],type:Pi(S(u),S(u)),value:Lam(S(u),V(0))}];
  assert(new Kernel(caps).run(["const","poly",[1]],Pi(S(1),S(1)),declarations).status===ACCEPT,"universe instantiation failed");
  assert(new Kernel(caps).run(["const","poly"],Pi(S(1),S(1)),declarations).status===REJECT,"wrong universe arity accepted");
  // Independent numeric denotation checks never authorize equality; they refute a broken algorithm.
  function numeric(e,env) {
    if(typeof e==="number") return e;
    if(e[0]==="param") return env[e[1]];
    if(e[0]==="succ") return numeric(e[1],env)+1;
    const a=numeric(e[1],env),b=numeric(e[2],env);
    return e[0]==="imax"&&b===0?0:Math.max(a,b);
  }
  const es=[0,1,2,u,v,succ(u),succ(v),imax(1,u),max(u,v),imax(u,v),imax(v,u),succ(imax(u,v)),max(succ(u),v),imax(max(2,u),succ(v))];
  let checked=0;
  for(const a of es) for(const b of es) {
    const eq=levelsEqual(a,b); let witnessed=false;
    for(let x=0;x<=5;x++) for(let y=0;y<=5;y++) if(numeric(a,{u:x,v:y})!==numeric(b,{u:x,v:y})) witnessed=true;
    assert(eq?!witnessed:witnessed,"finite independent cross-check disagreed");
    checked++;
  }
  emit({event:"universe-growth",laws:pairs.length,independent_pairs:checked,ablation_unknown:true,
    undeclared_parameter_rejected:true,wrong_arity_rejected:true});
  return {capabilities:caps,laws:pairs.length,independent_pairs:checked};
}


function runTheoremTests(base,emit=()=>{}) {
  const caps=[...base,"theorems"];
  const propIdTy=Pi(S(0),Pi(V(0),V(1)));
  const propId=Lam(S(0),Lam(V(0),V(0)));
  const idThm={kind:"thm",name:"idThm",levelParams:[],type:propIdTy,value:propId};

  assert(new Kernel(base).run(S(0),S(1),[idThm]).status===UNKNOWN,
    "theorem ablation did not restore the declaration frontier");
  assert(new Kernel(caps).run(S(0),S(1),[idThm]).status===ACCEPT,
    "well-typed theorem rejected");

  const nonProp={kind:"thm",name:"nonProp",levelParams:[],type:S(0),value:S(0)};
  assert(new Kernel(caps).run(S(0),S(1),[nonProp]).status===REJECT,
    "non-proposition theorem accepted");

  const self={kind:"thm",name:"self",levelParams:[],type:propIdTy,value:["const","self"]};
  assert(new Kernel(caps).run(S(0),S(1),[self]).status===REJECT,
    "self-referential theorem accepted");

  const usesPrior={kind:"thm",name:"usesPrior",levelParams:[],type:propIdTy,value:["const","idThm"]};
  assert(new Kernel(caps).run(S(0),S(1),[idThm,usesPrior]).status===ACCEPT,
    "theorem could not refer to an earlier theorem");

  // Hand-written format-3.1 export for theorem idThm : ∀ p : Prop, p → p.
  const meta={meta:{format:{version:"3.1.0"}}};
  const goodExport=[
    meta,
    {"in":1,str:{pre:0,str:"idThm"}},
    {"ie":0,sort:0},
    {"ie":1,bvar:0},
    {"ie":2,bvar:1},
    {"ie":3,forallE:{type:1,body:2}},
    {"ie":4,forallE:{type:0,body:3}},
    {"ie":5,lam:{type:1,body:1}},
    {"ie":6,lam:{type:0,body:5}},
    {thm:{name:1,levelParams:[],type:4,value:6,all:[]}}
  ].map(JSON.stringify).join("\n");
  assert(checkExport(goodExport,base).status===UNKNOWN,
    "export theorem ablation did not return UNKNOWN");
  assert(checkExport(goodExport,caps).status===ACCEPT,
    "well-typed exported theorem rejected");

  const badExport=[
    meta,
    {"in":1,str:{pre:0,str:"badThm"}},
    {"ie":0,sort:0},
    {thm:{name:1,levelParams:[],type:0,value:0,all:[]}}
  ].map(JSON.stringify).join("\n");
  assert(checkExport(badExport,caps).status===REJECT,
    "exported theorem whose type is not Prop was accepted");

  emit({event:"theorem-growth",cases:7,ablation_unknown:true,
    proposition_gate:true,self_reference_rejected:true,prior_theorem_reference:true,
    theorem_body_opaque:true});
  return {capabilities:caps,cases:7};
}


function runProofIrrelevanceTests(base,emit=()=>{}) {
  const caps=[...base,"proof-irrelevance"];
  const C=n=>["const",n];
  const AtoP=Pi(C("A"),C("P"));
  const qAt=x=>App(C("Q"),x);
  const hAt=x=>App(V(0),C(x));
  const fooType=Pi(AtoP,qAt(hAt("b")));
  const barType=Pi(AtoP,qAt(hAt("a")));
  const decls=[
    {kind:"axiom",name:"A",levelParams:[],type:S(1)},
    {kind:"axiom",name:"a",levelParams:[],type:C("A")},
    {kind:"axiom",name:"b",levelParams:[],type:C("A")},
    {kind:"axiom",name:"P",levelParams:[],type:S(0)},
    {kind:"axiom",name:"Q",levelParams:[],type:Pi(C("P"),S(0))},
    {kind:"axiom",name:"foo",levelParams:[],type:fooType},
    {kind:"thm",name:"bar",levelParams:[],type:barType,value:C("foo")}
  ];
  const before=new Kernel(base).run(S(0),S(1),decls);
  assert(before.status===UNKNOWN && before.reason==="conversion-frontier",
    "proof-irrelevance ablation did not restore the exact conversion frontier");
  assert(new Kernel(caps).run(S(0),S(1),decls).status===ACCEPT,
    "proof irrelevance under a binder failed");

  // Negative control: ordinary data terms a,b : A must not become definitionally equal.
  const nonProof=[
    {kind:"axiom",name:"A",levelParams:[],type:S(1)},
    {kind:"axiom",name:"a",levelParams:[],type:C("A")},
    {kind:"axiom",name:"b",levelParams:[],type:C("A")},
    {kind:"axiom",name:"R",levelParams:[],type:Pi(C("A"),S(0))},
    {kind:"axiom",name:"ra",levelParams:[],type:App(C("R"),C("a"))}
  ];
  const guard=new Kernel(caps).run(C("ra"),App(C("R"),C("b")),nonProof);
  assert(guard.status===UNKNOWN && guard.reason==="conversion-frontier",
    "proof irrelevance collapsed non-proof terms");

  emit({event:"proof-irrelevance-growth",ablation_unknown:true,
    binder_case:true,nonproof_negative_control:true});
  return {capabilities:caps,cases:2};
}


function runInductiveEnvelopeTests(base,emit=()=>{}) {
  const caps=[...base,"inductive-envelope"];
  const meta={meta:{format:{version:"3.1.0"}}};
  const nd=v=>[meta,{inductive:v}].map(JSON.stringify).join("\n");
  const valid={
    types:[{name:1}],ctors:[{name:2}],recs:[{name:3,numMinors:1}]
  };
  const ablated=checkExport(nd(valid),base);
  assert(ablated.status===UNKNOWN && ablated.reason==="declaration-frontier:inductive",
    "inductive envelope ablation did not restore the declaration frontier");
  const bounded=checkExport(nd(valid),caps);
  assert(bounded.status===UNKNOWN && bounded.reason==="inductive-semantics-frontier",
    "structurally valid inductive escaped the semantic frontier");

  const missingRec={types:[{name:1}],ctors:[],recs:[]};
  assert(checkExport(nd(missingRec),caps).status===REJECT,
    "inductive group missing its recursor was not rejected");

  const wrongMinors={types:[{name:1}],ctors:[{name:2}],recs:[{name:3,numMinors:0}]};
  assert(checkExport(nd(wrongMinors),caps).status===REJECT,
    "recursor/minor mismatch was not rejected");

  const dupCtor={
    types:[{name:1}],
    ctors:[{name:2},{name:2}],
    recs:[{name:3,numMinors:2}]
  };
  assert(checkExport(nd(dupCtor),caps).status===REJECT,
    "duplicate constructor identity was not rejected");

  emit({event:"inductive-envelope-growth",ablation_unknown:true,
    valid_remains_unknown:true,recursor_count:true,minor_count:true,
    constructor_identity:true});
  return {capabilities:caps,cases:4};
}

const target=new URL("./evidence/",import.meta.url);
mkdirSync(target,{recursive:true});
writeFileSync(new URL("events.jsonl",target),"");
const started=Date.now();
const report=runGrowth(row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const universe=runUniverseTests(row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const theorem=runTheoremTests(universe.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const proofIrrelevance=runProofIrrelevanceTests(theorem.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const inductiveEnvelope=runInductiveEnvelopeTests(proofIrrelevance.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const replay=evaluate(inductiveEnvelope.capabilities,growthSuite());
assert(replay.covered===report.training && !replay.wrong.length,"later growth regressed protected cases");
report.capabilities=inductiveEnvelope.capabilities;
report.universe_tests={laws:universe.laws,independent_pairs:universe.independent_pairs};
report.theorem_tests={cases:theorem.cases};
report.proof_irrelevance_tests={cases:proofIrrelevance.cases};
report.inductive_envelope_tests={cases:inductiveEnvelope.cases};
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
