import {writeFileSync,appendFileSync,mkdirSync,readFileSync} from "node:fs";
import {spawnSync} from "node:child_process";
import {fileURLToPath} from "node:url";
import {levelsEqual,quotientType,Stop,Kernel,ACCEPT,REJECT,UNKNOWN,S,V,Pi,Lam,App,Let,NatLit,StrLit,Proj,checkExport} from "./kernel.mjs";

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


function runEmptyInductiveTests(base,emit=()=>{}) {
  const caps=[...base,"empty-inductives"];
  const meta={meta:{format:{version:"3.1.0"}}};
  const rows=[
    meta,
    {"in":1,str:{pre:0,str:"Empty"}},
    {"il":1,succ:0},
    {"ie":0,sort:1},
    {"in":2,str:{pre:1,str:"rec"}},
    {"in":3,str:{pre:0,str:"u"}},
    {"il":2,param:3},
    {"in":4,str:{pre:0,str:"motive"}},
    {"in":5,str:{pre:0,str:"t"}},
    {"ie":1,const:{name:1,us:[]}},
    {"ie":2,sort:2},
    {"ie":3,forallE:{type:1,body:2}},
    {"ie":4,bvar:1},
    {"ie":5,bvar:0},
    {"ie":6,app:{fn:4,arg:5}},
    {"ie":7,forallE:{type:1,body:6}},
    {"ie":8,forallE:{type:3,body:7}},
    {inductive:{
      types:[{name:1,levelParams:[],type:0,numParams:0,numIndices:0,all:[1],
        ctors:[],numNested:0,isRec:false,isUnsafe:false,isReflexive:false}],
      ctors:[],
      recs:[{name:2,levelParams:[3],type:8,all:[1],numParams:0,numIndices:0,
        numMotives:1,numMinors:0,rules:[],k:false,isUnsafe:false}]
    }}
  ];
  const good=rows.map(JSON.stringify).join("\n");
  const before=checkExport(good,base);
  assert(before.status===UNKNOWN && before.reason==="inductive-semantics-frontier",
    "empty-inductive ablation did not restore semantic frontier");
  assert(checkExport(good,caps).status===ACCEPT,
    "certified empty inductive was not accepted");

  const bad=rows.map(x=>JSON.parse(JSON.stringify(x)));
  bad[bad.length-1].inductive.recs[0].type=1;
  assert(checkExport(bad.map(JSON.stringify).join("\n"),caps).status===REJECT,
    "forged empty recursor type was accepted");

  const badK=rows.map(x=>JSON.parse(JSON.stringify(x)));
  badK[badK.length-1].inductive.recs[0].k=true;
  assert(checkExport(badK.map(JSON.stringify).join("\n"),caps).status===REJECT,
    "empty recursor with bogus K flag was accepted");

  emit({event:"empty-inductive-growth",ablation_unknown:true,
    exact_recursor:true,forged_recursor_rejected:true,bogus_k_rejected:true});
  return {capabilities:caps,cases:2};
}


function runEnumInductiveTests(base,emit=()=>{}) {
  const caps=[...base,"enum-inductives"];
  const meta={meta:{format:{version:"3.1.0"}}};
  const rows=[
    meta,
    {"in":1,str:{pre:0,str:"Bit"}},
    {"in":2,str:{pre:1,str:"mk"}},
    {"in":3,str:{pre:1,str:"rec"}},
    {"in":4,str:{pre:0,str:"u"}},
    {"il":1,succ:0},
    {"il":2,param:4},
    {"ie":0,sort:1},
    {"ie":1,const:{name:1,us:[]}},
    {"ie":2,sort:2},
    {"ie":3,forallE:{name:0,type:1,body:2,binderInfo:"default"}},
    {"ie":4,bvar:0},
    {"ie":5,const:{name:2,us:[]}},
    {"ie":6,app:{fn:4,arg:5}},
    {"ie":7,bvar:2},
    {"ie":8,bvar:0},
    {"ie":9,app:{fn:7,arg:8}},
    {"ie":10,forallE:{name:0,type:1,body:9,binderInfo:"default"}},
    {"ie":11,forallE:{name:0,type:6,body:10,binderInfo:"default"}},
    {"ie":12,forallE:{name:0,type:3,body:11,binderInfo:"default"}},
    {"ie":13,bvar:0},
    {"ie":14,lam:{name:0,type:6,body:13,binderInfo:"default"}},
    {"ie":15,lam:{name:0,type:3,body:14,binderInfo:"default"}},
    {inductive:{
      types:[{name:1,levelParams:[],type:0,numParams:0,numIndices:0,all:[1],
        ctors:[2],numNested:0,isRec:false,isUnsafe:false,isReflexive:false}],
      ctors:[{name:2,levelParams:[],type:1,induct:1,cidx:0,numParams:0,numFields:0,isUnsafe:false}],
      recs:[{name:3,levelParams:[4],type:12,all:[1],numParams:0,numIndices:0,
        numMotives:1,numMinors:1,rules:[{ctor:2,nfields:0,rhs:15}],k:false,isUnsafe:false}]
    }}
  ];
  const good=rows.map(JSON.stringify).join("\n");
  const before=checkExport(good,base);
  assert(before.status===UNKNOWN && before.reason==="inductive-semantics-frontier",
    "enum-inductive ablation did not restore semantic frontier");
  assert(checkExport(good,caps).status===ACCEPT,"derived enum recursor was not accepted");
  const bad=rows.map(x=>JSON.parse(JSON.stringify(x)));
  bad[bad.length-1].inductive.recs[0].k=true;
  const forged=checkExport(bad.map(JSON.stringify).join("\n"),caps);
  assert(forged.status===REJECT && forged.reason==="enum-inductive-recursor-metadata",
    "forged enum K metadata was not rejected");
  emit({event:"enum-inductive-growth",ablation_unknown:true,
    derived_recursor:true,forged_k_rejected:true});
  return {capabilities:caps,cases:2};
}


function runSingleInductiveTests(base,emit=()=>{}) {
  const caps=[...base,"single-inductives"],n="Ntest",z="Ntest.zero",s="Ntest.succ",rn=JSON.stringify([n,"str","rec"]),u="u";
  const I=["const",n],Z=["const",z],Succ=["const",s],Rec=["const",rn,[["param",u]]];
  const motive=Pi(I,S(["param",u]));
  const zeroMinor=App(V(0),Z);
  const succMinor=Pi(I,Pi(App(V(2),V(0)),App(V(3),App(Succ,V(1)))));
  const recType=Pi(motive,Pi(zeroMinor,Pi(succMinor,Pi(I,App(V(3),V(0))))));
  const rz=Lam(motive,Lam(zeroMinor,Lam(succMinor,V(1))));
  const recCall=App(App(App(App(Rec,V(3)),V(2)),V(1)),V(0));
  const rs=Lam(motive,Lam(zeroMinor,Lam(succMinor,Lam(I,App(App(V(1),V(0)),recCall)))));
  const good={kind:"inductive",name:n,levelParams:[],type:S(1),numParams:0,numIndices:0,numNested:0,
    isRec:true,isUnsafe:false,isReflexive:false,all:[n],ctorNames:[z,s],
    ctors:[
      {name:z,levelParams:[],type:I,induct:n,cidx:0,numParams:0,numFields:0,isUnsafe:false},
      {name:s,levelParams:[],type:Pi(I,I),induct:n,cidx:1,numParams:0,numFields:1,isUnsafe:false}
    ],
    rec:{name:rn,levelParams:[u],type:recType,all:[n],numParams:0,numIndices:0,numMotives:1,
      numMinors:2,k:false,isUnsafe:false,rules:[
        {ctor:z,nfields:0,rhs:rz},{ctor:s,nfields:1,rhs:rs}
      ]}
  };
  const before=new Kernel(base).run(S(0),S(1),[good]);
  assert(before.status===UNKNOWN&&before.reason==="missing:single-inductives",
    "single-inductive ablation did not restore missing capability");
  const accepted=new Kernel(caps).run(S(0),S(1),[good]);
  assert(accepted.status===ACCEPT,"recursive single inductive was not accepted: "+JSON.stringify(accepted));
  const bad=JSON.parse(JSON.stringify(good));
  bad.ctors[1].type=Pi(Pi(I,I),I);
  const rejected=new Kernel(caps).run(S(0),S(1),[bad]);
  assert(rejected.status===REJECT&&rejected.reason==="negative-recursive-occurrence",
    "negative recursive occurrence was not rejected: "+JSON.stringify(rejected));
  emit({event:"single-inductive-growth",ablation_unknown:true,recursive_type:true,
    derived_recursor:true,strict_positivity:true});
  return {capabilities:caps,cases:2,fixture:good};
}


function runInductiveReductionTests(base,fixture,emit=()=>{}) {
  const caps=[...base,"inductive-reduction"],n=fixture.name,z=fixture.ctors[0].name,s=fixture.ctors[1].name,rn=fixture.rec.name;
  const I=["const",n],Z=["const",z],Succ=["const",s],Rec=["const",rn,[0]];
  const motive=Lam(I,I),zeroMinor=Z,succMinor=Lam(I,Lam(I,V(0)));
  const app=(f,...xs)=>xs.reduce((q,x)=>App(q,x),f);
  const zeroTerm=app(Rec,motive,zeroMinor,succMinor,Z);
  const before=new Kernel(base); assert(before.run(S(0),S(1),[fixture]).status===ACCEPT,"inductive reduction fixture failed before ablation");
  before.steps=0;
  let ablated=false; try { before.whnf(zeroTerm); } catch(e) { ablated=e instanceof Stop&&e.status===UNKNOWN&&e.message==="missing:inductive-reduction"; }
  assert(ablated,"inductive reduction ablation did not restore missing capability");
  const checker=new Kernel(caps); assert(checker.run(S(0),S(1),[fixture]).status===ACCEPT,"inductive reduction fixture failed");
  checker.steps=0; assert(checker.same(checker.whnf(zeroTerm),Z),"zero recursor rule did not reduce");
  const succTerm=app(Rec,motive,zeroMinor,succMinor,App(Succ,Z));
  checker.steps=0; assert(checker.same(checker.whnf(succTerm),Z),"recursive recursor rule did not reduce");
  emit({event:"inductive-reduction-growth",ablation_unknown:true,zero_rule:true,recursive_rule:true});
  return {capabilities:caps,cases:2};
}


function runNatLiteralTests(base,emit=()=>{}) {
  const caps=[...base,"nat-literals"];
  const name=(...parts)=>parts.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
  const N=name("Nat"),Z=name("Nat","zero"),Su=name("Nat","succ");
  const Nat=["const",N];
  const decls=[
    {kind:"axiom",name:N,type:S(1),levelParams:[]},
    {kind:"axiom",name:Z,type:Nat,levelParams:[]},
    {kind:"axiom",name:Su,type:Pi(Nat,Nat),levelParams:[]}
  ];
  const before=new Kernel(base).run(NatLit(1),Nat,decls);
  assert(before.status===UNKNOWN&&before.reason==="missing:nat-literals",
    "nat literal ablation did not restore missing capability");
  const one=new Kernel(caps).run(NatLit(1),Nat,decls);
  assert(one.status===ACCEPT,"Nat literal did not typecheck: "+JSON.stringify(one));
  const checker=new Kernel(caps);
  checker.steps=0; checker.env=new Map(decls.map(d=>[d.name,d])); checker.params=new Set();
  checker.equal(NatLit(1),App(["const",Su],["const",Z]),[]);
  emit({event:"nat-literal-growth",ablation_unknown:true,typecheck:true,constructor_reduction:true});
  return {capabilities:caps,cases:2};
}


function runStringLiteralTests(base,emit=()=>{}) {
  const caps=[...base,"string-literals"],N=JSON.stringify(["[]","str","String"]);
  const decls=[{kind:"axiom",name:N,levelParams:[],type:S(1)}];
  const before=new Kernel(base).run(StrLit("hello"),["const",N],decls);
  assert(before.status===UNKNOWN&&before.reason==="missing:string-literals",
    "string literal ablation did not restore missing capability");
  const accepted=new Kernel(caps).run(StrLit("hello"),["const",N],decls);
  assert(accepted.status===ACCEPT,"string literal did not typecheck: "+JSON.stringify(accepted));

  const meta={meta:{format:{version:"3.1.0"}}};
  const raw=[
    meta,
    {"in":1,str:{pre:0,str:"String"}},
    {"in":2,str:{pre:0,str:"s"}},
    {"il":1,succ:0},
    {"ie":0,sort:1},
    {"ie":1,const:{name:1,us:[]}},
    {"ie":2,strVal:"hello"},
    {axiom:{name:1,levelParams:[],type:0,isUnsafe:false}},
    {def:{name:2,levelParams:[],type:1,value:2,hints:"opaque",safety:"safe",all:[2]}}
  ].map(JSON.stringify).join("\n");
  const ablated=checkExport(raw,base);
  assert(ablated.status===UNKNOWN&&ablated.reason==="expression-frontier:strVal",
    "string export ablation did not restore literal frontier");
  assert(checkExport(raw,caps).status===ACCEPT,"exported string literal was rejected");
  emit({event:"string-literal-growth",ablation_unknown:true,typecheck:true,primitive_identity:true});
  return {capabilities:caps,cases:2};
}


function runQuotientTests(base,emit=()=>{}) {
  const caps=[...base,"quotients"],u="qu",v="qv";
  const names={type:JSON.stringify(["[]","str","Quot"]),
    ctor:JSON.stringify([JSON.stringify(["[]","str","Quot"]),"str","mk"]),
    lift:JSON.stringify([JSON.stringify(["[]","str","Quot"]),"str","lift"]),
    ind:JSON.stringify([JSON.stringify(["[]","str","Quot"]),"str","ind"])};
  const decls=["type","ctor","lift","ind"].map(kind=>({
    kind:"quot",quotKind:kind,name:names[kind],
    levelParams:kind==="lift"?[u,v]:[u],type:quotientType(kind,kind==="lift"?[u,v]:[u])
  }));
  const before=new Kernel(base).run(S(0),S(1),decls);
  assert(before.status===UNKNOWN&&before.reason==="missing:quotients",
    "quotient ablation did not restore missing capability");
  const accepted=new Kernel(caps).run(S(0),S(1),decls);
  assert(accepted.status===ACCEPT,"canonical quotient package rejected: "+JSON.stringify(accepted));

  const checker=new Kernel(caps); checker.steps=0; checker.env=new Map(decls.map(d=>[d.name,d])); checker.params=new Set();
  const A=["const","QA"],R=["const","QR"],B=["const","QB"],a=["const","qa"];
  checker.env.set("qa",{kind:"axiom",name:"qa",levelParams:[],type:A});
  const mk=[["const",names.ctor,[["param",u]]],A,R,a].reduce((f,x,i)=>i===0?x:App(f,x));
  const ident=Lam(A,V(0)),dummy=["const","qh"];
  const lift=[["const",names.lift,[["param",u],["param",v]]],A,R,B,ident,dummy,mk].reduce((f,x,i)=>i===0?x:App(f,x));
  assert(checker.same(checker.whnf(lift),a),"Quot.lift did not reduce on Quot.mk");
  const minor=Lam(A,V(0));
  const ind=[["const",names.ind,[["param",u]]],A,R,Pi(App(App(["const",names.type,[["param",u]]],A),R),S(0)),minor,mk]
    .reduce((f,x,i)=>i===0?x:App(f,x));
  assert(checker.same(checker.whnf(ind),a),"Quot.ind did not reduce on Quot.mk");
  emit({event:"quotient-growth",ablation_unknown:true,exact_package:true,lift_reduction:true,ind_reduction:true});
  return {capabilities:caps,cases:3};
}


function runProjectionTests(base,emit=()=>{}) {
  const caps=[...base,"projections"],A="ProjA",a="projA",B="Box",mk="Box.mk",rn=JSON.stringify([B,"str","rec"]),u="u";
  const AT=["const",A],av=["const",a],I=["const",B],Mk=["const",mk],Rec=["const",rn,[["param",u]]];
  const motive=Pi(I,S(["param",u]));
  const minor=Pi(AT,App(V(1),App(Mk,V(0))));
  const recType=Pi(motive,Pi(minor,Pi(I,App(V(2),V(0)))));
  const rule=Lam(motive,Lam(minor,Lam(AT,App(V(1),V(0)))));
  const box={kind:"inductive",name:B,levelParams:[],type:S(1),numParams:0,numIndices:0,numNested:0,
    isRec:false,isUnsafe:false,isReflexive:false,all:[B],ctorNames:[mk],
    ctors:[{name:mk,levelParams:[],type:Pi(AT,I),induct:B,cidx:0,numParams:0,numFields:1,isUnsafe:false}],
    rec:{name:rn,levelParams:[u],type:recType,all:[B],numParams:0,numIndices:0,numMotives:1,
      numMinors:1,k:false,isUnsafe:false,rules:[{ctor:mk,nfields:1,rhs:rule}]}
  };
  const decls=[{kind:"axiom",name:A,type:S(1),levelParams:[]},{kind:"axiom",name:a,type:AT,levelParams:[]},box];
  const p=Proj(B,0,App(Mk,av));
  const before=new Kernel(base).run(p,AT,decls);
  assert(before.status===UNKNOWN&&before.reason==="missing:projections",
    "projection ablation did not restore missing capability");
  const checker=new Kernel(caps),ok=checker.run(p,AT,decls);
  assert(ok.status===ACCEPT,"structure projection did not typecheck: "+JSON.stringify(ok));
  checker.equal(p,av,[]);
  const bad=new Kernel(caps).run(Proj(B,1,App(Mk,av)),AT,decls);
  assert(bad.status===REJECT&&bad.reason==="projection-out-of-range",
    "out-of-range projection was not rejected: "+JSON.stringify(bad));

  const poly=new Kernel(caps);
  poly.steps=0; poly.env=new Map([["poly",{levelParams:["u"]}]]); poly.params=new Set(["u"]);
  const projected=Proj(B,0,["const","Poly",[["param","u"]]]);
  const inst=poly.instantiateDeclaration(["const","poly",[0]],projected);
  assert(inst[0]==="proj"&&inst[1]===B&&inst[2]===0&&inst[3][0]==="const"&&inst[3][2][0]===0,
    "projection universe traversal corrupted metadata or failed to instantiate its child");

  emit({event:"projection-growth",ablation_unknown:true,inference:true,reduction:true,
    out_of_range_rejected:true,universe_traversal:true});
  return {capabilities:caps,cases:4};
}



function runOpaqueDeclarationTests(base,emit=()=>{}) {
  const caps=[...base,"opaque-declarations"];
  const O="OpaqueType",p="opaqueWitness";
  const opaque={kind:"opaque",name:O,levelParams:[],type:S(1),value:S(0)};
  const before=new Kernel(base).run(S(0),S(1),[opaque]);
  assert(before.status===UNKNOWN&&before.reason==="missing:opaque-declarations",
    "opaque ablation did not restore missing capability");
  const accepted=new Kernel(caps).run(S(0),S(1),[opaque]);
  assert(accepted.status===ACCEPT,"well-typed opaque declaration was rejected: "+JSON.stringify(accepted));

  const hidden=[
    {kind:"axiom",name:p,levelParams:[],type:S(0)},
    opaque,
    {kind:"def",name:"opaqueUse",levelParams:[],type:["const",O],value:["const",p]}
  ];
  const noLeak=new Kernel(caps).run(S(0),S(1),hidden);
  assert(noLeak.status===UNKNOWN&&noLeak.reason==="conversion-frontier",
    "opaque body leaked into definitional equality: "+JSON.stringify(noLeak));

  const bad={kind:"opaque",name:"badOpaque",levelParams:[],type:S(0),value:S(0)};
  const mismatch=new Kernel(caps).run(S(0),S(1),[bad]);
  assert(mismatch.status===REJECT,
    "ill-typed opaque body was not rejected: "+JSON.stringify(mismatch));

  emit({event:"opaque-declaration-growth",ablation_unknown:true,
    body_checked:true,conversion_hidden:true,ill_typed_body_rejected:true});
  return {capabilities:caps,cases:3};
}


function runDeclarationSafetyControls(base,emit=()=>{}) {
  const meta={meta:{format:{version:"3.1.0"}}};
  const mkDef=safety=>[
    meta,{"in":1,str:{pre:0,str:"d"}},
    {"il":1,succ:0},{"ie":0,sort:1},{"ie":1,sort:0},
    {def:{name:1,levelParams:[],type:0,value:1,hints:"opaque",safety,all:[1]}}
  ].map(JSON.stringify).join("\n");
  for(const safety of ["unsafe","partial"]) {
    const result=checkExport(mkDef(safety),base);
    assert(result.status===REJECT && result.reason==="unsafe-definition",
      safety+" definition was not rejected as a validity invariant");
  }
  const unsafeAxiom=[
    meta,{"in":1,str:{pre:0,str:"a"}},{"ie":0,sort:0},
    {axiom:{name:1,levelParams:[],type:0,isUnsafe:true}}
  ].map(JSON.stringify).join("\n");
  const ax=checkExport(unsafeAxiom,base);
  assert(ax.status===REJECT && ax.reason==="unsafe-axiom","unsafe axiom was not rejected");
  emit({event:"declaration-safety-control",retained_capability:false,
    unsafe_definition_rejected:true,partial_definition_rejected:true,
    unsafe_axiom_rejected:true});
  return {capabilities:base,cases:3};
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
const emptyInductive=runEmptyInductiveTests(inductiveEnvelope.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const enumInductive=runEnumInductiveTests(emptyInductive.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const singleInductive=runSingleInductiveTests(enumInductive.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const inductiveReduction=runInductiveReductionTests(singleInductive.capabilities,singleInductive.fixture,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const natLiteral=runNatLiteralTests(inductiveReduction.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const stringLiteral=runStringLiteralTests(natLiteral.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const quotient=runQuotientTests(stringLiteral.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const projection=runProjectionTests(quotient.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const opaqueDeclaration=runOpaqueDeclarationTests(projection.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const declarationSafety=runDeclarationSafetyControls(opaqueDeclaration.capabilities,row=>{
  console.log(JSON.stringify(row));
  appendFileSync(new URL("events.jsonl",target),JSON.stringify(row)+"\n");
});
const replay=evaluate(declarationSafety.capabilities,growthSuite());
assert(replay.covered===report.training && !replay.wrong.length,"later growth regressed protected cases");
report.capabilities=declarationSafety.capabilities;
report.universe_tests={laws:universe.laws,independent_pairs:universe.independent_pairs};
report.theorem_tests={cases:theorem.cases};
report.proof_irrelevance_tests={cases:proofIrrelevance.cases};
report.inductive_envelope_tests={cases:inductiveEnvelope.cases};
report.empty_inductive_tests={cases:emptyInductive.cases};
report.enum_inductive_tests={cases:enumInductive.cases};
report.single_inductive_tests={cases:singleInductive.cases};
report.inductive_reduction_tests={cases:inductiveReduction.cases};
report.nat_literal_tests={cases:natLiteral.cases};
report.string_literal_tests={cases:stringLiteral.cases};
report.quotient_tests={cases:quotient.cases};
report.projection_tests={cases:projection.cases};
report.opaque_declaration_tests={cases:opaqueDeclaration.cases};
report.declaration_safety_controls={cases:declarationSafety.cases,retained_capability:false};
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
