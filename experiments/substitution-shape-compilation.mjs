// Prospective exact substitution-shape compilation.
//
// For immutable (body identity, initial depth), compile the de-Bruijn
// substitution transform once into a recipe:
//   STATIC(term) — result independent of the substituted argument
//   HOLE(shift)   — exact shifted argument
//   NODE(...)     — only paths connecting holes
//
// Instantiation for a new argument traverses only dynamic recipe paths.
// This is semantics-preserving execution compilation, not a new equality rule.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import * as K from "../genesis/kernel.mjs";

const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const BUDGET=1_000_000;
const p=K.Kernel.prototype;
const retainedRun=p.run,retainedSubstitute=p.substitute;

const STATIC=0,HOLE=1,NODE=2,PROJ=3;

function recipeMap(k,e){
  k.__substRecipe??=new WeakMap();
  let m=k.__substRecipe.get(e);
  if(!m){m=new Map();k.__substRecipe.set(e,m);}
  return m;
}

// Compile and simultaneously construct the static lowered result whenever the
// target variable is absent. Each node is visited once per (identity, depth).
function compile(k,root,depth){
  const cache=recipeMap(k,root);
  if(cache.has(depth)){k.__substRecipeCompileHits++;return cache.get(depth);}
  k.__substRecipeCompiles++;
  const work=[{kind:"visit",e:root,d:depth}],vals=[];
  while(work.length){
    const f=work.pop();
    if(f.kind==="build"){
      const children=new Array(f.n);
      for(let i=f.n-1;i>=0;i--)children[i]=vals.pop();
      const dynamic=children.some(r=>r.kind!==STATIC);
      let r;
      if(!dynamic){
        if(f.tag==="proj") r={kind:STATIC,term:k.make("proj",f.name,f.index,children[0].term)};
        else r={kind:STATIC,term:k.make(f.tag,...children.map(x=>x.term))};
      }else if(f.tag==="proj"){
        r={kind:PROJ,name:f.name,index:f.index,children};
      }else r={kind:NODE,tag:f.tag,children};
      recipeMap(k,f.e).set(f.d,r);
      vals.push(r);
      continue;
    }
    const e=f.e,d=f.d,m=recipeMap(k,e);
    if(m.has(d)){k.__substRecipeCompileHits++;vals.push(m.get(d));continue;}
    k.tick();
    let r;
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":
        r={kind:STATIC,term:e};m.set(d,r);vals.push(r);break;
      case "var":
        if(e[1]===d)r={kind:HOLE,shift:d};
        else if(e[1]>d)r={kind:STATIC,term:k.make("var",e[1]-1)};
        else r={kind:STATIC,term:e};
        m.set(d,r);vals.push(r);break;
      case "pi":case "lam":
        work.push({kind:"build",tag:e[0],n:2,e,d});
        work.push({kind:"visit",e:e[2],d:d+1});
        work.push({kind:"visit",e:e[1],d});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2,e,d});
        work.push({kind:"visit",e:e[2],d});
        work.push({kind:"visit",e:e[1],d});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2],n:1,e,d});
        work.push({kind:"visit",e:e[3],d});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3,e,d});
        work.push({kind:"visit",e:e[3],d:d+1});
        work.push({kind:"visit",e:e[2],d});
        work.push({kind:"visit",e:e[1],d});
        break;
      default:return null;
    }
  }
  return vals.pop();
}

function instantiate(k,recipe,arg){
  if(recipe.kind===STATIC)return recipe.term;
  if(recipe.kind===HOLE)return k.shift(arg,recipe.shift);
  const work=[{kind:"visit",r:recipe}],vals=[];
  while(work.length){
    const f=work.pop(),r=f.r;
    if(f.kind==="build"){
      const xs=new Array(f.n);
      for(let i=f.n-1;i>=0;i--)xs[i]=vals.pop();
      vals.push(f.kindTag==="proj"
        ?k.make("proj",f.name,f.index,xs[0])
        :k.make(f.tag,...xs));
      continue;
    }
    k.__substRecipeInstVisits++;
    if(r.kind===STATIC){vals.push(r.term);continue;}
    if(r.kind===HOLE){vals.push(k.shift(arg,r.shift));continue;}
    if(r.kind===PROJ){
      work.push({kind:"build",kindTag:"proj",name:r.name,index:r.index,n:1});
      work.push({kind:"visit",r:r.children[0]});
      continue;
    }
    work.push({kind:"build",kindTag:"node",tag:r.tag,n:r.children.length});
    for(let i=r.children.length-1;i>=0;i--)work.push({kind:"visit",r:r.children[i]});
  }
  return vals.pop();
}

function install(enabled){
  p.run=retainedRun;p.substitute=retainedSubstitute;
  if(!enabled)return;
  p.run=function(...args){
    this.__substRecipe=new WeakMap();
    this.__substRecipeCompiles=0;this.__substRecipeCompileHits=0;
    this.__substRecipeInstVisits=0;this.__substRecipeUses=0;
    return retainedRun.apply(this,args);
  };
  p.substitute=function(e,arg,depth=0){
    if(!Array.isArray(e))return retainedSubstitute.call(this,e,arg,depth);
    const r=compile(this,e,depth);
    if(r===null)return retainedSubstitute.call(this,e,arg,depth);
    this.__substRecipeUses++;
    return instantiate(this,r,arg);
  };
}
function evalOne(label,enabled){
  install(enabled);
  const input=readFileSync("_build/tests/perf/shared-subterm.ndjson","utf8");
  const seen=[],oldRun=p.run;
  p.run=function(...args){seen.push(this);return oldRun.apply(this,args);};
  const t=Date.now(),r=K.checkExport(input,CAPS,BUDGET);
  p.run=oldRun;
  return {label,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,elapsed_ms:Date.now()-t,
    stats:{
      compiles:seen.reduce((n,k)=>n+(k.__substRecipeCompiles??0),0),
      compileHits:seen.reduce((n,k)=>n+(k.__substRecipeCompileHits??0),0),
      uses:seen.reduce((n,k)=>n+(k.__substRecipeUses??0),0),
      instVisits:seen.reduce((n,k)=>n+(k.__substRecipeInstVisits??0),0)
    }};
}
const candidate=evalOne("candidate",true);
const baseline=evalOne("baseline",false);
install(false);
const summary={experiment:"substitution-shape-compilation",budget:BUDGET,baseline,candidate,
  resolved:candidate.status==="ACCEPT",
  lawful_focus:candidate.status==="ACCEPT"||candidate.status==="UNKNOWN",
  claim_boundary:"Exact de-Bruijn substitution compilation by immutable body identity and initial depth. Static lowered subtrees are compiled once; only argument-dependent recipe paths are instantiated. No semantic or equality rule changes."};
const out="genesis/evidence/substitution-shape-compilation.json";
mkdirSync(dirname(out),{recursive:true});
writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("SUBSTITUTION_SHAPE_COMPILATION "+JSON.stringify(summary));
if(candidate.status==="REJECT")process.exit(1);
