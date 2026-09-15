// Focused separator: carry exact substitutions through an entire beta
// application spine as a closure environment, then reify once. This targets
// beta-ladder's documented eager-substitution O(n^2) cost without changing
// ordinary WHNF when the fast path cannot complete successfully.
import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
if(createHash("sha256").update(data).digest("hex")!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
wanted={"beta-ladder.ndjson","app-lam.ndjson","let-ladder.ndjson","shift-cascade.ndjson","church-numerals.ndjson"}
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.rsplit("/",1)[-1] in wanted:
      p=m.name.split("/")
      rows.append({"name":m.name,"expected":"ACCEPT" if "good" in p else "REJECT","input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype;
const retainedRun=proto.run, retainedWhnf=proto.whnf;
const EMPTY=Object.freeze({size:0,head:null,tail:null});

function ensure(k){
  k.__betaEnvArray??=new WeakMap();
  k.__betaReify??=new WeakMap();
}
function extend(k,head,tail){
  k.tick();
  return {head,tail,size:tail.size+1};
}
function envArray(k,env){
  ensure(k);
  const old=k.__betaEnvArray.get(env);
  if(old) return old;
  const a=new Array(env.size);
  let p=env;
  for(let i=0;i<a.length;i++){ k.tick(); a[i]=p.head; p=p.tail; }
  k.__betaEnvArray.set(env,a);
  return a;
}
function reify(k,closure,lift=0){
  ensure(k);
  let byEnv=k.__betaReify.get(closure.term);
  if(!byEnv){byEnv=new WeakMap();k.__betaReify.set(closure.term,byEnv);}
  let byLift=byEnv.get(closure.env);
  if(!byLift){byLift=new Map();byEnv.set(closure.env,byLift);}
  if(byLift.has(lift)) return byLift.get(lift);

  const envVals=envArray(k,closure.env);
  function go(term,depth,extra){
    k.tick();
    switch(term[0]){
      case "sort": case "const": case "nat": case "strlit": return term;
      case "var":{
        const i=term[1];
        if(i<depth) return term;
        const j=i-depth;
        if(j<envVals.length) return reify(k,envVals[j],extra+depth);
        const out=depth+(j-envVals.length)+extra;
        return out===i?term:k.make("var",out);
      }
      case "pi": case "lam":
        return k.make(term[0],go(term[1],depth,extra),go(term[2],depth+1,extra));
      case "app":
        return k.make("app",go(term[1],depth,extra),go(term[2],depth,extra));
      case "proj":
        return k.make("proj",term[1],term[2],go(term[3],depth,extra));
      case "let":
        return k.make("let",go(term[1],depth,extra),go(term[2],depth,extra),go(term[3],depth+1,extra));
      default: k.unknown("beta-spine-reify-syntax");
    }
  }
  const out=go(closure.term,0,lift);
  byLift.set(lift,out);
  return out;
}
function reduceBetaSpine(k,e){
  let cur={term:e,env:EMPTY};
  const args=[];
  let crossed=0;
  for(;;){
    k.tick();
    const t=cur.term,env=cur.env;
    if(t[0]==="var"&&env.size){
      const i=t[1];
      if(i<env.size){cur=envArray(k,env)[i];continue;}
      const n=i-env.size;
      cur={term:n===i?t:k.make("var",n),env:EMPTY};
      continue;
    }
    if(t[0]==="let"){
      k.need("reduction");
      cur={term:t[3],env:extend(k,{term:t[2],env},env)};
      crossed++;
      continue;
    }
    if(t[0]==="app"){
      args.push({term:t[2],env});
      cur={term:t[1],env};
      continue;
    }
    if(t[0]==="lam"&&args.length){
      k.need("application"); k.need("reduction");
      const arg=args.pop();
      cur={term:t[2],env:extend(k,arg,env)};
      crossed++;
      continue;
    }
    break;
  }
  if(!crossed) return null;
  let out=reify(k,cur);
  for(let i=args.length-1;i>=0;i--) out=k.make("app",out,reify(k,args[i]));
  return {out,crossed};
}

function install(enabled){
  proto.run=retainedRun; proto.whnf=retainedWhnf;
  if(!enabled) return;
  proto.run=function(...args){
    this.__betaEnvArray=new WeakMap();
    this.__betaReify=new WeakMap();
    return retainedRun.apply(this,args);
  };
  proto.whnf=function(e){
    if(this.__betaSpineDepth||!Array.isArray(e)||e[0]!=="app")
      return retainedWhnf.call(this,e);
    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    this.__betaSpineDepth=1;
    try{
      const r=reduceBetaSpine(this,e);
      if(r===null){
        this.steps=snap.steps; this.budget=snap.budget; this.conversionFrontier=snap.frontier;
        return retainedWhnf.call(this,e);
      }
      return retainedWhnf.call(this,r.out);
    }catch(_err){
      this.steps=snap.steps; this.budget=snap.budget; this.conversionFrontier=snap.frontier;
      return retainedWhnf.call(this,e);
    }finally{
      this.__betaSpineDepth=0;
    }
  };
}

function evaluate(mode,enabled){
  install(enabled);
  const out=[];
  for(const row of rows.sort((a,b)=>a.name.localeCompare(b.name))){
    const t0=Date.now();
    const r=K.checkExport(row.input,caps,1_000_000);
    out.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
      correct:r.status==="UNKNOWN"||r.status===row.expected});
  }
  console.log("BETA_CLOSURE_SPINE "+JSON.stringify({mode,results:out}));
  return out;
}
const baseline=evaluate("baseline",false);
const candidate=evaluate("closure-spine",true);
install(false);
const changed=candidate.map((r,i)=>({before:baseline[i],after:r})).filter(x=>x.before.status!==x.after.status||x.before.steps!==x.after.steps);
console.log("BETA_CLOSURE_SPINE_CONCLUSION "+JSON.stringify({changed,
  beta:candidate.find(x=>x.name.endsWith("beta-ladder.ndjson"))}));
