// Prospective separator v2: defer only direct beta and/or let chains.
// Ordinary WHNF is untouched. Persistent exact closure environments compile
// crossed binders; lookup and reification are memoized by exact identities.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "./kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("./evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==188) throw new Error("Arena row count changed: "+rows.length);

const proto=K.Kernel.prototype;
const originalRun=proto.run, originalWhnf=proto.whnf;
const EMPTY=Object.freeze({size:0,head:null,tail:null});

function extend(kernel,head,tail) {
  kernel.tick();
  return {head,tail,size:tail.size+1};
}
function lookup(kernel,env,i) {
  kernel.__closureLookup??=new WeakMap();
  let m=kernel.__closureLookup.get(env);
  if(!m){m=new Map();kernel.__closureLookup.set(env,m);}
  if(m.has(i)){kernel.tick();return m.get(i);}
  let p=env,j=i;
  while(j-->0){kernel.tick();p=p.tail;}
  const out=p.head;
  m.set(i,out);
  return out;
}
function reify(kernel,closure,lift=0) {
  kernel.__closureReify??=new WeakMap();
  let byEnv=kernel.__closureReify.get(closure.term);
  if(!byEnv){byEnv=new WeakMap();kernel.__closureReify.set(closure.term,byEnv);}
  let byLift=byEnv.get(closure.env);
  if(!byLift){byLift=new Map();byEnv.set(closure.env,byLift);}
  if(byLift.has(lift)){kernel.tick();return byLift.get(lift);}

  function go(term,env,depth,extra) {
    kernel.tick();
    switch(term[0]) {
      case "sort": case "const": case "nat": case "strlit": return term;
      case "var": {
        const i=term[1];
        if(i<depth) return term;
        const j=i-depth;
        if(j<env.size) return reify(kernel,lookup(kernel,env,j),extra+depth);
        const out=depth+(j-env.size)+extra;
        return out===i?term:kernel.make("var",out);
      }
      case "pi": case "lam":
        return kernel.make(term[0],go(term[1],env,depth,extra),go(term[2],env,depth+1,extra));
      case "app":
        return kernel.make("app",go(term[1],env,depth,extra),go(term[2],env,depth,extra));
      case "proj":
        return kernel.make("proj",term[1],term[2],go(term[3],env,depth,extra));
      case "let":
        return kernel.make("let",go(term[1],env,depth,extra),go(term[2],env,depth,extra),go(term[3],env,depth+1,extra));
      default:
        kernel.unknown("deferred-v2-reify-syntax");
    }
  }
  const out=go(closure.term,closure.env,0,lift);
  byLift.set(lift,out);
  return out;
}

function install(mode) {
  proto.run=originalRun; proto.whnf=originalWhnf;
  proto.run=function(...args){
    this.__closureLookup=new WeakMap();
    this.__closureReify=new WeakMap();
    return originalRun.apply(this,args);
  };
  const useLet=mode==="let"||mode==="both";
  const useBeta=mode==="beta"||mode==="both";
  const eligible=e=>Array.isArray(e)&&(
    (useLet&&e[0]==="let") ||
    (useBeta&&e[0]==="app"&&Array.isArray(e[1])&&e[1][0]==="lam")
  );
  proto.whnf=function(e) {
    if(!eligible(e)) return originalWhnf.call(this,e);
    let cur={term:e,env:EMPTY}, crossed=false;
    for(;;) {
      this.tick();
      const t=cur.term,env=cur.env;
      if(t[0]==="var"&&env.size) {
        if(t[1]<env.size){cur=lookup(this,env,t[1]);continue;}
        const n=t[1]-env.size;
        cur={term:n===t[1]?t:this.make("var",n),env:EMPTY};
        continue;
      }
      if(useLet&&t[0]==="let") {
        this.need("reduction"); crossed=true;
        cur={term:t[3],env:extend(this,{term:t[2],env},env)};
        continue;
      }
      if(useBeta&&t[0]==="app"&&Array.isArray(t[1])&&t[1][0]==="lam") {
        this.need("application"); this.need("reduction"); crossed=true;
        const lam=t[1],arg={term:t[2],env};
        cur={term:lam[2],env:extend(this,arg,env)};
        continue;
      }
      if(!crossed) return originalWhnf.call(this,e);
      const out=cur.env.size?reify(this,cur):cur.term;
      return originalWhnf.call(this,out);
    }
  };
}

const budget=1_000_000;
function evaluate(mode) {
  install(mode);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode:mode||"none",counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const variants=[evaluate(""),evaluate("let"),evaluate("beta"),evaluate("both")];
proto.run=originalRun; proto.whnf=originalWhnf;
const baseline=variants[0];
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
const summaries=[];
for(const v of variants){
  let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
  const resolvedCases=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status){
      protectedChanged++;
      if(regressions.length<20) regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
    }
    if(residual.has(r.name)){
      if(r.status!=="UNKNOWN"){
        if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({mode:v.mode,result:r}));
        resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
        resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
      } else remaining.push({name:r.name,reason:r.reason,steps:r.steps,constructed:r.constructed});
    }
  }
  const s={mode:v.mode,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,resolvedAccept,resolvedReject,
    totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,elapsed_ms:v.elapsed_ms,
    resolvedCases,regressions,remaining};
  summaries.push(s); console.log("DEFERRED_V2_VARIANT "+JSON.stringify(s));
}
const lawful=summaries.filter(s=>s.mode!=="none"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0)
  .sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),
  lawful_candidates:lawful.map(x=>x.mode),provisional_winner:lawful[0]?.mode??null,
  claim_boundary:"Prospective direct-redex closure machine. Ordinary WHNF is untouched; only syntactically direct beta and/or let chains use persistent exact environments. Closure lookup/reification are exact-identity memoized. Promotion requires default-stack integration and ablation."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/deferred-substitution-v2.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("DEFERRED_V2_CONCLUSION "+JSON.stringify(conclusion));
