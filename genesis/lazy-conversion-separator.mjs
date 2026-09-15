// Prospective lazy-conversion ordering separator.
// Base present: hash-consing + context-independent normal reuse.
// Frozen candidates: early proof irrelevance, positive raw-spine congruence,
// rigid constructor early refutation, and their combination.
// No new definitional equality rule is added.
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
const originals={make:proto.make,normal:proto.normal,equal:proto.equal};

function objectId(kernel,x){
  kernel.__ids??=new WeakMap(); kernel.__nextId??=1;
  if(!kernel.__ids.has(x)) kernel.__ids.set(x,kernel.__nextId++);
  return kernel.__ids.get(x);
}
function scalarKey(x){
  if(typeof x==="string") return "s:"+x;
  if(typeof x==="number") return "n:"+x;
  if(typeof x==="boolean") return "b:"+(x?1:0);
  if(x===null) return "null";
  return typeof x+":"+String(x);
}
function reset(){ for(const [n,f] of Object.entries(originals)) proto[n]=f; }

function installBase(){
  reset();
  proto.make=function(...xs){
    this.tick(); this.__cons??=new Map();
    const key=xs.map(x=>Array.isArray(x)?"a:"+objectId(this,x):scalarKey(x)).join("|");
    const old=this.__cons.get(key);
    if(old!==undefined) return old;
    this.allocations++; this.__cons.set(key,xs); objectId(this,xs); return xs;
  };
  const baseNormal=originals.normal;
  proto.normal=function(e){
    if(!Array.isArray(e)) return baseNormal.call(this,e);
    this.__normalMemo??=new WeakMap();
    if(this.__normalMemo.has(e)) return this.__normalMemo.get(e);
    const r=baseNormal.call(this,e); this.__normalMemo.set(e,r); return r;
  };
}
function rawSpine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse(); return {head:e,args};
}
function isCtorHead(kernel,h){
  return Array.isArray(h)&&h[0]==="const"&&kernel.env.get(h[1])?.kind==="ctor";
}
function install(mode){
  installBase();
  if(mode==="base") return;
  const useProof=mode==="proof"||mode==="all";
  const useCong=mode==="congruence"||mode==="all";
  const useCtor=mode==="ctor"||mode==="all";
  const baseEqual=originals.equal;

  proto.equal=function(a,b,ctx=[]){
    // Existing pointer/structural equality remains the cheapest first test.
    if(this.same(a,b)) return;

    if(useProof && this.caps.has("proof-irrelevance")){
      try{
        const ta=this.proofType(a,ctx),tb=this.proofType(b,ctx);
        if(ta!==null&&tb!==null){
          try{ this.equal(ta,tb,ctx); return; }
          catch(e){ if(!(e instanceof K.Stop)) throw e; }
        }
      } catch(e){ if(!(e instanceof K.Stop)) throw e; }
    }

    if(useCong||useCtor){
      const sa=rawSpine(a),sb=rawSpine(b);
      if(sa.args.length===sb.args.length && sa.args.length>0 && this.same(sa.head,sb.head)){
        const rigidCtor=useCtor&&isCtorHead(this,sa.head);
        try{
          for(let i=0;i<sa.args.length;i++) this.equal(sa.args[i],sb.args[i],ctx);
          return; // congruence is a positive proof of equality
        } catch(e){
          if(!(e instanceof K.Stop)) throw e;
          if(rigidCtor && e.status===K.REJECT) throw e; // constructor applications are rigid
          // Any failure under a reducible/non-rigid head merely declines the shortcut.
        }
      }
    }
    return baseEqual.call(this,a,b,ctx);
  };
}

const budget=1_000_000;
function evaluate(mode){
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
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const variants=["base","proof","congruence","ctor","all"].map(evaluate);
reset();
const baseline=variants[0];
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
if(residual.size!==17) throw new Error("baseline residual changed: "+residual.size);

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
      } else remaining.push({name:r.name,reason:r.reason,steps:r.steps});
    }
  }
  const s={mode:v.mode,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,resolvedAccept,resolvedReject,
    totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,elapsed_ms:v.elapsed_ms,
    resolvedCases,regressions,remaining};
  summaries.push(s); console.log("LAZY_CONVERSION_VARIANT "+JSON.stringify(s));
}
const lawful=summaries.filter(s=>s.mode!=="base"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0)
  .sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),
  lawful_candidates:lawful.map(x=>x.mode),provisional_winner:lawful[0]?.mode??null,
  claim_boundary:"Prospective ordering change only. Early proof irrelevance and congruence can only establish existing equalities; rigid constructor refutation applies only to already irreducible constructor heads. Full protected replay is authoritative."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/lazy-conversion-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("LAZY_CONVERSION_CONCLUSION "+JSON.stringify(conclusion));
