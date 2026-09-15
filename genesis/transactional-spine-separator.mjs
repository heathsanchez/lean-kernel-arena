// Prospective separator forced by the lazy-conversion residual.
// Raw-spine congruence is a sufficient proof of equality, but failed speculation
// must not consume the retained converter's budget. Constructor arguments may
// be scheduled cheapest-first because constructor injectivity is order-independent.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "./kernel.mjs";
import {Stop} from "./kernel-base.mjs";

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

const proto=K.Kernel.prototype, retained=proto.equal;

function rawSpine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse(); return {head:e,args};
}
function isCtorHead(kernel,h){
  return Array.isArray(h)&&h[0]==="const"&&kernel.env.get(h[1])?.kind==="ctor";
}
function cheapPair(a,b){
  if(a===b) return -1000000;
  if(!Array.isArray(a)||!Array.isArray(b)) return 0;
  if(a[0]!==b[0]) return -1000;
  if((a[0]==="const"||a[0]==="var"||a[0]==="nat"||a[0]==="strlit") &&
     (b[0]==="const"||b[0]==="var"||b[0]==="nat"||b[0]==="strlit")) return -500;
  let score=0;
  const stack=[a,b],seen=new Set();
  while(stack.length&&score<128){
    const x=stack.pop(); if(!Array.isArray(x)||seen.has(x)) continue;
    seen.add(x);score++;
    for(let i=1;i<x.length;i++) if(Array.isArray(x[i])) stack.push(x[i]);
  }
  return score;
}
function snap(kernel){return {steps:kernel.steps,frontier:kernel.conversionFrontier};}
function restore(kernel,s){kernel.steps=s.steps;kernel.conversionFrontier=s.frontier;}
function declined(e){return e instanceof Stop || e instanceof RangeError;}

function install(mode){
  proto.equal=retained;
  if(mode==="base") return;
  const useProof=mode==="proof-spine"||mode==="all";
  const useSpine=mode==="spine"||mode==="proof-spine"||mode==="ctor-cheap"||mode==="all";
  const useCtor=mode==="ctor-cheap"||mode==="all";

  proto.equal=function(a,b,ctx=[]){
    if(this.same(a,b)) return;

    if(useProof&&this.caps.has("proof-irrelevance")){
      const s=snap(this);
      try{
        const ta=this.proofType(a,ctx),tb=this.proofType(b,ctx);
        if(ta!==null&&tb!==null){
          this.equal(ta,tb,ctx);
          return;
        }
      }catch(e){if(!declined(e)) throw e;}
      restore(this,s);
    }

    if(useSpine){
      const sa=rawSpine(a),sb=rawSpine(b);
      if(sa.args.length>0&&sa.args.length===sb.args.length&&
         (sa.head===sb.head||this.same(sa.head,sb.head))){
        const ctor=useCtor&&isCtorHead(this,sa.head);
        const order=sa.args.map((_,i)=>i);
        if(ctor) order.sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
        const s=snap(this);
        try{
          for(const i of order) this.equal(sa.args[i],sb.args[i],ctx);
          return; // congruence proves the original applications equal
        }catch(e){
          if(!declined(e)) throw e;
          if(ctor && e instanceof Stop && e.status===K.REJECT) throw e;
          restore(this,s);
        }
      }
    }
    return retained.call(this,a,b,ctx);
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
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const variants=["base","spine","proof-spine","ctor-cheap","all"].map(evaluate);
proto.equal=retained;
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
      regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
    }
    if(residual.has(r.name)){
      if(r.status!=="UNKNOWN"){
        if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({mode:v.mode,result:r}));
        resolved++;if(r.status==="ACCEPT")resolvedAccept++;else resolvedReject++;
        resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
      }else remaining.push({name:r.name,reason:r.reason,steps:r.steps});
    }
  }
  const s={mode:v.mode,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,resolvedAccept,resolvedReject,
    totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,elapsed_ms:v.elapsed_ms,
    resolvedCases,regressions,remaining};
  summaries.push(s);console.log("TRANSACTIONAL_SPINE_VARIANT "+JSON.stringify(s));
}
const lawful=summaries.filter(s=>s.mode!=="base"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0)
  .sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps||a.mode.length-b.mode.length);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),
  lawful_candidates:lawful.map(x=>x.mode),provisional_winner:lawful[0]?.mode??null,
  claim_boundary:"Only sufficient equality consequences are retained. Failed speculative spine/proof probes restore semantic budget and diagnostic frontier. Constructor rejection is propagated only under an exact same rigid constructor head."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/transactional-spine-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("TRANSACTIONAL_SPINE_CONCLUSION "+JSON.stringify(conclusion));
