import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
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
const base={run:proto.run,getApp:proto.getApp,whnf:proto.whnf};
const stats={getapp:{q:0,h:0},whnf:{q:0,h:0}};

function objectId(k,x){
  k.__ldIds??=new WeakMap(); k.__ldNextId??=1;
  let id=k.__ldIds.get(x); if(id!==undefined) return id;
  id=k.__ldNextId++; k.__ldIds.set(x,id); return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length) return "";
  return ctx.map(x=>(x!==null&&(typeof x==="object"||typeof x==="function"))
    ?"o"+objectId(k,x):typeof x+":"+String(x)).join(",");
}
function reset(){ proto.run=base.run; proto.getApp=base.getApp; proto.whnf=base.whnf; }
function install(mode){
  reset();
  const useGetApp=mode==="getapp"||mode==="both";
  const useWhnf=mode==="whnf"||mode==="both";
  proto.run=function(...args){
    this.__ldGetApp=new WeakMap(); this.__ldWhnf=new WeakMap();
    this.__ldIds=new WeakMap(); this.__ldNextId=1;
    return base.run.apply(this,args);
  };
  if(useGetApp){
    proto.getApp=function(e){
      if(this.localDefs!==true||!Array.isArray(e)) return base.getApp.call(this,e);
      stats.getapp.q++;
      this.__ldGetApp??=new WeakMap();
      if(this.__ldGetApp.has(e)){stats.getapp.h++;return this.__ldGetApp.get(e);}
      const out=base.getApp.call(this,e); this.__ldGetApp.set(e,out); return out;
    };
  }
  if(useWhnf){
    proto.whnf=function(e){
      if(this.localDefs!==true||!Array.isArray(e)) return base.whnf.call(this,e);
      stats.whnf.q++;
      this.__ldWhnf??=new WeakMap();
      const key=ctxKey(this,this._activeCtx??[]);
      let by=this.__ldWhnf.get(e);
      if(!(by instanceof Map)){by=new Map();this.__ldWhnf.set(e,by);}
      if(by.has(key)){stats.whnf.h++;return by.get(key);}
      const out=base.whnf.call(this,e); by.set(key,out); return out;
    };
  }
}

function evaluate(mode){
  mode==="baseline"?reset():install(mode);
  const before=JSON.parse(JSON.stringify(stats));
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0}; let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]++; totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null});
  }
  const delta={};
  for(const [k,v] of Object.entries(stats)) delta[k]={q:v.q-before[k].q,h:v.h-before[k].h};
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:delta,results};
}

const variants=["baseline","getapp","whnf","both"].map(evaluate); reset();
const baseline=variants[0];
if(baseline.wrong) throw new Error("baseline wrong");
const summaries=[];
for(const v of variants){
  let protectedChanged=0; const resolved=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],c=v.results[i];
    if(b.status!=="UNKNOWN"&&c.status!==b.status){
      protectedChanged++; regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
    }
    if(b.status==="UNKNOWN"){
      if(c.status!=="UNKNOWN"){
        if(c.status!==c.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(c));
        resolved.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
      } else remaining.push({name:c.name,reason:c.reason,steps:c.steps,frontier_declaration:c.frontier_declaration});
    }
  }
  summaries.push({mode:v.mode,counts:v.counts,wrong:v.wrong,totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,
    elapsed_ms:v.elapsed_ms,stats:v.stats,protectedChanged,resolved,regressions,remaining,
    lawful:v.wrong===0&&protectedChanged===0,promotable:v.wrong===0&&protectedChanged===0&&resolved.length>0});
}
const lawful=summaries.filter(x=>x.mode!=="baseline"&&x.lawful).sort((a,b)=>
  b.resolved.length-a.resolved.length || a.counts.UNKNOWN-b.counts.UNKNOWN || a.totalSteps-b.totalSteps || a.totalConstructed-b.totalConstructed);
const report={arena_sha256:sha,budget:1_000_000,
  claim_boundary:"Exact completed consequence reuse only while localDefs===true. getApp keyed by exact term identity; WHNF keyed by exact term identity plus complete active LocalDef context identities. Failures/frontiers are never cached.",
  variants:summaries,provisional_winner:lawful[0]?.mode??null};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/localdef-consequence-bank.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
for(const s of summaries) console.log("LOCALDEF_CONSEQUENCE_VARIANT "+JSON.stringify(s));
console.log("LOCALDEF_CONSEQUENCE_BANK "+JSON.stringify({arena_sha256:sha,provisional_winner:report.provisional_winner,
  variants:summaries.map(({mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms,stats,protectedChanged,resolved,regressions,lawful,promotable})=>
    ({mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms,stats,protectedChanged,resolved,regressions,lawful,promotable}))}));
