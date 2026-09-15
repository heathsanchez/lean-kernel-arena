import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";

const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("fetch "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("corpus changed");

const py=String.raw`
import io,tarfile,sys
data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.endswith("good/perf/app-lam.ndjson"):
      sys.stdout.buffer.write(a.extractfile(m).read());break
`;
const input=execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}).toString("utf8");

const names=new Map([[0,"[]"]]), levels=new Map([[0,0]]), exprs=new Map();
let target=null, parsed=0;
const get=(m,n)=>m.get(n);
for(const line of input.split(/\r?\n/)){
  if(!line.trim()) continue;
  const row=JSON.parse(line); parsed++;
  if(row.in!==undefined){
    if(row.str) names.set(row.in,JSON.stringify([get(names,row.str.pre),"str",row.str.str]));
    else if(row.num) names.set(row.in,JSON.stringify([get(names,row.num.pre),"num",row.num.i]));
    continue;
  }
  if(row.il!==undefined){
    if(row.succ!==undefined) levels.set(row.il,["succ",get(levels,row.succ)]);
    else if(row.max) levels.set(row.il,["max",get(levels,row.max[0]),get(levels,row.max[1])]);
    else if(row.imax) levels.set(row.il,["imax",get(levels,row.imax[0]),get(levels,row.imax[1])]);
    else if(row.param!==undefined) levels.set(row.il,["param",get(names,row.param)]);
    continue;
  }
  if(row.ie!==undefined){
    let e;
    if(row.sort!==undefined)e=["sort",get(levels,row.sort)];
    else if(row.bvar!==undefined)e=["var",row.bvar];
    else if(row.const)e=row.const.us?.length?["const",get(names,row.const.name),row.const.us.map(u=>get(levels,u))]:["const",get(names,row.const.name)];
    else if(row.lam)e=["lam",get(exprs,row.lam.type),get(exprs,row.lam.body)];
    else if(row.forallE)e=["pi",get(exprs,row.forallE.type),get(exprs,row.forallE.body)];
    else if(row.app)e=["app",get(exprs,row.app.fn),get(exprs,row.app.arg)];
    else if(row.letE)e=["let",get(exprs,row.letE.type),get(exprs,row.letE.value),get(exprs,row.letE.body)];
    else if(row.mdata)e=get(exprs,row.mdata.expr);
    else if(row.natVal!==undefined)e=["nat",Number(row.natVal)];
    else if(row.strVal!==undefined)e=["strlit",row.strVal];
    else if(row.proj)e=["proj",get(names,row.proj.typeName),row.proj.idx,get(exprs,row.proj.struct)];
    else continue;
    exprs.set(row.ie,e);
    continue;
  }
  const tag=["def","thm","opaque"].find(k=>row[k]);
  if(tag){
    const d=row[tag];
    const name=get(names,d.name);
    if(name?.includes("dag_app_binder")) target=get(exprs,d.value);
  }
}
if(!target) throw new Error("target declaration not found");

let occurrences=0,maxDepth=0,duplicateOccurrences=0;
const seen=new WeakSet(), unique=[];
const stack=[{e:target,d:0}];
while(stack.length){
  const {e,d}=stack.pop();
  if(!Array.isArray(e)) continue;
  occurrences++; if(d>maxDepth)maxDepth=d;
  if(seen.has(e)){duplicateOccurrences++;continue;}
  seen.add(e); unique.push(e);
  for(let i=1;i<e.length;i++) if(Array.isArray(e[i])) stack.push({e:e[i],d:d+1});
}
const tags={};
for(const e of unique) tags[e[0]]=(tags[e[0]]??0)+1;

// Count immediate same-object duplicate arguments at app nodes.
let sameArgPairs=0, appNodes=0;
for(const e of unique){
  if(e[0]!=="app") continue;
  appNodes++;
  const fn=e[1];
  if(Array.isArray(fn)&&fn[0]==="app"&&fn[2]===e[2]) sameArgPairs++;
}

console.log("APP_LAM_DAG_IDENTITY "+JSON.stringify({
  arena_sha256:sha,parsed_records:parsed,expr_records:exprs.size,
  root_tag:target[0],occurrences,unique_arrays:unique.length,
  duplicate_occurrences:duplicateOccurrences,maxDepth,appNodes,sameArgPairs,tags
}));
