// Diagnostic only: identify why exact substitution memoization misses on
// shared-subterm. No semantic behavior is changed.
import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch "+response.status);
const data=Buffer.from(await response.arrayBuffer());
if(createHash("sha256").update(data).digest("hex")!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.endswith("good/perf/shared-subterm.ndjson"):
      print(json.dumps({"name":m.name,"input":a.extractfile(m).read().decode("utf-8")}))
      break
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype;
const retained=proto.substitute;
const ids=new WeakMap();let nextId=1;
const id=x=>{if(!Array.isArray(x))return 0;let v=ids.get(x);if(v===undefined){v=nextId++;ids.set(x,v);}return v;};
const roots=new Map(),args=new Map(),pairs=new Map(),byDecl=new Map(),byDepth=new Map();
let calls=0,totalDelta=0,zeroDelta=0,maxDelta=0;

proto.substitute=function(e,arg,depth=0){
  const ri=id(e),ai=id(arg),pk=ri+":"+ai+":"+depth;
  const before=this.steps??0;
  const out=retained.call(this,e,arg,depth);
  const delta=(this.steps??0)-before;
  calls++;totalDelta+=delta;if(delta===0)zeroDelta++;if(delta>maxDelta)maxDelta=delta;
  const r=roots.get(ri)??{rootId:ri,tag:e?.[0]??null,calls:0,ticks:0,args:new Set(),depths:new Set(),max:0};
  r.calls++;r.ticks+=delta;r.args.add(ai);r.depths.add(depth);r.max=Math.max(r.max,delta);roots.set(ri,r);
  const a=args.get(ai)??{argId:ai,tag:arg?.[0]??null,calls:0,ticks:0,roots:new Set(),max:0};
  a.calls++;a.ticks+=delta;a.roots.add(ri);a.max=Math.max(a.max,delta);args.set(ai,a);
  const p=pairs.get(pk)??{rootId:ri,argId:ai,depth,calls:0,ticks:0,max:0};
  p.calls++;p.ticks+=delta;p.max=Math.max(p.max,delta);pairs.set(pk,p);
  const d=this.currentDeclaration??"<none>";
  const ds=byDecl.get(d)??{decl:d,calls:0,ticks:0};ds.calls++;ds.ticks+=delta;byDecl.set(d,ds);
  const dep=byDepth.get(depth)??{depth,calls:0,ticks:0};dep.calls++;dep.ticks+=delta;byDepth.set(depth,dep);
  return out;
};

const r=K.checkExport(row.input,caps,1_000_000);
proto.substitute=retained;
const rootRows=[...roots.values()].map(x=>({...x,distinctArgs:x.args.size,distinctDepths:x.depths.size,args:undefined,depths:undefined}))
  .sort((a,b)=>b.ticks-a.ticks);
const argRows=[...args.values()].map(x=>({...x,distinctRoots:x.roots.size,roots:undefined}))
  .sort((a,b)=>b.ticks-a.ticks);
const pairRows=[...pairs.values()].sort((a,b)=>b.ticks-a.ticks);
const declRows=[...byDecl.values()].sort((a,b)=>b.ticks-a.ticks);
const depthRows=[...byDepth.values()].sort((a,b)=>b.ticks-a.ticks);
const summary={
  name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
  calls,totalDelta,zeroDelta,maxDelta,uniqueRoots:roots.size,uniqueArgs:args.size,uniquePairs:pairs.size,
  topRoots:rootRows.slice(0,20),topArgs:argRows.slice(0,20),topPairs:pairRows.slice(0,20),
  byDeclaration:declRows.slice(0,20),byDepth:depthRows
};
console.log("SHARED_SUBSTITUTION_SHAPE "+JSON.stringify(summary));
