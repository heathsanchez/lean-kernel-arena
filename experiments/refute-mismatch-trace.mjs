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
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.endswith(".ndjson") and "refute-cheap-" in m.name:
      rows.append({"name":m.name,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype, retainedEqual=proto.equal;

function spine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse(); return {head:e,args};
}
function info(k,e){
  const s=spine(e),h=s.head;
  if(!Array.isArray(h)) return {tag:typeof h,arity:s.args.length};
  if(h[0]!=="const") return {tag:h[0],arity:s.args.length};
  const d=k.env?.get(h[1]);
  const ind=d?.kind==="ctor"?k.env?.get(d.induct):null;
  return {tag:"const",kind:d?.kind??"const",name:h[1],induct:d?.induct??null,
    inductIsProp:ind?.isProp??null,arity:s.args.length};
}

let events=[];
proto.equal=function(a,b,ctx=[]){
  if(events.length<80){
    const ia=info(this,a),ib=info(this,b);
    const distinctCtor=ia.kind==="ctor"&&ib.kind==="ctor"&&ia.name!==ib.name;
    const distinctRigidConst=ia.tag==="const"&&ib.tag==="const"&&ia.name!==ib.name;
    if(distinctCtor||distinctRigidConst){
      events.push({steps:this.steps,ctxDepth:ctx.length,distinctCtor,ia,ib});
    }
  }
  return retainedEqual.call(this,a,b,ctx);
};

for(const row of rows){
  events=[];
  const r=K.checkExport(row.input,caps,1_000_000);
  console.log("REFUTE_MISMATCH_TRACE "+JSON.stringify({
    name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,events
  }));
}
proto.equal=retainedEqual;
