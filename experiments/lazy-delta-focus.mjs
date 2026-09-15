import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
wanted={"args-before-unfold.ndjson","folded-constant-first.ndjson","folded-constant-last.ndjson",
"unroll-versus-evaluate.ndjson","refute-cheap-first.ndjson","refute-cheap-last.ndjson"}
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if not m.isfile() or m.name.rsplit("/",1)[-1] not in wanted: continue
    p=m.name.split("/")
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype, retained=proto.equal;

function rawSpine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse(); return {head:e,args};
}
function rebuild(k,head,args){
  let out=head;
  for(const a of args) out=k.make("app",out,a);
  return out;
}
function administrative(k,t){
  let cur=t;
  for(let n=0;n<16;n++){
    if(!Array.isArray(cur)) return cur;
    if(cur[0]==="let"){
      k.tick(); k.need("reduction");
      cur=k.substitute(cur[3],cur[2]);
      continue;
    }
    const s=rawSpine(cur);
    if(Array.isArray(s.head)&&s.head[0]==="lam"&&s.args.length){
      k.tick(); k.need("reduction");
      let out=k.substitute(s.head[2],s.args[0]);
      out=rebuild(k,out,s.args.slice(1));
      cur=out; continue;
    }
    return cur;
  }
  return cur;
}
function rawIota(k,t){
  const s=rawSpine(t),rh=s.head,rargs=s.args;
  if(!Array.isArray(rh)||rh[0]!=="const") return null;
  const rd=k.env.get(rh[1]);
  if(rd?.kind!=="rec") return null;
  const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
  if(rargs.length<total) return null;
  const major=rargs[total-1],ms=rawSpine(major),mh=ms.head,margs=ms.args;
  const md=Array.isArray(mh)&&mh[0]==="const"?k.env.get(mh[1]):null;
  if(md?.kind!=="ctor"||md.induct!==rd.induct||margs.length!==md.numParams+md.numFields) return null;
  for(let i=0;i<rd.numParams;i++) if(!k.same(margs[i],rargs[i])) return null;
  const rule=rd.rules.find(rr=>rr.ctor===md.name);
  if(!rule) return null;
  k.need("inductive-reduction"); k.need("reduction");
  let rhs=k.instantiateDeclaration(rh,rule.rhs);
  const prefix=rargs.slice(0,rd.numParams+1+rd.numMinors);
  rhs=k.appN(rhs,prefix.concat(margs.slice(md.numParams)));
  for(const extra of rargs.slice(total)) rhs=k.make("app",rhs,extra);
  return administrative(k,rhs);
}
function reduceHeadOnce(k,t,allowMajor=true){
  let cur=administrative(k,t);
  const start=cur,s=rawSpine(cur);
  if(Array.isArray(s.head)&&s.head[0]==="const"){
    const d=k.env.get(s.head[1]);
    if(d?.kind==="def"){
      k.tick(); k.need("declarations"); k.need("reduction");
      let out=k.instantiateDeclaration(s.head,d.value);
      out=rebuild(k,out,s.args);
      out=administrative(k,out);
      const iota=rawIota(k,out);
      return iota??out;
    }
  }
  const iota=rawIota(k,cur);
  if(iota!==null) return iota;

  if(allowMajor){
    const rs=rawSpine(cur),rh=rs.head,rargs=rs.args;
    if(Array.isArray(rh)&&rh[0]==="const"){
      const rd=k.env.get(rh[1]);
      if(rd?.kind==="rec"){
        const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
        if(rargs.length>=total){
          const major=rargs[total-1];
          const next=reduceHeadOnce(k,major,false);
          if(next!==major){
            const xs=rargs.slice(); xs[total-1]=next;
            return rebuild(k,rh,xs);
          }
        }
      }
    }
  }
  return start===t?null:cur;
}
function headKey(k,t){
  const h=rawSpine(t).head;
  if(!Array.isArray(h)) return null;
  if(h[0]==="const"){
    const d=k.env.get(h[1]);
    return "const:"+(d?.kind??"?")+":"+h[1];
  }
  return h[0];
}
function install(enabled){
  proto.equal=retained;
  if(!enabled) return;
  proto.equal=function(a,b,ctx=[]){
    // The existing rigid-type transaction is the authority and budget owner.
    // Only change evaluation order while inside that already-verified transaction.
    if(this.localDefs || (this._rigidTypeSpineDepth??0)===0)
      return retained.call(this,a,b,ctx);
    if(this.same(a,b)) return;

    let x=a,y=b;
    for(let n=0;n<5000;n++){
      if(this.same(x,y)) return;
      const sx=rawSpine(x),sy=rawSpine(y);
      if(sx.args.length>0&&sx.args.length===sy.args.length&&
         (sx.head===sy.head||this.same(sx.head,sy.head)))
        return retained.call(this,x,y,ctx);

      const nx=reduceHeadOnce(this,x,true);
      if(nx!==null&&nx!==x){
        x=nx;
        if(this.same(x,y)) return;
        const hx=headKey(this,x),hy=headKey(this,y);
        if(hx!==null&&hx===hy) continue;
        // Left-biased lazy delta: after one lawful head step, re-observe before
        // touching the right side.
        continue;
      }
      const ny=reduceHeadOnce(this,y,true);
      if(ny!==null&&ny!==y){
        y=ny;
        continue;
      }
      return retained.call(this,x,y,ctx);
    }
    return retained.call(this,x,y,ctx);
  };
}

for(const enabled of [false,true]){
  install(enabled);
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    console.log("LAZY_DELTA_FOCUS "+JSON.stringify({
      mode:enabled?"candidate":"baseline",name:row.name,expected:row.expected,
      status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      correct:r.status==="UNKNOWN"||r.status===row.expected
    }));
  }
}
proto.equal=retained;
