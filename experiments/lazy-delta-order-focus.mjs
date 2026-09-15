import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

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

const proto=K.Kernel.prototype, fallback=proto.equal, CAP=650000;
function rawSpine(e){const args=[];while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}args.reverse();return {head:e,args};}
function rebuild(k,h,args){let out=h;for(const a of args)out=k.make("app",out,a);return out;}
function cheapPair(a,b){
  if(a===b)return -1000000;if(!Array.isArray(a)||!Array.isArray(b))return 0;
  if(a[0]!==b[0])return -10000;if(["const","var","nat","strlit","sort"].includes(a[0]))return -5000;
  let score=0,stack=[a,b],seen=new Set();
  while(stack.length&&score<128){const x=stack.pop();if(!Array.isArray(x)||seen.has(x))continue;seen.add(x);score++;for(let i=1;i<x.length;i++)if(Array.isArray(x[i]))stack.push(x[i]);}
  return score;
}
function headKind(k,t){
  const h=rawSpine(t).head;
  if(!Array.isArray(h))return null;
  if(h[0]!=="const")return h[0];
  return k.env.get(h[1])?.kind??"const";
}
function administrative(k,t){
  let cur=t;
  for(let n=0;n<16;n++){
    if(!Array.isArray(cur))return cur;
    if(cur[0]==="let"){k.tick();k.need("reduction");cur=k.substitute(cur[3],cur[2]);continue;}
    const s=rawSpine(cur);
    if(Array.isArray(s.head)&&s.head[0]==="lam"&&s.args.length){
      k.tick();k.need("reduction");cur=rebuild(k,k.substitute(s.head[2],s.args[0]),s.args.slice(1));continue;
    }
    return cur;
  }
  return cur;
}
function rawIota(k,t){
  const s=rawSpine(t),rh=s.head,rargs=s.args;
  if(!Array.isArray(rh)||rh[0]!=="const")return null;
  const rd=k.env.get(rh[1]);if(rd?.kind!=="rec")return null;
  const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;if(rargs.length<total)return null;
  const ms=rawSpine(rargs[total-1]),mh=ms.head,margs=ms.args;
  const md=Array.isArray(mh)&&mh[0]==="const"?k.env.get(mh[1]):null;
  if(md?.kind!=="ctor"||md.induct!==rd.induct||margs.length!==md.numParams+md.numFields)return null;
  for(let i=0;i<rd.numParams;i++)if(!k.same(margs[i],rargs[i]))return null;
  const rule=rd.rules.find(rr=>rr.ctor===md.name);if(!rule)return null;
  k.need("inductive-reduction");k.need("reduction");
  let rhs=k.instantiateDeclaration(rh,rule.rhs);
  rhs=k.appN(rhs,rargs.slice(0,rd.numParams+1+rd.numMinors).concat(margs.slice(md.numParams)));
  for(const extra of rargs.slice(total))rhs=k.make("app",rhs,extra);
  return administrative(k,rhs);
}
function reduceHeadOnce(k,t,allowMajor=true){
  let cur=administrative(k,t),s=rawSpine(cur);
  if(Array.isArray(s.head)&&s.head[0]==="const"){
    const d=k.env.get(s.head[1]);
    if(d?.kind==="def"){
      k.tick();k.need("declarations");k.need("reduction");
      let out=k.instantiateDeclaration(s.head,d.value);
      out=administrative(k,rebuild(k,out,s.args));
      return rawIota(k,out)??out;
    }
  }
  const iota=rawIota(k,cur);if(iota!==null)return iota;
  if(allowMajor){
    const rs=rawSpine(cur),rh=rs.head,rargs=rs.args;
    if(Array.isArray(rh)&&rh[0]==="const"){
      const rd=k.env.get(rh[1]);
      if(rd?.kind==="rec"){
        const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
        if(rargs.length>=total){
          const major=rargs[total-1],next=reduceHeadOnce(k,major,false);
          if(next!==null&&next!==major){const xs=rargs.slice();xs[total-1]=next;return rebuild(k,rh,xs);}
        }
      }
    }
  }
  return cur===t?null:cur;
}
function install(enabled){
  proto.equal=fallback;if(!enabled)return;
  proto.equal=function(a,b,ctx=[]){
    if(this.localDefs)return fallback.call(this,a,b,ctx);
    const depth=this._lazyOrderDepth??0;
    if(this.same(a,b))return;
    const sa=rawSpine(a),sb=rawSpine(b);
    const sameHead=sa.args.length>0&&sa.args.length===sb.args.length&&(sa.head===sb.head||this.same(sa.head,sb.head));
    const d=sameHead&&Array.isArray(sa.head)&&sa.head[0]==="const"?this.env.get(sa.head[1]):null;
    if(depth===0){
      if(!sameHead||d?.kind!=="inductive")return fallback.call(this,a,b,ctx);
      const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
      this.budget=Math.min(this.budget,this.steps+CAP);this._lazyOrderDepth=1;
      const order=sa.args.map((_,i)=>i).sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
      try{
        for(const i of order)this.equal(sa.args[i],sb.args[i],ctx);
        this._lazyOrderDepth=0;this.budget=snap.budget;return;
      }catch(e){
        this._lazyOrderDepth=0;this.budget=snap.budget;
        if(!(e instanceof Stop||e instanceof RangeError))throw e;
        this.steps=snap.steps;this.conversionFrontier=snap.frontier;
        return fallback.call(this,a,b,ctx);
      }
    }
    if(sameHead){
      const order=sa.args.map((_,i)=>i).sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
      for(const i of order)this.equal(sa.args[i],sb.args[i],ctx);
      return;
    }
    let x=a,y=b;
    for(let n=0;n<12000;n++){
      if(this.same(x,y))return;
      const sx=rawSpine(x),sy=rawSpine(y);
      if(sx.args.length>0&&sx.args.length===sy.args.length&&(sx.head===sy.head||this.same(sx.head,sy.head))){
        const order=sx.args.map((_,i)=>i).sort((i,j)=>cheapPair(sx.args[i],sy.args[i])-cheapPair(sx.args[j],sy.args[j]));
        for(const i of order)this.equal(sx.args[i],sy.args[i],ctx);
        return;
      }
      const kx=headKind(this,x),ky=headKind(this,y);
      // A folded definition is cheaper to expose than evaluating an already
      // exposed recursor. This is the unroll-vs-evaluate separator.
      if(ky==="def"&&kx!=="def"){
        const ny=reduceHeadOnce(this,y,true);if(ny!==null&&ny!==y){y=ny;continue;}
        const nx=reduceHeadOnce(this,x,true);if(nx!==null&&nx!==x){x=nx;continue;}
      }else{
        const nx=reduceHeadOnce(this,x,true);if(nx!==null&&nx!==x){x=nx;continue;}
        const ny=reduceHeadOnce(this,y,true);if(ny!==null&&ny!==y){y=ny;continue;}
      }
      return fallback.call(this,x,y,ctx);
    }
    return fallback.call(this,x,y,ctx);
  };
}
for(const enabled of [false,true]){
  install(enabled);
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    console.log("LAZY_DELTA_ORDER "+JSON.stringify({mode:enabled?"candidate":"baseline",name:row.name,
      expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      correct:r.status==="UNKNOWN"||r.status===row.expected,diagnostic_error:r.diagnostic_error??null}));
  }
}
proto.equal=fallback;
