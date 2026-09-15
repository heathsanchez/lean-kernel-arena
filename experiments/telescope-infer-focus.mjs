// Focused separator for application inference: preserve a Pi telescope plus
// an exact argument environment instead of materializing the entire codomain
// after every argument. Domains are instantiated on demand; the final result is
// instantiated once with all consumed arguments.
import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
wanted={"beta-ladder.ndjson","shared-subterm.ndjson"}
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.rsplit("/",1)[-1] in wanted:
      p=m.name.split("/"); e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
      if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==2)throw new Error("focus rows changed: "+rows.length);

const proto=K.Kernel.prototype, retainedInfer=proto.infer;

function substMany(kernel,root,args,depth=0){
  if(!args.length)return root;
  const work=[{kind:"visit",e:root,d:depth}],vals=[];
  while(work.length){
    const f=work.pop();
    if(f.kind==="build"){
      if(f.tag==="proj")vals.push(kernel.make("proj",f.name,f.index,vals.pop()));
      else{
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--)xs[i]=vals.pop();
        vals.push(kernel.make(f.tag,...xs));
      }
      continue;
    }
    const e=f.e,d=f.d;kernel.tick();
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":vals.push(e);break;
      case "var":{
        const i=e[1];
        if(i<d)vals.push(e);
        else{
          const j=i-d;
          if(j<args.length)vals.push(kernel.shift(args[args.length-1-j],d));
          else vals.push(kernel.make("var",i-args.length));
        }
        break;
      }
      case "pi":case "lam":
        work.push({kind:"build",tag:e[0],n:2});
        work.push({kind:"visit",e:e[2],d:d+1});
        work.push({kind:"visit",e:e[1],d});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2});
        work.push({kind:"visit",e:e[2],d});
        work.push({kind:"visit",e:e[1],d});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2]});
        work.push({kind:"visit",e:e[3],d});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3});
        work.push({kind:"visit",e:e[3],d:d+1});
        work.push({kind:"visit",e:e[2],d});
        work.push({kind:"visit",e:e[1],d});
        break;
      default:kernel.unknown("substitution-syntax");
    }
  }
  return vals.pop();
}

function install(candidate){
  proto.infer=retainedInfer;
  if(!candidate)return;
  proto.infer=function(e,ctx){
    if(!Array.isArray(e)||e[0]!=="app"||this.__telescopeInfer===true)
      return retainedInfer.call(this,e,ctx);

    const args=[];let head=e;
    while(Array.isArray(head)&&head[0]==="app"){args.push(head[2]);head=head[1];}
    args.reverse();
    if(args.length<2)return retainedInfer.call(this,e,ctx);

    this.__telescopeInfer=true;
    try{
      let raw=this.whnf(retainedInfer.call(this,head,ctx));
      // Only claim the direct telescope grain. If the raw codomain needs
      // reduction to reveal a later Pi, leave the case to retained inference.
      let p=raw;
      for(let i=0;i<args.length;i++){
        if(!Array.isArray(p)||p[0]!=="pi")return retainedInfer.call(this,e,ctx);
        p=p[2];
      }

      p=raw;
      const env=[];
      for(const arg of args){
        this.tick();this.need("application");
        const domain=substMany(this,p[1],env);
        this.equal(retainedInfer.call(this,arg,ctx),domain,ctx);
        env.push(arg);
        p=p[2];
      }
      return substMany(this,p,env);
    }finally{
      this.__telescopeInfer=false;
    }
  };
}

for(const row of rows){
  for(const candidate of [false,true]){
    install(candidate);
    const r=K.checkExport(row.input,caps,1_000_000);
    console.log("TELESCOPE_INFER_FOCUS "+JSON.stringify({name:row.name,candidate,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null,fallback_mode:r.fallback_mode??null,correct:r.status==="UNKNOWN"||r.status===row.expected}));
  }
}
proto.infer=retainedInfer;
