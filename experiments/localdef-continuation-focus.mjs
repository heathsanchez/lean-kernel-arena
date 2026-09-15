import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {levelIMax} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
wanted={"app-lam.ndjson","let-ladder.ndjson","shift-cascade.ndjson","repeated-subproblem.ndjson"}
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

const proto=K.Kernel.prototype;
const retainedInfer=proto.infer;

function inCtx(kernel,ctx,fn){
  return kernel.localDefs===true && typeof kernel.withCtx==="function"
    ? kernel.withCtx(ctx,fn)
    : fn();
}
function whnfIn(kernel,value,ctx){
  return inCtx(kernel,ctx,()=>kernel.whnf(value));
}

function localContinuationInfer(root,rootCtx){
  let e=root,ctx=rootCtx,value,returning=false;
  const kont=[];

  while(true){
    if(!returning){
      if(Array.isArray(e) && e[0]==="var"){
        this.tick(); this.need("binders");
        if(e[1]>=ctx.length) this.reject("unbound-variable");
        const entry=ctx[ctx.length-1-e[1]];
        const ty=entry?.__localDef===true?entry.type:entry;
        value=this.shift(ty,e[1]+1);
        returning=true; continue;
      }

      if(Array.isArray(e) && e[0]==="app"){
        this.tick(); this.need("application");
        kont.push({kind:"app-fn",arg:e[2],ctx});
        e=e[1]; continue;
      }

      if(Array.isArray(e) && e[0]==="lam"){
        this.tick(); this.need("binders");
        kont.push({kind:"lam-domain",domain:e[1],body:e[2],ctx});
        e=e[1]; continue;
      }

      if(Array.isArray(e) && e[0]==="pi"){
        this.tick(); this.need("binders");
        kont.push({kind:"pi-domain",domain:e[1],body:e[2],ctx});
        e=e[1]; continue;
      }

      if(Array.isArray(e) && e[0]==="let"){
        this.tick(); this.need("reduction");
        kont.push({kind:"let-type",type:e[1],valueTerm:e[2],body:e[3],ctx});
        e=e[1]; continue;
      }

      value=inCtx(this,ctx,()=>retainedInfer.call(this,e,ctx));
      returning=true; continue;
    }

    if(!kont.length) return value;
    const k=kont.pop();

    if(k.kind==="app-fn"){
      const fty=whnfIn(this,value,k.ctx);
      if(fty[0]!=="pi") this.reject("not-a-function");
      kont.push({kind:"app-arg",fty,arg:k.arg,ctx:k.ctx});
      e=k.arg; ctx=k.ctx; returning=false; continue;
    }
    if(k.kind==="app-arg"){
      inCtx(this,k.ctx,()=>this.equal(value,k.fty[1],k.ctx));
      value=this.substitute(k.fty[2],k.arg);
      ctx=k.ctx; continue;
    }

    if(k.kind==="lam-domain"){
      const s=whnfIn(this,value,k.ctx);
      if(s[0]!=="sort") this.reject("not-a-type");
      const bodyCtx=[...k.ctx,k.domain];
      kont.push({kind:"lam-body",domain:k.domain,ctx:k.ctx});
      e=k.body; ctx=bodyCtx; returning=false; continue;
    }
    if(k.kind==="lam-body"){
      value=this.make("pi",k.domain,value);
      ctx=k.ctx; continue;
    }

    if(k.kind==="pi-domain"){
      const s=whnfIn(this,value,k.ctx);
      if(s[0]!=="sort") this.reject("not-a-type");
      const bodyCtx=[...k.ctx,k.domain];
      kont.push({kind:"pi-body",domainLevel:s[1],ctx:k.ctx,bodyCtx});
      e=k.body; ctx=bodyCtx; returning=false; continue;
    }
    if(k.kind==="pi-body"){
      const s=whnfIn(this,value,k.bodyCtx);
      if(s[0]!=="sort") this.reject("not-a-type");
      value=this.make("sort",levelIMax(k.domainLevel,s[1]));
      ctx=k.ctx; continue;
    }

    if(k.kind==="let-type"){
      const s=whnfIn(this,value,k.ctx);
      if(s[0]!=="sort") this.reject("not-a-type");
      kont.push({kind:"let-value",type:k.type,valueTerm:k.valueTerm,body:k.body,ctx:k.ctx});
      e=k.valueTerm; ctx=k.ctx; returning=false; continue;
    }
    if(k.kind==="let-value"){
      inCtx(this,k.ctx,()=>this.equal(value,k.type,k.ctx));
      const entry={__localDef:true,type:k.type,value:k.valueTerm};
      const bodyCtx=[...k.ctx,entry];
      kont.push({kind:"let-body",valueTerm:k.valueTerm,ctx:k.ctx});
      e=k.body; ctx=bodyCtx; returning=false; continue;
    }
    if(k.kind==="let-body"){
      value=this.substitute(value,k.valueTerm);
      ctx=k.ctx; continue;
    }

    throw new Error("unknown local continuation "+k.kind);
  }
}

function install(enabled){
  proto.infer=retainedInfer;
  if(!enabled) return;
  proto.infer=function(e,ctx=[]){
    if(this.localDefs!==true) return retainedInfer.call(this,e,ctx);
    return localContinuationInfer.call(this,e,ctx);
  };
}

for(const enabled of [false,true]){
  install(enabled);
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    console.log("LOCALDEF_CONTINUATION_FOCUS "+JSON.stringify({
      mode:enabled?"candidate":"baseline",name:row.name,expected:row.expected,
      status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      fallback_mode:r.fallback_mode??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null,
      correct:r.status==="UNKNOWN"||r.status===row.expected
    }));
  }
}
proto.infer=retainedInfer;
