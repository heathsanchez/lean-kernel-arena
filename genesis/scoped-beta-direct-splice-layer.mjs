import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,retainedRun=p.run,retainedWhnf=p.whnf;

function collect(root){
  const args=[];let cur=root;
  while(Array.isArray(cur)&&cur[0]==="app"&&Array.isArray(cur[1])&&cur[1][0]==="lam"){
    args.push(cur[2]);cur=cur[1][2];
  }
  return {body:cur,args};
}
function materialize(k,body,args){
  const work=[{kind:"visit",term:body,capture:args.length,depth:0,extra:0}],vals=[];
  while(work.length){
    const f=work.pop();
    if(f.kind==="build"){
      let out;
      if(f.tag==="proj") out=k.make("proj",f.name,f.index,vals.pop());
      else{
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--)xs[i]=vals.pop();
        out=k.make(f.tag,...xs);
      }
      vals.push(out);continue;
    }
    const e=f.term;k.tick();
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":vals.push(e);break;
      case "var":{
        const i=e[1];
        if(i<f.depth){vals.push(e);break;}
        const j=i-f.depth;
        if(j<f.capture){
          const argIndex=f.capture-1-j,shift=f.extra+f.depth;
          if(shift===0){
            vals.push(args[argIndex]);
            k.__betaSpliceHits=(k.__betaSpliceHits??0)+1;
          }else{
            work.push({kind:"visit",term:args[argIndex],capture:argIndex,depth:0,extra:shift});
          }
        }else{
          const ni=f.depth+(j-f.capture)+f.extra;
          vals.push(ni===i?e:k.make("var",ni));
        }
        break;
      }
      case "pi":case "lam":
        work.push({kind:"build",tag:e[0],n:2});
        work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth+1,extra:f.extra});
        work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2});
        work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth,extra:f.extra});
        work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2]});
        work.push({kind:"visit",term:e[3],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3});
        work.push({kind:"visit",term:e[3],capture:f.capture,depth:f.depth+1,extra:f.extra});
        work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth,extra:f.extra});
        work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      default:k.unknown("beta-splice-syntax");
    }
  }
  return vals.pop();
}
p.run=function(...args){this.__betaSpliceHits=0;return retainedRun.apply(this,args);};
p.whnf=function(e){
  if(!Array.isArray(e)||e[0]!=="app")return retainedWhnf.call(this,e);
  const c=collect(e);
  if(c.args.length<2)return retainedWhnf.call(this,e);
  for(let i=0;i<c.args.length;i++){this.tick();this.need("application");this.need("reduction");}
  const out=materialize(this,c.body,c.args);
  return retainedWhnf.call(this,out);
};
