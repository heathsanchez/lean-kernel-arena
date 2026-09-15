import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,whnf0=p.whnf;

function flatten(e){
 const args=[];let h=e;
 while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
 args.reverse();return {h,args};
}
function materialize(k,body,args){
 const work=[{kind:"visit",term:body,capture:args.length,depth:0,extra:0}],vals=[];
 while(work.length){
  const f=work.pop();
  if(f.kind==="build"){
   let out;
   if(f.tag==="proj")out=k.make("proj",f.name,f.index,vals.pop());
   else{const xs=new Array(f.n);for(let i=f.n-1;i>=0;i--)xs[i]=vals.pop();out=k.make(f.tag,...xs);}
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
     const ai=f.capture-1-j,shift=f.extra+f.depth;
     if(shift===0){vals.push(args[ai]);k.__headBetaDirectSplices=(k.__headBetaDirectSplices??0)+1;}
     else work.push({kind:"visit",term:args[ai],capture:ai,depth:0,extra:shift});
    }else{
     const ni=f.depth+(j-f.capture)+f.extra;
     vals.push(ni===i?e:k.make("var",ni));
    }
    break;
   }
   case "pi":case "lam":
    work.push({kind:"build",tag:e[0],n:2});
    work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth+1,extra:f.extra});
    work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});break;
   case "app":
    work.push({kind:"build",tag:"app",n:2});
    work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth,extra:f.extra});
    work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});break;
   case "proj":
    work.push({kind:"build",tag:"proj",name:e[1],index:e[2]});
    work.push({kind:"visit",term:e[3],capture:f.capture,depth:f.depth,extra:f.extra});break;
   case "let":
    work.push({kind:"build",tag:"let",n:3});
    work.push({kind:"visit",term:e[3],capture:f.capture,depth:f.depth+1,extra:f.extra});
    work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth,extra:f.extra});
    work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});break;
   default:k.unknown("head-beta-materialize-syntax");
  }
 }
 return vals.pop();
}
p.run=function(...args){this.__headBetaSpines=0;this.__headBetaDirectSplices=0;return run0.apply(this,args);};
p.whnf=function(e){
 if(!Array.isArray(e)||e[0]!=="app")return whnf0.call(this,e);
 const {h,args}=flatten(e);
 if(!Array.isArray(h)||h[0]!=="lam"||!args.length)return whnf0.call(this,e);
 let body=h,used=0;
 while(used<args.length&&Array.isArray(body)&&body[0]==="lam"){body=body[2];used++;}
 if(used===0)return whnf0.call(this,e);
 for(let i=0;i<used;i++){this.tick();this.need("application");this.need("reduction");}
 this.__headBetaSpines=(this.__headBetaSpines??0)+1;
 let out=materialize(this,body,args.slice(0,used));
 for(const a of args.slice(used))out=this.make("app",out,a);
 return whnf0.call(this,out);
};
