import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,whnf0=p.whnf;
const MAX_KEY_BYTES=262144;

p.run=function(...args){
  this.__structWhnf=new Map();
  this.__structWhnfKeys=new WeakMap();
  this.__structWhnfStats={hits:0,stores:0,skipped:0,keyBytes:0,maxKeyBytes:0};
  return run0.apply(this,args);
};

function keyOf(k,e){
  let byEpoch=k.__structWhnfKeys.get(e);
  const epoch=k.env?.size??0;
  if(byEpoch?.epoch===epoch)return byEpoch.key;
  const raw=JSON.stringify(e);
  const key=raw.length<=MAX_KEY_BYTES?epoch+"|"+raw:null;
  k.__structWhnfKeys.set(e,{epoch,key});
  return key;
}

p.whnf=function(e){
  if(this.localDefs===true||!Array.isArray(e))return whnf0.call(this,e);
  this.__structWhnf??=new Map();
  this.__structWhnfKeys??=new WeakMap();
  this.__structWhnfStats??={hits:0,stores:0,skipped:0,keyBytes:0,maxKeyBytes:0};
  const key=keyOf(this,e);
  if(key===null){this.__structWhnfStats.skipped++;return whnf0.call(this,e);}
  if(this.__structWhnf.has(key)){this.__structWhnfStats.hits++;return this.__structWhnf.get(key);}
  const out=whnf0.call(this,e);
  this.__structWhnf.set(key,out);
  const n=key.length;this.__structWhnfStats.stores++;this.__structWhnfStats.keyBytes+=n;
  if(n>this.__structWhnfStats.maxKeyBytes)this.__structWhnfStats.maxKeyBytes=n;
  return out;
};
