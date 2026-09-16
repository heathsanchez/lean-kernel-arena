import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./compiled-le-nat-dictionary-layer.mjs";
import "./compiled-nat-class-reduction-layer.mjs";
import "./compiled-constant-decidable-nat-layer.mjs";
import "./compiled-nat-pow-layer.mjs";
import "./compiled-decidable-nat-composition-layer.mjs";
import "./compiled-nat-isvalidchar-consequence-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";


const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
function pretty(s){try{let x=JSON.parse(s),p=[];while(Array.isArray(x)&&x.length===3){p.push(String(x[2]));x=JSON.parse(x[0]);}return p.reverse().join('.')}catch{return s}}
function sk(e,d=12){if(!Array.isArray(e))return e;if(d<=0)return ['...',e[0]];if(e[0]==='const')return ['const',pretty(e[1]),e[2]??[]];return e.map(x=>sk(x,d-1));}
const p=K.Kernel.prototype,old=p.equal,rows=[];
p.equal=function(a,b,ctx=[]){try{return old.call(this,a,b,ctx)}catch(e){if(e?.status==='REJECT'&&pretty(this.currentDeclaration)==='Nat.zero_sub'){rows.push({reason:e.message,a:sk(a),b:sk(b),ctx:ctx.map(x=>sk(x,6)),wa:sk(this.whnf(a)),wb:sk(this.whnf(b)),na:sk(this.normal(a)),nb:sk(this.normal(b))});if(rows.length>8)rows.shift();}throw e}};
const r=K.checkExport(readFileSync('_build/tests/perf/grind-ring-5.ndjson','utf8'),CAPS,2_000_000);
console.log(JSON.stringify({result:r,rows}));
