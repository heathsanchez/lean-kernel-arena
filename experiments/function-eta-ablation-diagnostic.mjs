import {Kernel,Stop,S,Pi,Lam,App} from "../genesis/kernel.mjs";

const C=name=>["const",name], V=n=>["var",n];
const base=[
  "sort-direct","sort","binders","reduction","declarations","application",
  "universes","theorems","proof-irrelevance"
];
const A="EtaA",F="etaF";
const AT=C(A),FT=Pi(AT,AT),CF=C(F);
const decls=[
  {kind:"axiom",name:A,levelParams:[],type:S(1)},
  {kind:"axiom",name:F,levelParams:[],type:FT}
];
function setup(caps){
  const q=new Kernel(caps);
  q.steps=0;q.params=new Set();q.env=new Map(decls.map(d=>[d.name,d]));
  return q;
}
const eta=Lam(AT,App(CF,V(0)));
for(const caps of [base,[...base,"function-eta"]]){
  const q=setup(caps);
  try {
    q.equal(eta,CF,[]);
    console.log("ETA_DIAGNOSTIC "+JSON.stringify({caps,status:"RETURNED",steps:q.steps,depth:q._lazyDeltaDepth??null}));
  } catch(e) {
    console.log("ETA_DIAGNOSTIC "+JSON.stringify({caps,status:e instanceof Stop?e.status:e?.name??"ERROR",
      reason:e?.message??String(e),steps:q.steps,depth:q._lazyDeltaDepth??null,
      stack:String(e?.stack??e).split("\n").slice(0,12)}));
  }
}
