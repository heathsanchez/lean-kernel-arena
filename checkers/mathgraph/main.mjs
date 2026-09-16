import {readFileSync,statSync} from "node:fs";
import {checkExport,productionConfig} from "../../genesis/production.mjs";

if(process.argv.length!==3){
  console.error("usage: node main.mjs <export.ndjson>");
  process.exit(3);
}

let input;
try {
  const config=productionConfig();
  if(statSync(process.argv[2]).size>config.inputBytes) process.exit(2);
  input=readFileSync(process.argv[2],"utf8");
  const r=checkExport(input,config);
  process.exit(r.status==="ACCEPT"?0:r.status==="REJECT"?1:2);
} catch (err) {
  console.error(String(err?.message??err));
  process.exit(3);
}
