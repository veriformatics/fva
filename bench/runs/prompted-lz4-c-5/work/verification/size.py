#!/usr/bin/env python3
from pathlib import Path
import json
sets={
 'statements_and_semantics':['Proofs/Binary.lean','Proofs/Wasm.lean','Proofs/Results.lean'],
 'generated_data':['Proofs/Bytes.lean','Proofs/Code.lean'],
 'check_support':['verification/check.py','verification/embed.py','verification/decode.py',
   'verification/runtime.py','verification/Export.lean','verification/ProbeGen.lean',
   'verification/cases.json','verification/roots.txt','verification/size.py'],
}
result={}
for kind,files in sets.items():
 rows=[]
 for file in files:
  data=Path(file).read_bytes()
  rows.append({'file':file,'lines':len(data.splitlines()),'bytes':len(data)})
 result[kind]={'files':rows,'lines':sum(x['lines'] for x in rows),'bytes':sum(x['bytes'] for x in rows)}
extra=[]
for file,prefixes in [('Proofs/Code.lean',('theorem linked','def function','  if i ==')),('Proofs/Bytes.lean',('def byteAt','  let c ←','  c[a %'))]:
    extra.extend(l for l in Path(file).read_text().splitlines(keepends=True) if l.startswith(prefixes))
result['formal_review_with_generated_routing']={'lines':result['statements_and_semantics']['lines']+len(extra),
    'bytes':result['statements_and_semantics']['bytes']+sum(len(l.encode()) for l in extra)}
Path('verification/sizes.json').write_text(json.dumps(result,indent=2)+'\n')
for key,values in result.items(): print(f'{key}: {values["lines"]} lines, {values["bytes"]} bytes')
