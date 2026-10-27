"""Extract handwritten definitions and exported theorem types for human review."""
from pathlib import Path
import re
import sys
roots={s.removeprefix('Verify.') for s in Path('verification/roots.txt').read_text().split()}
start=re.compile(r'^(?:noncomputable )?(def|abbrev|theorem|instance)\b')
parts=[]
for path in map(Path,['Proofs/Bounds.lean','Proofs/Spec.lean','Proofs/Conformance.lean','Proofs/Results.lean','Proofs/Certificates.lean']):
    lines=path.read_text().splitlines()
    indices=[i for i,l in enumerate(lines) if start.match(l)]+[len(lines)]
    for k,i in enumerate(indices[:-1]):
        line=lines[i]
        m=start.match(line)
        kind=m.group(1)
        name=line[m.end():].strip().split()[0].split('(')[0]
        if kind=='instance' or (kind=='theorem' and name not in roots):continue
        if path.name=='Certificates.lean' and kind!='theorem':continue
        block=lines[i:indices[k+1]]
        block=[l for l in block if l!='end Verify' and not l.startswith('#print') and not l.startswith('namespace ')]
        if kind=='theorem':block='\n'.join(block).split(':= by',1)[0].rstrip().splitlines()
        while block and (not block[-1].strip() or block[-1].startswith('--')):block.pop()
        parts+=['-- '+str(path)+':'+str(i+1),*block,'']
text='\n'.join(parts)+'\n'
if '--check' in sys.argv:
    assert Path('verification/review.txt').read_text()==text, 'review slice is stale'
else:
    Path('verification/review.txt').write_text(text)
print(f'Human statement/definition slice: {len(text.splitlines())} lines, {len(text.encode())} bytes')
