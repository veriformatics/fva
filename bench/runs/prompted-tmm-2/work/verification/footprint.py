"""Count the unfolded semantic dependency closure of exported theorem TYPES.
Proof bodies are excluded; definitions, opaque values, and inductive rules are included.
This is a size report, not a proof checker.
"""
import json
from collections import Counter
from pathlib import Path
import sys

names = {0: ''}
exprs, decls = {}, {}
for line in Path(sys.argv[1]).open():
    row = json.loads(line)
    if 'in' in row:
        part = row.get('str', row.get('num'))
        suffix = part.get('str', str(part.get('i')))
        pre = names[part['pre']]
        names[row['in']] = pre + ('.' if pre else '') + suffix
    elif 'ie' in row:
        exprs[row['ie']] = {k:v for k,v in row.items() if k != 'ie'}
    elif 'inductive' in row:
        group = row['inductive']
        for kind, entries in group.items():
            for entry in entries:
                decls[entry['name']] = (kind, entry, group)
    elif any(k in row for k in ['def','opaque','thm','axiom','quot']):
        kind = next(iter(row))
        entry = row[kind]
        decls[entry['name']] = (kind, entry, None)

seen_exprs, seen_decls = set(), set()
pending_exprs, pending_decls = [], []
roots = sys.argv[3:]
for root in roots:
    ids = [idx for idx,name in names.items() if name == root]
    if len(ids) != 1 or ids[0] not in decls:
        raise RuntimeError('Missing or ambiguous exported root: ' + root)
    pending_exprs.append(decls[ids[0]][1]['type'])

def expression_edges(row):
    if 'const' in row:
        pending_decls.append(row['const']['name'])
    if 'proj' in row:
        pending_decls.append(row['proj']['typeName'])
    for kind, fields in [('app',['fn','arg']), ('lam',['type','body']),
                         ('forallE',['type','body']), ('letE',['type','value','body']),
                         ('proj',['struct']), ('mdata',['expr'])]:
        if kind in row:
            for field in fields:
                if field in row[kind]:
                    pending_exprs.append(row[kind][field])

while pending_exprs or pending_decls:
    while pending_exprs:
        idx = pending_exprs.pop()
        if idx not in seen_exprs:
            seen_exprs.add(idx)
            expression_edges(exprs[idx])
    if not pending_decls:
        continue
    idx = pending_decls.pop()
    if idx in seen_decls:
        continue
    seen_decls.add(idx)
    kind, entry, group = decls[idx]
    pending_exprs.append(entry['type'])
    if kind in ['def','opaque']:
        pending_exprs.append(entry['value'])
    if group:
        for entries in group.values():
            for item in entries:
                pending_decls.append(item['name'])
                for rule in item.get('rules', []):
                    pending_exprs.append(rule['rhs'])

report = {'roots': roots, 'declarations': len(seen_decls),
    'kinds': dict(Counter(decls[i][0] for i in seen_decls)),
    'expression_nodes': len(seen_exprs),
    'expression_json_bytes': sum(len(json.dumps(exprs[i],separators=(',',':')).encode()) for i in seen_exprs),
    'names': sorted(names[i] for i in seen_decls)}
Path(sys.argv[2]).write_text(json.dumps(report,indent=2)+'\n')
print('Unfolded statement/definition closure:', report['declarations'],
      'declarations,', report['expression_nodes'], 'expression nodes,',
      report['expression_json_bytes'], 'bytes of expression JSON')
