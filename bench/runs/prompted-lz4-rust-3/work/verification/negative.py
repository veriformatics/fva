#!/usr/bin/env python3
"""Change the value of a well-formed theorem to an existing, ill-typed term.
   This tests proof rejection, not merely JSON syntax rejection."""
import json
import sys
from pathlib import Path
src, dst, target = sys.argv[1:]
rows = [json.loads(s) for s in Path(src).read_text().splitlines()]
names = {0: ''}
for r in rows:
    if 'in' in r:
        if 'str' in r:
            n = r['str']
            names[r['in']] = '.'.join(filter(None, [names[n['pre']], n['str']]))
        elif 'num' in r:
            n = r['num']
            names[r['in']] = names[n['pre']] + '.' + str(n['i'])
# Nat literal zero has type Nat, never the equality/Bool theorem being checked.
zero = next(r['ie'] for r in rows if r.get('natVal') == '0')
count = 0
for r in rows:
    if 'thm' in r and names[r['thm']['name']] == target:
        r['thm']['value'] = zero
        count += 1
assert count == 1, (count, target)
Path(dst).write_text(''.join(json.dumps(r, separators=(',', ':'))+'\n' for r in rows))
