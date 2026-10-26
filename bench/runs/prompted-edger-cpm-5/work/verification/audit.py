#!/usr/bin/env python3
"""Audit the complete export and construct well-formed but ill-typed proofs."""
import collections
import json
from pathlib import Path
import sys

path = Path(sys.argv[1])
rows = [json.loads(s) for s in path.read_text().splitlines()]
names = {0:''}
exprs = {}
levels = {}
decls = {}
for x in rows:
    if 'in' in x:
        y = x.get('str',x.get('num'))
        names[x['in']] = (names[y['pre']]+'.'+str(y.get('str',y.get('i')))).lstrip('.')
    if 'ie' in x:
        exprs[x['ie']] = x
    if 'il' in x:
        levels[x['il']] = x
    for k in ['def','thm','axiom','inductive','quot','opaque']:
        if k in x:
            y = x[k]
            if isinstance(y,dict) and 'name' in y:
                decls[names[y['name']]] = (k,y)
expected = {'Verification.r1_exact_and_overflow','Verification.r2_rounding_intervals',
            'Verification.r2_fractional_sample_threshold'}
assert all(decls[n][0]=='thm' for n in expected)
axioms = {n for n,(k,_) in decls.items() if k=='axiom'}
assert axioms == {'propext','Quot.sound','Classical.choice'}, axioms
assert not any('sorryAx' in n or 'Lean.ofReduceBool' in n or 'native_decide' in n for n in names.values())
print('Export audit: all three target theorems present; only propext, Quot.sound, Classical.choice')
print('Export audit:',len(exprs),'expressions;',len(decls),'named declarations')

# List the entire statement/definition closure, without proof bodies.
by_name = dict(decls)
for x in rows:
    if 'inductive' in x:
        for kind in ['types','ctors','recs']:
            for y in x['inductive'][kind]:
                by_name[names[y['name']]] = (kind,y)
def references(root):
    todo = [root]
    seen = set()
    result = set()
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        x = exprs[i]
        if 'const' in x:
            result.add(names[x['const']['name']])
        for k in ['app','lam','forallE','letE','proj']:
            if k in x:
                y = x[k]
                todo.extend(y[j] for j in ['fn','arg','type','body','value','struct'] if j in y)
                if 'typeName' in y:
                    result.add(names[y['typeName']])
    return result
closure = set()
todo = set().union(*(references(decls[n][1]['type']) for n in expected))
while todo:
    n = todo.pop()
    if n in closure:
        continue
    closure.add(n)
    k,y = by_name[n]
    roots = [y['type']]
    if k in ['def','opaque']:
        roots.append(y['value'])
    roots.extend(r['rhs'] for r in y.get('rules',[]))
    for i in roots:
        todo.update(references(i)-closure)
# The numbers include standard-library arithmetic and logic, rather than
# hiding those definitions in the claimed local specification size.
counts = collections.Counter(by_name[n][0] for n in closure)
path.with_name('statement-dependencies.tsv').write_text(''.join(
    f'{by_name[n][0]}\t{n}\n' for n in sorted(closure)))
print('Statement closure:',len(closure),'declarations;',dict(sorted(counts.items())))

# Two false proofs with completely valid serialization. Both kernels must
# reject their TYPES, not merely reject a corrupt file or missing import.
next_expr = max(exprs)+1
next_name = max(names)+1
new = []
def expr(body):
    global next_expr
    i = next_expr
    next_expr += 1
    new.append(dict(ie=i,**body))
    return i
def const(n,us=[]):
    return expr({'const':{'name':next(i for i,s in names.items() if s==n),'us':us}})
def app(f,a):
    return expr({'app':{'fn':f,'arg':a}})
def output(file,typ,val):
    extra = [{'in':next_name,'str':{'pre':0,'str':'KnownFalseProof'}},
             {'thm':{'all':[next_name],'levelParams':[],'name':next_name,'type':typ,'value':val}}]
    with path.with_name(file).open('w') as f:
        for x in rows+new+extra:
            f.write(json.dumps(x,separators=(',',':'))+'\n')
false = const('False')
true_intro = const('True.intro')
output('false-proposition.export',false,true_intro)
new = []
next_expr = max(exprs)+1
level_one = next(i for i,x in levels.items() if x.get('succ')==0)
nat = const('Nat')
zero = expr({'natVal':'0'})
one = expr({'natVal':'1'})
eq = app(app(app(const('Eq',[level_one]),nat),zero),one)
refl = app(app(const('Eq.refl',[level_one]),nat),zero)
output('false-equality.export',eq,refl)
# A third negative checks the axiom audit itself: kernels correctly permit
# axioms, so rejecting an explicit assumption False is the audit's job.
new = []
next_expr = max(exprs)+1
false = const('False')
extra = [{'in':next_name,'str':{'pre':0,'str':'KnownFalseAxiom'}},
         {'axiom':{'name':next_name,'levelParams':[],'type':false,'isUnsafe':False}}]
with path.with_name('false-axiom.export').open('w') as f:
    for x in rows+new+extra:
        f.write(json.dumps(x,separators=(',',':'))+'\n')
