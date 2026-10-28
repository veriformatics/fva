#!/usr/bin/env python3
"""Lift restricted execution paths of the exact Wasm into ACSL-annotated C.

Every conditional branch is asserted, not assumed. WP proves that each trace
follows the actual instructions for all states in its precondition. No decoder
algorithm is reimplemented. See VERIFICATION.md for scope and trust boundaries.
"""
import hashlib
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
binary = ROOT / 'lz4-c.wasm'
assert len(binary.read_bytes()) == 8469
assert hashlib.sha256(binary.read_bytes()).hexdigest() == EXPECTED
subprocess.run(['wasm-tools', 'validate', str(binary)], check=True)
wat = subprocess.check_output(['wasm-tools', 'print', str(binary)], text=True)
assert '(export "LZ4_decompress_safe" (func 2))' in wat
assert '(memory (;0;) 32 32)' in wat


def function(index):
    """Parse the flat, no-block-results WAT emitted by wasm-tools print."""
    lines = wat.splitlines()
    start = next(i for i, s in enumerate(lines) if s.startswith(f'  (func (;{index};)'))
    header = lines[start]
    params = re.search(r'\(param ([^)]*)\)', header)[1].split()
    assert params == ['i32'] * (4 if index == 2 else 3)
    assert '(result i32)' in header
    locals_ = lines[start + 1].strip()
    assert locals_.startswith('(local ')
    local_types = locals_[7:-1].split()
    assert set(local_types) == {'i32'}
    count = len(params) + len(local_types)
    body = []
    groups = [body]
    for s in lines[start + 2:]:
        s = s.split(';;')[0].strip()
        s = re.sub(r'\(;.*?;\)', '', s).strip()
        if s == ')':
            break
        if s in ('block', 'loop'):
            child = []
            groups[-1].append((s, child))
            groups.append(child)
        elif s == 'end':
            assert len(groups) > 1
            groups.pop()
        else:
            assert '(' not in s and ')' not in s
            groups[-1].append(s)
    assert len(groups) == 1
    return count, body


MOVE_CONTRACT = r'''/*@
  requires memory: \valid(m + (0..2097151));
  requires length: n <= 14;
  requires source: 131072 <= s && s + n <= 2097152;
  requires destination: 131072 <= d && d + n <= 2097152;
  requires separate: d + n <= s || s + n <= d;
  assigns m[d..d+n-1];
  ensures result: \result == d;
  ensures copy: \forall integer k; 0 <= k < n ==> m[d+k] == \old(m[s+k]);
*/'''

DECODE_CONTRACT = r'''/*@
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires separate: d + cap <= s || s + size <= d;
  requires domain: cap == 0 || size == 0 ||
    (1 <= size <= 15 && m[s] / 16 == size - 1);
  assigns m[d..d+cap-1];
  ensures zero_capacity: cap == 0 ==>
    (\result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295));
  ensures empty_source: size == 0 ==> \result == 4294967295;
  ensures literals_fit: cap > 0 && size > 0 && size - 1 <= cap ==> \result == size - 1;
  ensures literals_large: cap > 0 && size > 0 && size - 1 > cap ==> \result == 4294967294;
  ensures content: cap > 0 && size > 0 && size - 1 <= cap ==>
    (\forall integer k; 0 <= k < size - 1 ==> m[d+k] == \old(m[s+1+k]));
*/'''


def cfg(body):
    """Resolve Wasm's relative structured branch depths to instruction indices."""
    code, labels = [], {}
    branch = 0
    def walk(nodes, targets):
        nonlocal branch
        for ins in nodes:
            if isinstance(ins, tuple):
                kind, child = ins
                target = object()
                if kind == 'loop': labels[target] = len(code)
                walk(child, targets + [target])
                if kind == 'block': labels[target] = len(code)
            else:
                parts = ins.split()
                if parts[0] in ('br', 'br_if'):
                    code.append((parts[0], targets[-1-int(parts[1])], branch))
                    if parts[0] == 'br_if': branch += 1
                else:
                    code.append(tuple(parts))
    walk(body, [])
    code.append(('return',))  # Implicit function return.
    resolved = []
    for ins in code:
        if ins[0] in ('br', 'br_if'):
            resolved.append((ins[0], labels[ins[1]], ins[2]))
        else: resolved.append(ins)
    return resolved


class Trace:
    def __init__(self, index, choices, fixed=None):
        self.index, self.choices, self.fixed = index, choices, fixed or {}
        self.lines, self.serial = [], 0
        self.affine = {'s': ('s', 0), 'd': ('d', 0)}

    def emit(self, line): self.lines.append('  ' + line)

    def value(self, expression, known=None):
        name = f't{self.serial}'
        self.serial += 1
        self.emit(f'unsigned int {name} = {expression};')
        return name, known

    def access(self, a, width, write=False):
        self.emit(f'/*@ assert physical_bounds: {a} <= 2097152 - {width}; */')
        if self.index == 4:
            base = 'd' if write else 's'
            region = f'{base} <= {a} && {a} + {width} <= {base} + n'
        else:
            region = f'(d <= {a} && {a} + {width} <= d + cap)'
            if not write:
                region += f' || (s <= {a} && {a} + {width} <= s + size)'
        self.emit(f'/*@ assert {"write" if write else "read"}_footprint: {region}; */')

    def run(self, contract, name, params):
        count, ast = function(self.index)
        code = cfg(ast)
        local = [('0U', 0)] * count
        for i, param in enumerate(params):
            if param in self.fixed:
                k = self.fixed[param]
                self.emit(f'/*@ assert fixed_parameter: {param} == {k}; */')
                local[i] = (f'{k}U', k)
            else: local[i] = (param, None)
        pc, stack, fuel = 0, [], 10000
        while True:
            fuel -= 1
            assert fuel > 0, 'trace did not terminate'
            ins = code[pc]; pc += 1
            op, *args = ins
            self.emit(f'/* Wasm instruction {pc-1}: {op} */')
            if op == 'i32.const':
                k = int(args[0]) % 2**32
                stack.append((f'{k}U', k))
            elif op == 'local.get': stack.append(local[int(args[0])])
            elif op in ('local.set', 'local.tee'):
                local[int(args[0])] = stack.pop()
                if op == 'local.tee': stack.append(local[int(args[0])])
            elif op == 'br': pc = args[0]
            elif op == 'br_if':
                (c, k), target, bid = stack.pop(), args[0], args[1]
                taken = bool(k) if k is not None else self.choices[bid]
                self.emit(f'/*@ assert branch_{bid}: {c} {"!=" if taken else "=="} 0; */')
                if taken: pc = target
            elif op == 'return':
                if self.index == 4:
                    for k in range(self.fixed['n']):
                        self.emit(f'/*@ assert copied_byte_{k}: m[d+{k}] == \\at(m[s+{k}],Pre); */')
                self.emit(f'return {stack.pop()[0]};')
                assert not stack
                break
            elif op == 'drop': stack.pop()
            elif op == 'select':
                (c, ck), (b, bk), (a, ak) = stack.pop(), stack.pop(), stack.pop()
                stack.append(self.value(f'{c} ? {a} : {b}', (ak if ck else bk) if ck is not None else None))
            elif op == 'call':
                assert self.index == 2 and args == ['4'], 'unsupported reached call'
                n, s, d = stack.pop()[0], stack.pop()[0], stack.pop()[0]
                stack.append(self.value(f'move4(m, {d}, {s}, {n})'))
            elif '.load' in op or '.store' in op:
                store = '.store' in op
                v = stack.pop()[0] if store else None
                a = stack.pop()[0]
                offset = next((int(x[7:]) for x in args if x.startswith('offset=')), 0)
                if offset:
                    self.emit(f'/*@ assert effective_address_no_wrap: {a} <= 4294967295 - {offset}; */')
                    a = self.value(f'{a} + {offset}U')[0]
                width = {'i32.load8_u': 1, 'i32.load16_u': 2, 'i32.load': 4,
                         'i32.store8': 1, 'i32.store': 4}[op]
                self.access(a, width, store)
                if store:
                    for j in range(width): self.emit(f'm[{a} + {j}U] = (unsigned char)({v} >> {j*8});')
                else:
                    stack.append(self.value(' | '.join(f'((unsigned int)m[{a} + {j}U] << {j*8})' for j in range(width))))
            elif op == 'i32.eqz':
                a, ak = stack.pop()
                stack.append(self.value(f'!{a}', int(not ak) if ak is not None else None))
            else:
                (b, bk), (a, ak) = stack.pop(), stack.pop()
                operations = {'i32.add': ('+', lambda a,b: a+b), 'i32.sub': ('-', lambda a,b: a-b),
                    'i32.and': ('&', lambda a,b: a&b), 'i32.xor': ('^', lambda a,b: a^b),
                    'i32.eq': ('==', lambda a,b: int(a==b)), 'i32.ne': ('!=', lambda a,b: int(a!=b)),
                    'i32.lt_u': ('<', lambda a,b: int(a<b)), 'i32.gt_u': ('>', lambda a,b: int(a>b)),
                    'i32.le_u': ('<=', lambda a,b: int(a<=b)), 'i32.ge_u': ('>=', lambda a,b: int(a>=b)),
                    'i32.shr_u': ('>>', lambda a,b: a>>(b&31)), 'i32.shl': ('<<', lambda a,b: a<<(b&31))}
                if op == 'i32.lt_s':
                    expression = f'(int){a} < (int){b}'
                    signed = lambda x: x if x < 2**31 else x - 2**32
                    k = int(signed(ak) < signed(bk)) if ak is not None and bk is not None else None
                else:
                    symbol, operation = operations[op]
                    expression = f'{a} {symbol} ' + (f'({b} & 31U)' if op in ('i32.shr_u', 'i32.shl') else b)
                    k = operation(ak, bk) % 2**32 if ak is not None and bk is not None else None
                v = self.value(expression, k)
                if self.index == 2 and op == 'i32.shr_u' and bk == 4:
                    self.emit(f'/*@ assert literal_length: {v[0]} == size - 1; */')
                affine = None
                if op == 'i32.add':
                    if a in self.affine and bk is not None:
                        base, off = self.affine[a]; affine = base, off + bk
                    elif b in self.affine and ak is not None:
                        base, off = self.affine[b]; affine = base, off + ak
                elif op == 'i32.sub' and a in self.affine and bk is not None:
                    base, off = self.affine[a]; affine = base, off - bk
                if affine is not None:
                    base, off = affine
                    off = (off + 2**31) % 2**32 - 2**31
                    self.affine[v[0]] = base, off
                    self.emit(f'/*@ assert address_normalization: {v[0]} == {base} + ({off}); */')
                stack.append(v)
        return contract + '\nunsigned int ' + name + '(unsigned char *m, ' + ', '.join('unsigned int ' + p for p in params) + ') {\n' + '\n'.join(self.lines) + '\n}\n'


def specialize(contract, predicate):
    return contract.replace('/*@', f'/*@\n  requires specialization: {predicate};', 1)


code = '/* Generated from SHA256 ' + EXPECTED + ' by verification/lift.py. */\n'
code += '_Static_assert(sizeof(unsigned int) == 4 && sizeof(int) == 4, "i32 machine model");\n'
for n in range(15):
    for forward in (False, True):
        predicate = f'n == {n} && d {"<" if forward else ">="} s'
        byte_contract = '\n'.join(f'  ensures byte_{k}: m[d+{k}] == \\old(m[s+{k}]);' for k in range(n))
        contract = MOVE_CONTRACT.replace('  ensures copy: \\forall integer k; 0 <= k < n ==> m[d+k] == \\old(m[s+k]);', byte_contract)
        code += Trace(4, {0: forward}, {'n': n}).run(specialize(contract, predicate),
            f'move4_{n}_{int(forward)}', ['d', 's', 'n'])
code += MOVE_CONTRACT + '\nunsigned int move4(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {\n  switch(n) {\n'
for n in range(15):
    code += f'  case {n}: if (d < s) return move4_{n}_1(m,d,s,n); else return move4_{n}_0(m,d,s,n);\n'
code += '  default: /*@ assert \\false; */ return 0;\n  }\n}\n'
common_choices = {0: False, 1: False, 2: True, 4: False, 5: False, 6: False, 20: False, 21: False}
cases = [
    ('zero_one', 'cap == 0 && size == 1', {0: False}, {'cap': 0, 'size': 1}),
    ('zero_other', 'cap == 0 && size != 1', {0: False, 3: True}, {'cap': 0}),
    ('empty', 'cap > 0 && size == 0', {0: False, 1: False, 2: True}, {'size': 0}),
    ('short_fail', 'cap > 0 && size > 0 && cap < size-1', {**common_choices, 19: True, 22: True}, {}),
    ('short_tight', 'cap > 0 && size > 0 && size-1 <= cap < size+11', {**common_choices, 19: True, 22: False}, {}),
    ('short_roomy', 'cap > 0 && size > 0 && cap >= size+11', {**common_choices, 19: False, 22: False}, {}),
]
for name, predicate, choices, fixed in cases:
    code += Trace(2, choices, fixed).run(specialize(DECODE_CONTRACT, predicate), 'decode_' + name, ['s', 'd', 'size', 'cap'])
code += DECODE_CONTRACT + '''
unsigned int decode2(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  if (cap == 0) {
    if (size == 1) return decode_zero_one(m,s,d,size,cap);
    return decode_zero_other(m,s,d,size,cap);
  }
  if (size == 0) return decode_empty(m,s,d,size,cap);
  if (cap < size-1) return decode_short_fail(m,s,d,size,cap);
  if (cap < size+11) return decode_short_tight(m,s,d,size,cap);
  return decode_short_roomy(m,s,d,size,cap);
}
'''
output = ROOT / 'verification' / 'traces.c'
output.write_text(code)
print(f'Checked artifact hash, exports, memory and Wasm validation; generated {output.relative_to(ROOT)}')

# Small, independent certificate: no data-copy loop or unproved callee contract.
BASE_CONTRACT = r'''/*@
  requires memory: \valid(m + (0..2097151));
  requires source: 131072 <= s <= 2097151 && size <= 1966080 && s + size <= 2097152;
  requires destination: 131072 <= d <= 2097151 && cap <= 1966080 && d + cap <= 2097152;
  requires domain: cap == 0 || size == 0 || (size == 1 && m[s] == 0);
  assigns \nothing;
  ensures result: \result == ((size == 1 && \old(m[s]) == 0) ? 0 : 4294967295);
*/'''
ZERO_MOVE_CONTRACT = r'''/*@
  requires zero: n == 0;
  assigns \nothing;
  ensures result: \result == d;
*/'''
base = '/* Independently checked base cases; generated from SHA256 ' + EXPECTED + '. */\n'
base += '_Static_assert(sizeof(unsigned int) == 4 && sizeof(int) == 4, "i32 machine model");\n'
for forward in (False, True):
    contract = specialize(ZERO_MOVE_CONTRACT, f'd {"<" if forward else ">="} s')
    base += Trace(4, {0: forward}, {'n': 0}).run(contract, f'move_zero_{int(forward)}', ['d', 's', 'n'])
base += ZERO_MOVE_CONTRACT + '''
unsigned int move4(unsigned char *m, unsigned int d, unsigned int s, unsigned int n) {
  if (d < s) return move_zero_1(m,d,s,n);
  return move_zero_0(m,d,s,n);
}
'''
base_cases = cases[:3] + [
    ('empty_tight', 'size == 1 && m[s] == 0 && 0 < cap < 12',
     {**common_choices, 19: True, 22: False}, {'size': 1}),
    ('empty_roomy', 'size == 1 && m[s] == 0 && cap >= 12',
     {**common_choices, 19: False, 22: False}, {'size': 1}),
]
for name, predicate, choices, fixed in base_cases:
    base += Trace(2, choices, fixed).run(specialize(BASE_CONTRACT, predicate), 'base_' + name, ['s', 'd', 'size', 'cap'])
base += BASE_CONTRACT + '''
unsigned int decode_base(unsigned char *m, unsigned int s, unsigned int d, unsigned int size, unsigned int cap) {
  if (cap == 0) {
    if (size == 1) return base_zero_one(m,s,d,size,cap);
    return base_zero_other(m,s,d,size,cap);
  }
  if (size == 0) return base_empty(m,s,d,size,cap);
  if (cap < 12) return base_empty_tight(m,s,d,size,cap);
  return base_empty_roomy(m,s,d,size,cap);
}
'''
(ROOT / 'verification' / 'base.c').write_text(base)
print('Generated independent verification/base.c (nine functions, no copy-loop contracts)')

