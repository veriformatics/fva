#!/usr/bin/env python3
"""Fail-closed lifting of the decoder and its callees from the pinned artifact.

The supported instruction set is deliberately small. Operand-stack values are
captured in temporaries, so local.tee and later local.set preserve evaluation
order. Branches target the end of a block or the back edge of a loop.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = "8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6"
assert hashlib.sha256((ROOT / "lz4-c.wasm").read_bytes()).hexdigest() == EXPECTED
wat = subprocess.check_output(["wasm-tools", "print", str(ROOT / "lz4-c.wasm")], text=True)
assert '(memory (;0;) 32 32)' in wat
assert '(export "LZ4_decompress_safe" (func 2))' in wat
data = re.findall(r'\(data .*?\(i32.const (\d+)\) "(.*?)"\)', wat)
table = [0, 1, 2, 1, 0, 4, 4, 4, 0, 0, 0, 0xffffffff, 0xfffffffc, 1, 2, 3]
assert data == [('65536', ''.join('\\%02x' % b for w in table for b in w.to_bytes(4, 'little')))]
annotations = json.loads((ROOT / "verification/annotations.json").read_text())


def lift(index):
    body = re.search(r'  \(func \(;' + str(index) + r';\).*?\n  \)', wat, re.S).group()
    lines = body.splitlines()
    argc = 4 if index == 2 else 3
    nlocal = lines[1].count('i32')
    stack, scopes, code, temps, loops = [], [], [], [], []
    constants = {}
    label = 0

    def emit(s):
        code.append('  ' + s)

    def temp(expr):
        t = 't' + str(len(temps))
        temps.append(t)
        emit(f'uint32_t {t} = {expr};')
        stack.append(t)

    def pop():
        return stack.pop()

    def branch(depth):
        kind, ident, height = scopes[-1 - depth]
        assert len(stack) == height, (index, depth, stack, scopes)
        return ('back' if kind == 'loop' else 'end') + str(ident)

    binary = {'add': '+', 'sub': '-', 'and': '&', 'xor': '^', 'shl': '<<', 'shr_u': '>>',
              'eq': '==', 'ne': '!=', 'lt_u': '<', 'le_u': '<=', 'gt_u': '>', 'ge_u': '>='}
    for raw in lines[2:-1]:
        line = raw.split(';;')[0]
        line = re.sub(r'\(;.*?;\)', '', line).strip()
        if not line:
            continue
        op, *args = line.split()
        if op in ('block', 'loop'):
            label += 1
            ident = label
            scopes.append((op, ident, len(stack)))
            if op == 'loop':
                loops.append(ident)
                key = f'{index}:{ident}'
                emit(annotations.get(key, '/* LOOP ' + key + ' */') + f' /* FRAME {ident} */')
                emit('while (1) {')
            else:
                emit('{')
        elif op == 'end':
            kind, ident, height = scopes.pop()
            assert len(stack) == height
            if kind == 'loop':
                emit(f'break; back{ident}: ;')
            emit('}')
            if kind == 'block':
                emit(f'end{ident}: ;')
        elif op in ('br', 'br_if'):
            cond = pop() if op == 'br_if' else None
            target = branch(int(args[0]))
            emit(f'if ({cond}) goto {target};' if cond else f'goto {target};')
        elif op == 'local.get':
            temp('v' + args[0])
        elif op in ('local.set', 'local.tee'):
            x = pop()
            emit(f'v{args[0]} = {x};')
            if op == 'local.tee':
                stack.append(x)
        elif op == 'i32.const':
            temp(str(int(args[0]) % (2**32)) + 'u')
            constants[stack[-1]] = int(args[0]) % (2**32)
        elif op == 'i32.eqz':
            temp('!' + pop())
        elif op.startswith('i32.') and op[4:] in binary:
            b, a = pop(), pop()
            k = constants.get(b)
            if op == 'i32.and' and k in (3, 15):
                temp(f'{a} % {k+1}u')
            elif op == 'i32.and' and k == 4294967292:
                temp(f'{a} - {a} % 4u')
            elif op == 'i32.xor' and k == 4294967295:
                temp(f'4294967295u - {a}')
            elif op == 'i32.shr_u' and k is not None:
                assert k < 32
                temp(f'{a} / {2**k}u')
            elif op == 'i32.shl' and k is not None:
                assert k < 32
                temp(f'{a} * {2**k}u')
            else:
                temp(f'{a} {binary[op[4:]]} {b}')
        elif op == 'i32.lt_s':
            b, a = pop(), pop()
            assert constants.get(b) == 0
            temp(f'{a} >= 2147483648u')
        elif op in ('i32.load8_u', 'i32.load16_u', 'i32.load'):
            a = pop()
            offset = next((int(x[7:]) for x in args if x.startswith('offset=')), 0)
            bits = {'i32.load8_u': 8, 'i32.load16_u': 16, 'i32.load': 32}[op]
            temp(f'load{bits}((uint64_t){a} + {offset}u)')
        elif op in ('i32.store8', 'i32.store'):
            value, a = pop(), pop()
            offset = next((int(x[7:]) for x in args if x.startswith('offset=')), 0)
            bits = 8 if op == 'i32.store8' else 32
            emit(f'store{bits}((uint64_t){a} + {offset}u, {value});')
        elif op == 'call':
            target = int(args[0])
            assert target in (3, 4)
            c, b, a = pop(), pop(), pop()
            temp(f'f{target}({a}, {b}, {c})')
        elif op == 'drop':
            pop()
        elif op == 'select':
            c, b, a = pop(), pop(), pop()
            temp(f'{c} ? {a} : {b}')
        elif op == 'return':
            emit('return ' + pop() + ';')
        else:
            raise ValueError((index, line))
    assert not scopes and len(stack) == 1
    emit('return ' + pop() + ';')
    # Infer loop frames syntactically; only invariants/variants are hand-written.
    for ident in loops:
        marker = f'/* FRAME {ident} */'
        start = next(i for i, s in enumerate(code) if marker in s)
        finish = next(i for i, s in enumerate(code) if f'back{ident}: ;' in s)
        writes = sorted(set(re.findall(r'^  (v[0-9]+) = [^=]', '\n'.join(code[start+1:finish+1]), re.M)))
        frame = ('mem[db .. de-1]' if index == 2 else
                 'mem[\\at(v0,Pre) .. \\at(v0,Pre)+\\at(v2,Pre)-1]')
        writes.append(frame)
        frame_text = 'loop assigns ' + ', '.join(writes) + ';\n '
        annot = code[start].replace(marker, '')
        if 'loop variant' in annot:
            annot = annot.replace('loop variant', frame_text + 'loop variant')
        elif '/*@' in annot:
            annot = annot.replace('*/', frame_text + '*/')
        else:
            annot += '/*@ ' + frame_text + '*/'
        code[start] = annot
    contract = annotations.get(str(index), '')
    params = ', '.join(f'uint32_t v{i}' for i in range(argc))
    locals_ = ', '.join(f'v{i} = 0' for i in range(argc, argc+nlocal))
    return f'{contract}\nuint32_t f{index}({params}) {{\n  uint32_t {locals_};\n' + '\n'.join(code) + '\n}\n', loops


out = ['/* Generated by verification/lift.py from the pinned Wasm bytes. */', '#include "memory.h"']
for i in (3, 4, 2):
    function, loops = lift(i)
    out.append(function)
    print(f'f{i}: loop labels {loops}')
(ROOT / 'verification/lifted.c').write_text('\n'.join(out))

# Verify the exact early-return prefix independently, without any loop summary.
# The assertion proves that the omitted suffix is unreachable under this
# theorem's extra hypothesis. No "assume false" is used.
function, _ = lift(2)
prefix = function[function.index('uint32_t f2('):].split('  uint32_t t17 = v1;')[0]
assert prefix.endswith('  if (t16) goto end1;\n')
prefix = prefix.replace('uint32_t f2(', 'uint32_t f2_early(', 1)
early_contract = r'''/*@ requires arena;
 requires v0 == sb && v1 == db;
 requires v2 == se-sb && v3 == de-db;
 requires v2 == 0 || v3 == 0;
 assigns \nothing;
 ensures \result == ((v3 == 0 && v2 == 1 && mem[v0] == 0) ? 0 : 4294967295);
*/
'''
(ROOT / 'verification/early.c').write_text(
    '#include "memory.h"\n' + early_contract + prefix +
    '  /*@ assert unreachable_suffix: \\false; */\n  }\nend1: ;\n  return v4;\n}\n')
