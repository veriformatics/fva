#!/usr/bin/env python3
"""Bind a stack-machine model to the hash-pinned shipped Wasm function 7.
No source compilation is involved. Reject unsupported syntax rather than guessing.
"""
import hashlib
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXPECTED = '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775'

def program():
    data = (ROOT / 'lz4-flex.wasm').read_bytes()
    assert len(data) == 7161 and hashlib.sha256(data).hexdigest() == EXPECTED
    wat = subprocess.check_output(['wasm-tools', 'print', str(ROOT / 'lz4-flex.wasm')], text=True)
    assert '(memory (;0;) 32 32)' in wat
    assert '(export "lz4_decompress" (func 7))' in wat
    section = wat.split('  (func (;7;) ', 1)[1].split('  (func (;8;) ', 1)[0]
    lines = section.splitlines()
    assert lines[0] == '(type 4) (param i32 i32 i32 i32) (result i32)'
    assert lines[1].strip() == '(local ' + ' '.join(['i32'] * 17 + ['i64'] * 7) + ')'
    ops, labels, pending = [], [], []
    height, unreachable = 0, False
    for raw in lines[2:]:
        line = raw.split(';;', 1)[0].strip()
        if line == ')':
            continue
        parts = line.split()
        if not parts:
            continue
        name = parts[0]
        if name in ('block', 'loop'):
            # All labels have no parameters or results, and have empty entry stack.
            assert height == 0 or unreachable, (line, height)
            label = {'kind': name, 'start': len(ops), 'height': height, 'uses': []}
            labels.append(label)
            continue
        if name == 'end':
            label = labels.pop()
            assert height == label['height'] or unreachable
            for index in label['uses']:
                target = label['start'] if label['kind'] == 'loop' else len(ops)
                ops[index] = ops[index].replace('TARGET', str(target))
            height, unreachable = label['height'], False
            continue
        if name in ('br', 'br_if'):
            depth = int(parts[1])
            label = labels[-1-depth]
            if name == 'br_if':
                height -= 1
            assert height == 0 or unreachable
            label['uses'].append(len(ops))
            ops.append('Op::' + ('Jump' if name == 'br' else 'JumpIf') + '(TARGET)')
            if name == 'br':
                unreachable = True
            continue
        if name == 'i32.const':
            ops.append(f'Op::Const({int(parts[1]) % 2**32})')
            height += 1
        elif name.startswith('local.'):
            kind = {'local.get': 'Get', 'local.set': 'Set', 'local.tee': 'Tee'}[name]
            index = int(parts[1])
            assert 0 <= index < 28
            ops.append(f'Op::{kind}({index})')
            height += {'Get': 1, 'Set': -1, 'Tee': 0}[kind]
        elif '.load' in name or '.store' in name:
            width = {'i32.load8_u': 1, 'i32.load16_u': 2, 'i32.load': 4, 'i64.load': 8,
                     'i32.store8': 1, 'i32.store16': 2, 'i32.store': 4, 'i64.store': 8}[name]
            offset = 0
            for arg in parts[1:]:
                if arg.startswith('offset='):
                    offset = int(arg[7:])
                else:
                    assert arg.startswith('align=')
            is_load = '.load' in name
            ops.append(f'Op::{"Load" if is_load else "Store"}({width}, {offset})')
            height -= 0 if is_load else 2
        elif name in ('memory.copy', 'memory.fill'):
            ops.append('Op::' + ('Copy' if name == 'memory.copy' else 'Fill'))
            height -= 3
        elif name == 'select':
            ops.append('Op::Select')
            height -= 2
        elif name == 'i32.eqz':
            ops.append('Op::Eqz')
        elif name.startswith('i32.'):
            kind = {'i32.add': 'Add', 'i32.sub': 'Sub', 'i32.and': 'And', 'i32.shr_u': 'Shr',
                    'i32.eq': 'Eq', 'i32.ne': 'Ne', 'i32.gt_u': 'Gt', 'i32.ge_u': 'Ge',
                    'i32.lt_u': 'Lt', 'i32.le_u': 'Le'}[name]
            ops.append(f'Op::Binary(Bin::{kind})')
            height -= 1
        elif name == 'return':
            assert height == 1 or unreachable
            ops.append('Op::Return')
            unreachable = True
        elif name == 'unreachable' or name == 'call':
            # We make NO claim about a run reaching a call: it is Unsupported.
            # Thus no callee semantics are trusted by our concrete proofs.
            if name == 'call':
                assert int(parts[1]) in (1, 2, 8)
            ops.append('Op::Unsupported')
            unreachable = True
        else:
            raise AssertionError(line)
        assert height >= 0 or unreachable, line
    assert not labels
    assert not any('TARGET' in op for op in ops)
    # These programs never fall out of the function; falling out is Unsupported too.
    ops.append('Op::Unsupported')
    return ops

def tree(ops, lo, hi, indent):
    if hi - lo == 1:
        return ' ' * indent + ops[lo]
    mid = (lo + hi) // 2
    return (' ' * indent + f'if pc < {mid} {{\n' + tree(ops, lo, mid, indent+4)
            + '\n' + ' '*indent + '} else {\n' + tree(ops, mid, hi, indent+4)
            + '\n' + ' '*indent + '}')

def generate():
    ops = program()
    return ('// Generated by verification/generate.py; do not edit.\n'
            f'// Artifact SHA256: {EXPECTED}; function 7, {len(ops)} flattened operations.\n'
            'verus! {\npub open spec fn program(pc: int) -> Op {\n'
            f'    if pc < 0 || pc >= {len(ops)} {{ Op::Unsupported }} else {{\n'
            + tree(ops, 0, len(ops), 8) + '\n    }\n}\n}\n')

if __name__ == '__main__':
    result = generate()
    target = ROOT / 'verification' / 'program.inc.rs'
    if sys.argv[1:] == ['--check']:
        assert target.read_text() == result, 'generated model differs; rerun generate.py and review'
        print('PASS: exact artifact hash, export, memory, and generated opcode model')
    else:
        assert not sys.argv[1:]
        target.write_text(result)
        print('Wrote', target.relative_to(ROOT))
