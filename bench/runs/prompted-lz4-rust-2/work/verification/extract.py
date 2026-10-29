#!/usr/bin/env python3
"""Fail-closed translation of wasm-tools' linear WAT to a small Wasm AST."""
import hashlib, pathlib, re, subprocess
ROOT = pathlib.Path(__file__).resolve().parent.parent
WASM = ROOT / 'lz4-flex.wasm'
assert len(WASM.read_bytes()) == 7161
assert hashlib.sha256(WASM.read_bytes()).hexdigest() == '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775'
subprocess.run(['wasm-tools', 'validate', str(WASM)], check=True)
wat = subprocess.check_output(['wasm-tools', 'print', str(WASM)], text=True)
assert '(memory (;0;) 32 32)' in wat
assert '(export "lz4_decompress" (func 7))' in wat
assert '(global (;0;) (mut i32) i32.const 65536)' in wat
assert all('('+s+' ' not in wat for s in ('import', 'start', 'table', 'elem', 'tag'))
funcs = {}
for m in re.finditer(r'^  \(func \(;(\d+);\).*?^  \)', wat, re.M | re.S):
    lines = m[0].splitlines()
    params = lines[0].split('(param ')[1].split(')')[0].split()
    returns = '(result i32)' in lines[0]
    locals_ = []
    if lines[1].strip().startswith('(local '):
        locals_ = lines.pop(1).strip()[7:-1].split()
    assert set(params + locals_) <= {'i32', 'i64'}
    funcs[int(m[1])] = (len(params), len(locals_), returns, lines[1:-1])
assert set(funcs) == set(range(9))
assert funcs[7][0] == 4 and funcs[7][2]
reachable, pending = set(), [7]
while pending:
    f = pending.pop()
    if f in reachable:
        continue
    reachable.add(f)
    for line in funcs[f][3]:
        if line.strip().startswith('call '):
            pending.append(int(line.strip().split()[1]))
assert reachable == {1, 2, 7, 8}
binops = {'add':'add', 'sub':'sub', 'mul':'mul', 'div_u':'divU', 'and':'band',
          'or':'bor', 'xor':'bxor', 'shl':'shl', 'shr_u':'shr', 'eq':'eq',
          'ne':'ne', 'lt_u':'lt', 'le_u':'le', 'gt_u':'gt', 'ge_u':'ge'}
def translate(lines, function):
    code, blocks = [], []
    for raw in lines:
        line = re.sub(r'\(;.*?;\)|;;.*', '', raw).strip()
        words = line.split()
        op, args = words[0], words[1:]
        if op in ('block', 'loop'):
            assert not args
            blocks.append((len(code), op))
            code.append(None)
            continue
        if op == 'end':
            assert not args and blocks
            start, kind = blocks.pop()
            code[start] = f'.{kind} {len(code)+1}'
            instr = '.endBlock'
        elif op in ('br', 'br_if', 'call', 'local.get', 'local.set', 'local.tee', 'global.get', 'global.set'):
            assert len(args) == 1
            if op in ('br', 'br_if'): assert 0 <= int(args[0]) < len(blocks)
            name = {'br_if':'brIf', 'local.get':'getLocal', 'local.set':'setLocal',
                    'local.tee':'teeLocal', 'global.get':'getGlobal', 'global.set':'setGlobal'}.get(op, op)
            instr = f'.{name} {int(args[0])}'
        elif op in ('unreachable', 'return', 'select', 'memory.copy', 'memory.fill'):
            assert not args
            instr = '.' + {'unreachable':'trap', 'return':'ret', 'select':'select',
                            'memory.copy':'copy', 'memory.fill':'fill'}[op]
        elif op in ('i32.eqz', 'i32.ctz', 'i32.wrap_i64', 'i64.extend_i32_u'):
            assert not args
            instr = '.' + {'i32.eqz':'eqz', 'i32.ctz':'ctz', 'i32.wrap_i64':'wrap',
                            'i64.extend_i32_u':'extend'}[op]
        else:
            width, kind = op.split('.')
            assert width in ('i32', 'i64')
            bits = int(width[1:])
            if kind == 'const':
                assert len(args) == 1
                instr = f'.const {int(args[0]) % (1 << bits)}'
            elif kind in binops:
                assert not args
                instr = f'.bin .{binops[kind]} {bits}'
            else:
                assert kind in ('load', 'load8_u', 'load16_u', 'store', 'store8', 'store16')
                n = {'load8_u':1, 'load16_u':2, 'store8':1, 'store16':2}.get(kind, bits // 8)
                offset = 0
                for arg in args:
                    key, value = arg.split('=')
                    assert key in ('offset', 'align')
                    if key == 'offset':
                        offset = int(value)
                instr = f'.{"load" if kind.startswith("load") else "store"} {n} {offset}'
        code.append(instr)
    assert not blocks and all(i is not None for i in code)
    code.append('.ret')  # implicit function return
    generated = []
    def tree(items):
        if len(items) <= 8:
            body = ' else '.join(f'if pc = {i} then some ({ins})' for i,ins in enumerate(items)) + ' else none'
        else:
            mid = len(items)//2
            left, right = tree(items[:mid]), tree(items[mid:])
            body = f'if pc < {mid} then {left} pc else {right} (pc-{mid})'
        name = f'f{function}_code{len(generated)}'
        generated.append(f'def {name} (pc : Nat) : Option Wasm.Instr := {body}')
        return name
    root = tree(code)
    out.extend(generated)
    return root
# Decode the single active data segment; other module sections are not modeled.
data = re.findall(r'^  \(data \(;\d+;\) \(i32.const (\d+)\) "(.*)"\)$', wat, re.M)
assert len(data) == 1 and int(data[0][0]) == 65536
raw, decoded, i = data[0][1], [], 0
while i < len(raw):
    if raw[i] == '\\':
        assert re.fullmatch('[0-9a-f]{2}', raw[i+1:i+3])
        decoded.append(int(raw[i+1:i+3], 16)); i += 3
    else:
        assert 32 <= ord(raw[i]) < 127
        decoded.append(ord(raw[i])); i += 1
out = ['-- Generated by verification/extract.py from the hash-pinned shipped artifact.',
       'import Proofs.Wasm', 'namespace Artifact']
for f in sorted(reachable):
    params, locals_, returns, lines = funcs[f]
    out.append(f'def f{f} : Wasm.Func := ⟨{params}, {locals_}, {str(returns).lower()}, {translate(lines, f)}⟩')
out += ['def program : Nat → Option Wasm.Func',
        *[f'  | {f} => some f{f}' for f in sorted(reachable)], '  | _ => none',
        'def dataBytes : List Nat := ' + str(decoded), 'end Artifact', '']
(ROOT / 'Proofs' / 'Artifact.lean').write_text('\n'.join(out))
print('Artifact: exact SHA-256, Wasm validation, and reachable functions 1, 2, 7, 8 checked')
