"""Emit byte data and single-instruction facts. Every fact is proved by rfl."""
from pathlib import Path


def generate(wasm: Path, out: Path):
    b = wasm.read_bytes()
    out.mkdir(parents=True, exist_ok=True)
    data = ',\n   '.join(','.join(map(str, b[i:i+16])) for i in range(0, len(b), 16))
    (out / 'Artifact.lean').write_text(
        '-- Generated from isqrt.wasm.\nnamespace Artifact\ndef bytes : List Nat :=\n  [' + data + ']\nend Artifact\n')
    code = b[58:]
    lines = ['import Semantics', 'import Artifact', 'namespace Wasm',
             'def steps (code : List Nat) : Nat → Config → Option Config',
             '  | 0, c => some c',
             '  | k+1, c => (step code c).bind (steps code k)',
             'end Wasm', 'namespace Verification',
             'abbrev code := Artifact.bytes.drop 58']
    pc = 0
    names = []
    while pc < len(code):
        start = pc
        op = code[pc]
        pc += 1
        ls = [f'v{i}' for i in range(6)]
        srcstack, srclabels = 'st', 'labels'
        dststack, dstlabels = 'st', 'labels'
        if op in (0x20, 0x21, 0x22):
            idx = code[pc]
            pc += 1
            if idx >= 6:
                raise ValueError('local index out of range')
            if op == 0x20:
                dststack = f'({ls[idx]}::st)'
            else:
                srcstack = '(a::st)'
                ls[idx] = 'a'
                dststack = 'st' if op == 0x21 else '(a::st)'
        elif op == 0x41:
            value, shift = 0, 0
            while True:
                x = code[pc]
                pc += 1
                value += (x & 127) << shift
                shift += 7
                if x < 128:
                    break
            dststack = f'({value % (2**32)}::st)'
        elif op == 0xad:
            srcstack, dststack = '(a::st)', '((a % 2^32)::st)'
        elif op in (0x6a, 0x6b, 0x76, 0x7e, 0x4b, 0x56):
            srcstack = '(b::a::st)'
            expr = {0x6a: '(a+b) % 2^32', 0x6b: '(a+2^32-b) % 2^32',
                    0x76: 'a / 2^(b % 32)', 0x7e: '(a*b) % 2^64',
                    0x4b: 'if b < a then 1 else 0', 0x56: 'if b < a then 1 else 0'}[op]
            dststack = f'(({expr})::st)'
        elif op == 0x1b:
            srcstack, dststack = '(c::b::a::st)', '((if c = 0 then b else a)::st)'
        elif op == 0x03 and code[pc] == 0x40:
            pc += 1
            dstlabels = f'({pc}::labels)'
        elif op == 0x0d and code[pc] == 0:
            pc += 1
            srcstack, srclabels, dstlabels = '(c::st)', '(target::labels)', '(target::labels)'
        elif op == 0x0b:
            if pc == len(code):
                srcstack, srclabels = '[a]', '[]'
            else:
                srclabels = '(target::labels)'
        else:
            raise ValueError(f'unsupported opcode {op:#x} at {start}')
        src = f'(.live {start} [v0,v1,v2,v3,v4,v5] {srcstack} {srclabels})'
        dst = f'some (.live {pc} [{",".join(ls)}] {dststack} {dstlabels})'
        if op == 0x0d:
            dst = f'if c = 0 then {dst} else some (.live target [{",".join(ls)}] st (target::labels))'
        elif op == 0x0b and pc == len(code):
            dst = 'some (.done a)'
        name = f'at_{start}'
        names.append(name)
        lines += [f'theorem {name} (v0 v1 v2 v3 v4 v5 a b c target : Nat) (st labels : List Nat) :',
                  f'    Wasm.step code {src} = {dst} := by rfl']
    lines += ['macro "execute_bytecode" : tactic =>',
              '  `(tactic| simp only [Wasm.steps, ' + ', '.join(names) +
              ', Option.bind_some, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv])',
              'end Verification']
    # Auto-bound unused parameters must be inferred: omit unused binders.
    import re
    for i, line in enumerate(lines):
        if line.startswith('theorem at_'):
            stmt = lines[i+1]
            nats = [v for v in ['v0','v1','v2','v3','v4','v5','a','b','c','target']
                    if re.search(r'\b' + v + r'\b', stmt)]
            lists = [v for v in ['st','labels'] if re.search(r'\b'+v+r'\b',stmt)]
            lines[i] = line[:line.index(' (')] + ' ('+' '.join(nats)+' : Nat)' + (
                ' ('+' '.join(lists)+' : List Nat)' if lists else '')+' :'
    (out / 'Bytecode.lean').write_text('\n'.join(lines)+'\n')


if __name__ == '__main__':
    import sys
    generate(Path(sys.argv[1]), Path(sys.argv[2]))
