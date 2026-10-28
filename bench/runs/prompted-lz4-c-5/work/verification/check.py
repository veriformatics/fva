#!/usr/bin/env python3
"""Rebuild, replay, falsify the checking setup, and run the unchanged artifact."""
from pathlib import Path
import hashlib, json, shutil, subprocess, sys, time
ROOT=Path(__file__).resolve().parent.parent
EXPECTED='8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
KERNEL=Path(shutil.which('lean')).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}

def run(args, output=None):
    print('+ '+' '.join(map(str,args)),flush=True)
    if output:
        with Path(output).open('w') as f:
            subprocess.run(list(map(str,args)),cwd=ROOT,stdout=f,check=True)
    else:
        subprocess.run(list(map(str,args)),cwd=ROOT,check=True)

def reject(args, needles, codes):
    print('+ expect rejection: '+' '.join(map(str,args)),flush=True)
    p=subprocess.run(list(map(str,args)),cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if p.returncode not in codes or not all(x in p.stdout for x in needles):
        raise RuntimeError(f'wrong rejection ({p.returncode}): {p.stdout}')
    print(p.stdout.strip(),flush=True)

def pinned(raw):
    return len(raw)==8469 and hashlib.sha256(raw).hexdigest()==EXPECTED

def inspect_export(path, required):
    names={0:''}; axioms=[]; declarations={}; counts={}
    for line in Path(path).open():
        obj=json.loads(line)
        if 'in' in obj:
            node=obj.get('str',obj.get('num'))
            parent=names[node['pre']]
            suffix=str(node.get('str',node.get('i')))
            names[obj['in']]=parent+'.'+suffix if parent else suffix
        for kind in ['def','thm','opaque','axiom','inductive','quot']:
            if kind not in obj: continue
            counts[kind]=counts.get(kind,0)+1
            rec=obj[kind]
            if 'name' in rec:
                name=names[rec['name']]; declarations[name]=kind
                if kind=='axiom': axioms.append(name)
    for name in required:
        if declarations.get(name)!='thm':
            raise RuntimeError(f'export missing theorem {name}')
    unexpected=set(axioms)-ALLOWED
    if unexpected: raise RuntimeError(f'unapproved axioms: {unexpected}')
    print('Export roots present; axioms:',sorted(axioms),'declarations:',counts,flush=True)
    return {'axioms':axioms,'declarations':counts,'roots':required}

def nanoda_config(export, config):
    Path(config).write_text(json.dumps({'export_file_path':str(export),
        'permitted_axioms':sorted(ALLOWED),'unpermitted_axiom_hard_error':True,
        'nat_extension':True,'string_extension':True,'print_success_message':True}))

def main():
    import os
    os.chdir(ROOT)
    t=time.monotonic()
    raw=Path('lz4-c.wasm').read_bytes()
    assert pinned(raw), 'artifact identity mismatch'
    assert not pinned(raw[:-1]+bytes([raw[-1]^1])), 'hash negative control accepted'
    for tool in ['lean','lake','wasmtime','wasm-tools']:
        assert shutil.which(tool), f'missing {tool}'
    for tool in ['nanoda_bin','con-ron','leanchecker-paranoid']:
        assert (KERNEL/tool).is_file(), f'missing {KERNEL/tool}'
    run(['wasm-tools','validate','lz4-c.wasm'])
    run([sys.executable,'verification/embed.py','--check'])
    run([sys.executable,'verification/decode.py','--check'])
    # Only generated local Lake products are removed, never dependency packages.
    shutil.rmtree('.lake/build',ignore_errors=True)
    run(['lake','build'])
    run(['lake','env',KERNEL/'leanchecker-paranoid','Proofs'])
    roots=Path('verification/roots.txt').read_text().split()
    run(['lake','env','lean','--run','verification/Export.lean','Proofs',*roots],
        'verification/proofs.ndjson')
    census=inspect_export('verification/proofs.ndjson',roots)
    nanoda_config('verification/proofs.ndjson','verification/nanoda.json')
    run([KERNEL/'nanoda_bin','verification/nanoda.json'])
    run([KERNEL/'con-ron','--jobs=2','verification/proofs.ndjson'])
    # The ordinary frontend must reject the obvious false proof.
    Path('verification/FrontendFalse.lean').write_text('example : (0 : Nat) = 1 := by rfl\n')
    reject(['lake','env','lean','verification/FrontendFalse.lean'],['error','0 = 1'],{1})
    # An intentionally malformed .olean contains Eq.refl 0, claimed to prove 0=1.
    run(['lake','env','lean','--run','verification/ProbeGen.lean'])
    reject(['lake','env',KERNEL/'leanchecker-paranoid','KernelProbe'],
        ['knownFalse','declaration type mismatch'],{1})
    run(['lake','env','lean','--run','verification/Export.lean','KernelProbe','knownFalse'],
        'verification/false-selected.ndjson')
    inspect_export('verification/false-selected.ndjson',['knownFalse'])
    nanoda_config('verification/false-selected.ndjson','verification/nanoda-false.json')
    reject([KERNEL/'nanoda_bin','verification/nanoda-false.json'],
        ['assertion failed: self.def_eq'],{101})
    reject([KERNEL/'con-ron','--jobs=2','verification/false-selected.ndjson'],
        ['rejected','type mismatch','knownFalse'],{1})
    run([sys.executable,'verification/runtime.py'])
    good=Path('verification/runtime.wast').read_text()
    old='(assert_return (invoke $test0 "check") (i32.const 1))'
    assert old in good
    Path('verification/runtime-false.wast').write_text(good.replace(old,
        '(assert_return (invoke $test0 "check") (i32.const 0))',1))
    reject(['wasmtime','wast','-C','cache=n','verification/runtime-false.wast'],
        ['expected','actual'],{1})
    run([sys.executable,'verification/size.py'])
    census['elapsed_seconds']=round(time.monotonic()-t,1)
    Path('verification/census.json').write_text(json.dumps(census,indent=2)+'\n')
    print('CHECK PASSED: scoped theorems replayed; false proofs rejected; Wasmtime cases passed.',flush=True)
    print('R1, R2, R3 remain UNPROVED in general. See VERIFICATION.md.',flush=True)

if __name__=='__main__': main()
