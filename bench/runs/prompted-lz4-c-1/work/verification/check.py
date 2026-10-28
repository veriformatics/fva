#!/usr/bin/env python3
"""Fresh source checking, independent kernel replay, negative controls, artifact execution."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
WORK = ROOT / '.lake' / 'verification'
WORK.mkdir(parents=True, exist_ok=True)
LEANBIN = Path(shutil.which('lean')).resolve().parent
ROOTS = ['Artifact.code_link', 'Artifact.metadata_link', 'Verification.no_input',
         'Verification.zero_capacity', 'Certificates.checked_cases']
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def run(args, *, env=None, stdout=None):
    p = subprocess.run([str(a) for a in args], env=env, text=True,
                       stdout=stdout or subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode:
        raise RuntimeError(f'Command failed ({p.returncode}): {args}\n{p.stdout or ""}\n{p.stderr}')
    return p.stdout or ''

def tool(name):
    p = LEANBIN / name
    assert p.is_file(), f'Required offline checker missing: {p}'
    return p

def artifact():
    bs = Path('lz4-c.wasm').read_bytes()
    assert len(bs) == 8469
    assert hashlib.sha256(bs).hexdigest() == '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
    source = Path('Proofs/Artifact.lean').read_text()
    literal = re.search(r'\ndef bytes : Bytes := \[([0-9,\s]+)\]\ndef functions', source)
    assert literal, 'Missing literal byte quotation'
    quoted = [int(x) for x in literal[1].split(',') if x.strip()]
    assert quoted == list(bs), 'Lean byte quotation differs from the shipped artifact'
    run(['wasm-tools','validate','lz4-c.wasm'])
    print('PASS: original artifact hash, every quoted byte, Wasm validation', flush=True)

def audit_export(path):
    names = {0:''}; declared = set(); axioms = set()
    for line in path.read_text().splitlines():
        x = json.loads(line)
        if 'in' in x:
            b = x.get('str',x.get('num'))
            names[x['in']] = '.'.join(filter(None,[names[b['pre']],str(b.get('str',b.get('i')))]))
        for kind in ['def','thm','opaque','axiom']:
            if kind in x:
                name = names[x[kind]['name']]; declared.add(name)
                if kind == 'axiom': axioms.add(name)
    assert set(ROOTS) <= declared, 'Export omitted a required theorem'
    assert axioms <= AXIOMS, f'Unapproved axioms in proof closure: {axioms-AXIOMS}'
    print('PASS: theorem export complete; axioms: '+str(sorted(axioms)), flush=True)

def kernels(stream, temp):
    conf = temp / 'nanoda.json'
    conf.write_text(json.dumps({'export_file_path':str(stream), 'permitted_axioms':sorted(AXIOMS),
      'unpermitted_axiom_hard_error':True, 'nat_extension':True, 'string_extension':True,
      'print_success_message':True}))
    print('Checking with Nanoda...',flush=True)
    print(run([tool('nanoda_bin'),conf]).strip(),flush=True)
    print('Checking with Con-ron (--verified)...',flush=True)
    print(run([tool('con-ron'),'--verified','--jobs=2',stream]).strip(),flush=True)

def negative_controls(env, temp):
    good = temp/'control.ndjson'
    with good.open('w') as out:
        run([tool('leanexport'),'Proofs.Probe','--','False','Probe.good'],env=env,stdout=out)
    kernels(good,temp)
    run([sys.executable,'verification/negative.py',good,temp])
    for name in ['false','zero_eq_one']:
        stream = temp/(name+'.ndjson')
        conf = temp/(name+'.json')
        conf.write_text(json.dumps({'export_file_path':str(stream), 'permitted_axioms':[],
          'unpermitted_axiom_hard_error':True, 'nat_extension':True, 'string_extension':True}))
        p = subprocess.run([tool('nanoda_bin'),conf],capture_output=True,text=True)
        assert p.returncode == 101 and 'src/tc.rs' in p.stderr and 'self.def_eq(u, v)' in p.stderr, p
        p = subprocess.run([tool('con-ron'),'--verified','--jobs=2',stream],capture_output=True,text=True)
        assert p.returncode == 1 and 'rejected: type mismatch' in p.stderr, p
        print(f'PASS: both independent kernels rejected forged {name} proof terms',flush=True)
    bad = temp/'Bad.lean'
    bad.write_text('theorem forged : (0 : Nat) = 1 := by rfl\n')
    p = subprocess.run(['lean',str(bad)],env=env,capture_output=True,text=True)
    assert p.returncode != 0 and 'Tactic `rfl` failed' in p.stdout, p
    print('PASS: Lean rejected false source proof 0 = 1',flush=True)

def main():
    artifact()
    assert '4.35.0' in run(['lean','--version'])
    with tempfile.TemporaryDirectory(prefix='check-',dir=WORK) as d:
        temp = Path(d); oleans = temp/'olean'; (oleans/'Proofs').mkdir(parents=True)
        env = dict(os.environ,LEAN_PATH=str(oleans))
        def compile_module(mod):
            source = Path(mod.replace('.','/')+'.lean')
            output = oleans/(mod.replace('.','/')+'.olean')
            output.parent.mkdir(parents=True,exist_ok=True)
            print('Fresh Lean compilation: '+str(source),flush=True)
            run(['lean','-j2','-o',output,source],env=env)
        for mod in ['Proofs.Wasm','Proofs.Artifact','Proofs.Spec','Proofs.Cases','Proofs.Composition']:
            compile_module(mod)
        with ThreadPoolExecutor(max_workers=4) as pool:
            list(pool.map(compile_module,['Proofs.Certificates.C'+str(i) for i in range(16)]))
        for mod in ['Proofs.Certificates','Proofs','Proofs.Probe']:
            compile_module(mod)
        audit = run(['lean','verification/axioms.lean'],env=env)
        (WORK/'axioms.txt').write_text(audit)
        assert 'sorryAx' not in audit and 'Lean.trustCompiler' not in audit
        print(audit.strip(),flush=True)
        stream = WORK/'proofs.ndjson'
        with stream.open('w') as out:
            run([tool('leanexport'),'Proofs','--',*ROOTS],env=env,stdout=out)
        audit_export(stream)
        negative_controls(env,temp)
        kernels(stream,temp)
        cases = WORK/'cases.json'
        cases.write_text(run(['lean','--run','verification/export_cases.lean'],env=env))
        print(run([sys.executable,'verification/runtime.py',cases,WORK/'runtime.wast']).strip(),flush=True)
        wrong = json.loads(cases.read_text())[:1]; wrong[0]['expected'] -= 1
        (temp/'wrong.json').write_text(json.dumps(wrong))
        p = subprocess.run([sys.executable,'verification/runtime.py',temp/'wrong.json',temp/'wrong.wast'],capture_output=True,text=True)
        assert p.returncode != 0 and 'unreachable' in p.stderr, p
        print('PASS: Wasmtime harness rejected a deliberately wrong expected return',flush=True)
    print('PASS: all stated partial results checked; universal R1, R2, R3 remain UNPROVED',flush=True)

if __name__ == '__main__':
    main()
