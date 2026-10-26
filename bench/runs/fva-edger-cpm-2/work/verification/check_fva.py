#!/usr/bin/env python3
"""Link the supplied, prebuilt FVA objects into a checker outside this project.

Use the supplied link response file, relocating only FVA object paths. Mathlib
objects and Lean system libraries remain those of the installed toolchain.
FVA sources, manifests, and pinned canaries are copied unchanged. No network.
"""
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FVA = ROOT / 'fva'

with tempfile.TemporaryDirectory(prefix='edger-fva-checker-', dir='/tmp') as temp:
    checker = Path(temp) / 'fva'
    binary = checker / '.lake/build/bin/fva'
    binary.parent.mkdir(parents=True)
    for name in ['FVA', 'trust', '.cache']:
        shutil.copytree(FVA / name, checker / name)
    shutil.copy2(FVA / 'lake-manifest.json', checker / 'lake-manifest.json')
    arguments = shlex.split((FVA / '.lake/build/bin/fva.rsp').read_text())
    relocated = []
    for argument in arguments:
        marker = '/fva/.lake/build/ir/'
        if marker in argument:
            relative = Path('.lake/build/ir') / argument.split(marker, 1)[1]
            target = checker / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(FVA / relative, target)
            argument = str(target)
        relocated.append(argument)
    sysroot = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
    subprocess.run([str(sysroot / 'bin/clang'), '-o', str(binary), *relocated], check=True)
    result = subprocess.run([str(binary), 'trust', '.', '--spec-module', 'Proofs.Spec',
                             '--root-module', 'Proofs'], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (ROOT / 'verification/fva-trust.txt').write_text(result.stdout)
    print(result.stdout, end='')
    raise SystemExit(result.returncode)
