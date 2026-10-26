#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
sha256sum -c verification/inputs.sha256
lake build
python3 verification/make-wast.py
wasmtime wast -C cache=n verification/full-artifact.wast
echo 'WASMTIME COUNTEREXAMPLES PASS'
node verification/run-wasm.js
Rscript verification/filter.R

# Freeze the provided FVA package outside the audited project, and link its
# prebuilt object files there. Its embedded base manifest remains unchanged.
verifier_dir=$(mktemp -d /tmp/edger-fva-check.XXXXXXXX)
trap 'rm -rf "$verifier_dir"' EXIT
cp -a --reflink=auto fva/. "$verifier_dir/"
python3 - "$verifier_dir" <<'PY'
import pathlib
import shlex
import subprocess
import sys
root = pathlib.Path(sys.argv[1])
rsp = root / '.lake/build/bin/fva.rsp'
args = shlex.split(rsp.read_text())
main = next(a for a in args if a.endswith('/.lake/build/ir/Main.c.o.export'))
old = main.removesuffix('/.lake/build/ir/Main.c.o.export')
args = [a.replace(old + '/', str(root) + '/') for a in args]
subprocess.run(['leanc', '-o', str(root / '.lake/build/bin/fva'), *args], check=True)
PY
"$verifier_dir/.lake/build/bin/fva" trust . --spec-module Proofs.Spec --root-module Proofs --surface-budget 120 | tee verification/trust.txt
