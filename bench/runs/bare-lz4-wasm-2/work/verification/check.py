#!/usr/bin/env python3
"""Run counterexamples on hash-pinned, unmodified shipped Wasm bytes."""
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
artifact = (ROOT / "lz4-block-codec.wasm").read_bytes()
expected = "4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf"
if len(artifact) != 1226 or hashlib.sha256(artifact).hexdigest() != expected:
    raise SystemExit("FAIL: shipped artifact size/hash differs from README")
subprocess.run(["wasm-tools", "validate", str(ROOT / "lz4-block-codec.wasm")], check=True)
# The WAST binary directive embeds these exact bytes; no recompilation of WAT.
quoted = "".join(f"\\{b:02x}" for b in artifact)
prefix = f'(module $codec binary "{quoted}")\n(register "codec" $codec)\n'
with tempfile.TemporaryDirectory(prefix="lz4-verification-") as tmp:
    env = dict(os.environ, XDG_CACHE_HOME=tmp)
    for name in ("r1", "r2", "r3"):
        script = Path(tmp) / f"{name}.wast"
        script.write_text(prefix + (ROOT / "verification" / f"{name}.wast").read_text())
        subprocess.run(["wasmtime", "wast", str(script)], check=True, env=env)
        print(f"PASS {name.upper()}: all counterexample assertions checked", flush=True)
print(f"PASS artifact: {len(artifact)} bytes, sha256 {expected}")
