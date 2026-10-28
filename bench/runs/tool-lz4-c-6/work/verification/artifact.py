"""Rebuild without replacing the artifact, then compare every byte."""
from pathlib import Path
import hashlib
import shlex
import subprocess

root = Path(__file__).resolve().parent.parent
artifact = root / 'lz4-c.wasm'
expected = '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6'
assert hashlib.sha256(artifact.read_bytes()).hexdigest() == expected
build = (root / 'build.sh').read_text().replace('\\\n', ' ')
commands = [line for line in build.splitlines() if line.startswith('clang ')]
assert len(commands) == 1
command = shlex.split(commands[0])
assert command[-2:] == ['-o', 'lz4-c.wasm']
command[-1] = 'verification/rebuilt.wasm'
subprocess.run(command, cwd=root, check=True)
assert artifact.read_bytes() == (root / command[-1]).read_bytes(), 'build differs'
subprocess.run(['wasm-tools', 'validate', str(artifact)], check=True)
print('Artifact: 8469 bytes, SHA-256 ' + expected)
print('Rebuild: byte-identical; Wasm validation: passed')
