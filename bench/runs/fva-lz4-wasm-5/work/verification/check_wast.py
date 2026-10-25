"""Check that the WAST embeds the shipped bytes, then run its assertions."""
from pathlib import Path
import hashlib
import re
import subprocess

root = Path(__file__).resolve().parent.parent
artifact = (root / "lz4-block-codec.wasm").read_bytes()
assert hashlib.sha256(artifact).hexdigest() == (
    "4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf"
)
wast = root / "verification/reproduce.wast"
first = wast.read_text().splitlines()[0]
match = re.fullmatch(r'\(module binary "((?:\\[0-9a-f]{2})+)"\)', first)
assert match and bytes.fromhex(match[1].replace("\\", "")) == artifact
subprocess.run(["wasmtime", "wast", "-C", "cache=n", str(wast)], check=True)
print("PASS: shipped bytes match; all Wasmtime counterexample assertions passed")
