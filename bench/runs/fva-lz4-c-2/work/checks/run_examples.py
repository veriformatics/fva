from pathlib import Path
import hashlib
import subprocess
import tempfile

artifact = Path("lz4-c.wasm").read_bytes()
assert len(artifact) == 8469
assert hashlib.sha256(artifact).hexdigest() == "8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6"
cases=[
([0],[],0),([0],[],1),
([80,65,66,67,68,69],[65,66,67,68,69],5),
([19,65,1,0,80,66,67,68,69,70],[65]*8+[66,67,68,69,70],13),
([240,0]+list(range(65,80)),list(range(65,80)),15),
([31,65,1,0,0,80,66,67,68,69,70],[65]*20+[66,67,68,69,70],25),
([3,0,0,80,65,66,67,68,69],[0]*7+[65,66,67,68,69],12)]
esc=lambda bs: ''.join(f'\\{b:02x}' for b in bs)
w=[f'(module $subject binary "{esc(Path("lz4-c.wasm").read_bytes())}")', '(register "subject" $subject)', '''(module $probe
(import "subject" "memory" (memory 32 32))
(func (export "store") (param i32 i32) local.get 0 local.get 1 i32.store8)
(func (export "fill") (param i32 i32 i32) local.get 0 local.get 1 local.get 2 memory.fill)
(func (export "byte") (param i32) (result i32) local.get 0 i32.load8_u))''']
for bs,out,cap in cases:
 w.append(f'(invoke $probe "fill" (i32.const 196607) (i32.const 165) (i32.const {cap+2}))')
 for k,b in enumerate(bs): w.append(f'(invoke $probe "store" (i32.const {131072+k}) (i32.const {b}))')
 w.append(f'(assert_return (invoke $subject "LZ4_decompress_safe" (i32.const 131072) (i32.const 196608) (i32.const {len(bs)}) (i32.const {cap})) (i32.const {len(out)}))')
 for k,b in enumerate(out): w.append(f'(assert_return (invoke $probe "byte" (i32.const {196608+k})) (i32.const {b}))')
 for k in [196607,196608+cap]: w.append(f'(assert_return (invoke $probe "byte" (i32.const {k})) (i32.const 165))')
for b in range(256):
 w.append(f'(invoke $probe "store" (i32.const 131072) (i32.const {b}))')
 w.append(f'(assert_return (invoke $subject "LZ4_decompress_safe" (i32.const 131072) (i32.const 196608) (i32.const 1) (i32.const 0)) (i32.const {0 if b==0 else -1}))')
w.append('(assert_return (invoke $subject "LZ4_decompress_safe" (i32.const 131072) (i32.const 196608) (i32.const 0) (i32.const 1)) (i32.const -1))')
with tempfile.TemporaryDirectory(prefix="lz4-examples-") as d:
 p=Path(d)/"examples.wast"
 p.write_text('\n'.join(w)+'\n')
 subprocess.run(["wasmtime", "wast", "-C", "cache=n", str(p)],check=True)
print("Wasmtime: 7 decode cases, 256 one-byte zero-capacity cases, and empty-source rejection passed.")
