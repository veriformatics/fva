import fs from 'node:fs';
import assert from 'node:assert/strict';

const cases = JSON.parse(fs.readFileSync('.verification/cases.json', 'utf8'));
const bytes = fs.readFileSync('lz4-block-codec.wasm');
const module = new WebAssembly.Module(bytes);
const fresh = () => new WebAssembly.Instance(module).exports;
const memory = e => new Uint8Array(e.memory.buffer);
const put = (e, at, data) => memory(e).set(data, at);
const checkBytes = (e, at, data) =>
  assert.deepEqual([...memory(e).slice(at, at + data.length)], data);

let e = fresh();
assert.equal(e.getLinearMemoryOffset(), 0);
assert.equal(e.memory.grow(5), 1);
new Int32Array(e.memory.buffer, 0, 65536).fill(-65536);
put(e, 262144, cases.encoderInput);
assert.equal(e.lz4BlockEncode(262144, cases.encoderInput.length, 327680),
  cases.encoderBlock.length);
checkBytes(e, 327680, cases.encoderBlock);
checkBytes(e, 262144, cases.encoderInput);
console.log('V8 R1: encode(abcdabcdEFGHI) = 40616263640400504546474849');

e = fresh();
put(e, 4096, cases.validBlock);
assert.equal(e.lz4BlockDecode(4096, cases.validBlock.length, 0), 1);
checkBytes(e, 0, [97, ...Array(12).fill(0)]);
console.log('V8 R2: valid block decodes to length 1, expected 13');

// Positive control: this same block succeeds with output above input.
e = fresh();
put(e, 4096, cases.validBlock);
assert.equal(e.lz4BlockDecode(4096, cases.validBlock.length, 8192), 13);
checkBytes(e, 8192, cases.validContent);

// The only supplied byte is valid token 00. The next byte is inaccessible.
e = fresh();
put(e, 65535, cases.emptyBlock);
assert.throws(() => e.lz4BlockDecode(65535, 1, 0),
  err => err instanceof WebAssembly.RuntimeError && /out of bounds/.test(err.message));
console.log('V8 R2/R3: valid empty block at 65535 traps out of bounds');

// A completed outside read is observable even without a memory boundary.
for (const [outside, result] of [[0, 0], [1, 4]]) {
  e = fresh();
  put(e, 4096, cases.emptyBlock);
  put(e, 4097, [outside, 0]);
  assert.equal(e.lz4BlockDecode(4096, 1, 8192), result);
}
console.log('V8 R3: changing byte 4097 outside [4096,4097) changes return 0 -> 4');

// Independent engine: embed the UNCHANGED binary, importing only its exports
// into small setup/readback helpers. No codec instruction is translated.
const binary = [...bytes].map(b => '\\' + b.toString(16).padStart(2, '0')).join('');
const suite = [];
function instance(name, grow, data, table = false) {
  suite.push(`(module $${name} binary "${binary}")`, `(register "${name}" $${name})`);
  const stores = data.flatMap(([at, values]) => values.map((v, i) =>
    `(i32.store8 (i32.const ${at + i}) (i32.const ${v}))`)).join('\n');
  const init = table ? `(local.set $p (i32.const 0))
    (loop $fill (i32.store (local.get $p) (i32.const -65536))
      (local.set $p (i32.add (local.get $p) (i32.const 4)))
      (br_if $fill (i32.lt_u (local.get $p) (i32.const 262144))))` : '';
  suite.push(`(module $${name}h (import "${name}" "memory" (memory 1))
    (func (export "setup") (local $p i32)
      (drop (memory.grow (i32.const ${grow}))) ${init} ${stores})
    (func (export "byte") (param i32) (result i32) (i32.load8_u (local.get 0))))`,
    `(invoke $${name}h "setup")`);
}
function returns(name, fn, args, expected) {
  suite.push(`(assert_return (invoke $${name} "${fn}" ${args.map(n =>
    `(i32.const ${n})`).join(' ')}) (i32.const ${expected}))`);
}
function readback(name, at, values) {
  values.forEach((v, i) => returns(name + 'h', 'byte', [at + i], v));
}
instance('r1', 5, [[262144, cases.encoderInput]], true);
returns('r1', 'getLinearMemoryOffset', [], 0);
returns('r1', 'lz4BlockEncode', [262144, cases.encoderInput.length, 327680],
  cases.encoderBlock.length);
readback('r1', 327680, cases.encoderBlock);
readback('r1', 262144, cases.encoderInput);
instance('r2', 0, [[4096, cases.validBlock]]);
returns('r2', 'lz4BlockDecode', [4096, cases.validBlock.length, 0], 1);
readback('r2', 0, [97, ...Array(12).fill(0)]);
instance('positive', 0, [[4096, cases.validBlock]]);
returns('positive', 'lz4BlockDecode', [4096, cases.validBlock.length, 8192], 13);
readback('positive', 8192, cases.validContent);
instance('empty', 0, [[65535, cases.emptyBlock]]);
suite.push('(assert_trap (invoke $empty "lz4BlockDecode" (i32.const 65535) (i32.const 1) (i32.const 0)) "out of bounds memory access")');
for (const [outside, result] of [[0, 0], [1, 4]]) {
  const name = 'outside' + outside;
  instance(name, 0, [[4096, cases.emptyBlock], [4097, [outside, 0]]]);
  returns(name, 'lz4BlockDecode', [4096, 1, 8192], result);
}
fs.writeFileSync('.verification/runtime.wast', suite.join('\n') + '\n');
// Deliberately false assertion, checked by the same Wasmtime runner.
fs.writeFileSync('.verification/false-runtime.wast', suite.join('\n') +
  '\n(assert_return (invoke $r2 "getLinearMemoryOffset") (i32.const 1))\n');
console.log('V8 PASS; exact-binary Wasmtime suite generated');
