// Runtime checks of the exact artifact and an instrumented copy. These are tests,
// not universal proofs. No npm dependencies; deterministic cases and RNG.
import fs from 'node:fs';
import assert from 'node:assert/strict';
import crypto from 'node:crypto';

const bytes = fs.readFileSync('lz4-c.wasm');
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6');
const original = (await WebAssembly.instantiate(bytes)).instance.exports;
let config;
let accesses = 0;
function guard(a, width, write) {
  a >>>= 0;
  for (let i = 0; i < width; ++i) {
    const p = a + i;
    if (p < 131072) continue;
    const {src, dst, size, cap} = config;
    if (!((!write && p >= src && p < src + size) ||
      (p >= dst && p < dst + cap)))
      assert.fail(`R1 access: ${JSON.stringify({...config, address:p, write})}`);
  }
  ++accesses;
}
const traced = (await WebAssembly.instantiate(fs.readFileSync(process.argv[2]), {
  checks: {read: (a,w) => guard(a,w,false), write: (a,w) => guard(a,w,true)}
})).instance.exports;
const memories = [original, traced].map(e => new Uint8Array(e.memory.buffer));
assert.equal(memories[0].length, 2097152);
let cases = 0, accepted = 0, valid = 0;

// Grammar and forward byte-at-a-time match semantics, independent of C fast paths.
// End-of-block restrictions are deliberately absent: R3 permits their violation.
function decode(input) {
  let p = 0;
  const out = [];
  const length = base => {
    let n = base;
    if (base === 15) {
      let b;
      do {
        if (p === input.length) throw Error('truncated length');
        b = input[p++]; n += b;
      } while (b === 255);
    }
    return n;
  };
  while (p < input.length) {
    const token = input[p++];
    const literals = length(token >> 4);
    if (p + literals > input.length) throw Error('truncated literals');
    for (let i = 0; i < literals; ++i) out.push(input[p++]);
    if (p === input.length) return out;
    if (p + 2 > input.length) throw Error('truncated offset');
    const offset = input[p++] + 256 * input[p++];
    const match = length(token & 15) + 4;
    if (offset > out.length) throw Error('offset precedes output');
    if (out.length + match > config.cap) throw Error('output exceeds capacity');
    for (let i = 0; i < match; ++i)
      out.push(offset === 0 ? 0 : out[out.length - offset]);
  }
  throw Error('missing final literal sequence');
}

function check(input, cap, expected = null, layout = 0) {
  const size = input.length;
  let src, dst;
  switch (layout % 6) {
    case 0: src = 131072; dst = src + size; break;
    case 1: dst = 131072; src = dst + cap; break;
    case 2: src = 2097152 - size; dst = src - cap; break;
    case 3: dst = 2097152 - cap; src = dst - size; break;
    case 4: src = 131073; dst = 1048577; break;
    default: dst = 131075; src = 1048579;
  }
  assert.ok(src >= 131072 && dst >= 131072 &&
    src + size <= 2097152 && dst + cap <= 2097152 &&
    (src + size <= dst || dst + cap <= src));
  config = {src, dst, size, cap};
  for (const m of memories) {
    // Reset the caller region too, so prior tests cannot supply hidden dictionary bytes.
    m.fill(0xa5, Math.min(src,dst), Math.max(src+size,dst+cap));
    m.set(input, src);
  }
  const r = original.LZ4_decompress_safe(src, dst, size, cap);
  const t = traced.LZ4_decompress_safe(src, dst, size, cap);
  assert.equal(r, t, 'instrumentation return mismatch');
  assert.deepEqual(memories[0].subarray(dst, dst+cap),
    memories[1].subarray(dst, dst+cap), 'instrumentation output mismatch');
  if (r >= 0) {
    ++accepted;
    assert.ok(r <= cap, 'R3 length');
    let decoded;
    try { decoded = decode(input); }
    catch (e) { throw Error(`R3 parse: ${e.message}; ${JSON.stringify({...config,input:[...input],r})}`); }
    assert.equal(r, decoded.length, 'R3 decoded length');
    assert.deepEqual([...memories[0].subarray(dst, dst+r)], decoded, 'R3 content');
  }
  if (expected !== null) {
    ++valid;
    assert.equal(r, expected.length, 'R2 decoded length');
    assert.deepEqual([...memories[0].subarray(dst, dst+r)], expected, 'R2 content');
  }
  ++cases;
}

let seed = 0x7834ab21;
function random(n) { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return (seed >>> 0) % n; }
function extension(n) {
  const a = [];
  while (n >= 255) { a.push(255); n -= 255; }
  a.push(n); return a;
}
function final(literals, low = 0) {
  return [(Math.min(literals.length,15) << 4) | low,
    ...(literals.length >= 15 ? extension(literals.length-15) : []), ...literals];
}
function sequence(literals, offset, match) {
  return [(Math.min(literals.length,15) << 4) | Math.min(match-4,15),
    ...(literals.length >= 15 ? extension(literals.length-15) : []), ...literals,
    offset & 255, offset >> 8, ...(match >= 19 ? extension(match-19) : [])];
}

// All zero/one/two-byte source strings, representative capacity thresholds.
for (const cap of [0,1,4,8,12,31,32,33,64]) check([],cap);
for (let a = 0; a < 256; ++a) {
  for (const cap of [0,1,4,8,12,31,32,33,64]) check([a], cap, a < 16 && cap > 0 || a === 0 ? [] : null, a);
  for (let b = 0; b < 256; ++b)
    check([a,b], [0,1,8,12,32,64][(a+b)%6], null, a+b);
}
// Literal extension thresholds, unused final low nibble, and exact/extra capacity.
for (const n of [0,1,4,5,12,14,15,16,269,270,271,524,525,4096]) {
  const data = Array.from({length:n}, (_,i) => (i*73+11)&255);
  for (let low = 0; low < 16; ++low)
    for (const slack of [0,1,32])
      check(final(data, low), n+slack, n+slack > 0 || low === 0 ? data : null, low+slack);
}
// Offset and length boundaries, overlapping matches, zero-offset extension.
for (const offset of [0,1,2,3,4,5,6,7,8,9,15,16,31,255,256,65535]) {
  for (const ml of [4,7,8,11,12,15,16,18,19,20,273,274,275,530]) {
    const literals = Array.from({length:Math.max(offset,1)}, (_,i) => (i*17+3)&255);
    const tail = Array.from({length:Math.max(5,12-ml)}, (_,i) => 240+i);
    const input = [...sequence(literals,offset,ml), ...final(tail)];
    const content = [...literals];
    for (let i=0;i<ml;++i) content.push(offset === 0 ? 0 : content[content.length-offset]);
    content.push(...tail);
    for (const slack of [0,1,32])
      check(input, content.length+slack, offset ? content : null, offset+ml+slack);
    check(input, content.length-1, null, offset+ml);
  }
}
// Independently generated valid blocks with several sequences.
for (let k=0;k<1000;++k) {
  const input = [], content = [];
  for (let j=0;j<1+random(6);++j) {
    const n = j === 0 ? 1+random(300) : random(300);
    const literals = Array.from({length:n}, () => random(256));
    content.push(...literals);
    const offset = 1+random(Math.min(65535,content.length));
    const match = 4+random(600);
    input.push(...sequence(literals,offset,match));
    for (let i=0;i<match;++i) content.push(content[content.length-offset]);
  }
  const tail = Array.from({length:12+random(40)}, () => random(256));
  input.push(...final(tail)); content.push(...tail);
  check(input,content.length+random(64),content,k);
  // Mutations: check safety and the R3 implication regardless of validity.
  for (let j=0;j<3;++j) {
    const corrupt = [...input]; corrupt[random(corrupt.length)] = random(256);
    check(corrupt,content.length+random(64),null,k+j);
  }
}
for (let k=0;k<10000;++k) {
  const input = Array.from({length:random(150)}, () => random(256));
  check(input,random(600),null,k);
}
console.log(`PASS: ${cases} cases; ${accepted} nonnegative returns checked against grammar; ${valid} valid-input expectations; ${accesses} instrumented accesses`);
