// Deterministic finite checks against the shipped bytes, guarded bytes, and lift.
import fs from 'node:fs';
import assert from 'node:assert/strict';
import crypto from 'node:crypto';
const dir = new URL('./', import.meta.url);
const bytes = fs.readFileSync(new URL('../lz4-c.wasm', dir));
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'), '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6');
const instantiate = async b => (await WebAssembly.instantiate(b)).instance.exports;
const original = await instantiate(bytes);
const guarded = await instantiate(fs.readFileSync(new URL('guarded.wasm', dir)));
const lifted = await instantiate(fs.readFileSync(new URL('lifted.wasm', dir)));
const instances = [original, guarded, lifted];
const memories = instances.map((x, i) => new Uint8Array(x.memory.buffer, i === 2 ? x.getmem() : 0, 2097152));
for (const m of memories) m.fill(0xa5, 131072);
let total = 0, valid = 0, accepted = 0, seed = 0x9e3779b9;
const rand = () => { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return seed >>> 0; };

function decode(src, cap) {
  let p = 0; const out = [];
  const byte = () => { if (p >= src.length) throw Error('truncated'); return src[p++]; };
  const length = n => { if (n === 15) { let b; do { b = byte(); n += b; } while (b === 255); } return n; };
  if (!src.length) throw Error('empty encoded input');
  while (p < src.length) {
    const token = byte(), n = length(token >>> 4);
    for (let j = 0; j < n; j++) out.push(byte());
    if (out.length > cap) throw Error('capacity');
    if (p === src.length) return out;
    const offset = byte() + 256 * byte(), match = length(token & 15) + 4;
    if (offset > out.length || out.length + match > cap) throw Error('invalid match');
    for (let j = 0; j < match; j++) out.push(offset ? out[out.length-offset] : 0);
  }
  return out; // R3 permits departures from end-of-block conditions.
}
function run(src, cap, expected, placement) {
  const k = total++ % 4;
  const dst = placement?.dst ?? (k === 0 ? 2097152-cap : k === 1 ? 131072 : 262144);
  const source = placement?.source ?? (k === 1 ? 2097152-src.length : 131072 + (k === 3 ? 3 : 0));
  assert(!src.length || !cap || source + src.length <= dst || dst + cap <= source);
  guarded.verify_config(source, source+src.length, dst, dst+cap);
  const results = [];
  for (let i = 0; i < 3; i++) {
    const m = memories[i];
    m.fill(0xa5, dst, Math.min(dst+cap+32,2097152));
    m.set(src, source);
    const r = i === 2 ? lifted.f2(source,dst,src.length,cap) | 0 : instances[i].LZ4_decompress_safe(source,dst,src.length,cap);
    results.push(r);
    assert.deepEqual(Array.from(m.slice(source,source+src.length)), src, `source modified, case ${total}`);
  }
  assert.equal(results[0], results[1]); assert.equal(results[0], results[2]);
  assert.deepEqual(memories[0].slice(dst,dst+cap), memories[1].slice(dst,dst+cap));
  assert.deepEqual(memories[0].slice(dst,dst+cap), memories[2].slice(dst,dst+cap));
  const r = results[0];
  if (expected !== undefined) {
    valid++;
    assert.equal(r, expected.length, `R2 case ${total}: ${src.slice(0,50)}`);
    assert.deepEqual(Array.from(memories[0].slice(dst,dst+r)), expected);
  }
  if (r >= 0) {
    accepted++; assert(r <= cap);
    assert.deepEqual(Array.from(memories[0].slice(dst,dst+r)), decode(src,cap), `R3 case ${total}`);
  }
}
const extensions = n => { const b=[]; while(n >= 255) { b.push(255); n-=255; } b.push(n); return b; };
function literals(n) {
  const content = Array.from({length:n}, (_,i) => (i*37+11)&255);
  return [[Math.min(n,15)<<4, ...(n>=15 ? extensions(n-15) : []), ...content],content];
}
for (let b=0; b<256; b++) for (const cap of [0,1,4,32,64]) run([b],cap,b===0 ? [] : undefined);
run([],0); run([],100);
for(const n of [0,1,4,5,14,15,16,254,255,269,270,271,1024,65535,100000]) {
  const [src,content]=literals(n);
  for(const extra of [0,1,32,100]) run(src,n+extra,content);
  if(n>0) run(src,n-1);
}
for(const offset of [1,2,3,4,5,6,7,8,9,15,16,17,31,255,256,65535]) {
  for(const match of [4,7,8,9,12,15,16,17,18,19,20,254,255,274,1000]) {
    const n=offset, ml=match-4, [lit,content]=literals(n);
    lit[0] |= Math.min(ml,15);
    const suffix=[91,92,93,94,95,96,97,98];
    const src=[...lit,offset&255,offset>>>8,...(ml>=15?extensions(ml-15):[]),0x80,...suffix];
    for(let j=0;j<match;j++) content.push(content[content.length-offset]);
    content.push(...suffix);
    for(const extra of [0,32]) run(src,content.length+extra,content);
    run(src,content.length-1);
  }
}
for (const match of [4,8,18,19,20,40,274,1000]) {
  const ml=match-4;
  run([Math.min(ml,15),0,0,...(ml>=15?extensions(ml-15):[]),0x80,1,2,3,4,5,6,7,8],match+40);
}
for(let i=0;i<10000;i++) {
  const n=rand()%100, src=Array.from({length:n},()=>rand()&255);
  run(src,rand()%300);
}
run([],64,undefined,{source:262176,dst:262144});
run([0],0,[],{source:262144,dst:262144});
run([1],0,undefined,{source:262144,dst:262144});
run([],0,undefined,{source:262144,dst:262144});
console.log(`PASS: ${total} cases; ${valid} R2 checks; ${accepted} successful returns checked for R3; guarded accesses and lifted execution agree.`);
