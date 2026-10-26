import { readFileSync, writeFileSync } from 'node:fs';
const dir = process.argv[2];
const env = (await WebAssembly.instantiate(readFileSync(`${dir}/env.wasm`))).instance.exports;
const edge = (await WebAssembly.instantiate(readFileSync('edgeR.so'),
  { env, 'GOT.mem': env, 'GOT.func': env })).instance.exports;
const caller = (await WebAssembly.instantiate(readFileSync(`${dir}/caller.wasm`),
  { env, edge })).instance.exports;
for (const [k, length] of [1, 1, 4, 4, 1].entries()) {
  const data = Buffer.alloc(8 * length);
  for (let i = 0; i < length; i++) data.writeBigInt64LE(caller[`case${k}`](i), 8*i);
  writeFileSync(`${dir}/case${k}.bin`, data);
  console.log(`V8 case${k}: ${data.toString('hex')}`);
}
