import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const [out] = process.argv.slice(2);
const load = p => new WebAssembly.Module(readFileSync(p));
const imports = {};
for (const name of ['env', 'GOT.mem', 'GOT.func']) {
  imports[name] = new WebAssembly.Instance(load(resolve(out, `${name}.wasm`))).exports;
}
// Load the original bytes, without recompilation, rewriting, or slicing.
imports.edgeR = new WebAssembly.Instance(load('edgeR.so'), imports).exports;
const probe = new WebAssembly.Instance(load(resolve(out, 'probe.wasm')), imports).exports;
const cases = JSON.parse(readFileSync(resolve(out, 'cases.json'), 'utf8'));
console.log(JSON.stringify(cases.map(c => ({
  ...c, output: probe.cpm_bits(BigInt(c.count), BigInt(c.library)).toString()
}))));
