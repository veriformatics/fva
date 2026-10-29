import fs from 'node:fs';
import assert from 'node:assert/strict';
import crypto from 'node:crypto';
const wasm=fs.readFileSync('lz4-flex.wasm');
assert.equal(crypto.createHash('sha256').update(wasm).digest('hex'),'1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775');
const {instance}=await WebAssembly.instantiate(wasm);
const mem=new Uint8Array(instance.exports.memory.buffer);
let seed=0x12345678, count=0, accepted=0;
function rnd(n){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%n;}
// Independent sequence parser. End-of-block restrictions deliberately omitted (R3).
function decode(b){let i=0,o=[];if(!b.length)return null;
 const extra=()=>{let x,n=0;do{if(i===b.length)throw 0;x=b[i++];n+=x;}while(x===255);return n;};
 try{while(i<b.length){let t=b[i++],l=t>>>4;if(l===15)l+=extra();
 if(i+l>b.length)throw 0;for(let k=0;k<l;k++)o.push(b[i++]);
 if(i===b.length)return o;if(i+2>b.length)throw 0;
 let off=b[i++]|b[i++]<<8;if(off===0||off>o.length)throw 0;
 let m=(t&15)+4;if(m===19)m+=extra();if(o.length+m>2097152)throw 0;
 for(let k=0;k<m;k++)o.push(o[o.length-off]);}return o;}catch{return null;}}
function test(b,cap,expected=null,edge=false){
 const src=edge?2097152-b.length:131072,dst=edge?131072:1048576;
 assert(src+b.length<=dst||dst+cap<=src);
 mem.fill(0xa5,dst-32,dst+cap+32);mem.set(b,src);
 const before=mem.slice(dst-32,dst+cap+32);
 let r;try{r=instance.exports.lz4_decompress(src,dst,b.length,cap);}catch(e){throw new Error(`trap: ${JSON.stringify({b,cap,edge})}: ${e}`);}
 count++;let ref=decode(b);
 if(r>=0){accepted++;assert(ref!==null,`R3 accepted invalid ${JSON.stringify({b,cap,r})}`);assert.equal(r,ref.length);assert(r<=cap);assert.deepEqual([...mem.slice(dst,dst+r)],ref);}
 if(expected&&expected.length<=cap){assert.equal(r,expected.length);assert.deepEqual([...mem.slice(dst,dst+r)],expected);}
 assert.deepEqual(mem.slice(dst-32,dst),before.slice(0,32));
 assert.deepEqual(mem.slice(dst+cap,dst+cap+32),before.slice(cap+32));
 assert.deepEqual([...mem.slice(src,src+b.length)],b);
}
function ext(n){let r=[];while(n>=255){r.push(255);n-=255;}r.push(n);return r;}
function seq(lit,off=0,m=0){let b=[Math.min(lit.length,15)*16+(off?Math.min(m-4,15):0)];if(lit.length>=15)b.push(...ext(lit.length-15));b.push(...lit);if(off){b.push(off&255,off>>>8);if(m>=19)b.push(...ext(m-19));}return b;}
for(let n=0;n<=2;n++){let k=256**n;for(let v=0;v<k;v++){let b=Array.from({length:n},(_,i)=>(v>>8*i)&255);for(let cap of [0,4,34,80])test(b,cap);}}
for(let it=0;it<20000;it++){
 let b=[],out=[];const n=rnd(5);
 for(let j=0;j<n;j++){let lit=Array.from({length:1+rnd(40)},()=>rnd(256));out.push(...lit);let off=1+rnd(out.length),m=4+rnd(350);b.push(...seq(lit,off,m));for(let k=0;k<m;k++)out.push(out[out.length-off]);}
 let tail=Array.from({length:n?12+rnd(300):rnd(600)},()=>rnd(256));b.push(...seq(tail));out.push(...tail);
 for(let cap of [...new Set([Math.max(0,out.length-1),out.length,out.length+80])])test(b,cap,out,it%2===0);
 if(it<10000){let x=b.slice();x[rnd(x.length)]=rnd(256);test(x,out.length+100);test(b.slice(0,rnd(b.length)),out.length+100);}
}
console.log(`PASS ${count} original-artifact calls; ${accepted} nonnegative returns agree with independent parser. This is testing, not universal verification; canaries detect tested writes, not reads.`);
