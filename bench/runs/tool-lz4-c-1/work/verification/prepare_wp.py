"""Generate ACSL-annotated helpers and an early-exit source slice.
Run from the project root. The slice is not a proof of the general decoder.
"""
from pathlib import Path
import hashlib
import re

expected = {
    'src/lz4.c': '9396f7de527bc8435de9c7569fb7998e56545a84b4f3c2d808c0235c01774539',
    'src/lz4.h': '26b82efc53d1570f3b54eef02e9c4764c1ad374ff03cac04e2ced5ea4d4c552f',
    'src/c-memory.c': '70ea0160f9bf1ac2ba178cac8b3be49c706e7742c6c7b947167e7b5d5f207343',
    'src/c-memory.h': '64e153ac5ce4bd8e6b4940ff1c8eb286df86a0946e58069c278b187113962a62',
}
for name, digest in expected.items():
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, name
s = Path('src/lz4.c').read_text()
contract = r'''/*@
  requires src != \null;
  requires 0 <= srcSize <= 1966080;
  requires 0 <= outputSize <= 1966080;
  requires outputSize == 0 || srcSize == 0;
  requires srcSize > 0 ==> \valid_read(src + (0 .. srcSize-1));
  requires partialDecoding == decode_full_block;
  requires dict == noDict && dictSize == 0 && dictStart == \null;
  requires lowPrefix == (const BYTE*)dst;
  terminates \true;
  assigns \nothing;
  ensures outputSize == 0 && srcSize == 1 && src[0] == 0 ==> \result == 0;
  ensures !(outputSize == 0 && srcSize == 1 && src[0] == 0) ==> \result == -1;
*/
'''
anchor = 'LZ4_FORCE_INLINE int\nLZ4_decompress_generic('
assert s.count(anchor) == 1
s = s.replace(anchor, contract + anchor)
# Keep the exact source prefix through the two early exits. The residual is
# unreachable under the contract; WP must establish the false assertion.
start = s.index('LZ4_decompress_generic(')
cut_text = '        if (unlikely(srcSize==0)) { return -1; }'
cut = s.index(cut_text, start) + len(cut_text)
end = s.index('/*===== Instantiate the API decoding functions. =====*/', cut)
s = s[:cut] + '\n        /*@ assert \\false; */\n        return -1;\n    }\n}\n\n' + s[end:]
wrapper_contract = contract.replace('srcSize', 'compressedSize').replace('outputSize', 'maxDecompressedSize').replace('src[0]', 'source[0]').replace('src !=', 'source !=').replace('src +', 'source +')
wrapper_contract = '\n'.join(line for line in wrapper_contract.split('\n') if not any(t in line for t in ['partialDecoding', 'dict ==', 'lowPrefix']))
anchor = 'LZ4_FORCE_O2\nint LZ4_decompress_safe('
assert s.count(anchor) == 1
s = s.replace(anchor, wrapper_contract + '\n' + anchor)
Path('verification/lz4-sliced.c').write_text(s)
m = Path('src/c-memory.c').read_text().replace('#include "c-memory.h"', '#include "memory-contracts.h"')
fwd = r'''/*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> d[k] == \at(((const unsigned char*)src)[k],Pre);
      loop assigns i, d[0 .. n-1];
      loop variant n-i;
    */
    '''
m = m.replace('for (size_t i = 0; i < n; ++i) d[i] = s[i];', fwd + 'for (size_t i = 0; i < n; ++i) d[i] = s[i];')
back = r'''/*@
          loop invariant 0 <= n <= \at(n,Pre);
          loop invariant \forall integer k; 0 <= k < \at(n,Pre) ==>
            s[k] == \at(((const unsigned char*)src)[k],Pre);
          loop invariant \forall integer k; n <= k < \at(n,Pre) ==>
            d[k] == \at(((const unsigned char*)src)[k],Pre);
          loop assigns n, d[0 .. \at(n,Pre)-1];
          loop variant n;
        */
        '''
m = m.replace('while (n != 0)', back + 'while (n != 0)')
fill = r'''/*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> d[k] == (unsigned char)byte;
      loop assigns i, d[0 .. n-1];
      loop variant n-i;
    */
    '''
m = m.replace('for (size_t i = 0; i < n; ++i) d[i] = (unsigned char)byte;', fill + 'for (size_t i = 0; i < n; ++i) d[i] = (unsigned char)byte;')
Path('verification/memory-annotated.c').write_text(m)

# Ensure memory-helper executable tokens are unchanged by annotation insertion.
def normalize(text):
    text = re.sub(r'/\*@.*?\*/', '', text, flags=re.S)
    return re.sub(r'\s+', ' ', text).strip()
assert normalize(m.replace('#include "memory-contracts.h"', '#include "c-memory.h"')) == normalize(Path('src/c-memory.c').read_text())
print('PASS: source digests and annotation-only memory-helper transformation')
