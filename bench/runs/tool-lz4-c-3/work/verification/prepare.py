#!/usr/bin/env python3
"""Insert ACSL into an exact copy of the shipped memory-support source."""
from pathlib import Path
import hashlib
import re

ROOT = Path(__file__).resolve().parent.parent
p = ROOT / 'src/c-memory.c'
s = p.read_text()
assert hashlib.sha256(p.read_bytes()).hexdigest() == '70ea0160f9bf1ac2ba178cac8b3be49c706e7742c6c7b947167e7b5d5f207343'
contracts = {
'void *memcpy': r'''/*@ requires n <= 2097152;
    requires \valid((unsigned char*)dst + (0..n-1));
    requires \valid_read((const unsigned char*)src + (0..n-1));
    requires \separated((unsigned char*)dst + (0..n-1),
                         (const unsigned char*)src + (0..n-1));
    terminates \true;
    assigns ((unsigned char*)dst)[0..n-1];
    ensures \result == dst;
    ensures \forall integer k; 0 <= k < \old(n) ==>
        ((unsigned char*)dst)[k] == \old(((const unsigned char*)src)[k]);
    exits \false;
*/
''',
'void *memmove': r'''/*@ requires n <= 2097152;
    requires \valid((unsigned char*)dst + (0..n-1));
    requires \valid_read((const unsigned char*)src + (0..n-1));
    requires \separated((unsigned char*)dst + (0..n-1),
                         (const unsigned char*)src + (0..n-1));
    terminates \true;
    assigns ((unsigned char*)dst)[0..n-1];
    ensures \result == dst;
    ensures \forall integer k; 0 <= k < \old(n) ==>
        ((unsigned char*)dst)[k] == \old(((const unsigned char*)src)[k]);
    exits \false;
*/
''',
'void *memset': r'''/*@ requires n <= 2097152;
    requires \valid((unsigned char*)dst + (0..n-1));
    terminates \true;
    assigns ((unsigned char*)dst)[0..n-1];
    ensures \result == dst;
    ensures \forall integer k; 0 <= k < \old(n) ==>
        ((unsigned char*)dst)[k] == (unsigned char)byte;
    exits \false;
*/
'''
}
for needle, annotation in contracts.items():
    assert s.count(needle) == 1
    s = s.replace(needle, annotation + needle)
forward = r'''/*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < n ==>
            s[k] == \at(((const unsigned char*)src)[k],Pre);
        loop invariant \forall integer k; 0 <= k < i ==> d[k] == \at(((const unsigned char*)src)[k],Pre);
        loop assigns i, d[0..n-1];
        loop variant n-i;
    */
    '''
needle = 'for (size_t i = 0; i < n; ++i) d[i] = s[i];'
assert s.count(needle) == 2
s = s.replace(needle, forward + needle)
s = s.replace('for (size_t i = 0; i < n; ++i) d[i] = s[i];', r'''for (size_t i = 0; i < n; ++i)
        /*@ assert s[i] == \at(((const unsigned char*)src)[\at(i,Here)],Pre); */
        d[i] = s[i];''')
needle = 'while (n != 0) { --n; d[n] = s[n]; }'
assert s.count(needle) == 1
s = s.replace(needle, r'''/*@ loop invariant 0 <= n <= \at(n,Pre);
            loop invariant \forall integer k; 0 <= k < \at(n,Pre) ==>
                s[k] == \at(((const unsigned char*)src)[k],Pre);
            loop invariant \forall integer k; n <= k < \at(n,Pre) ==>
                d[k] == \at(((const unsigned char*)src)[k],Pre);
            loop assigns n, d[0..\at(n,Pre)-1];
            loop variant n;
        */
        ''' + needle)
needle = 'for (size_t i = 0; i < n; ++i) d[i] = (unsigned char)byte;'
assert s.count(needle) == 1
s = s.replace(needle, r'''/*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> d[k] == (unsigned char)byte;
        loop assigns i, d[0..n-1];
        loop variant n-i;
    */
    ''' + needle)
s = '#define memcpy proof_memcpy\n#define memmove proof_memmove\n#define memset proof_memset\n' + s
s = s.replace('#include "c-memory.h"', '#include "../src/c-memory.h"')
s = s.replace('while (n != 0) { --n; d[n] = s[n]; }', r'''while (n != 0) {
            --n;
            /*@ assert n + 1 == \at(n,LoopCurrent); */
            /*@ assert s[n] == \at(((const unsigned char*)src)[\at(n,Here)],Pre); */
            d[n] = s[n];
            /*@ assert d[n] == \at(((const unsigned char*)src)[\at(n,Here)],Pre); */
        }''')
# Removing annotations and macro renaming must recover the original C tokens.
prefix = '#define memcpy proof_memcpy\n#define memmove proof_memmove\n#define memset proof_memset\n'
assert s.startswith(prefix)
recovered = s[len(prefix):].replace('#include "../src/c-memory.h"', '#include "c-memory.h"')
def tokens(code):
    code = re.sub(r'/\*.*?\*/', '', code, flags=re.S)
    return re.findall(r'"[^"\n]*"|[a-zA-Z_][a-zA-Z_0-9]*|[0-9]+|[^\s]', code)
assert tokens(recovered) == tokens(p.read_text())
(ROOT / 'verification/memory.c').write_text(s)
print('Prepared verification/memory.c from hash-checked src/c-memory.c')

h = '#include <stddef.h>\n'
for name, annotation in contracts.items():
    decl = {'void *memcpy': 'void *proof_memcpy(void *dst, const void *src, size_t n);',
            'void *memmove': 'void *proof_memmove(void *dst, const void *src, size_t n);',
            'void *memset': 'void *proof_memset(void *dst, int byte, size_t n);'}[name]
    h += annotation + decl + '\n'
(ROOT / 'verification/memory.h').write_text(h)

# Keep the exact generic-decoder entry prefix. The omitted suffix is reached only
# through a call whose precondition is false; WP must prove it unreachable.
lz4 = (ROOT / 'src/lz4.c').read_text()
assert hashlib.sha256(lz4.encode()).hexdigest() == '9396f7de527bc8435de9c7569fb7998e56545a84b4f3c2d808c0235c01774539'
start = lz4.index('LZ4_FORCE_INLINE int\nLZ4_decompress_generic(')
end = lz4.index('\n    /* LZ4_FAST_DEC_LOOP:', start)
prefix = lz4[start:end]
assert prefix.endswith('if (unlikely(srcSize==0)) { return -1; }\n')
# The only caller-byte read is routed through a proved pure accessor. Its
# precondition is the source-buffer read-footprint obligation.
assert prefix.count('*ip==0') == 1
prefix = prefix.replace('*ip==0', 'entry_read(ip, (const BYTE*)src, srcSize)==0')
shim = '''#include <stddef.h>
#include <stdint.h>
typedef uint8_t BYTE;
#define LZ4_FORCE_INLINE static
#define unlikely(x) ((x) != 0)
#define assert(condition) ((void)0)
#define DEBUGLOG(l, ...) {}
'''
for name in ['dict_directive', 'earlyEnd_directive']:
    pattern = r'typedef enum \{[^}]*\} ' + name + ';'
    matches = re.findall(pattern, lz4)
    assert len(matches) == 1
    shim += matches[0] + '\n'
kb = re.findall(r'^#define KB .+$', lz4, flags=re.M)
assert len(kb) == 1
shim += kb[0] + '\n'
shim += r'''
/*@ requires count == 1 && p == begin;
    requires \valid_read(p);
    terminates \true;
    assigns \nothing;
    ensures \result == *p;
    exits \false;
*/
static BYTE entry_read(const BYTE *p, const BYTE *begin, int count) {
    return *p;
}

/*@ requires \false;
    terminates \false;
    exits \true;
*/
int omitted_decoder_tail(void);

/*@ requires src != \null && dst != \null;
    requires 0 <= srcSize <= 2097152;
    requires 0 <= outputSize <= 2097152;
    requires outputSize == 0 || srcSize == 0;
    requires partialDecoding == decode_full_block && dict == noDict;
    requires lowPrefix == (BYTE*)dst && dictStart == \null && dictSize == 0;
    requires \valid_read(src + (-32..srcSize-1));
    requires \valid(dst + (-32..outputSize-1));
    terminates \true;
    assigns \nothing;
    ensures \result == ((outputSize == 0 && srcSize == 1 && *(const BYTE*)src == 0)
                         ? 0 : -1);
    exits \false;
*/
'''
a = lz4.index('int LZ4_decompress_safe(')
b = lz4.index('\n}', a) + 2
export = lz4[a:b]
(ROOT / 'verification/entry_prefix.c').write_text(
    '/* GENERATED exact source prefix and export; see prepare.py. */\n' + shim +
    prefix + '\n        return omitted_decoder_tail();\n    }\n}\n\n' + export + '\n')
print('Prepared exact decoder prefix; its suffix has a false-precondition guard')
