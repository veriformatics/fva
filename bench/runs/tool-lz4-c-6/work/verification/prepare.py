"""Copy shipped decoder, adding annotations only; no C tokens are changed."""
from pathlib import Path
root = Path(__file__).resolve().parent.parent
source = (root / 'src/lz4.c').read_text()
needle = '''        while (1) {
            assert(ip < iend);
            token = *ip++;'''
annotation = r'''        /*@ loop invariant ip == (const BYTE*)src;
            loop invariant op == (BYTE*)dst;
            loop invariant \forall integer k; 0 <= k < srcSize ==>
                ((const BYTE*)src)[k] == \at(((const BYTE*)src)[k],Pre);
            loop assigns ip, op, cpy, match, offset, token, length,
                         ((BYTE*)dst)[0 .. outputSize-1];
            loop variant 1;
        */
'''
assert source.count(needle) == 1
source = source.replace(needle, annotation + needle)
# These calls are unreachable for the restricted literal theorem. Every call
# generates a false-precondition goal; WP must discharge it at the caller.
for declaration in ['LZ4_FORCE_INLINE\nvoid LZ4_wildCopy8(',
                    'LZ4_FORCE_INLINE Rvl_t\nread_variable_length(']:
    assert source.count(declaration) == 1
    source = source.replace(declaration, '/*@ requires \\false; assigns \\nothing; */\n' + declaration)
needle_match = "    _copy_match:\n"
assert source.count(needle_match) == 1
source = source.replace(needle_match, needle_match + "            /*@ assert no_match_for_restricted_inputs: \\false; */\n")
(root / 'verification/lz4.annotated.c').write_text(source)
memory = (root / 'src/c-memory.c').read_text()
# Both branches implement a copy. The harness has disjoint buffers.
memory = memory.replace('''        for (size_t i = 0; i < n; ++i) d[i] = s[i];''', r'''        /*@ loop invariant 0 <= i <= n;
            loop invariant \forall integer k; 0 <= k < n ==> s[k] == \at(((const unsigned char*)src)[k],Pre);
            loop invariant \forall integer k; 0 <= k < i ==> d[k] == \at(((const unsigned char*)src)[k],Pre);
            loop assigns i, d[0 .. n-1];
            loop variant n-i;
        */
        for (size_t i = 0; i < n; ++i) d[i] = s[i];''')
memory = memory.replace('''        while (n != 0) { --n; d[n] = s[n]; }''', r'''        /*@ loop invariant 0 <= n <= \at(n,Pre);
            loop invariant \forall integer k; 0 <= k < \at(n,Pre) ==> s[k] == \at(((const unsigned char*)src)[k],Pre);
            loop invariant \forall integer k; n <= k < \at(n,Pre) ==> d[k] == \at(((const unsigned char*)src)[k],Pre);
            loop assigns n, d[0 .. \at(n,Pre)-1];
            loop variant n;
        */
        while (n != 0) { --n; d[n] = s[n]; }''')
memory = memory.replace('void *memmove(', r"""/*@ requires n <= 2097152;
    requires \valid((unsigned char*)dst + (0 .. n-1));
    requires \valid_read((const unsigned char*)src + (0 .. n-1));
    requires \separated((unsigned char*)dst + (0 .. n-1),
                        (const unsigned char*)src + (0 .. n-1));
    terminates \true;
    assigns ((unsigned char*)dst)[0 .. n-1];
    ensures \result == dst;
    ensures \forall integer k; 0 <= k < \old(n) ==>
        ((unsigned char*)dst)[k] == \old(((const unsigned char*)src)[k]);
*/
void *memmove(""")
memory = memory.replace('--n; d[n] = s[n];', r'''--n; /*@ assert decrement: n == \at(n,LoopCurrent)-1; */
                /*@ assert copied_byte: \let k = n; s[k] == \at(((const unsigned char*)src)[k],Pre); */
                /*@ assert suffix_before_write: \forall integer k; n < k < \at(n,Pre) ==>
                        d[k] == \at(((const unsigned char*)src)[k],Pre); */
                /*@ assert distinct_suffix: \forall integer k; n < k < \at(n,Pre) ==>
                        \separated(d+n,d+k);
                */ d[n] = s[n];''')
memory = memory.replace('        for (size_t i = 0; i < n; ++i) d[i] = s[i];', r"""        for (size_t i = 0; i < n; ++i)
            /*@ assert copied_forward: \let k = i; s[k] == \at(((const unsigned char*)src)[k],Pre); */
            /*@ assert distinct_prefix: \forall integer k; 0 <= k < i ==> \separated(d+i,d+k); */
            d[i] = s[i];""")
(root / 'verification/memory.annotated.c').write_text(memory)

# Check that annotations are the only change, including within quoted strings.
import re
c_lex = re.compile(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_]\w*|[0-9]+|[^\s]', re.S)
def c_tokens(text):
    return [token for token in c_lex.findall(text)
            if not token.startswith(('/*', '//'))]
for original, annotated in [('src/lz4.c', 'verification/lz4.annotated.c'),
                            ('src/c-memory.c', 'verification/memory.annotated.c')]:
    assert c_tokens((root/original).read_text()) == c_tokens((root/annotated).read_text()), original
print('Annotated copies: identical C token streams; only comments differ.')
