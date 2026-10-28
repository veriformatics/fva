/* Proofs of the extracted entry prefix. Its omitted suffix must be unreachable. */
#include "entry_prefix.c"

unsigned char memory[2097152];

/*@ requires 131072 <= src < 2097152;
    requires 131072 <= dst < 2097152;
    requires 0 <= size <= 2097152 - src;
    terminates \true;
    assigns \nothing;
    ensures \result == ((size == 1 && memory[src] == 0) ? 0 : -1);
    exits \false;
*/
int verify_zero_capacity(int src, int dst, int size) {
    return LZ4_decompress_safe((const char *)memory + src,
                               (char *)memory + dst, size, 0);
}

/*@ requires 131072 <= src < 2097152;
    requires 131072 <= dst < 2097152;
    requires 0 <= cap <= 2097152 - dst;
    terminates \true;
    assigns \nothing;
    ensures \result == -1;
    exits \false;
*/
int verify_empty_source(int src, int dst, int cap) {
    return LZ4_decompress_safe((const char *)memory + src,
                               (char *)memory + dst, 0, cap);
}
