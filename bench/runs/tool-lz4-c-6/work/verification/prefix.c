/* C model of the checked entry prefix of Wasm function 2.
   No tail of the decoder is modeled. The assertion at the cut must be proved.
   The model uses Wasm byte offsets, not host addresses, for s and d. */
typedef unsigned int u32;
typedef unsigned char byte;

/*@ requires 131072 <= s <= 2097151;
    requires 131072 <= d <= 2097151;
    requires size <= 2097152-s;
    requires cap <= 2097152-d;
    requires cap == 0 || size == 0;
    requires size == 1 ==> \valid_read(m+s);
    terminates \true;
    assigns \nothing;
    ensures \result == ((cap == 0 && size == 1 && m[s] == 0) ? 0 : -1);
*/
int wasm_entry_prefix(const byte *m, u32 s, u32 d, u32 size, u32 cap) {
    int l4 = -1;
    if (s == 0) return l4;
    /* i32.lt_s(cap,0), written without a C signed conversion. */
    if (cap >= 2147483648U) return l4;
    if (cap == 0) {
        if (size != 1) return l4;
        /*@ assert read_in_source: size == 1 && s < s+size; */
        u32 token = m[s];
        /* i32.const -1; i32.const 0; token; select */
        return token ? -1 : 0;
    }
    if (size == 0) return l4;
    /*@ assert unreachable_tail: \false; */
    return 0;
}
