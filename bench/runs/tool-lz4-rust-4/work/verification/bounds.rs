use vstd::prelude::*;
verus! {
// Arithmetic obligations for the source's memory footprints, not a Wasm proof.
pub open spec fn range(base: int, size: int, addr: int, width: int) -> bool {
    131072 <= base && 0 <= size && base + size <= 2097152
        && 0 <= width && base <= addr && addr + width <= base + size
}

// Every relative access contained in a caller slice is in its absolute range;
// neither a Wasm i32 address nor its end wraps.
pub proof fn relocate(base: int, size: int, index: int, width: int)
    requires 131072 <= base, 0 <= size, base + size <= 2097152,
        0 <= index, 0 <= width, index + width <= size,
    ensures range(base, size, base + index, width),
        0 <= base + index < 4294967296int,
        0 <= base + index + width < 4294967296int,
{}

// `input_pos` here is just AFTER consuming the token. Fits-token means both
// nibbles < 15. This covers the sixteen-byte input slice, offset within that
// slice, sixteen-byte output write, and the eighteen-byte match wild copy.
pub proof fn hot_bounds(n: int, cap: int, ip: int, op: int,
    lit: int, ml: int, off: int)
    requires 0 <= n <= 2097152, 0 <= cap <= 2097152,
        1 <= ip <= n, ip <= if n >= 18 { n - 18 } else { 0 },
        0 <= op < if cap >= 34 { cap - 34 } else { 0 },
        0 <= lit <= 14, 4 <= ml <= 18,
        1 <= off <= op + lit,
    ensures ip + 16 <= n, lit + 2 <= 16,
        ip + lit + 2 <= n, op + 16 <= cap,
        op + lit + 18 <= cap,
        0 <= op + lit - off,
        op + lit - off + 18 <= cap,
        op + lit + ml <= cap,
{}

pub open spec fn wild_length(op: int, cap: int, ml: int) -> int {
    if ml <= 32 && op + 32 <= cap { 32 }
    else if 33 <= ml <= 64 && op + 64 <= cap { 64 }
    else { ml }
}

// Slow non-overlapping duplicate_slice: its 32/64/exact read and write spans
// are within output capacity, even if the READ includes not-yet-decoded bytes.
pub proof fn slow_wild_bounds(op: int, cap: int, ml: int, off: int)
    requires 0 <= op <= cap <= 2097152, 4 <= ml,
        op + ml <= cap, ml <= off <= op,
    ensures 0 <= op - off,
        ml <= wild_length(op, cap, ml),
        op + wild_length(op, cap, ml) <= cap,
        op - off + wild_length(op, cap, ml) <= cap,
{}

// Offset-one fill and arbitrary forward overlapping matches.
pub proof fn forward_bounds(op: int, cap: int, off: int, ml: int, i: int)
    requires 1 <= off <= op <= cap <= 2097152,
        4 <= ml, op + ml <= cap, 0 <= i < ml,
    ensures 0 <= op + i - off < op + i < cap,
        0 <= op - off < cap,
{}

// fastcpy's overlapping end copies are still inside both nominal slices.
pub proof fn double_copy_bounds(len: int, chunk: int)
    requires 0 < chunk <= len,
    ensures 0 <= len - chunk, chunk <= len,
        (len - chunk) + chunk == len,
{}

// Each extension byte adds <=255. At most n source bytes can be consumed.
// Even invalid inputs in the entire caller region cannot overflow wasm32 usize.
pub proof fn length_no_wrap(n: int, used: int, sum: int, byte: int)
    requires 0 <= used < n <= 2097152 - 131072,
        0 <= sum <= 255 * used, 0 <= byte <= 255,
    ensures 0 <= sum + byte <= 255 * (used + 1),
        sum + byte + 19 + 2097152 < 4294967296int,
{}

// Errors may preserve a partly modified destination. Disjoint slice ranges
// ensure permitted destination writes do not change source bytes.
pub proof fn noninterference(src: int, n: int, dst: int, cap: int, a: int)
    requires 0 <= n, 0 <= cap, src + n <= dst || dst + cap <= src,
        dst <= a < dst + cap,
    ensures !(src <= a < src + n),
{}
fn main() {}
}
