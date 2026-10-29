use vstd::prelude::*;
verus! {
// Integer counterpart of check_read/check_write emitted by replay.py.
pub open spec fn permitted(a: int, end: int, src: int, n: int,
    dst: int, cap: int, read: bool) -> bool {
    a == end || end <= 131072
        || (dst <= a && end <= dst + cap)
        || (read && src <= a && end <= src + n)
}

pub open spec fn allowed_byte(a: int, src: int, n: int, dst: int, cap: int, read: bool) -> bool {
    dst <= a < dst + cap || (read && src <= a < src + n)
}

pub proof fn monitor_sound(base: int, offset: int, len: int,
    src: int, n: int, dst: int, cap: int, read: bool)
    requires
        0 <= base <= 4294967295int,
        0 <= offset <= 4294967295int,
        0 <= len <= 4294967295int,
        131072 <= src, 0 <= n, src + n <= 2097152,
        131072 <= dst, 0 <= cap, dst + cap <= 2097152,
        permitted(base + offset, base + offset + len, src, n, dst, cap, read),
    ensures
        0 <= base + offset <= base + offset + len < 18446744073709551616int,
        forall|a: int| base + offset <= a < base + offset + len
            && 131072 <= a < 2097152 ==>
                #[trigger] allowed_byte(a, src, n, dst, cap, read),
{}
}
fn main() {}
