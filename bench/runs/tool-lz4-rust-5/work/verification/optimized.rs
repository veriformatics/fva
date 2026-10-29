use vstd::prelude::*;
use vstd::assert_seqs_equal;
mod decoder;
use decoder::*;

verus! {

// Fixed-size output memory and a logical cursor model SliceSink. In particular,
// bytes beyond the logical cursor exist and can be read by a wild copy.
pub fn literal_copy(buf: &mut Vec<u8>, pos: usize, s: &Vec<u8>, p: usize,
    wild: usize, used: usize)
    requires pos <= old(buf).len(), wild <= old(buf).len() - pos,
        p <= s.len(), wild <= s.len() - p, used <= wild,
    ensures final(buf).len() == old(buf).len(),
        final(buf)@.subrange(0, (pos + used) as int)
            == old(buf)@.subrange(0, pos as int) + s@.subrange(p as int, (p + used) as int),
{
    let ghost before = buf@;
    let mut i = 0;
    while i < wild
        invariant used <= wild, i <= wild, pos <= buf.len(), wild <= buf.len() - pos,
            p <= s.len(), wild <= s.len() - p,
            buf.len() == before.len(),
            forall|k: int| 0 <= k < pos ==> #[trigger] buf@[k] == before[k],
            forall|k: int| 0 <= k < i ==> #[trigger] buf@[pos + k] == s@[p + k],
        decreases wild - i,
    {
        buf.set(pos + i, s[p + i]);
        i += 1;
    }
    proof {
        assert forall|k: int| pos <= k < pos + used implies
            #[trigger] buf@[k] == s@[p + k - pos] by {
            let j = k - pos;
            assert(buf@[pos + j] == s@[p + j]);
        }
        assert_seqs_equal!(buf@.subrange(0, (pos + used) as int),
            before.subrange(0, pos as int) + s@.subrange(p as int, (p + used) as int));
    }
}

// Snapshot copy is the semantics of Rust copy_within / Wasm memory.copy.
pub fn within_copy(buf: &mut Vec<u8>, pos: usize, start: usize, wild: usize, used: usize)
    requires pos <= old(buf).len(), wild <= old(buf).len() - pos,
        start <= old(buf).len(), wild <= old(buf).len() - start, used <= wild,
    ensures final(buf).len() == old(buf).len(),
        final(buf)@.subrange(0, (pos + used) as int)
            == old(buf)@.subrange(0, pos as int)
                + old(buf)@.subrange(start as int, (start + used) as int),
{
    let snapshot = buf.clone();
    literal_copy(buf, pos, &snapshot, start, wild, used);
}

pub proof fn nonoverlap_match(prefix: Seq<u8>, off: int, n: nat)
    requires 0 < off <= prefix.len(), n <= off,
    ensures match_bytes(prefix, off, n) == prefix
        + prefix.subrange(prefix.len() - off, prefix.len() - off + n),
    decreases n,
{
    if n > 0 { nonoverlap_match(prefix, off, (n - 1) as nat); }
    assert_seqs_equal!(match_bytes(prefix, off, n),
        prefix + prefix.subrange(prefix.len() - off, prefix.len() - off + n));
}

pub fn overlap_copy(buf: &mut Vec<u8>, pos: usize, off: usize, used: usize)
    requires 0 < off <= pos <= old(buf).len(), used <= old(buf).len() - pos,
    ensures final(buf).len() == old(buf).len(),
        final(buf)@.subrange(0, (pos + used) as int)
            == match_bytes(old(buf)@.subrange(0, pos as int), off as int, used as nat),
{
    let ghost before = buf@.subrange(0, pos as int);
    let ghost size = buf.len();
    let mut i = 0;
    while i < used
        invariant i <= used, 0 < off <= pos <= buf.len(), used <= buf.len() - pos,
            buf.len() == size, before.len() == pos,
            buf@.subrange(0, (pos + i) as int) == match_bytes(before, off as int, i as nat),
        decreases used - i,
    {
        let b = buf[pos + i - off];
        buf.set(pos + i, b);
        proof {
            assert_seqs_equal!(buf@.subrange(0, (pos + i + 1) as int),
                match_bytes(before, off as int, (i + 1) as nat));
        }
        i += 1;
    }
}

// Models the offset-one fill used by duplicate_overlapping_slice.
pub fn fill_copy(buf: &mut Vec<u8>, pos: usize, used: usize)
    requires 0 < pos <= old(buf).len(), used <= old(buf).len() - pos,
    ensures final(buf).len() == old(buf).len(),
        final(buf)@.subrange(0, (pos + used) as int)
            == match_bytes(old(buf)@.subrange(0, pos as int), 1, used as nat),
{
    let b = buf[pos - 1];
    let ghost before = buf@.subrange(0, pos as int);
    let ghost size = buf.len();
    let mut i = 0;
    while i < used
        invariant i <= used, 0 < pos <= buf.len(), used <= buf.len() - pos,
            buf.len() == size, before.len() == pos,
            buf@.subrange(0, (pos + i) as int) == match_bytes(before, 1, i as nat),
            buf@[pos + i - 1] == b,
        decreases used - i,
    {
        buf.set(pos + i, b);
        proof {
            assert_seqs_equal!(buf@.subrange(0, (pos + i + 1) as int),
                match_bytes(before, 1, (i + 1) as nat));
        }
        i += 1;
    }
}

pub open spec fn buffer_result(r: Option<usize>, buf: Seq<u8>) -> Option<Seq<u8>> {
    match r { None => None, Some(n) => Some(buf.subrange(0, n as int)) }
}

// The control structure is recursive at sequence boundaries, rather than the
// original loop. It implements both of decompress_safe.rs's fast and slow paths.
pub fn optimized_from(s: &Vec<u8>, p: usize, buf: &mut Vec<u8>, pos: usize)
    -> (result: Option<usize>)
    requires s.len() <= LIMIT, p <= s.len(), pos <= old(buf).len() <= LIMIT,
    ensures final(buf).len() == old(buf).len(),
        match result { None => true, Some(r) => r <= final(buf).len() },
        buffer_result(result, final(buf)@)
            == decode(s@, p as int, old(buf)@.subrange(0, pos as int), old(buf).len() as int),
    decreases s.len() - p,
{
    let ghost before = buf@.subrange(0, pos as int);
    let cap = buf.len();
    if p == s.len() { return None; }
    let token = s[p];
    let hi = (token / 16) as usize;
    let lo = (token % 16) as usize;
    let ip = p + 1;
    let safe_input = if s.len() >= 18 { s.len() - 18 } else { 0 };
    let safe_output = if cap >= 34 { cap - 34 } else { 0 };
    if hi < 15 && lo < 15 && ip <= safe_input && pos < safe_output {
        literal_copy(buf, pos, s, ip, 16, hi);
        let q = ip + hi;
        let off = s[q] as usize + 256 * s[q + 1] as usize;
        let next = pos + hi;
        let len = lo + 4;
        proof {
            assert(literals(s@, p as int) == Some((ip as int, hi as int)));
            assert(match_header(s@, q as int, token) == Some(((q + 2) as int, off as int, len as int)));
        }
        if off == 0 || off > next { return None; }
        if off >= len {
            let ghost prefix = buf@.subrange(0, next as int);
            within_copy(buf, next, next - off, 18, len);
            proof {
                nonoverlap_match(prefix, off as int, len as nat);
                assert_seqs_equal!(buf@.subrange(0, (next + len) as int),
                    match_bytes(prefix, off as int, len as nat));
            }
        } else {
            overlap_copy(buf, next, off, len);
        }
        proof {
            assert(buf@.subrange(0, (next + len) as int) == match_bytes(
                before + s@.subrange(ip as int, q as int), off as int, len as nat));
        }
        return optimized_from(s, q + 2, buf, next + len);
    }
    let (q, n) = match literal_header(s, p) { None => return None, Some(x) => x };
    if n > s.len() - q || n > cap - pos { return None; }
    literal_copy(buf, pos, s, q, n, n);
    let next = pos + n;
    let e = q + n;
    if e == s.len() { return Some(next); }
    let (r, off, len) = match read_match(s, e, token) { None => return None, Some(x) => x };
    if off == 0 || off > next || len > cap - next { return None; }
    if len > off {
        if off == 1 { fill_copy(buf, next, len); }
        else { overlap_copy(buf, next, off, len); }
    } else {
        let ghost prefix = buf@.subrange(0, next as int);
        let wild = if len <= 32 && 32 <= cap - next { 32 }
            else if 33 <= len && len <= 64 && 64 <= cap - next { 64 } else { len };
        within_copy(buf, next, next - off, wild, len);
        proof {
                nonoverlap_match(prefix, off as int, len as nat);
                assert_seqs_equal!(buf@.subrange(0, (next + len) as int),
                    match_bytes(prefix, off as int, len as nat));
            }
    }
    proof {
        assert(buf@.subrange(0, (next + len) as int) == match_bytes(
            before + s@.subrange(q as int, e as int), off as int, len as nat));
    }
    optimized_from(s, r, buf, next + len)
}

pub fn optimized_decompress(s: &Vec<u8>, buf: &mut Vec<u8>) -> (r: Option<usize>)
    requires s.len() <= LIMIT, old(buf).len() <= LIMIT,
    ensures final(buf).len() == old(buf).len(),
        match r { None => true, Some(n) => n <= final(buf).len() },
        buffer_result(r, final(buf)@) == decode(s@, 0, Seq::empty(), old(buf).len() as int),
        buffer_result(r, final(buf)@) == match format_decode(s@, 0, Seq::empty()) {
            None => None,
            Some(out) => if out.len() <= old(buf).len() { Some(out) } else { None },
        },
{
    let r = optimized_from(s, 0, buf, 0);
    proof { capacity_equivalence(s@, 0, Seq::empty(), buf.len() as int); }
    r
}

// Relates the division/remainder spelling in this model to the source masks.
pub proof fn token_fields(t: u8)
    ensures t >> 4 == t / 16, t & 15 == t % 16,
        (!((t & 15) == 15 || (t & 240) == 240))
            == (t / 16 < 15 && t % 16 < 15),
{
    assert(t >> 4 == t / 16 && t & 15 == t % 16
        && (!((t & 15) == 15 || (t & 240) == 240))
            == (t / 16 < 15 && t % 16 < 15)) by (bit_vector);
}

pub fn abi_result(r: Option<usize>) -> (v: isize)
    requires match r { None => true, Some(n) => n <= LIMIT },
    ensures match r { None => v == -1, Some(n) => v == n as int && 0 <= v <= LIMIT },
{
    match r { None => -1, Some(n) => n as isize }
}

pub proof fn caller_layout(src: int, dst: int, n: int, cap: int, i: int, j: int)
    requires 131072 <= src, 0 <= n, src + n <= 2097152,
        131072 <= dst, 0 <= cap, dst + cap <= 2097152,
        src + n <= dst || dst + cap <= src,
        0 <= i < n, 0 <= j < cap,
    ensures 131072 <= src + i < 2097152,
        131072 <= dst + j < 2097152,
        !(dst <= src + i < dst + cap), !(src <= dst + j < src + n),
        0 <= src + i < 4294967296int, 0 <= dst + j < 4294967296int,
{}

} // verus!
fn main() {}
