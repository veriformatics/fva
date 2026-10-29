use vstd::prelude::*;
use vstd::assert_seqs_equal;

verus! {
// This is a reference model, not a replacement for the shipped module.
pub const LIMIT: usize = 2_097_152;

pub open spec fn extension(s: Seq<u8>, p: int) -> Option<(int, int)>
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() { None }
    else if s[p] < 255 { Some((p + 1, s[p] as int)) }
    else {
        match extension(s, p + 1) {
            None => None,
            Some((q, n)) => Some((q, n + 255)),
        }
    }
}

pub fn read_extension(s: &Vec<u8>, p: usize) -> (r: Option<(usize, usize)>)
    requires s.len() <= LIMIT, p <= s.len(),
    ensures
        match r {
            None => extension(s@, p as int) == None,
            Some((q, n)) => extension(s@, p as int) == Some((q as int, n as int))
                && p < q <= s.len() && n <= 255 * (s.len() - p),
        },
    decreases s.len() - p,
{
    if p == s.len() { return None; }
    let b = s[p] as usize;
    if b < 255 { return Some((p + 1, b)); }
    match read_extension(s, p + 1) {
        None => None,
        Some((q, n)) => Some((q, n + 255)),
    }
}

// A header result is (first literal byte, literal count).
pub open spec fn literals(s: Seq<u8>, p: int) -> Option<(int, int)> {
    if p < 0 || p >= s.len() { None }
    else if s[p] / 16 < 15 { Some((p + 1, (s[p] / 16) as int)) }
    else {
        match extension(s, p + 1) {
            None => None,
            Some((q, n)) => Some((q, n + 15)),
        }
    }
}

pub fn literal_header(s: &Vec<u8>, p: usize) -> (r: Option<(usize, usize)>)
    requires s.len() <= LIMIT, p < s.len(),
    ensures match r {
        None => literals(s@, p as int) == None,
        Some((q, n)) => literals(s@, p as int) == Some((q as int, n as int))
            && p < q <= s.len() && n <= 255 * s.len() + 15,
    },
{
    let n = (s[p] / 16) as usize;
    if n < 15 { return Some((p + 1, n)); }
    match read_extension(s, p + 1) {
        None => None,
        Some((q, n)) => Some((q, n + 15)),
    }
}

// Match header: (next sequence position, offset, match length).
pub open spec fn match_header(s: Seq<u8>, p: int, token: u8) -> Option<(int, int, int)> {
    if p < 0 || p + 2 > s.len() { None }
    else {
        let off = s[p] as int + 256 * s[p + 1] as int;
        let n = (token % 16) as int + 4;
        if n < 19 { Some((p + 2, off, n)) }
        else {
            match extension(s, p + 2) {
                None => None,
                Some((q, extra)) => Some((q, off, extra + 19)),
            }
        }
    }
}

pub fn read_match(s: &Vec<u8>, p: usize, token: u8) -> (r: Option<(usize, usize, usize)>)
    requires s.len() <= LIMIT, p <= s.len(),
    ensures match r {
        None => match_header(s@, p as int, token) == None,
        Some((q, off, n)) => match_header(s@, p as int, token)
                == Some((q as int, off as int, n as int))
            && p < q <= s.len() && off <= 65535 && 4 <= n <= 255 * s.len() + 19,
    },
{
    if s.len() - p < 2 { return None; }
    let off = s[p] as usize + 256 * s[p + 1] as usize;
    let n = (token % 16) as usize + 4;
    if n < 19 { return Some((p + 2, off, n)); }
    match read_extension(s, p + 2) {
        None => None,
        Some((q, extra)) => Some((q, off, extra + 19)),
    }
}

pub open spec fn match_bytes(prefix: Seq<u8>, off: int, n: nat) -> Seq<u8>
    recommends 0 < off <= prefix.len(),
    decreases n,
{
    if n == 0 { prefix }
    else {
        let prev = match_bytes(prefix, off, (n - 1) as nat);
        prev.push(prev[prev.len() - off])
    }
}

pub proof fn match_length(prefix: Seq<u8>, off: int, n: nat)
    requires 0 < off <= prefix.len(),
    ensures match_bytes(prefix, off, n).len() == prefix.len() + n,
        match_bytes(prefix, off, n).subrange(0, prefix.len() as int) == prefix,
    decreases n,
{
    if n > 0 { match_length(prefix, off, (n - 1) as nat); }
    assert(match_bytes(prefix, off, n).subrange(0, prefix.len() as int) == prefix) by {
        assert_seqs_equal!(match_bytes(prefix, off, n).subrange(0, prefix.len() as int), prefix);
    }
}

pub fn append_literals(out: &mut Vec<u8>, s: &Vec<u8>, p: usize, n: usize)
    requires p <= s.len(), n <= s.len() - p,
        old(out).len() + n <= LIMIT,
    ensures final(out)@ == old(out)@ + s@.subrange(p as int, (p + n) as int),
{
    let ghost before = out@;
    let mut i = 0;
    while i < n
        invariant p <= s.len(), n <= s.len() - p, i <= n, out@ == before + s@.subrange(p as int, (p + i) as int),
            before.len() + n <= LIMIT,
        decreases n - i,
    {
        out.push(s[p + i]);
        proof {
            assert_seqs_equal!(out@, before + s@.subrange(p as int, (p + i + 1) as int));
        }
        i += 1;
    }
}

pub fn append_match(out: &mut Vec<u8>, off: usize, n: usize)
    requires 0 < off <= old(out).len(), old(out).len() + n <= LIMIT,
    ensures final(out)@ == match_bytes(old(out)@, off as int, n as nat),
        final(out).len() == old(out).len() + n,
{
    let ghost before = out@;
    let mut i = 0;
    while i < n
        invariant i <= n, out@ == match_bytes(before, off as int, i as nat),
            0 < off <= before.len(), before.len() + n <= LIMIT,
            out.len() == before.len() + i,
        decreases n - i,
    {
        let b = out[out.len() - off];
        out.push(b);
        proof {
            reveal_with_fuel(match_bytes, 1);
            assert(out@ == match_bytes(before, off as int, (i + 1) as nat));
        }
        i += 1;
    }
}

// Operational LZ4 sequence grammar. A final literal sequence must consume all input.
// End-of-block compatibility conditions are intentionally handled separately.
pub open spec fn decode(s: Seq<u8>, p: int, prefix: Seq<u8>, cap: int) -> Option<Seq<u8>>
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() { None }
    else {
        match literals(s, p) {
            None => None,
            Some((q, n)) => {
                if q < p + 1 || q > s.len() || n < 0 || n > s.len() - q
                    || prefix.len() + n > cap { None }
                else {
                    let e = q + n;
                    let next = prefix + s.subrange(q, e);
                    if e == s.len() { Some(next) }
                    else {
                        match match_header(s, e, s[p]) {
                            None => None,
                            Some((r, off, len)) => {
                                if r <= p || r > s.len() || off <= 0 || off > next.len()
                                    || len < 4 || next.len() + len > cap { None }
                                else { decode(s, r, match_bytes(next, off, len as nat), cap) }
                            }
                        }
                    }
                }
            }
        }
    }
}


// Capacity-independent grammar/meaning. Positive offsets and sequential overlapping
// matches are part of this definition; compatibility end conditions are not.
pub open spec fn format_decode(s: Seq<u8>, p: int, prefix: Seq<u8>) -> Option<Seq<u8>>
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() { None }
    else {
        match literals(s, p) {
            None => None,
            Some((q, n)) => {
                if q < p + 1 || q > s.len() || n < 0 || n > s.len() - q { None }
                else {
                    let e = q + n;
                    let next = prefix + s.subrange(q, e);
                    if e == s.len() { Some(next) }
                    else {
                        match match_header(s, e, s[p]) {
                            None => None,
                            Some((r, off, len)) => {
                                if r <= p || r > s.len() || off <= 0 || off > next.len()
                                    || len < 4 { None }
                                else { format_decode(s, r, match_bytes(next, off, len as nat)) }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub proof fn format_grows(s: Seq<u8>, p: int, prefix: Seq<u8>)
    ensures match format_decode(s, p, prefix) {
        None => true,
        Some(out) => out.len() >= prefix.len()
            && out.subrange(0, prefix.len() as int) == prefix,
    },
    decreases s.len() - p,
{
    if 0 <= p < s.len() {
        if let Some((q, n)) = literals(s, p) {
            if p + 1 <= q <= s.len() && 0 <= n <= s.len() - q {
                let e = q + n;
                let next = prefix + s.subrange(q, e);
                assert(next.subrange(0, prefix.len() as int) == prefix) by {
                    assert_seqs_equal!(next.subrange(0, prefix.len() as int), prefix);
                }
                if e != s.len() {
                    if let Some((r, off, len)) = match_header(s, e, s[p]) {
                        if p < r <= s.len() && 0 < off <= next.len() && 4 <= len {
                            match_length(next, off, len as nat);
                            let more = match_bytes(next, off, len as nat);
                            format_grows(s, r, more);
                            if let Some(out) = format_decode(s, r, more) {
                                assert(out.subrange(0, prefix.len() as int) == prefix) by {
                                    assert_seqs_equal!(out.subrange(0, prefix.len() as int), prefix);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

// This is both completeness and soundness for the capacity-limited model.
pub proof fn capacity_equivalence(s: Seq<u8>, p: int, prefix: Seq<u8>, cap: int)
    requires prefix.len() <= cap,
    ensures decode(s, p, prefix, cap) == match format_decode(s, p, prefix) {
        Some(out) => if out.len() <= cap { Some(out) } else { None },
        None => None,
    },
    decreases s.len() - p,
{
    if 0 <= p < s.len() {
        if let Some((q, n)) = literals(s, p) {
            if p + 1 <= q <= s.len() && 0 <= n <= s.len() - q {
                let e = q + n;
                let next = prefix + s.subrange(q, e);
                if e != s.len() {
                    if let Some((r, off, len)) = match_header(s, e, s[p]) {
                        if p < r <= s.len() && 0 < off <= next.len() && 4 <= len {
                            match_length(next, off, len as nat);
                            let more = match_bytes(next, off, len as nat);
                            format_grows(s, r, more);
                            if more.len() <= cap {
                                capacity_equivalence(s, r, more, cap);
                            }
                        }
                    }
                }
            }
        }
    }
}

pub proof fn model_r2(s: Seq<u8>, expected: Seq<u8>, cap: int)
    requires 0 <= cap, format_decode(s, 0, Seq::empty()) == Some(expected),
        expected.len() <= cap,
    ensures decode(s, 0, Seq::empty(), cap) == Some(expected),
{
    capacity_equivalence(s, 0, Seq::empty(), cap);
}

pub proof fn model_r3(s: Seq<u8>, out: Seq<u8>, cap: int)
    requires 0 <= cap, decode(s, 0, Seq::empty(), cap) == Some(out),
    ensures out.len() <= cap,
        format_decode(s, 0, Seq::empty()) == Some(out),
{
    capacity_equivalence(s, 0, Seq::empty(), cap);
}

pub open spec fn result_view(r: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match r { None => None, Some(v) => Some(v@) }
}

pub fn decode_from(s: &Vec<u8>, p: usize, mut out: Vec<u8>, cap: usize)
    -> (r: Option<Vec<u8>>)
    requires s.len() <= LIMIT, p <= s.len(), out.len() <= cap <= LIMIT,
    ensures result_view(r) == decode(s@, p as int, out@, cap as int),
        match r { None => true, Some(v) => v.len() <= cap },
    decreases s.len() - p,
{
    if p == s.len() { return None; }
    let (q, n) = match literal_header(s, p) { None => return None, Some(x) => x };
    if n > s.len() - q || n > cap - out.len() { return None; }
    let e = q + n;
    append_literals(&mut out, s, q, n);
    if e == s.len() { return Some(out); }
    let (r, off, len) = match read_match(s, e, s[p]) {
        None => return None, Some(x) => x,
    };
    if off == 0 || off > out.len() || len > cap - out.len() { return None; }
    append_match(&mut out, off, len);
    decode_from(s, r, out, cap)
}

pub fn reference_decompress(s: &Vec<u8>, cap: usize) -> (r: Option<Vec<u8>>)
    requires s.len() <= LIMIT, cap <= LIMIT,
    ensures result_view(r) == decode(s@, 0, Seq::empty(), cap as int),
        match r { None => true, Some(v) => v.len() <= cap },
{
    decode_from(s, 0, Vec::new(), cap)
}

} // verus!
fn main() {}
