use vstd::prelude::*;

verus! {

// Mathematical LZ4 block semantics. Positions and lengths here are unbounded integers.
pub open spec fn extension(s: Seq<u8>, p: int) -> Option<(int, int)>
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() { None }
    else if s[p] != 255 { Some((p + 1, s[p] as int)) }
    else {
        match extension(s, p + 1) {
            None => None,
            Some((q, n)) => Some((q, 255 + n)),
        }
    }
}

pub open spec fn length(s: Seq<u8>, p: int, small: int, bias: int) -> Option<(int, int)> {
    if small < 15 { Some((p, small + bias)) }
    else {
        match extension(s, p) {
            None => None,
            Some((q, n)) => Some((q, 15 + bias + n)),
        }
    }
}

// One-byte-at-a-time match copying defines overlap without assuming a memmove.
pub open spec fn grow(pre: Seq<u8>, off: int, count: nat) -> Seq<u8>
    decreases count,
{
    if count == 0 { pre }
    else {
        let before = grow(pre, off, (count - 1) as nat);
        before.push(before[before.len() - off])
    }
}

pub proof fn grow_size(pre: Seq<u8>, off: int, count: nat)
    ensures grow(pre, off, count).len() == pre.len() + count,
    decreases count,
{
    if count > 0 { grow_size(pre, off, (count - 1) as nat); }
}

// Includes final literal-only sequences; deliberately omits end-of-block restrictions,
// as permitted by R3. R2's valid blocks form a subset of these semantics.
pub open spec fn decode(s: Seq<u8>, p: int, pre: Seq<u8>) -> Option<Seq<u8>>
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() { None }
    else {
        let token = s[p] as int;
        match length(s, p + 1, token / 16, 0) {
            None => None,
            Some((q, ll)) => {
                if q < p + 1 || ll < 0 || q + ll > s.len() { None }
                else {
                    let after = pre + s.subrange(q, q + ll);
                    let next = q + ll;
                    if next == s.len() { Some(after) }
                    else if next + 2 > s.len() { None }
                    else {
                        let off = s[next] as int + 256 * s[next + 1] as int;
                        if off == 0 || off > after.len() { None }
                        else {
                            match length(s, next + 2, token % 16, 4) {
                                None => None,
                                Some((r, ml)) => {
                                    if r < next + 2 || r > s.len() || ml < 4 { None }
                                    else { decode(s, r, grow(after, off, ml as nat)) }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub proof fn decode_size(s: Seq<u8>, p: int, pre: Seq<u8>)
    ensures match decode(s, p, pre) {
        None => true,
        Some(out) => out.len() >= pre.len(),
    },
    decreases s.len() - p,
{
    if 0 <= p < s.len() {
        let token = s[p] as int;
        if let Some((q, ll)) = length(s, p + 1, token / 16, 0) {
            if q >= p + 1 && ll >= 0 && q + ll <= s.len() {
                let after = pre + s.subrange(q, q + ll);
                let next = q + ll;
                if next < s.len() && next + 2 <= s.len() {
                    let off = s[next] as int + 256 * s[next + 1] as int;
                    if off != 0 && off <= after.len() {
                        if let Some((r, ml)) = length(s, next + 2, token % 16, 4) {
                            if next + 2 <= r <= s.len() && ml >= 4 {
                                grow_size(after, off, ml as nat);
                                decode_size(s, r, grow(after, off, ml as nat));
                            }
                        }
                    }
                }
            }
        }
    }
}

pub proof fn after_literals_size(s: Seq<u8>, p: int, pre: Seq<u8>, q: int, ll: int)
    requires 0 <= p < s.len(), length(s, p + 1, s[p] as int / 16, 0) == Some((q, ll)),
        p + 1 <= q, 0 <= ll, q + ll <= s.len(),
    ensures match decode(s, p, pre) {
        None => true,
        Some(out) => out.len() >= pre.len() + ll,
    },
{
    let after = pre + s.subrange(q, q + ll);
    let next = q + ll;
    if next < s.len() && next + 2 <= s.len() {
        let off = s[next] as int + 256 * s[next + 1] as int;
        if off != 0 && off <= after.len() {
            if let Some((r, ml)) = length(s, next + 2, s[p] as int % 16, 4) {
                if next + 2 <= r <= s.len() && ml >= 4 {
                    grow_size(after, off, ml as nat);
                    decode_size(s, r, grow(after, off, ml as nat));
                }
            }
        }
    }
}

pub proof fn extension_prefix(s: Seq<u8>, p: int, q: int)
    requires 0 <= p <= q <= s.len(),
        forall |k: int| p <= k < q ==> #[trigger] s[k] == 255,
    ensures extension(s, p) == match extension(s, q) {
        None => None,
        Some((r, n)) => Some((r, 255 * (q - p) + n)),
    },
    decreases q - p,
{
    if p < q { extension_prefix(s, p + 1, q); }
}

pub fn read_extension(input: &Vec<u8>, p: usize) -> (res: Option<(usize, usize)>)
    requires input.len() <= 2097152, p <= input.len(),
    ensures match res {
        None => extension(input@, p as int).is_none(),
        Some((q, n)) => extension(input@, p as int) == Some((q as int, n as int))
            && p < q <= input.len() && n <= 255 * (q - p),
    },
{
    let mut q = p;
    let mut total = 0usize;
    while q < input.len()
        invariant input.len() <= 2097152, p <= q <= input.len(),
            total == 255 * (q - p),
            forall |k: int| p <= k < q ==> #[trigger] input@[k] == 255,
        decreases input.len() - q,
    {
        let b = input[q] as usize;
        if b != 255 {
            proof { extension_prefix(input@, p as int, q as int); }
            return Some((q + 1, total + b));
        }
        total += 255;
        q += 1;
    }
    proof { extension_prefix(input@, p as int, q as int); }
    None
}

pub fn read_length(input: &Vec<u8>, p: usize, small: usize, bias: usize)
    -> (res: Option<(usize, usize)>)
    requires input.len() <= 2097152, p <= input.len(), small <= 15, bias <= 4,
    ensures match res {
        None => length(input@, p as int, small as int, bias as int).is_none(),
        Some((q, n)) => length(input@, p as int, small as int, bias as int)
            == Some((q as int, n as int)) && p <= q <= input.len()
            && bias <= n <= 19 + 255 * input.len(),
    },
{
    if small < 15 { return Some((p, small + bias)); }
    match read_extension(input, p) {
        None => None,
        Some((q, n)) => Some((q, 15 + bias + n)),
    }
}

pub fn copy_literals(input: &Vec<u8>, output: &mut Vec<u8>, q: usize, pos: usize, n: usize)
    requires q + n <= input.len(), pos + n <= old(output).len(),
    ensures final(output).len() == old(output).len(),
        final(output)@.subrange(0, (pos + n) as int)
            == old(output)@.subrange(0, pos as int) + input@.subrange(q as int, (q + n) as int),
{
    let ghost pre = output@.subrange(0, pos as int);
    let mut i = 0;
    while i < n
        invariant i <= n, q + n <= input.len(), pos + n <= output.len(),
            pre.len() == pos,
            output.len() == old(output).len(),
            output@.subrange(0, (pos + i) as int)
                == pre + input@.subrange(q as int, (q + i) as int),
        decreases n - i,
    {
        let ghost before = output@;
        let b = input[q + i];
        output.set(pos + i, b);
        proof {
            assert forall |k: int| 0 <= k < pos + i + 1 implies
                #[trigger] output@.subrange(0, (pos + i + 1) as int)[k]
                    == (pre + input@.subrange(q as int, (q + i + 1) as int))[k] by {
                if k < pos + i {
                    assert(output@[k] == before[k]);
                    assert(before.subrange(0, (pos + i) as int)[k]
                        == (pre + input@.subrange(q as int, (q + i) as int))[k]);
                }
            }
            assert(output@.subrange(0, (pos + i + 1) as int)
                =~= pre + input@.subrange(q as int, (q + i + 1) as int));
        }
        i += 1;
    }
}

pub fn copy_match(output: &mut Vec<u8>, pos: usize, off: usize, n: usize)
    requires 1 <= off <= pos, pos + n <= old(output).len(),
    ensures final(output).len() == old(output).len(),
        final(output)@.subrange(0, (pos + n) as int)
            == grow(old(output)@.subrange(0, pos as int), off as int, n as nat),
{
    let ghost pre = output@.subrange(0, pos as int);
    let mut i = 0;
    while i < n
        invariant i <= n, 1 <= off <= pos, pos + n <= output.len(),
            output.len() == old(output).len(),
            output@.subrange(0, (pos + i) as int) == grow(pre, off as int, i as nat),
        decreases n - i,
    {
        let ghost before = output@.subrange(0, (pos + i) as int);
        let b = output[pos + i - off];
        output.set(pos + i, b);
        proof {
            assert(output@.subrange(0, (pos + i + 1) as int) =~= before.push(b));
            assert(grow(pre, off as int, (i + 1) as nat) == before.push(b));
        }
        i += 1;
    }
}

pub fn decode_from(input: &Vec<u8>, output: &mut Vec<u8>, p: usize, pos: usize)
    -> (res: Option<usize>)
    requires input.len() <= 2097152, old(output).len() <= 2097152,
        p <= input.len(), pos <= old(output).len(),
    ensures final(output).len() == old(output).len(),
        match res {
            Some(r) => r <= final(output).len()
                && decode(input@, p as int, old(output)@.subrange(0, pos as int))
                    == Some(final(output)@.subrange(0, r as int)),
            None => match decode(input@, p as int, old(output)@.subrange(0, pos as int)) {
                None => true,
                Some(out) => out.len() > final(output).len(),
            },
        },
    decreases input.len() - p,
{
    let ghost pre = output@.subrange(0, pos as int);
    if p == input.len() { return None; }
    let token = input[p] as usize;
    let (q, ll) = match read_length(input, p + 1, token / 16, 0) {
        None => { return None; }, Some(v) => v,
    };
    if ll > input.len() - q { return None; }
    let next = q + ll;
    let ghost after = pre + input@.subrange(q as int, next as int);
    if ll > output.len() - pos {
        proof { after_literals_size(input@, p as int, pre, q as int, ll as int); }
        return None;
    }
    copy_literals(input, output, q, pos, ll);
    let newpos = pos + ll;
    if next == input.len() { return Some(newpos); }
    if input.len() - next < 2 { return None; }
    let off = input[next] as usize + 256 * input[next + 1] as usize;
    if off == 0 || off > newpos { return None; }
    let (r, ml) = match read_length(input, next + 2, token % 16, 4) {
        None => { return None; }, Some(v) => v,
    };
    if ml > output.len() - newpos {
        proof {
            grow_size(after, off as int, ml as nat);
            decode_size(input@, r as int, grow(after, off as int, ml as nat));
        }
        return None;
    }
    copy_match(output, newpos, off, ml);
    decode_from(input, output, r, newpos + ml)
}

pub fn model_decompress(input: &Vec<u8>, output: &mut Vec<u8>) -> (res: Option<usize>)
    requires input.len() <= 2097152, old(output).len() <= 2097152,
    ensures final(output).len() == old(output).len(),
        match res {
            Some(r) => r <= final(output).len()
                && decode(input@, 0, Seq::empty()) == Some(final(output)@.subrange(0, r as int)),
            None => match decode(input@, 0, Seq::empty()) {
                None => true,
                Some(out) => out.len() > final(output).len(),
            },
        },
{
    decode_from(input, output, 0, 0)
}


// R2 for the reference model, stated without a requirement on initial output bytes.
pub fn model_complete(input: &Vec<u8>, output: &mut Vec<u8>, Ghost(expected): Ghost<Seq<u8>>)
    -> (r: usize)
    requires input.len() <= 2097152, old(output).len() <= 2097152,
        decode(input@, 0, Seq::empty()) == Some(expected),
        expected.len() <= old(output).len(),
    ensures r == expected.len(), final(output).len() == old(output).len(),
        final(output)@.subrange(0, r as int) == expected,
{
    let res = model_decompress(input, output);
    match res {
        Some(r) => r,
        None => { proof { assert(false); } 0 },
    }
}

// Safety margins used by the optimized hot loop (after reading the token).
pub proof fn hot_loop_bounds(n: int, cap: int, ip: int, pos: int, literals: int, ml: int)
    requires 0 <= n <= 2097152, 0 <= cap <= 2097152,
        1 <= ip <= if n >= 18 { n - 18 } else { 0 },
        0 <= pos < if cap >= 34 { cap - 34 } else { 0 },
        0 <= literals <= 14, 4 <= ml <= 18,
    ensures ip + 16 <= n, ip + literals + 2 <= n,
        pos + 16 <= cap, pos + literals + 18 <= cap,
        pos + literals + ml <= cap,
{}

// Wild match reads start at pos-offset. Both source and destination stay in cap.
pub proof fn wild_match_bounds(pos: int, off: int, w: int, ml: int, cap: int)
    requires 1 <= off <= pos, 0 <= ml <= w, ml <= off,
        0 <= pos, pos + w <= cap,
    ensures 0 <= pos - off, pos - off + w <= cap,
        pos + ml <= cap,
{}

// 32-bit length arithmetic cannot overflow within the README's memory limits.
pub proof fn length_arithmetic(n: int, pos: int, count: int)
    requires 0 <= n <= 2097152, 0 <= pos <= 2097152,
        0 <= count <= 19 + 255 * n,
    ensures count < 4294967296int, pos + count < 4294967296int,
{}

pub proof fn grow_nonoverlap(pre: Seq<u8>, off: int, count: nat)
    requires 1 <= off <= pre.len(), count <= off,
    ensures grow(pre, off, count)
        == pre + pre.subrange(pre.len() - off, pre.len() - off + count),
    decreases count,
{
    if count == 0 {
        assert(pre + pre.subrange(pre.len() - off, pre.len() - off) =~= pre);
    } else {
        grow_nonoverlap(pre, off, (count - 1) as nat);
        grow_size(pre, off, (count - 1) as nat);
        let before = grow(pre, off, (count - 1) as nat);
        assert(before[before.len() - off] == pre[pre.len() - off + count - 1]);
        assert(grow(pre, off, count)
            =~= pre + pre.subrange(pre.len() - off, pre.len() - off + count));
    }
}

pub open spec fn blit(before: Seq<u8>, pos: int, source: Seq<u8>) -> Seq<u8> {
    before.subrange(0, pos) + source + before.subrange(pos + source.len(), before.len() as int)
}

// SliceSink::extend_from_slice_wild: extra copied bytes do not alter the logical prefix.
pub proof fn wild_literals(before: Seq<u8>, source: Seq<u8>, pos: int, ll: int)
    requires 0 <= pos, pos + source.len() <= before.len(), 0 <= ll <= source.len(),
    ensures blit(before, pos, source).len() == before.len(),
        blit(before, pos, source).subrange(0, pos + ll)
            == before.subrange(0, pos) + source.subrange(0, ll),
        forall |k: int| 0 <= k < before.len() && (k < pos || k >= pos + source.len())
            ==> #[trigger] blit(before, pos, source)[k] == before[k],
{
    assert(blit(before, pos, source).subrange(0, pos + ll)
        =~= before.subrange(0, pos) + source.subrange(0, ll));
}

// SliceSink::extend_from_within: memmove's logical prefix equals LZ4 copying
// when the true match length does not exceed the offset, even if the wild copy overlaps.
pub proof fn wild_match(before: Seq<u8>, pos: int, off: int, w: int, ml: nat)
    requires 1 <= off <= pos, pos + w <= before.len(), ml <= w, ml <= off,
    ensures blit(before, pos, before.subrange(pos - off, pos - off + w)).len() == before.len(),
        blit(before, pos, before.subrange(pos - off, pos - off + w)).subrange(0, pos + ml)
            == grow(before.subrange(0, pos), off, ml),
{
    wild_match_bounds(pos, off, w, ml as int, before.len() as int);
    grow_nonoverlap(before.subrange(0, pos), off, ml);
    wild_literals(before, before.subrange(pos - off, pos - off + w), pos, ml as int);
    assert(before.subrange(pos - off, pos - off + w).subrange(0, ml as int)
        =~= before.subrange(0, pos).subrange(pos - off, pos - off + ml));
}

// Concrete non-vacuity checks for the semantics, including a valid 13-byte
// independent block whose last match starts exactly 12 bytes before the end.
pub proof fn format_examples()
    ensures
        decode(seq![0u8], 0, Seq::empty()) == Some(Seq::<u8>::empty()),
        decode(seq![0x13u8, 65, 1, 0, 0x50, 66, 67, 68, 69, 70], 0, Seq::empty())
            == Some(seq![65u8, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]),
        decode(seq![0x10u8, 65, 0, 0, 0], 0, Seq::empty()) == None,
        decode(seq![0x10u8, 65, 2, 0, 0], 0, Seq::empty()) == None,
{
    assert(decode(seq![0u8], 0, Seq::empty()) == Some(Seq::<u8>::empty())) by (compute);
    assert(decode(seq![0x13u8, 65, 1, 0, 0x50, 66, 67, 68, 69, 70], 0, Seq::empty())
        == Some(seq![65u8, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70])) by (compute);
    assert(decode(seq![0x10u8, 65, 0, 0, 0], 0, Seq::empty()) == None) by (compute);
    assert(decode(seq![0x10u8, 65, 2, 0, 0], 0, Seq::empty()) == None) by (compute);
}

} // verus!
// Unverified I/O adapter for using the verified model as an executable test oracle.
// The core contracts above are checked; these byte framing and standard I/O calls are trusted.
fn main() {
    use std::io::{Read, Write};
    fn word(data: &[u8], cursor: &mut usize) -> usize {
        let result = u32::from_le_bytes(data[*cursor..*cursor + 4].try_into().unwrap());
        *cursor += 4;
        result as usize
    }
    let mut data = Vec::new();
    std::io::stdin().read_to_end(&mut data).unwrap();
    let mut cursor = 0;
    let count = word(&data, &mut cursor);
    let mut stdout = std::io::BufWriter::new(std::io::stdout().lock());
    for _ in 0..count {
        let n = word(&data, &mut cursor);
        let cap = word(&data, &mut cursor);
        assert!(n <= 2097152 && cap <= 2097152);
        let input = data[cursor..cursor + n].to_vec();
        cursor += n;
        let mut output = vec![0x5a; cap];
        match model_decompress(&input, &mut output) {
            None => stdout.write_all(&(-1i32).to_le_bytes()).unwrap(),
            Some(r) => {
                assert!(r <= cap);
                stdout.write_all(&(r as i32).to_le_bytes()).unwrap();
                stdout.write_all(&output[..r]).unwrap();
            }
        }
    }
    assert_eq!(cursor, data.len());
    stdout.flush().unwrap();
}
