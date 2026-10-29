use vstd::prelude::*;

verus! {
// No architecture size axiom: Verus checks usize arithmetic for either supported
// word size (32 or 64). In particular, this includes Wasm's 32-bit usize.
pub proof fn word_sizes()
    ensures usize::MAX == 4294967295 || usize::MAX == 18446744073709551615,
{}

// A model, NOT a verified translation of the Wasm. All sizes are bounded by the
// README's entire caller region, which is smaller than 2^21 bytes.
pub const LIMIT: usize = 2097152;

// Length extensions: consume 255 bytes until a terminating byte < 255.
pub open spec fn extension(s: Seq<u8>, p: int) -> Option<(nat, int)>
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() { None }
    else if s[p] < 255 { Some((s[p] as nat, p + 1)) }
    else {
        match extension(s, p + 1) {
            None => None,
            Some((v, q)) => Some((255 + v, q)),
        }
    }
}

pub open spec fn length(s: Seq<u8>, p: int, nibble: nat, base: nat)
    -> Option<(nat, int)>
{
    if nibble < 15 { Some((base + nibble, p)) }
    else {
        match extension(s, p) {
            None => None,
            Some((v, q)) => Some((base + 15 + v, q)),
        }
    }
}

// Parser independent of capacity or decoder fast/slow branches.
// Final sequence has no offset/match; its low token nibble is ignored.
#[derive(PartialEq, Eq)]
pub struct Piece {
    pub lit_start: usize,
    pub lit_len: usize,
    pub offset: usize,
    pub match_len: usize,
    pub next: usize,
    pub last: bool,
}

pub open spec fn parse(s: Seq<u8>, p: int) -> Option<Piece> {
    if p < 0 || p >= s.len() { None }
    else {
        match length(s, p + 1, (s[p] / 16) as nat, 0) {
            None => None,
            Some((ll, q)) => {
                if q + ll > s.len() { None }
                else if q + ll == s.len() {
                    Some(Piece { lit_start: q as usize, lit_len: ll as usize,
                        offset: 0, match_len: 0, next: s.len() as usize, last: true })
                } else if q + ll + 2 > s.len() { None }
                else {
                    let off = s[q + ll] as nat + 256 * s[q + ll + 1] as nat;
                    match length(s, q + ll + 2, (s[p] % 16) as nat, 4) {
                        None => None,
                        Some((ml, r)) => {
                            if off == 0 { None }
                            else { Some(Piece { lit_start: q as usize, lit_len: ll as usize,
                                offset: off as usize, match_len: ml as usize,
                                next: r as usize, last: false }) }
                        }
                    }
                }
            }
        }
    }
}

// Byte-at-a-time forward match expansion, including overlapping matches.
pub open spec fn repeat(h: Seq<u8>, off: nat, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 { h }
    else {
        let prev = repeat(h, off, (n - 1) as nat);
        prev.push(prev[prev.len() - off])
    }
}

pub proof fn repeat_len(h: Seq<u8>, off: nat, n: nat)
    ensures repeat(h, off, n).len() == h.len() + n,
    decreases n,
{
    if n > 0 { repeat_len(h, off, (n - 1) as nat); }
}

// Grammar/semantics of an accepted independent block: a nonempty sequence of
// Pieces consuming all source bytes, valid back references, and forward copies.
// Omits only the end-of-block restrictions explicitly relaxed by R3.
pub open spec fn decodes(s: Seq<u8>, p: int, h: Seq<u8>) -> Option<Seq<u8>>
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() { None }
    else {
        match parse(s, p) {
            None => None,
            Some(a) => {
                let h2 = h + s.subrange(a.lit_start as int, (a.lit_start + a.lit_len) as int);
                if a.last { Some(h2) }
                else if a.next <= p || a.next > s.len()
                    || a.offset == 0 || a.offset > h2.len() { None }
                else {
                    decodes(s, a.next as int, repeat(h2, a.offset as nat, a.match_len as nat))
                }
            }
        }
    }
}

fn read_ext(s: &Vec<u8>, p: usize) -> (r: Option<(usize, usize)>)
    requires s.len() <= LIMIT, p <= s.len(),
    ensures
        match r {
            None => extension(s@, p as int).is_none(),
            Some((v, q)) => extension(s@, p as int) == Some((v as nat, q as int))
                && p < q <= s.len() && v <= 255 * (q - p),
        },
    decreases s.len() - p,
{
    if p == s.len() { return None; }
    let b = s[p];
    if b < 255 { return Some((b as usize, p + 1)); }
    match read_ext(s, p + 1) {
        None => None,
        Some((v, q)) => {
            assert(v <= 255 * (s.len() - p - 1));
            Some((255 + v, q))
        }
    }
}

fn read_length(s: &Vec<u8>, p: usize, nibble: usize, base: usize)
    -> (r: Option<(usize, usize)>)
    requires s.len() <= LIMIT, p <= s.len(), nibble <= 15, base <= 4,
    ensures
        match r {
            None => length(s@, p as int, nibble as nat, base as nat).is_none(),
            Some((v, q)) => length(s@, p as int, nibble as nat, base as nat)
                == Some((v as nat, q as int))
                && p <= q <= s.len() && v <= 19 + 255 * (s.len() - p),
        },
{
    if nibble < 15 { return Some((base + nibble, p)); }
    match read_ext(s, p) {
        None => None,
        Some((v, q)) => Some((base + 15 + v, q)),
    }
}

fn parse_piece(s: &Vec<u8>, p: usize) -> (r: Option<Piece>)
    requires s.len() <= LIMIT, p < s.len(),
    ensures r == parse(s@, p as int),
        match r {
            None => true,
            Some(a) => p < a.lit_start <= s.len()
                && a.lit_start + a.lit_len <= s.len()
                && p < a.next <= s.len()
                && a.match_len <= 19 + 255 * s.len()
                && (a.last ==> a.next == s.len() && a.match_len == 0)
                && (!a.last ==> 1 <= a.offset <= 65535 && a.match_len >= 4),
        },
{
    let token = s[p];
    let (ll, q) = match read_length(s, p + 1, (token / 16) as usize, 0) {
        None => { return None; },
        Some(x) => x,
    };
    if ll > s.len() - q { return None; }
    let end = q + ll;
    if end == s.len() {
        return Some(Piece { lit_start: q, lit_len: ll, offset: 0,
            match_len: 0, next: end, last: true });
    }
    if s.len() - end < 2 { return None; }
    let off = s[end] as usize + 256 * s[end + 1] as usize;
    let (ml, r) = match read_length(s, end + 2, (token % 16) as usize, 4) {
        None => { return None; },
        Some(x) => x,
    };
    if off == 0 { return None; }
    Some(Piece { lit_start: q, lit_len: ll, offset: off,
        match_len: ml, next: r, last: false })
}

// SliceSink's literal copy. `wild` may exceed logical bytes consumed.
fn literals(s: &Vec<u8>, out: &mut Vec<u8>, p: usize, q: usize,
    logical: usize, wild: usize)
    requires p <= old(out).len(), q <= s.len(),
        logical <= wild, wild <= s.len() - q,
        wild <= old(out).len() - p,
    ensures final(out).len() == old(out).len(),
        final(out)@.subrange(0, (p + logical) as int)
            == old(out)@.subrange(0, p as int)
                + s@.subrange(q as int, (q + logical) as int),
        forall|j: int| 0 <= j < final(out).len() && (j < p || j >= p + wild)
            ==> final(out)@[j] == old(out)@[j],
{
    let ghost before = out@;
    let mut i = 0usize;
    while i < wild
        invariant out.len() == before.len(), p <= out.len(), q <= s.len(),
            logical <= wild, wild <= s.len() - q, wild <= out.len() - p,
            i <= wild,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[p + j] == s@[q + j],
            forall|j: int| 0 <= j < out.len() && (j < p || j >= p + i)
                ==> #[trigger] out@[j] == before[j],
        decreases wild - i,
    {
        out.set(p + i, s[q + i]);
        i += 1;
    }
    assert forall|j: int| 0 <= j < p + logical implies
        #[trigger] out@[j] == (before.subrange(0, p as int)
            + s@.subrange(q as int, (q + logical) as int))[j] by {
        if j >= p { assert(out@[p + (j - p)] == s@[q + (j - p)]); }
    }
    assert(out@.subrange(0, (p + logical) as int)
        =~= before.subrange(0, p as int) + s@.subrange(q as int, (q + logical) as int));
}

// Forward match expansion. Non-overlapping wild-copy optimization is treated
// separately below; this helper deliberately uses the LZ4 overlap semantics.
fn matches(out: &mut Vec<u8>, p: usize, off: usize, n: usize)
    requires 1 <= off <= p <= old(out).len(), n <= old(out).len() - p,
    ensures final(out).len() == old(out).len(),
        final(out)@.subrange(0, (p + n) as int)
            == repeat(old(out)@.subrange(0, p as int), off as nat, n as nat),
        forall|j: int| 0 <= j < final(out).len() && (j < p || j >= p + n)
            ==> final(out)@[j] == old(out)@[j],
{
    let ghost before = out@;
    let mut i = 0usize;
    while i < n
        invariant out.len() == before.len(), 1 <= off <= p <= out.len(),
            n <= out.len() - p, i <= n,
            out@.subrange(0, (p + i) as int)
                == repeat(before.subrange(0, p as int), off as nat, i as nat),
            forall|j: int| 0 <= j < out.len() && (j < p || j >= p + i)
                ==> #[trigger] out@[j] == before[j],
        decreases n - i,
    {
        let ghost prev = out@.subrange(0, (p + i) as int);
        let b = out[p + i - off];
        out.set(p + i, b);
        assert(out@.subrange(0, (p + i + 1) as int) =~= prev.push(b));
        i += 1;
    }
}

// Non-overlapping prefix of a snapshot copy equals forward LZ4 expansion,
// even when the wider physical copy overlaps the destination.
pub proof fn snapshot_repeat(h: Seq<u8>, off: nat, n: nat)
    requires 1 <= off <= h.len(), n <= off,
    ensures repeat(h, off, n)
        == h + h.subrange((h.len() - off) as int, (h.len() - off + n) as int),
    decreases n,
{
    if n > 0 {
        snapshot_repeat(h, off, (n - 1) as nat);
        let prev = repeat(h, off, (n - 1) as nat);
        assert(prev.len() - off < h.len());
        assert(prev[prev.len() - off] == h[h.len() - off + n - 1]);
        assert((h + h.subrange((h.len() - off) as int, (h.len() - off + n) as int))
            =~= prev.push(h[h.len() - off + n - 1]));
    } else {
        assert(h + h.subrange((h.len() - off) as int, (h.len() - off) as int) =~= h);
    }
}

// SliceSink::extend_from_within has memmove/snapshot semantics. Cloning is
// used here to express this directly, rather than reasoning about memcpy IR.
fn wild_match(out: &mut Vec<u8>, p: usize, off: usize, n: usize, wild: usize)
    requires 1 <= off <= p <= old(out).len(), n <= off, n <= wild,
        wild <= old(out).len() - p,
    ensures final(out).len() == old(out).len(),
        final(out)@.subrange(0, (p + n) as int)
            == repeat(old(out)@.subrange(0, p as int), off as nat, n as nat),
        forall|j: int| 0 <= j < final(out).len() && (j < p || j >= p + wild)
            ==> final(out)@[j] == old(out)@[j],
{
    let snapshot = out.clone();
    let mut i = 0usize;
    while i < wild
        invariant out.len() == snapshot.len(), 1 <= off <= p <= out.len(),
            n <= off, n <= wild, wild <= out.len() - p, i <= wild,
            forall|j: int| 0 <= j < i
                ==> #[trigger] out@[p + j] == snapshot@[p - off + j],
            forall|j: int| 0 <= j < out.len() && (j < p || j >= p + i)
                ==> #[trigger] out@[j] == snapshot@[j],
        decreases wild - i,
    {
        out.set(p + i, snapshot[p - off + i]);
        i += 1;
    }
    proof {
        let h = snapshot@.subrange(0, p as int);
        snapshot_repeat(h, off as nat, n as nat);
        assert forall|j: int| 0 <= j < p + n implies
            #[trigger] out@[j]
                == (h + h.subrange((p - off) as int, (p - off + n) as int))[j] by {
            if j >= p {
                assert(out@[p + (j - p)] == snapshot@[p - off + (j - p)]);
            }
        }
        assert(out@.subrange(0, (p + n) as int)
            =~= h + h.subrange((p - off) as int, (p - off + n) as int));
    }
}

// Executable decoder model with the source's successful-path wild copy sizes.
// Parsing is factored out, and errors may be detected earlier than in the source;
// it is not a verified translation of the source, stdlib, or Wasm.
fn decode_from(s: &Vec<u8>, out: &mut Vec<u8>, ip: usize, op: usize)
    -> (r: Option<usize>)
    requires s.len() <= LIMIT, out.len() <= LIMIT,
        ip <= s.len(), op <= old(out).len(),
    ensures final(out).len() == old(out).len(),
        match r {
            Some(n) => op <= n <= final(out).len()
                && decodes(s@, ip as int, old(out)@.subrange(0, op as int))
                    == Some(final(out)@.subrange(0, n as int)),
            None => match decodes(s@, ip as int, old(out)@.subrange(0, op as int)) {
                None => true,
                Some(content) => content.len() > final(out).len(),
            },
        },
        forall|j: int| 0 <= j < op ==> final(out)@[j] == old(out)@[j],
    decreases s.len() - ip,
{
    if ip == s.len() { return None; }
    let a = match parse_piece(s, ip) {
        None => { return None; },
        Some(a) => a,
    };
    let token = s[ip];
    let hot = token / 16 < 15 && token % 16 < 15
        && s.len() >= 18 && ip + 1 <= s.len() - 18
        && out.len() >= 34 && op < out.len() - 34;
    let ghost h = out@.subrange(0, op as int);
    let ghost h2 = h + s@.subrange(a.lit_start as int, (a.lit_start + a.lit_len) as int);
    if a.lit_len > out.len() - op {
        proof { too_long(s@, ip as int, h, out.len() as nat); }
        return None;
    }
    let literal_wild = if hot { 16 } else { a.lit_len };
    literals(s, out, op, a.lit_start, a.lit_len, literal_wild);
    let pos = op + a.lit_len;
    if a.last { return Some(pos); }
    if a.offset > pos { return None; }
    if a.match_len > out.len() - pos {
        proof { too_long(s@, ip as int, h, out.len() as nat); }
        return None;
    }
    if a.offset >= a.match_len {
        let wild = if hot { 18 } else if a.match_len <= 32 && out.len() - pos >= 32 { 32 }
            else if 33 <= a.match_len && a.match_len <= 64 && out.len() - pos >= 64 { 64 }
            else { a.match_len };
        wild_match(out, pos, a.offset, a.match_len, wild);
    } else {
        matches(out, pos, a.offset, a.match_len);
    }
    let end = pos + a.match_len;
    decode_from(s, out, a.next, end)
}

// Every successful parse monotonically extends the already decoded content.
pub proof fn output_grows(s: Seq<u8>, p: int, h: Seq<u8>)
    ensures match decodes(s, p, h) {
        Some(content) => content.len() >= h.len(),
        None => true,
    },
    decreases s.len() - p,
{
    if 0 <= p < s.len() {
        if let Some(a) = parse(s, p) {
            let h2 = h + s.subrange(a.lit_start as int, (a.lit_start + a.lit_len) as int);
            repeat_len(h2, a.offset as nat, a.match_len as nat);
            if !a.last && p < a.next <= s.len() && 1 <= a.offset <= h2.len() {
                output_grows(s, a.next as int, repeat(h2, a.offset as nat, a.match_len as nat));
            }
        }
    }
}

proof fn too_long(s: Seq<u8>, p: int, h: Seq<u8>, cap: nat)
    requires 0 <= p < s.len(),
        parse(s, p).is_some(),
        ({ let a = parse(s, p).unwrap();
           let h2 = h + s.subrange(a.lit_start as int, (a.lit_start + a.lit_len) as int);
           h2.len() > cap || (!a.last && h2.len() + a.match_len > cap) }),
    ensures match decodes(s, p, h) {
        None => true,
        Some(content) => content.len() > cap,
    },
{
    let a = parse(s, p).unwrap();
    let h2 = h + s.subrange(a.lit_start as int, (a.lit_start + a.lit_len) as int);
    repeat_len(h2, a.offset as nat, a.match_len as nat);
    if !a.last && p < a.next <= s.len() && 1 <= a.offset <= h2.len() {
        output_grows(s, a.next as int, repeat(h2, a.offset as nat, a.match_len as nat));
    }
}

// Combined model R2/R3: success iff there is a grammatical independent
// decoding that fits. The prefix is exactly that decoding; capacity unchanged.
pub fn decode(s: &Vec<u8>, out: &mut Vec<u8>) -> (r: Option<usize>)
    requires s.len() <= LIMIT, out.len() <= LIMIT,
    ensures final(out).len() == old(out).len(),
        match r {
            Some(n) => n <= final(out).len()
                && decodes(s@, 0, Seq::empty()) == Some(final(out)@.subrange(0, n as int)),
            None => match decodes(s@, 0, Seq::empty()) {
                None => true,
                Some(content) => content.len() > final(out).len(),
            },
        },
{
    decode_from(s, out, 0, 0)
}

// End restrictions are a separate predicate. On a literal-only block, fewer
// than five literals are permitted. Otherwise the final literals number >=5,
// and every match (thus the last match) starts >=12 bytes before content end.
pub open spec fn end_conditions(s: Seq<u8>, p: int, produced: nat, total: nat) -> bool
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() { false }
    else { match parse(s, p) {
        None => false,
        Some(a) => if a.last { p == 0 || a.lit_len >= 5 }
            else { p < a.next <= s.len()
                && produced + a.lit_len + 12 <= total
                && end_conditions(s, a.next as int,
                    (produced + a.lit_len + a.match_len) as nat, total) },
    } }
}

pub open spec fn valid_independent_block(s: Seq<u8>, content: Seq<u8>) -> bool {
    decodes(s, 0, Seq::empty()) == Some(content)
        && end_conditions(s, 0, 0, content.len())
}

// Exact R2 contract for the MODEL, expressed as an executable wrapper.
pub fn model_r2(s: &Vec<u8>, out: &mut Vec<u8>, Ghost(content): Ghost<Seq<u8>>)
    -> (r: Option<usize>)
    requires s.len() <= LIMIT, out.len() <= LIMIT,
        valid_independent_block(s@, content), content.len() <= old(out).len(),
    ensures final(out).len() == old(out).len(),
        r.is_some(), r.unwrap() == content.len(),
        final(out)@.subrange(0, r.unwrap() as int) == content,
{
    decode(s, out)
}

// Exact R3 contract for the MODEL. `decodes` includes the consumed source
// partition, nonzero backward offsets, and sequential match semantics.
pub fn model_r3(s: &Vec<u8>, out: &mut Vec<u8>) -> (r: Option<usize>)
    requires s.len() <= LIMIT, out.len() <= LIMIT,
    ensures final(out).len() == old(out).len(),
        r.is_some() ==> r.unwrap() <= final(out).len()
            && decodes(s@, 0, Seq::empty())
                == Some(final(out)@.subrange(0, r.unwrap() as int)),
{
    decode(s, out)
}

// Sanity checks of the specification, proved by evaluation inside Verus.
pub proof fn format_examples()
    ensures
        valid_independent_block(seq![0u8], Seq::empty()),
        valid_independent_block(seq![0x13u8, 97u8, 1u8, 0u8, 0x50u8,
            98u8, 99u8, 100u8, 101u8, 102u8],
            seq![97u8, 97u8, 97u8, 97u8, 97u8, 97u8, 97u8, 97u8,
                98u8, 99u8, 100u8, 101u8, 102u8]),
        decodes(seq![0u8, 0u8, 0u8, 0u8], 0, Seq::empty()).is_none(),
        decodes(seq![0x10u8, 97u8, 2u8, 0u8, 0u8], 0, Seq::empty()).is_none(),
        decodes(seq![0xf0u8, 255u8], 0, Seq::empty()).is_none(),
{
    assert(valid_independent_block(seq![0u8], Seq::empty())) by (compute);
    assert(valid_independent_block(seq![0x13u8, 97u8, 1u8, 0u8, 0x50u8,
        98u8, 99u8, 100u8, 101u8, 102u8],
        seq![97u8, 97u8, 97u8, 97u8, 97u8, 97u8, 97u8, 97u8,
            98u8, 99u8, 100u8, 101u8, 102u8])) by (compute);
    assert(decodes(seq![0u8, 0u8, 0u8, 0u8], 0, Seq::empty()).is_none()) by (compute);
    assert(decodes(seq![0x10u8, 97u8, 2u8, 0u8, 0u8], 0, Seq::empty()).is_none()) by (compute);
    assert(decodes(seq![0xf0u8, 255u8], 0, Seq::empty()).is_none()) by (compute);
}

fn main() {}
}
