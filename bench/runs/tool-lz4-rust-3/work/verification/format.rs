use vstd::prelude::*;

verus! {

// Independent mathematical grammar. All lengths and addresses here are integers.
pub open spec fn extension(s: Seq<u8>, p: int, q: int, n: int) -> bool {
    0 <= p < q <= s.len()
    && s[q - 1] < 255
    && (forall|i: int| p <= i < q - 1 ==> s[i] == 255)
    && n == 255 * (q - p - 1) + s[q - 1] as int
}

pub open spec fn field(s: Seq<u8>, p: int, q: int, nibble: int, n: int) -> bool {
    0 <= p <= s.len() && 0 <= nibble <= 15
    && if nibble < 15 { q == p && n == nibble }
       else { extension(s, p, q, n - 15) }
}

pub open spec fn read_extension(s: Seq<u8>, p: int) -> Option<(int, int)>
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() { None }
    else if s[p] < 255 { Some((p + 1, s[p] as int)) }
    else {
        match read_extension(s, p + 1) {
            None => None,
            Some((q, n)) => Some((q, n + 255)),
        }
    }
}

pub proof fn extension_sound(s: Seq<u8>, p: int)
    ensures match read_extension(s, p) {
        None => true,
        Some((q, n)) => extension(s, p, q, n),
    },
    decreases s.len() - p,
{
    if 0 <= p < s.len() && s[p] == 255 {
        extension_sound(s, p + 1);
        if let Some((q, n)) = read_extension(s, p + 1) {
            assert forall|i: int| p <= i < q - 1 implies s[i] == 255 by {
                if i != p { assert(p + 1 <= i); }
            }
        }
    }
}

pub proof fn extension_complete(s: Seq<u8>, p: int, q: int, n: int)
    requires extension(s, p, q, n),
    ensures read_extension(s, p) == Some((q, n)),
    decreases q - p,
{
    if p + 1 < q {
        assert(s[p] == 255);
        assert(extension(s, p + 1, q, n - 255));
        extension_complete(s, p + 1, q, n - 255);
    }
}

pub open spec fn read_field(s: Seq<u8>, p: int, nibble: int) -> Option<(int, int)> {
    if p < 0 || p > s.len() || nibble < 0 || nibble > 15 { None }
    else if nibble < 15 { Some((p, nibble)) }
    else {
        match read_extension(s, p) {
            None => None,
            Some((q, n)) => Some((q, n + 15)),
        }
    }
}

pub proof fn field_sound(s: Seq<u8>, p: int, nibble: int)
    ensures match read_field(s, p, nibble) {
        None => true,
        Some((q, n)) => field(s, p, q, nibble, n),
    },
{
    extension_sound(s, p);
}

pub proof fn field_complete(s: Seq<u8>, p: int, q: int, nibble: int, n: int)
    requires field(s, p, q, nibble, n),
    ensures read_field(s, p, nibble) == Some((q, n)),
{
    if nibble == 15 { extension_complete(s, p, q, n - 15); }
}

pub proof fn field_bounds(s: Seq<u8>, p: int, q: int, nibble: int, n: int)
    requires field(s, p, q, nibble, n),
    ensures p <= q <= s.len(), 0 <= n <= 15 + 255 * (q - p),
{}

pub struct Piece {
    pub next: int,
    pub lit: int,
    pub literals: int,
    pub offset: int,
    pub matches: int,
    pub last: bool,
}

// A sequence in the block grammar, with positions serving as a parsing witness.
// End-of-block restrictions are deliberately omitted, as allowed in R3.
pub open spec fn sequence(s: Seq<u8>, ip: int, produced: int, x: Piece) -> bool {
    let end = x.lit + x.literals;
    0 <= ip < s.len() && 0 <= produced
    && field(s, ip + 1, x.lit, s[ip] as int / 16, x.literals)
    && end <= s.len()
    && if x.last {
        end == s.len() && x.next == s.len() && x.offset == 0 && x.matches == 0
    } else {
        end + 2 <= s.len()
        && x.offset == s[end] as int + 256 * s[end + 1] as int
        && 1 <= x.offset <= produced + x.literals
        && field(s, end + 2, x.next, s[ip] as int % 16, x.matches - 4)
    }
}

// A reference parser; not a translation of the shipped Rust or WebAssembly.
pub open spec fn parse_sequence(s: Seq<u8>, ip: int, produced: int) -> Option<Piece> {
    if ip < 0 || ip >= s.len() || produced < 0 { None }
    else {
        match read_field(s, ip + 1, s[ip] as int / 16) {
            None => None,
            Some((lp, ll)) => {
                let end = lp + ll;
                if end > s.len() { None }
                else if end == s.len() {
                    Some(Piece { next: end, lit: lp, literals: ll,
                                 offset: 0, matches: 0, last: true })
                } else if end + 2 > s.len() { None }
                else {
                    let off = s[end] as int + 256 * s[end + 1] as int;
                    if off == 0 || off > produced + ll { None }
                    else {
                        match read_field(s, end + 2, s[ip] as int % 16) {
                            None => None,
                            Some((next, ml)) => Some(Piece {
                                next, lit: lp, literals: ll,
                                offset: off, matches: ml + 4, last: false,
                            }),
                        }
                    }
                }
            }
        }
    }
}

pub proof fn sequence_sound(s: Seq<u8>, ip: int, produced: int)
    ensures match parse_sequence(s, ip, produced) {
        None => true,
        Some(x) => sequence(s, ip, produced, x),
    },
{
    if 0 <= ip < s.len() && produced >= 0 {
        field_sound(s, ip + 1, s[ip] as int / 16);
        if let Some((lp, ll)) = read_field(s, ip + 1, s[ip] as int / 16) {
            field_bounds(s, ip + 1, lp, s[ip] as int / 16, ll);
            if lp + ll + 2 <= s.len() {
                field_sound(s, lp + ll + 2, s[ip] as int % 16);
            }
        }
    }
}

pub proof fn sequence_complete(s: Seq<u8>, ip: int, produced: int, x: Piece)
    requires sequence(s, ip, produced, x),
    ensures parse_sequence(s, ip, produced) == Some(x),
{
    field_complete(s, ip + 1, x.lit, s[ip] as int / 16, x.literals);
    field_bounds(s, ip + 1, x.lit, s[ip] as int / 16, x.literals);
    if !x.last {
        field_complete(s, x.lit + x.literals + 2, x.next,
                       s[ip] as int % 16, x.matches - 4);
    }
}

pub proof fn sequence_bounds(s: Seq<u8>, ip: int, produced: int, x: Piece)
    requires sequence(s, ip, produced, x),
    ensures ip < x.next <= s.len(),
            0 <= x.lit <= x.lit + x.literals <= s.len(),
            0 <= x.matches,
            !x.last ==> 1 <= x.offset <= produced + x.literals,
            !x.last ==> x.offset <= 65535 && x.matches >= 4,
{
    field_bounds(s, ip + 1, x.lit, s[ip] as int / 16, x.literals);
    if !x.last {
        field_bounds(s, x.lit + x.literals + 2, x.next,
                     s[ip] as int % 16, x.matches - 4);
    }
}

// Byte-by-byte forward copying gives overlapping LZ4 matches their meaning.
pub open spec fn expand(out: Seq<u8>, off: int, n: int) -> Seq<u8>
    decreases n,
{
    if n <= 0 { out }
    else { expand(out.push(out[out.len() - off]), off, n - 1) }
}

pub proof fn expand_correct(out: Seq<u8>, off: int, n: int)
    requires 1 <= off <= out.len(), 0 <= n,
    ensures expand(out, off, n).len() == out.len() + n,
        expand(out, off, n).subrange(0, out.len() as int) == out,
        forall|i: int| out.len() <= i < out.len() + n ==>
            #[trigger] expand(out, off, n)[i] == expand(out, off, n)[i - off],
    decreases n,
{
    if n > 0 {
        let one = out.push(out[out.len() - off]);
        expand_correct(one, off, n - 1);
        let result = expand(out, off, n);
        assert(result.subrange(0, out.len() as int) =~= out);
        assert forall|i: int| out.len() <= i < out.len() + n implies
            #[trigger] result[i] == result[i - off] by {
            if i == out.len() {
                assert(result[i] == one[i]);
                assert(result[i - off] == one[i - off]);
            }
        }
    } else {
        assert(out.subrange(0, out.len() as int) =~= out);
    }
}

pub open spec fn apply(s: Seq<u8>, out: Seq<u8>, x: Piece) -> Seq<u8> {
    let lits = out + s.subrange(x.lit, x.lit + x.literals);
    if x.last { lits } else { expand(lits, x.offset, x.matches) }
}

pub proof fn apply_length(s: Seq<u8>, ip: int, out: Seq<u8>, x: Piece)
    requires sequence(s, ip, out.len() as int, x),
    ensures apply(s, out, x).len() == out.len() + x.literals + x.matches,
            out.len() <= apply(s, out, x).len(),
{
    sequence_bounds(s, ip, out.len() as int, x);
    if !x.last {
        expand_correct(out + s.subrange(x.lit, x.lit + x.literals), x.offset, x.matches);
    }
}

pub open spec fn trace(s: Seq<u8>, ip: int, out: Seq<u8>, xs: Seq<Piece>) -> bool
    decreases xs.len(),
{
    xs.len() > 0 && sequence(s, ip, out.len() as int, xs[0])
    && if xs[0].last { xs.len() == 1 }
       else { trace(s, xs[0].next, apply(s, out, xs[0]), xs.drop_first()) }
}

pub open spec fn trace_output(s: Seq<u8>, out: Seq<u8>, xs: Seq<Piece>) -> Seq<u8>
    decreases xs.len(),
{
    if xs.len() == 0 { out }
    else { trace_output(s, apply(s, out, xs[0]), xs.drop_first()) }
}

pub proof fn trace_bounds(s: Seq<u8>, ip: int, out: Seq<u8>, xs: Seq<Piece>)
    requires trace(s, ip, out, xs),
    ensures out.len() <= trace_output(s, out, xs).len(),
            xs.len() <= s.len() - ip,
    decreases xs.len(),
{
    reveal_with_fuel(trace_output, 2);
    sequence_bounds(s, ip, out.len() as int, xs[0]);
    apply_length(s, ip, out, xs[0]);
    if !xs[0].last {
        trace_bounds(s, xs[0].next, apply(s, out, xs[0]), xs.drop_first());
    } else {
        assert(xs.drop_first().len() == 0);
    }
}

pub struct Decoded {
    pub out: Seq<u8>,
    pub pieces: Seq<Piece>,
}

pub open spec fn decode(s: Seq<u8>, ip: int, out: Seq<u8>, cap: int, fuel: nat)
    -> Option<Decoded>
    decreases fuel,
{
    if fuel == 0 { None }
    else {
        match parse_sequence(s, ip, out.len() as int) {
            None => None,
            Some(x) => {
                let next_out = apply(s, out, x);
                if next_out.len() > cap { None }
                else if x.last { Some(Decoded { out: next_out, pieces: seq![x] }) }
                else {
                    match decode(s, x.next, next_out, cap, (fuel - 1) as nat) {
                        None => None,
                        Some(d) => Some(Decoded { out: d.out, pieces: seq![x] + d.pieces }),
                    }
                }
            }
        }
    }
}

pub proof fn decode_sound(s: Seq<u8>, ip: int, out: Seq<u8>, cap: int, fuel: nat)
    ensures match decode(s, ip, out, cap, fuel) {
        None => true,
        Some(d) => d.out.len() <= cap && trace(s, ip, out, d.pieces)
                   && d.out == trace_output(s, out, d.pieces),
    },
    decreases fuel,
{
    reveal_with_fuel(trace_output, 2);
    reveal_with_fuel(trace, 2);
    if fuel > 0 {
        sequence_sound(s, ip, out.len() as int);
        if let Some(x) = parse_sequence(s, ip, out.len() as int) {
            let next_out = apply(s, out, x);
            if next_out.len() <= cap {
                if x.last {
                    assert(seq![x].drop_first() =~= Seq::<Piece>::empty());
                } else {
                    decode_sound(s, x.next, next_out, cap, (fuel - 1) as nat);
                    if let Some(d) = decode(s, x.next, next_out, cap, (fuel - 1) as nat) {
                        assert((seq![x] + d.pieces).drop_first() =~= d.pieces);
                    }
                }
            }
        }
    }
}

pub proof fn decode_complete(s: Seq<u8>, ip: int, out: Seq<u8>, cap: int,
                             fuel: nat, xs: Seq<Piece>)
    requires trace(s, ip, out, xs), xs.len() <= fuel,
             trace_output(s, out, xs).len() <= cap,
    ensures decode(s, ip, out, cap, fuel) == Some(Decoded {
        out: trace_output(s, out, xs), pieces: xs,
    }),
    decreases xs.len(),
{
    let x = xs[0];
    let next_out = apply(s, out, x);
    sequence_complete(s, ip, out.len() as int, x);
    apply_length(s, ip, out, x);
    if x.last {
        assert(xs =~= seq![x]);
        assert(xs.drop_first().len() == 0);
    } else {
        trace_bounds(s, x.next, next_out, xs.drop_first());
        decode_complete(s, x.next, next_out, cap, (fuel - 1) as nat, xs.drop_first());
        assert(seq![x] + xs.drop_first() =~= xs);
    }
}

pub proof fn model_r2(s: Seq<u8>, cap: int, xs: Seq<Piece>)
    requires trace(s, 0, Seq::empty(), xs),
             trace_output(s, Seq::empty(), xs).len() <= cap,
    ensures decode(s, 0, Seq::empty(), cap, s.len() + 1) == Some(Decoded {
        out: trace_output(s, Seq::empty(), xs), pieces: xs,
    }),
{
    trace_bounds(s, 0, Seq::empty(), xs);
    decode_complete(s, 0, Seq::empty(), cap, s.len() + 1, xs);
}

pub proof fn model_r3(s: Seq<u8>, cap: int)
    ensures match decode(s, 0, Seq::empty(), cap, s.len() + 1) {
        None => true,
        Some(d) => 0 <= d.out.len() <= cap && trace(s, 0, Seq::empty(), d.pieces)
                   && d.out == trace_output(s, Seq::empty(), d.pieces),
    },
{
    decode_sound(s, 0, Seq::empty(), cap, s.len() + 1);
}

// Relevant arithmetic for wasm32 and the widened copies in the source.
pub proof fn length_accumulator_fits(consumed: int, base: int)
    requires 0 <= consumed <= 2097152 - 131072, 0 <= base <= 19,
    ensures 0 <= 255 * consumed + base < 4294967296,
{}

pub proof fn widened_copy_bounds(cap: int, pos: int, off: int, width: int)
    requires 0 <= pos, 1 <= off <= pos, 0 <= width, pos + width <= cap,
    ensures 0 <= pos - off, pos - off + width <= cap,
            0 <= pos, pos + width <= cap,
{}

pub proof fn fast_path_bounds(n: int, cap: int, ip: int, op: int, literals: int)
    requires 0 <= ip, ip + 1 <= n - 18,
             0 <= op, op < cap - 34, 0 <= literals <= 14,
    ensures ip + 1 + 16 <= n,
            ip + 1 + literals + 2 <= n,
            op + 16 <= cap,
            op + literals + 18 <= cap,
{}

pub proof fn placed_access(base: int, len: int, index: int, width: int)
    requires 131072 <= base, 0 <= len, base + len <= 2097152,
             0 <= index, 0 <= width, index + width <= len,
    ensures 131072 <= base + index,
            base + index + width <= 2097152,
            base + index + width < 4294967296,
{}

pub open spec fn match_source(produced: int, x: Piece, i: int) -> int {
    produced + x.literals + i - x.offset
}

pub proof fn successful_sequence_access_bounds(s: Seq<u8>, ip: int,
                                               produced: int, cap: int, x: Piece)
    requires sequence(s, ip, produced, x), produced <= cap,
             produced + x.literals + x.matches <= cap,
    ensures 0 <= ip < s.len(),
            ip + 1 <= x.lit <= x.lit + x.literals <= s.len(),
            produced <= produced + x.literals <= cap,
            !x.last ==> x.lit + x.literals + 2 <= x.next <= s.len(),
            forall|i: int| 0 <= i < x.matches ==>
                0 <= #[trigger] match_source(produced, x, i)
                   < produced + x.literals + i < cap,
{
    sequence_bounds(s, ip, produced, x);
    field_bounds(s, ip + 1, x.lit, s[ip] as int / 16, x.literals);
    if !x.last {
        field_bounds(s, x.lit + x.literals + 2, x.next,
                     s[ip] as int % 16, x.matches - 4);
    }
}

// A non-vacuous grammar witness satisfying the strict end conditions too:
// one literal 'a', a 7-byte match at offset 1, then five final literals.
// The last match starts at position 1, 12 bytes before the decoded end (13).
pub proof fn example_independent_block()
    ensures {
        let s = seq![0x13u8, 97u8, 1u8, 0u8, 0x50u8, 98u8, 99u8, 100u8, 101u8, 102u8];
        let xs = seq![
            Piece { next: 4, lit: 1, literals: 1, offset: 1, matches: 7, last: false },
            Piece { next: 10, lit: 5, literals: 5, offset: 0, matches: 0, last: true },
        ];
        trace(s, 0, Seq::empty(), xs)
        && trace_output(s, Seq::empty(), xs)
           == seq![97u8, 97u8, 97u8, 97u8, 97u8, 97u8, 97u8, 97u8,
                   98u8, 99u8, 100u8, 101u8, 102u8]
    },
{
    reveal_with_fuel(trace, 3);
    reveal_with_fuel(trace_output, 3);
    reveal_with_fuel(expand, 8);
}

} // verus!

fn main() {}
