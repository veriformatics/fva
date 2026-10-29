//! Independent certificate definitions from lz4_Block_format.md.
//! No production Rust decoder is called by this specification.
use vstd::prelude::*;
verus! {
pub struct Piece {
    pub token: int,
    pub literal_extension: Seq<int>,
    pub literals: Seq<int>,
    pub offset: int,
    pub match_extension: Seq<int>,
    pub match_length: nat,
}
pub open spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { s.first() + sum(s.drop_first()) }
}
pub open spec fn bytes(s: Seq<int>) -> bool
    decreases s.len(),
{
    if s.len() == 0 { true } else { 0 <= s.first() < 256 && bytes(s.drop_first()) }
}
pub open spec fn extension(s: Seq<int>) -> bool
    decreases s.len(),
{
    if s.len() == 0 { false }
    else if s.len() == 1 { 0 <= s.first() < 255 }
    else { s.first() == 255 && extension(s.drop_first()) }
}
pub open spec fn length_field(base: int, extra: Seq<int>, length: int) -> bool {
    0 <= base <= 15 && if base < 15 { extra.len() == 0 && length == base }
    else { extension(extra) && length == 15 + sum(extra) }
}
pub open spec fn piece_ok(p: Piece, last: bool, produced: int) -> bool {
    0 <= p.token < 256 && bytes(p.literals)
    && length_field(p.token / 16, p.literal_extension, p.literals.len() as int)
    && if last {
        p.offset == 0 && p.match_length == 0 && p.match_extension.len() == 0
    } else {
        1 <= p.offset <= 65535 && p.offset <= produced + p.literals.len()
        && p.match_length >= 4
        && length_field(p.token % 16, p.match_extension, p.match_length - 4)
    }
}
pub open spec fn encode_piece(p: Piece, last: bool) -> Seq<int> {
    seq![p.token] + p.literal_extension + p.literals
    + if last { seq![] } else {
        seq![p.offset % 256, p.offset / 256] + p.match_extension
    }
}
pub open spec fn repeat_match(prefix: Seq<int>, offset: int, count: nat) -> Seq<int>
    decreases count,
{
    if count == 0 { prefix } else {
        let next = prefix.push(prefix[prefix.len() - offset]);
        repeat_match(next, offset, (count-1) as nat)
    }
}
pub open spec fn apply(prefix: Seq<int>, p: Piece, last: bool) -> Seq<int> {
    let lit = prefix + p.literals;
    if last { lit } else { repeat_match(lit, p.offset, p.match_length) }
}
pub open spec fn encoding(ps: Seq<Piece>) -> Seq<int>
    decreases ps.len(),
{
    if ps.len() == 0 { seq![] } else {
        encode_piece(ps.first(),ps.len()==1) + encoding(ps.drop_first())
    }
}
pub open spec fn decoded(ps: Seq<Piece>, prefix: Seq<int>) -> Seq<int>
    decreases ps.len(),
{
    if ps.len() == 0 { prefix } else {
        decoded(ps.drop_first(),apply(prefix,ps.first(),ps.len()==1))
    }
}
pub open spec fn grammar(ps: Seq<Piece>, prefix: Seq<int>) -> bool
    decreases ps.len(),
{
    if ps.len() == 0 { true } else {
        piece_ok(ps.first(),ps.len()==1,prefix.len() as int)
        && grammar(ps.drop_first(),apply(prefix,ps.first(),ps.len()==1))
    }
}
pub open spec fn before_last_match(ps: Seq<Piece>, prefix: Seq<int>) -> int
    decreases ps.len(),
{
    if ps.len() < 2 { 0 }
    else if ps.len() == 2 { (prefix.len() + ps.first().literals.len()) as int }
    else { before_last_match(ps.drop_first(),apply(prefix,ps.first(),false)) }
}
pub open spec fn valid_block(ps: Seq<Piece>) -> bool {
    ps.len() > 0 && grammar(ps, seq![])
    && (ps.len() == 1 || (ps.last().literals.len() >= 5
        && decoded(ps,seq![]).len() - before_last_match(ps,seq![]) >= 12))
}

// General bounds: for buffers allowed by README, no extension length can
// approach a 32-bit wraparound. These lemmas do not assert decoder refinement.
pub proof fn sum_bound(s: Seq<int>)
    requires bytes(s),
    ensures 0 <= sum(s) <= 255 * s.len(),
    decreases s.len(),
{
    if s.len() > 0 { sum_bound(s.drop_first()); }
}
pub proof fn length_no_u32_overflow(s: Seq<int>, base: int)
    requires bytes(s), s.len() <= 1966080, 0 <= base <= 19,
    ensures 0 <= base + sum(s) <= 501350419,
            base + sum(s) < 4294967296,
{
    sum_bound(s);
}

// Mathematical obligation for the hot loop's 16-byte literal copy and
// 18-byte match copy. Sizes are integers here, not wrapping machine words.
pub proof fn hot_copy_bounds(n: int, cap: int, ip: int, op: int,
                             lit: int, offset: int, ml: int)
    requires
        0 <= n <= 1966080, 0 <= cap <= 1966080,
        0 <= ip, ip + 1 <= if n >= 18 { n-18 } else { 0 },
        0 <= op, op < if cap >= 34 { cap-34 } else { 0 },
        0 <= lit <= 14, 4 <= ml <= 18,
        1 <= offset <= op + lit,
    ensures
        ip + 1 + 16 <= n,
        ip + 1 + lit + 2 <= n,
        op + 16 <= cap,
        op + lit + ml <= cap,
        0 <= op + lit - offset,
        op + lit + 18 <= cap,
        op + lit - offset + 18 <= cap,
{}

// Independent, overlapping LZ4 match semantics preserve the existing prefix.
pub proof fn repeat_match_preserves_prefix(prefix: Seq<int>, offset: int, count: nat)
    requires 1 <= offset <= prefix.len(),
    ensures
        repeat_match(prefix,offset,count).len() == prefix.len() + count,
        forall|i: int| 0 <= i < prefix.len() ==>
            #[trigger] repeat_match(prefix,offset,count)[i] == prefix[i],
    decreases count,
{
    if count > 0 {
        let next = prefix.push(prefix[prefix.len()-offset]);
        repeat_match_preserves_prefix(next,offset,(count-1) as nat);
    }
}

// A snapshot copy gives the correct match bytes when length <= offset.
// Thus extra bytes in a wild copy do not change the meaningful prefix.
pub proof fn snapshot_match_byte(prefix: Seq<int>, offset: int, count: nat, i: int)
    requires 1 <= offset <= prefix.len(), count <= offset, 0 <= i < count,
    ensures
        repeat_match(prefix,offset,count)[prefix.len()+i]
            == prefix[prefix.len()-offset+i],
    decreases count,
{
    let next = prefix.push(prefix[prefix.len()-offset]);
    assert(repeat_match(prefix,offset,count) == repeat_match(next,offset,(count-1) as nat));
    if i == 0 {
        repeat_match_preserves_prefix(next,offset,(count-1) as nat);
        assert(next[prefix.len() as int] == prefix[prefix.len()-offset]);
    } else {
        snapshot_match_byte(next,offset,(count-1) as nat,i-1);
        assert(next.len()+i-1 == prefix.len()+i);
        assert(next.len()-offset+i-1 == prefix.len()-offset+i);
        assert(0 <= prefix.len()-offset+i < prefix.len());
    }
}
}
