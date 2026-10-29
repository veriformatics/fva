//! Small-step, integer-valued interpreter for precisely the opcodes on the
//! successful, call-free paths of the shipped lz4_decompress function.
//! Reaching an unmodeled instruction, call, invalid stack or memory access
//! produces Unsupported, never a successful verification result.
use vstd::prelude::*;
mod format;
use format::*;

verus! {

pub enum Bin { Add, Sub, And, Shr, Eq, Ne, Gt, Ge, Lt, Le }
pub enum Op {
    Const(int), Get(int), Set(int), Tee(int), Binary(Bin), Eqz,
    Load(int, int), Store(int, int), Copy, Fill, Select,
    Jump(int), JumpIf(int), Return, Unsupported,
}
pub enum Status { Running, Returned(int), Unsupported }
pub struct Write { pub address: int, pub byte: int }
pub struct Init {
    pub src: int, pub dst: int, pub input: Seq<int>, pub cap: int, pub seed: int,
}
pub struct State {
    pub pc: int, pub locals: Seq<int>, pub stack: Seq<int>,
    pub writes: Seq<Write>, pub status: Status, pub safe: bool,
}

pub open spec fn init_ok(m: Init) -> bool {
    131072 <= m.src && m.src + m.input.len() <= 2097152
    && 131072 <= m.dst && 0 <= m.cap && m.dst + m.cap <= 2097152
    && (m.src + m.input.len() <= m.dst || m.dst + m.cap <= m.src)
    && 0 <= m.seed < 256
    && bytes(m.input)
}
pub open spec fn initial(m: Init) -> State {
    State { pc: 0, locals: seq![m.src, m.dst, m.input.len() as int, m.cap]
                + Seq::new(24, |i: int| 0),
            stack: Seq::empty(), writes: Seq::empty(),
            status: Status::Running, safe: true }
}
pub open spec fn inside(a: int, n: int, base: int, len: int) -> bool {
    0 <= n && base <= a && a + n <= base + len
}
pub open spec fn permitted(m: Init, a: int, n: int, write: bool) -> bool {
    // Zero-length bulk accesses neither read nor write any bytes.
    n == 0 || inside(a, n, m.dst, m.cap)
        || (!write && inside(a, n, m.src, m.input.len() as int))
}
pub open spec fn in_memory(a: int, n: int) -> bool {
    0 <= a && 0 <= n && a + n <= 2097152
}
pub open spec fn byte(m: Init, w: Seq<Write>, a: int) -> int
    decreases w.len(),
{
    if w.len() > 0 {
        let last = w.last();
        if last.address == a { last.byte } else { byte(m, w.drop_last(), a) }
    } else if m.src <= a < m.src + m.input.len() {
        m.input[a - m.src]
    } else if m.dst <= a < m.dst + m.cap {
        m.seed
    } else {
        // Successful theorems below prove safe, hence never depend on this
        // placeholder for memory outside the caller's two buffers.
        0
    }
}
pub open spec fn load(m: Init, w: Seq<Write>, a: int, n: nat) -> int
    decreases n,
{
    if n == 0 { 0 } else { byte(m, w, a) + 256 * load(m, w, a + 1, (n-1) as nat) }
}
pub open spec fn store(w: Seq<Write>, a: int, n: nat, v: int) -> Seq<Write>
    decreases n,
{
    if n == 0 { w } else {
        store(w.push(Write { address: a, byte: v % 256 }), a+1, (n-1) as nat, v / 256)
    }
}
pub open spec fn copy(m: Init, original: Seq<Write>, w: Seq<Write>,
                     dst: int, src: int, n: nat) -> Seq<Write>
    decreases n,
{
    if n == 0 { w } else {
        copy(m, original, w.push(Write { address: dst, byte: byte(m, original, src) }),
             dst+1, src+1, (n-1) as nat)
    }
}
pub open spec fn fill(w: Seq<Write>, dst: int, n: nat, v: int) -> Seq<Write>
    decreases n,
{
    if n == 0 { w } else {
        fill(w.push(Write { address: dst, byte: v % 256 }), dst+1, (n-1) as nat, v)
    }
}
pub open spec fn eval(b: Bin, a: int, c: int) -> int {
    match b {
        Bin::Add => (a + c) % 4294967296,
        Bin::Sub => (a + 4294967296 - c) % 4294967296,
        Bin::And => ((a as u32) & (c as u32)) as int,
        Bin::Shr => ((a as u32) >> ((c % 32) as u32)) as int,
        Bin::Eq => if a == c { 1 } else { 0 },
        Bin::Ne => if a != c { 1 } else { 0 },
        Bin::Gt => if a > c { 1 } else { 0 },
        Bin::Ge => if a >= c { 1 } else { 0 },
        Bin::Lt => if a < c { 1 } else { 0 },
        Bin::Le => if a <= c { 1 } else { 0 },
    }
}
pub open spec fn unsupported(s: State) -> State {
    State { status: Status::Unsupported, ..s }
}
pub open spec fn step(m: Init, s: State) -> State {
    let op = program(s.pc);
    let t = s.stack;
    let n = t.len() as int;
    let next = State { pc: s.pc + 1, ..s };
    match op {
        Op::Unsupported => unsupported(s),
        Op::Const(v) => State { stack: t.push(v), ..next },
        Op::Get(i) => if 0 <= i < s.locals.len() {
            State { stack: t.push(s.locals[i]), ..next }
        } else { unsupported(s) },
        Op::Set(i) => if n > 0 && 0 <= i < s.locals.len() {
            State { locals: s.locals.update(i, t[n-1]), stack: t.drop_last(), ..next }
        } else { unsupported(s) },
        Op::Tee(i) => if n > 0 && 0 <= i < s.locals.len() {
            State { locals: s.locals.update(i, t[n-1]), ..next }
        } else { unsupported(s) },
        Op::Binary(b) => if n >= 2 {
            State { stack: t.subrange(0,n-2).push(eval(b,t[n-2],t[n-1])), ..next }
        } else { unsupported(s) },
        Op::Eqz => if n > 0 {
            State { stack: t.drop_last().push(if t[n-1] == 0 { 1 } else { 0 }), ..next }
        } else { unsupported(s) },
        Op::Select => if n >= 3 {
            State { stack: t.subrange(0,n-3).push(if t[n-1] != 0 { t[n-3] } else { t[n-2] }), ..next }
        } else { unsupported(s) },
        Op::Jump(pc) => State { pc, stack: Seq::empty(), ..s },
        Op::JumpIf(pc) => if n > 0 {
            if t[n-1] != 0 { State { pc, stack: Seq::empty(), ..s } }
            else { State { stack: t.drop_last(), ..next } }
        } else { unsupported(s) },
        Op::Return => if n > 0 {
            State { status: Status::Returned(t[n-1]), ..s }
        } else { unsupported(s) },
        Op::Load(width, offset) => if n > 0 && 0 < width <= 8
            && in_memory(t[n-1] + offset, width) {
            State {
                stack: t.drop_last().push(load(m,s.writes,t[n-1]+offset,width as nat)),
                safe: s.safe && permitted(m,t[n-1]+offset,width,false), ..next
            }
        } else { unsupported(s) },
        Op::Store(width, offset) => if n >= 2 && 0 < width <= 8
            && in_memory(t[n-2] + offset, width) {
            State {
                stack: t.subrange(0,n-2),
                writes: store(s.writes,t[n-2]+offset,width as nat,t[n-1]),
                safe: s.safe && permitted(m,t[n-2]+offset,width,true), ..next
            }
        } else { unsupported(s) },
        Op::Copy => if n >= 3 && in_memory(t[n-3],t[n-1]) && in_memory(t[n-2],t[n-1]) {
            State {
                stack: t.subrange(0,n-3),
                writes: copy(m,s.writes,s.writes,t[n-3],t[n-2],t[n-1] as nat),
                safe: s.safe && permitted(m,t[n-3],t[n-1],true)
                             && permitted(m,t[n-2],t[n-1],false), ..next
            }
        } else { unsupported(s) },
        Op::Fill => if n >= 3 && in_memory(t[n-3],t[n-1]) {
            State {
                stack: t.subrange(0,n-3),
                writes: fill(s.writes,t[n-3],t[n-1] as nat,t[n-2]),
                safe: s.safe && permitted(m,t[n-3],t[n-1],true), ..next
            }
        } else { unsupported(s) },
    }
}
pub open spec fn run(m: Init, s: State, fuel: nat) -> State
    decreases fuel,
{
    if fuel == 0 { s }
    else { match s.status {
        Status::Running => run(m,step(m,s),(fuel-1) as nat),
        _ => s,
    } }
}
pub open spec fn read_output(m: Init, s: State, start: int, count: nat) -> Seq<int>
    decreases count,
{
    if count == 0 { seq![] } else {
        seq![byte(m,s.writes,m.dst+start)] + read_output(m,s,start+1,(count-1) as nat)
    }
}
pub open spec fn returned(s: State, r: int) -> bool {
    match s.status { Status::Returned(v) => v == r % 4294967296, _ => false }
}
}
include!("program.inc.rs");
verus! {
pub open spec fn test_input(input: Seq<int>, cap: int) -> Init {
    Init { src: 131072, dst: 262144, input, cap, seed: 165 }
}
}
fn main() {}

include!("cases.inc.rs");
verus! {
pub proof fn zero_length_input_all_placements(src: int, dst: int, cap: int, seed: int)
    requires init_ok(Init { src, dst, input: seq![], cap, seed }),
    ensures ({
        let m = Init { src, dst, input: seq![], cap, seed };
        let s = run(m,initial(m),20);
        s.safe && returned(s,-1) && s.writes.len() == 0
    }),
{
    assert(({
        let m = Init { src, dst, input: seq![], cap, seed };
        let s = run(m,initial(m),20);
        s.safe && returned(s,-1) && s.writes.len() == 0
    })) by(compute);
}
}
