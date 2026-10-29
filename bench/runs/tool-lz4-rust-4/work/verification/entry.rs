use vstd::prelude::*;
verus! {
// This constant is bound to the actual export body by check_entry.py.
// block void; local.get 2; br_if 0; i32.const -1; return; end
pub const PREFIX: [u8; 10] = [0x02, 0x40, 0x20, 0x02, 0x0d, 0x00, 0x41, 0x7f, 0x0f, 0x0b];

pub enum Control {
    Running { pc: int, stack: Seq<i32> },
    Returned { value: i32 },
    LeftPrefix,
    Unsupported,
}

pub struct State {
    pub control: Control,
    // Linear-memory event trace. Local accesses are not linear-memory accesses.
    pub reads: Seq<int>,
    pub writes: Seq<int>,
}

// A small-step semantics ONLY for the instruction subset in PREFIX.
// A taken br_if 0 exits the entry block and this fragment. An untaken br_if
// pops its condition. i32.const 0x7f is signed LEB128 -1.
pub open spec fn step(code: Seq<u8>, n: i32, st: State) -> State {
    match st.control {
        Control::Running { pc, stack } => {
            let control = if pc < 0 || pc >= code.len() { Control::Unsupported }
            else if code[pc] == 0x02 && pc + 1 < code.len() && code[pc + 1] == 0x40 {
                Control::Running { pc: pc + 2, stack }
            } else if code[pc] == 0x20 && pc + 1 < code.len() && code[pc + 1] == 2 {
                Control::Running { pc: pc + 2, stack: stack.push(n) }
            } else if code[pc] == 0x0d && pc + 1 < code.len() && code[pc + 1] == 0
                && stack.len() > 0 {
                if stack.last() != 0 { Control::LeftPrefix }
                else { Control::Running { pc: pc + 2, stack: stack.drop_last() } }
            } else if code[pc] == 0x41 && pc + 1 < code.len() && code[pc + 1] == 0x7f {
                Control::Running { pc: pc + 2, stack: stack.push(-1i32) }
            } else if code[pc] == 0x0f && stack.len() > 0 {
                Control::Returned { value: stack.last() }
            } else { Control::Unsupported };
            State { control, reads: st.reads, writes: st.writes }
        },
        _ => st,
    }
}

pub open spec fn execute(code: Seq<u8>, n: i32, fuel: nat) -> State
    decreases fuel,
{
    if fuel == 0 {
        State { control: Control::Running { pc: 0, stack: Seq::empty() },
            reads: Seq::empty(), writes: Seq::empty() }
    } else { step(code, n, execute(code, n, (fuel - 1) as nat)) }
}

// Actual entry-fragment result for all calls whose third argument is zero.
// Other function arguments and the contents of linear memory are irrelevant.
pub proof fn entry_n_zero()
    ensures execute(PREFIX@, 0, 5).control == (Control::Returned { value: -1i32 }),
        execute(PREFIX@, 0, 5).reads == Seq::<int>::empty(),
        execute(PREFIX@, 0, 5).writes == Seq::<int>::empty(),
{
    assert(execute(PREFIX@, 0, 5).control == (Control::Returned { value: -1i32 })) by (compute);
    assert(execute(PREFIX@, 0, 5).reads == Seq::<int>::empty()) by (compute);
    assert(execute(PREFIX@, 0, 5).writes == Seq::<int>::empty()) by (compute);
}
fn main() {}
}
