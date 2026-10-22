import FVA.Impl.Exec.Ref

/-!
# Choice points of the reference stepper

NaN results, growth and host calls may have several successors under `Step`; trap propagation
has administrative choices that keep the store and end at the same trap. `uniqueStep` excludes
these cases, `runDet` runs while it holds (normalizing pending traps), and
`FVA.Proof.Exec.Det` proves every other executable step unique and `runDet`'s final states
outcomes of every execution (`runDet_must`).
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- The stepper's numeric result is the spec's only one: anything but a NaN float result
(conservative: a NaN bit pattern from `reinterpret` also counts as a choice). -/
def numUnique (i : Instr) (args : List Val) : Bool :=
  match numStep i args with
  | some (some (.f32 b)) => !Num.Impl.isNaN (ofBits f32fmt b)
  | some (some (.f64 b)) => !Num.Impl.isNaN (ofBits f64fmt b)
  | _ => true

/-- The redex `i` with operand stack `vs` (top first) is no choice point. -/
def instrUnique (i : Instr) (vs : List Val) : Bool :=
  match i, vs with
  | .funop .., a :: _ | .cvtop _, a :: _ => numUnique i [a]
  | .fbinop .., b :: a :: _ => numUnique i [a, b]
  | .memoryGrow, _ | .tableGrow _, _ => false
  | _, _ => true

mutual
/-- The next redex of `es` (as `seq` finds it) is no choice point of the spec. -/
def seqUnique (s : Store) (f : Frame) (vs : List Val) : List AInstr → Bool
  | [] => true
  | e :: rest => match toVal e with
    | some v => seqUnique s f (v :: vs) rest
    | none => atUnique s f vs e

/-- The redex at the non-value `e` (values `vs` before it, top first) is no choice point. -/
def atUnique (s : Store) (f : Frame) (vs : List Val) : AInstr → Bool
  | .label _ _ body => seqUnique s f [] body
  | .frame _ fi body => seqUnique s fi [] body
  | .invoke a => match s.funcs[a]? with
    | some (.host ..) => false
    | _ => true
  | .plain i => instrUnique i vs
  | .trap => false
  | _ => true
end

mutual
/-- A trap is the next redex, possibly inside labels and frames. -/
def seqTraps : List AInstr → Bool
  | [] => false
  | e :: rest => match toVal e with
    | some _ => seqTraps rest
    | none => atTrap e

/-- A non-value instruction has a pending trap. -/
def atTrap : AInstr → Bool
  | .trap => true
  | .label _ _ body | .frame _ _ body => seqTraps body
  | _ => false
end

/-- The next step of `c` is the spec's only one. -/
def uniqueStep (c : Config) : Bool := seqUnique c.store c.frame [] c.instrs

/-- Run deterministic steps, normalize pending traps, and stop at other choice points. -/
def runDet : Nat → Config → Option Config
  | 0, _ => none
  | n + 1, c =>
    bif seqTraps c.instrs then some ⟨c.store, c.frame, [.trap]⟩
    else bif uniqueStep c then
      match seq c.store c.frame [] c.instrs with
      | .step s f es => runDet n ⟨s, f, es⟩
      | .final => some c
      | _ => none
    else none

end FVA.Wasm.Exec.Ref
