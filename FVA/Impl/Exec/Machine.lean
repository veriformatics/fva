import FVA.Impl.Exec.Ref
import FVA.Impl.Exec.Chunks

/-!
# Optimized machine (verified implementation)

Operand stack (top first) + current code + control stack (the zipper: innermost first) over a
store whose memories are chunk tries. One step = one instruction or one control exit; a plain
instruction outside control and memory delegates to the reference stepper's `Ref.instrStep` on
the abstract store, so both read the same rule. `abs` rebuilds the spec configuration the
stepper runs on; `FVA.Proof.Exec.Machine` proves every step is `k` stepper steps between the
abstractions (`docs/contracts/U26-machine.md`).
-/

namespace FVA.Wasm.Exec.Machine

open FVA.Wasm FVA.Wasm.Exec

/-- The store with chunk-trie memories; `base.mems` is never read. -/
structure MStore where
  /-- Every store part but memories. -/
  base : Store
  /-- Memories. -/
  mems : List MMem

/-- The spec store. -/
def MStore.abs (s : MStore) : Store := { s.base with mems := s.mems.map MMem.abs }

/-- A suspended context: a block's label or a caller's frame. -/
inductive Ctl where
  /-- `label_n{cont}` with the operands below it and the instructions after it. -/
  | label (n : Nat) (cont : List Instr) (saved : List Val) (rest : List AInstr)
  /-- `frame_n{caller}`: the caller's frame, operands below the call and instructions after. -/
  | frame (n : Nat) (caller : Frame) (saved : List Val) (rest : List AInstr)

/-- A machine state. -/
structure MState where
  /-- Store. -/
  store : MStore
  /-- The running function's frame. -/
  frame : Frame
  /-- Operands of the innermost block, top first. -/
  stack : List Val
  /-- The rest of the innermost block. -/
  code : List AInstr
  /-- Suspended contexts, innermost first. -/
  ctl : List Ctl

/-- Wrap the innermost instructions `es` (running in frame `f`) in the control stack: the
outermost frame and instruction sequence. -/
def wrap : List Ctl → Frame → List AInstr → Frame × List AInstr
  | [], f, es => (f, es)
  | .label n cont saved rest :: ctl, f, es =>
    wrap ctl f (vals saved.reverse ++ [.label n cont es] ++ rest)
  | .frame n caller saved rest :: ctl, f, es =>
    wrap ctl caller (vals saved.reverse ++ [.frame n f es] ++ rest)

/-- The spec configuration a machine state denotes. -/
def MState.abs (m : MState) : Config :=
  let (f, es) := wrap m.ctl m.frame (vals m.stack.reverse ++ m.code)
  ⟨m.store.abs, f, es⟩

/-- Pop operands and labels for `br l`: the operands, code and control after the branch. -/
def brPop : Nat → List Val → List Ctl → Option (List Val × List AInstr × List Ctl)
  | 0, stk, .label n cont saved rest :: ctl =>
    bif Nat.blt stk.length n then none else some (stk.take n ++ saved, cont.map .plain ++ rest, ctl)
  | l + 1, stk, .label .. :: ctl => brPop l stk ctl
  | _, _, _ => none

/-- Pop operands, labels and the innermost frame for `return`. -/
def retPop : List Val → List Ctl → Option (Frame × List Val × List AInstr × List Ctl)
  | stk, .label .. :: ctl => retPop stk ctl
  | stk, .frame n caller saved rest :: ctl =>
    bif Nat.blt stk.length n then none else some (caller, stk.take n ++ saved, rest, ctl)
  | _, [] => none

/-- The outermost frame (the configuration's frame). -/
def outerFrame : List Ctl → Frame → Frame
  | [], f => f
  | .label .. :: ctl, f => outerFrame ctl f
  | .frame _ caller _ _ :: ctl, _ => outerFrame ctl caller

namespace MState

/-- Replace memory `a`. -/
def setMem (m : MState) (a : Nat) (mm : MMem) : MState :=
  { m with store := { m.store with mems := m.store.mems.set a mm } }

/-- The frame's memory 0 with its address. -/
def mem0 (m : MState) : Option (Nat × MMem) :=
  match m.frame.inst.mems[0]? with
  | some a => (m.store.mems[a]?).map (a, ·)
  | none => none

/-- Continue with operands `stk` and instructions `out` before `rest`. -/
def cont (m : MState) (stk : List Val) (out rest : List AInstr) : MState :=
  { m with stack := stk, code := out ++ rest }

/-- Enter a block: its label, its parameters as the new operands. -/
def enter (m : MState) (n : Nat) (cont : List Instr) (k : Nat) (body : List Instr)
    (rest : List AInstr) : Option MState :=
  bif Nat.blt m.stack.length k then none
  else some { m with stack := m.stack.take k, code := body.map .plain,
                     ctl := .label n cont (m.stack.drop k) rest :: m.ctl }

/-- Call function address `a` before `rest`. -/
def invoke (m : MState) (a : Nat) (rest : List AInstr) : Option MState :=
  match m.store.base.funcs[a]? with
  | some (.wasm ft inst code) =>
    let k := ft.params.length
    bif Nat.blt m.stack.length k then none
    else some { m with
      frame := ⟨(m.stack.take k).reverse ++ code.localDefaults, inst⟩, stack := [],
      code := code.body.map .plain,
      ctl := .label ft.results.length [] [] [] ::
        .frame ft.results.length m.frame (m.stack.drop k) rest :: m.ctl }
  | _ => none

/-- A trap: every context collapses, the store stays. -/
def trapOut (m : MState) : MState :=
  { m with frame := outerFrame m.ctl m.frame, stack := [], code := [.trap], ctl := [] }

/-- One step at plain instruction `i` before `rest`. -/
def stepPlain (m : MState) (i : Instr) (rest : List AInstr) : Option MState :=
  match i, m.stack with
  | .block bt body, _ => (bt.expand m.frame).bind fun ft =>
    m.enter ft.results.length [] ft.params.length body rest
  | .loop bt body, _ => (bt.expand m.frame).bind fun ft =>
    m.enter ft.params.length [.loop bt body] ft.params.length body rest
  | .br l, stk => (brPop l stk m.ctl).map fun (stk', code, ctl) =>
    { m with stack := stk', code, ctl }
  | .return_, stk => (retPop stk m.ctl).map fun (f, stk', code, ctl) =>
    { m with frame := f, stack := stk', code, ctl }
  | .load t ma, .i32 i :: stk => m.mem0.map fun (_, mm) =>
    let ea := i.toNat + ma.offset
    bif Nat.blt mm.size (ea + t.bytes) then m.cont stk [.trap] rest
    else m.cont (t.val (mm.read ea t.bytes) :: stk) [] rest
  | .loadPacked w p sx ma, .i32 i :: stk => m.mem0.map fun (_, mm) =>
    let ea := i.toNat + ma.offset
    bif Nat.blt mm.size (ea + p.bits / 8) then m.cont stk [.trap] rest
    else m.cont (packedVal w p.bits sx (mm.read ea (p.bits / 8)) :: stk) [] rest
  | .store t ma, v :: .i32 i :: stk => match m.mem0, v.numBits t with
    | some (a, mm), some c =>
      let ea := i.toNat + ma.offset
      bif Nat.blt mm.size (ea + t.bytes) then some (m.cont stk [.trap] rest)
      else some ((m.setMem a (mm.write ea t.bytes c)).cont stk [] rest)
    | _, _ => none
  | .storePacked w p ma, v :: .i32 i :: stk => match m.mem0, v.intBits w with
    | some (a, mm), some c =>
      let ea := i.toNat + ma.offset
      bif Nat.blt mm.size (ea + p.bits / 8) then some (m.cont stk [.trap] rest)
      else some ((m.setMem a (mm.write ea (p.bits / 8) c)).cont stk [] rest)
    | _, _ => none
  | .memoryGrow, .i32 n :: stk => m.mem0.map fun (a, mm) =>
    match mm.grow n.toNat with
    | some mm' => (m.setMem a mm').cont (.i32 (BitVec.ofNat 32 mm.pages) :: stk) [] rest
    | none => m.cont (.i32 (BitVec.ofInt 32 (-1)) :: stk) [] rest
  | .memoryFill, .i32 n :: v :: .i32 d :: stk => m.mem0.bind fun (a, mm) =>
    bif Nat.blt mm.size (d.toNat + n.toNat) then some (m.cont stk [.trap] rest)
    else bif Nat.beq n.toNat 0 then some (m.cont stk [] rest)
    else (v.intBits .w32).map fun c =>
      (m.setMem a (mm.fill d.toNat n.toNat (c % 256))).cont stk [] rest
  | .memoryCopy, .i32 n :: .i32 s' :: .i32 d :: stk => m.mem0.map fun (a, mm) =>
    bif Nat.blt mm.size (s'.toNat + n.toNat) || Nat.blt mm.size (d.toNat + n.toNat) then
      m.cont stk [.trap] rest
    else (m.setMem a (mm.copy d.toNat s'.toNat n.toNat)).cont stk [] rest
  | .memoryInit x, .i32 n :: .i32 s' :: .i32 d :: stk =>
    match m.mem0, m.frame.inst.datas[x]? with
    | some (a, mm), some da => (m.store.base.datas[da]?).bind fun di =>
      bif Nat.blt di.data.length (s'.toNat + n.toNat) || Nat.blt mm.size (d.toNat + n.toNat)
      then some (m.cont stk [.trap] rest)
      -- a source range past 2^32 (only a segment longer than any valid module's) wraps in the
      -- stepper's i32 arithmetic: no step here
      else bif Nat.blt (2 ^ 32) (s'.toNat + n.toNat) then none
      else some ((m.setMem a (mm.init d.toNat ((di.data.drop s'.toNat).take n.toNat))).cont stk []
        rest)
    | _, _ => none
  | i, stk => (Ref.instrStep m.store.abs m.frame i stk).map fun (s', f', stk', out) =>
    { m with store := { m.store with base := s' }, frame := f', stack := stk', code := out ++ rest }

/-- One machine step; `none` = final (only values or only `trap` remain) or stuck. -/
def step (m : MState) : Option MState :=
  match m.code with
  | e :: rest => match Ref.toVal e with
    | some v => some { m with stack := v :: m.stack, code := rest }
    | none => match e with
      | .plain i => m.stepPlain i rest
      | .invoke a => m.invoke a rest
      | .trap => bif m.ctl.isEmpty && m.stack.isEmpty && rest.isEmpty then none else some m.trapOut
      | _ => none
  | [] => match m.ctl with
    | [] => none
    | .label _ _ saved rest :: ctl => some { m with stack := m.stack ++ saved, code := rest, ctl }
    | .frame n caller saved rest :: ctl =>
      bif Nat.beq m.stack.length n then
        some { m with frame := caller, stack := m.stack ++ saved, code := rest, ctl }
      else none

/-- Run up to `fuel` steps: the last state reached and whether fuel ran out. -/
def run : Nat → MState → MState × Bool
  | 0, m => (m, true)
  | n + 1, m => match m.step with
    | some m' => run n m'
    | none => (m, false)

/-- The configuration `invoke a` on `args` from outside (`invokeConfig`). -/
def ofInvoke (s : MStore) (a : Nat) (args : List Val) : MState :=
  { store := s, frame := ⟨[], {}⟩, stack := args.reverse, code := [.invoke a], ctl := [] }

/-- How a run ended: only values remain, only `trap` remains, or neither (stuck). -/
inductive Ending where
  | returned (vs : List Val)
  | trapped
  | stuck

/-- The ending of a state with no step. -/
def ending (m : MState) : Ending :=
  match m.ctl, m.code, m.stack with
  | [], [], stk => .returned stk.reverse
  | [], [.trap], [] => .trapped
  | _, _, _ => .stuck

end MState

/-- A spec memory as a trie (bytes `[0, size)`; a valid memory reads zero past its size). -/
def MMem.ofMemInst (m : MemInst) : MMem :=
  (List.range m.size).foldl (fun mm a =>
    let b := (m.byte a).toNat
    bif b == 0 then mm else { mm with data := mm.data.set mm.depth a b })
    (MMem.alloc m.pages m.max)

/-- A spec store with its memories as tries. -/
def MStore.ofStore (s : Store) : MStore := { base := s, mems := s.mems.map MMem.ofMemInst }

/-- `allocModule` with fresh memories as empty tries. -/
def MStore.alloc (s : MStore) (m : Module) (imports : List ExternVal) (gvals : List Val)
    (erefs : List (List Ref)) : MStore × ModuleInst :=
  let (s', inst) := allocModule s.abs m imports gvals erefs
  ({ base := s', mems := s.mems ++ m.mems.map fun lim => MMem.alloc lim.min lim.max }, inst)

/-- The initialization run of `m` (§4.5.4) after allocation with evaluated initializers, as in
`Ref.instantiate`: the final state or `none` when an initializer fails or disagrees. -/
def initRun (fuel : Nat) (s : MStore) (m : Module) (imports : List ExternVal) :
    Option (MState × Bool) := do
  let (s₀, inst₀) := s.alloc m imports (m.globals.map fun g => g.type.val.default)
    (m.elems.map fun _ => [])
  let gvals ← m.globals.mapM fun g => Ref.evalConst fuel s₀.abs inst₀ g.init
  let erefs ← m.elems.mapM fun e =>
    e.init.mapM fun ex => Ref.evalConst fuel s₀.abs inst₀ ex >>= Ref.asRef
  let (s₁, inst) := s.alloc m imports gvals erefs
  let gvals₁ ← m.globals.mapM fun g => Ref.evalConst fuel s₁.abs inst g.init
  let erefs₁ ← m.elems.mapM fun e =>
    e.init.mapM fun ex => Ref.evalConst fuel s₁.abs inst ex >>= Ref.asRef
  guard (gvals₁ == gvals && erefs₁ == erefs)
  some (MState.run fuel
    { store := s₁, frame := ⟨[], inst⟩, stack := [], code := (initCode m).map .plain, ctl := [] })

/-- Instantiate as `Ref.instantiate` does, the initialization code run on the machine. -/
def instantiate (fuel : Nat) (s : MStore) (m : Module) (imports : List ExternVal) :
    Option (MStore × ModuleInst) := do
  let (m', exhausted) ← initRun fuel s m imports
  match exhausted, m'.ending with
  | false, .returned [] => some (m'.store, m'.frame.inst)
  | _, _ => none

end FVA.Wasm.Exec.Machine
