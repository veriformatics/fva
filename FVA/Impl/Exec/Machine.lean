import FVA.Impl.Exec.Det
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

/-- A suspended context: a block's label, a caller's frame or an exception handler. -/
inductive Ctl where
  /-- `label_n{cont}` with the operands below it and the instructions after it. -/
  | label (n : Nat) (cont : List Instr) (saved : List Val) (rest : List AInstr)
  /-- `frame_n{caller}`: the caller's frame, operands below the call and instructions after. -/
  | frame (n : Nat) (caller : Frame) (saved : List Val) (rest : List AInstr)
  /-- `handler_n{catch*}` (P′, `try_table`): its clauses, operands below it and instructions
  after; no frame: the frame current when it is innermost is the one its tags resolve in. -/
  | handler (n : Nat) (cs : List Catch) (saved : List Val) (rest : List AInstr)

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
  | .handler n cs saved rest :: ctl, f, es =>
    wrap ctl f (vals saved.reverse ++ [.handler n cs es] ++ rest)

/-- The spec configuration a machine state denotes. -/
def MState.abs (m : MState) : Config :=
  let (f, es) := wrap m.ctl m.frame (vals m.stack.reverse ++ m.code)
  ⟨m.store.abs, f, es⟩

/-- Pop operands, labels and handlers for `br l` (a handler is no branch target): the operands,
code and control after the branch. -/
def brPop : Nat → List Val → List Ctl → Option (List Val × List AInstr × List Ctl)
  | 0, stk, .label n cont saved rest :: ctl =>
    bif Nat.blt stk.length n then none else some (stk.take n ++ saved, cont.map .plain ++ rest, ctl)
  | l + 1, stk, .label .. :: ctl => brPop l stk ctl
  | l, stk, .handler .. :: ctl => brPop l stk ctl
  | _, _, _ => none

/-- Pop operands, labels, handlers and the innermost frame for `return`. -/
def retPop : List Val → List Ctl → Option (Frame × List Val × List AInstr × List Ctl)
  | stk, .label .. :: ctl | stk, .handler .. :: ctl => retPop stk ctl
  | stk, .frame n caller saved rest :: ctl =>
    bif Nat.blt stk.length n then none else some (caller, stk.take n ++ saved, rest, ctl)
  | _, [] => none

/-- Pop labels + handlers to the innermost frame and that frame for a tail call: the caller,
its operands below the call, the code after it and the control below. -/
def framePop : List Ctl → Option (Frame × List Val × List AInstr × List Ctl)
  | .label .. :: ctl | .handler .. :: ctl => framePop ctl
  | .frame _ caller saved rest :: ctl => some (caller, saved, rest, ctl)
  | [] => none

/-- The outermost frame (the configuration's frame). -/
def outerFrame : List Ctl → Frame → Frame
  | [], f => f
  | .label .. :: ctl, f | .handler .. :: ctl, f => outerFrame ctl f
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
  | some (.wasm dt inst code) => dt.expand.bind fun ft =>
    let k := ft.params.length
    bif Nat.blt m.stack.length k then none
    else some { m with
      frame := ⟨(m.stack.take k).reverse.map some ++ code.localDefaults, inst⟩, stack := [],
      code := code.body.map .plain,
      ctl := .label ft.results.length [] [] [] ::
        .frame ft.results.length m.frame (m.stack.drop k) rest :: m.ctl }
  | _ => none

/-- A trap: every context collapses (handlers do not catch traps), the store stays. -/
def trapOut (m : MState) : MState :=
  { m with frame := outerFrame m.ctl m.frame, stack := [], code := [.trap], ctl := [] }

/-- Enter `try_table`: its handler outside its result label, its parameters as the operands. -/
def enterTry (m : MState) (n : Nat) (cs : List Catch) (k : Nat) (body : List Instr)
    (rest : List AInstr) : Option MState :=
  bif Nat.blt m.stack.length k then none
  else some { m with stack := m.stack.take k, code := body.map .plain,
                     ctl := .label n [] [] [] :: .handler n cs (m.stack.drop k) rest :: m.ctl }

/-- Exception `a` alone in the innermost block (`[ref.exn a, throw_ref]`): the innermost entry
takes it (3.0 `throw_ref-label`, `-frame`, `-handler-*`), one reduction; `none` at the top
(uncaught, `ending`). A label or frame passes it out with its operands + code restored around
it (a later step drops them); a handler tries its first clause in the current frame. -/
def throwPop (m : MState) (a : Nat) : Option MState :=
  match m.ctl with
  | [] => none
  | .label _ _ saved rest :: ctl =>
    some { m with stack := .ref (.exn a) :: saved, code := .plain .throwRef :: rest, ctl }
  | .frame _ caller saved rest :: ctl =>
    some { m with frame := caller, stack := .ref (.exn a) :: saved,
                  code := .plain .throwRef :: rest, ctl }
  | .handler n cs saved rest :: ctl => match cs with
    | [] => some { m with stack := .ref (.exn a) :: saved, code := .plain .throwRef :: rest, ctl }
    | c :: cs' => match Ref.catchStep m.store.abs m.frame a c with
      | some out => some { m with stack := saved, code := out ++ rest, ctl }
      | none => some { m with ctl := .handler n cs' saved rest :: ctl }

/-- A tail call of `a` (`return_invoke`): the callee's arguments replace the innermost frame's
labels, handlers and operands; the call runs in the caller's place. -/
def retInvoke (m : MState) (a : Nat) : Option MState :=
  match m.store.base.funcs[a]? with
  | some fn => fn.type.expand.bind fun ft =>
    let k := ft.params.length
    bif Nat.blt m.stack.length k then none
    else (framePop m.ctl).map fun (caller, saved, rest, ctl) =>
      { m with frame := caller, stack := m.stack.take k ++ saved, code := .invoke a :: rest, ctl }
  | none => none

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
  | .tryTable bt cs body, _ => (bt.expand m.frame).bind fun ft =>
    m.enterTry ft.results.length cs ft.params.length body rest
  -- 3.0 `throw_ref-instrs`: other operands or code around the exception are dropped first
  | .throwRef, .ref (.exn a) :: stk =>
    bif stk.isEmpty && rest.isEmpty then m.throwPop a
    else some (m.cont [.ref (.exn a)] [.plain .throwRef] [])
  | .throwRef, .ref .null :: stk => some (m.cont stk [.trap] rest)
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
      | .returnInvoke a => m.retInvoke a
      | .trap => bif m.ctl.isEmpty && m.stack.isEmpty && rest.isEmpty then none else some m.trapOut
      | _ => none
  | [] => match m.ctl with
    | [] => none
    | .label _ _ saved rest :: ctl | .handler _ _ saved rest :: ctl =>
      some { m with stack := m.stack ++ saved, code := rest, ctl }
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

/-- The next step is no choice point of the spec under growth policy `fits` (U27): a value, a
control exit, a plain instruction `Ref.atUnique` admits (`throw_ref` on an exception: alone in
its block), a call of a module function or a tail call; a host call or a trap is one. -/
def uniq (fits : Bool) (m : MState) : Bool :=
  match m.code with
  | e :: rest => match Ref.toVal e with
    | some _ => true
    | none => match e with
      | .plain .throwRef => match m.stack with
        | .ref (.exn _) :: stk => stk.isEmpty && rest.isEmpty
        | _ => true
      | .plain i => Ref.instrUnique fits i m.stack
      | .invoke a => match m.store.base.funcs[a]? with
        | some (.wasm ..) => true
        | _ => false
      | .returnInvoke _ => true
      | _ => false
  | [] => true

/-- The next step drops the operands or code around a thrown exception (3.0 `throw_ref-instrs`):
a choice point of the spec whose every choice reaches the same handler, or the top, with the
same exception and store (`FVA.Proof.Exec.MachineSys`: `must_admin`, `sysMust_admin`). -/
def admin (m : MState) : Bool :=
  match m.code, m.stack with
  | .plain .throwRef :: rest, .ref (.exn _) :: stk => !(stk.isEmpty && rest.isEmpty)
  | _, _ => false

/-- Run up to `fuel` steps while each is no choice point under `fits` or an administrative
throw step: the last state reached and whether fuel ran out. -/
def runU (fits : Bool) : Nat → MState → MState × Bool
  | 0, m => (m, true)
  | n + 1, m => bif m.uniq fits || m.admin then
      match m.step with
      | some m' => runU fits n m'
      | none => (m, false)
    else (m, false)

/-- At a host call on enough values: the host id, its arity and the code after the call. -/
def hostCall (m : MState) : Option (Nat × Nat × List AInstr) :=
  match m.code with
  | .invoke a :: rest => match m.store.base.funcs[a]? with
    | some (.host dt id) => dt.expand.bind fun ft =>
      bif Nat.blt m.stack.length ft.params.length then none
      else some (id, ft.params.length, rest)
    | _ => none
  | _ => none

/-- The machine resumed after a host call on its `k` top values: the call's result
instructions `out` (values or `trap`) in its place, the store `ms` the host left. -/
def hostResume (m : MState) (ms : MStore) (out rest : List AInstr) (k : Nat) : MState :=
  { m with store := ms, stack := m.stack.drop k, code := out ++ rest }

/-- How a run ended: only values remain, only `trap` remains, an uncaught exception, or
neither (stuck). -/
inductive Ending where
  | returned (vs : List Val)
  | trapped
  | thrown (a : Nat)
  | stuck

/-- The ending of a state with no step. -/
def ending (m : MState) : Ending :=
  match m.ctl, m.code, m.stack with
  | [], [], stk => .returned stk.reverse
  | [], [.trap], [] => .trapped
  | [], [.plain .throwRef], [.ref (.exn a)] => .thrown a
  | _, _, _ => .stuck

end MState

/-- An executable host call's result on machine stores: values or a trap. -/
inductive MHostOut where
  | returned (vs : List Val)
  | trapped

/-- The spec outcome of a machine host result whose store is `ms`. -/
def MHostOut.spec (ms : MStore) : MHostOut → HostOutcome
  | .returned vs => .returned ms.abs vs
  | .trapped => .trapped ms.abs

/-- The instructions a machine host result leaves in the call's place. -/
def MHostOut.out : MHostOut → List AInstr
  | .returned vs => vals vs
  | .trapped => [.trap]

/-- A process on the machine with executable host `X` (U27): unique core steps (`fits = true`),
administrative throw steps and host calls; stops at an exit, a final or stuck state, a choice
point, a host call `X` leaves undefined, or when fuel runs out (`true`). -/
def sysRun {St : Type} (exited : St → Option Nat)
    (X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut)) :
    Nat → St × MState → St × MState × Bool
  | 0, (σ, m) => (σ, m, true)
  | n + 1, (σ, m) =>
    match exited σ with
    | some _ => (σ, m, false)
    | none => match m.hostCall with
      | some (id, k, rest) => match X σ id m.store (m.stack.take k).reverse with
        | some (τ, ms, r) => sysRun exited X n (τ, m.hostResume ms r.out rest k)
        | none => (σ, m, false)
      | none => bif m.uniq true || m.admin then
          match m.step with
          | some m' => sysRun exited X n (σ, m')
          | none => (σ, m, false)
        else (σ, m, false)

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
    (trefs : List Ref) (erefs : List (List Ref)) : MStore × ModuleInst :=
  let (s', inst) := allocModule s.abs m imports gvals trefs erefs
  ({ base := s', mems := s.mems ++ m.mems.map fun lim => MMem.alloc lim.min lim.max }, inst)

/-- The initialization run of `m` (§4.5.4) after allocation with evaluated initializers, as in
`Ref.instantiate`: the final state or `none` when an initializer fails or disagrees. -/
def initRun (fuel : Nat) (s : MStore) (m : Module) (imports : List ExternVal) :
    Option (MState × Bool) := do
  let (gvals, trefs, erefs) ← Ref.initCandidates fuel s.abs m imports
  guard (Ref.initAgrees fuel s.abs m imports gvals trefs erefs)
  let (s₁, inst) := s.alloc m imports gvals trefs erefs
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
