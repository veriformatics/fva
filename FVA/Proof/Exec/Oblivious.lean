import FVA.Proof.Exec.MachineSys
import FVA.Impl.Exec.WasiHost

/-!
# Data-oblivious framing (contract U28g F1)

A concrete machine run that never inspects some positions of its state transfers to every state
that differs from it at those positions alone. A position (`Pos`) is a byte of a store memory, a
local of the running frame, a local of a caller frame saved in a control entry, or an operand
saved in a control entry (entries counted from the bottom, so pushes and pops above an entry keep
its number). `put` writes patches at positions; the checker `tstep` follows each position through
one step (its image, or `none` once overwritten or discarded) and fails when the step reads one;
`trun` composes it along a `sysRun` with the executable WASI host, whose calls it admits only
where their memory footprint is known (`environ_sizes_get`).
-/

namespace FVA.Wasm.Exec.Machine.Oblivious

open FVA.Wasm FVA.Wasm.Exec FVA.Wasi

/-- A position of input-dependent data. -/
inductive Pos where
  /-- Byte `a` of store memory `mi`. -/
  | byte (mi a : Nat)
  /-- Local `i` of the running frame. -/
  | top (i : Nat)
  /-- Local `i` of the caller frame saved in control entry `k` (from the bottom). -/
  | loc (k i : Nat)
  /-- Operand `j` (top first) saved in control entry `k` (from the bottom). -/
  | saved (k j : Nat)
  deriving DecidableEq, Repr

/-- A patch value: a byte (`< 256`) or a slot value. -/
inductive TVal where
  | byte (b : Nat)
  | val (v : Val)

/-- `xs` with `f` applied at index `n`. -/
def modifyAt {α : Type} (f : α → α) : Nat → List α → List α
  | _, [] => []
  | 0, x :: xs => f x :: xs
  | n + 1, x :: xs => x :: modifyAt f n xs

/-- The list index of control entry `k` (the list holds the innermost entry first). -/
def ctlAt (ctl : List Ctl) (k : Nat) : Nat := ctl.length - 1 - k

/-- A saved caller frame's local `i` set to `v`. -/
def setCallerLocal (i : Nat) (v : Val) : Ctl → Ctl
  | .frame n f saved rest => .frame n { f with locals := f.locals.set i (some v) } saved rest
  | c => c

/-- An entry's saved operand `j` set to `v`. -/
def setSaved (j : Nat) (v : Val) : Ctl → Ctl
  | .label n cont saved rest => .label n cont (saved.set j v) rest
  | .frame n f saved rest => .frame n f (saved.set j v) rest
  | .handler n cs saved rest => .handler n cs (saved.set j v) rest

/-- One patch. -/
def put1 (m : MState) : Pos × TVal → MState
  | (.byte mi a, .byte b) =>
    { m with store :=
      { m.store with mems := modifyAt (fun mm => mm.writeBytes a [b]) mi m.store.mems } }
  | (.top i, .val v) => { m with frame := { m.frame with locals := m.frame.locals.set i (some v) } }
  | (.loc k i, .val v) => { m with ctl := modifyAt (setCallerLocal i v) (ctlAt m.ctl k) m.ctl }
  | (.saved k j, .val v) => { m with ctl := modifyAt (setSaved j v) (ctlAt m.ctl k) m.ctl }
  | _ => m

/-- The patches `ts`, in order. -/
def put (ts : List (Pos × TVal)) (m : MState) : MState := ts.foldl put1 m

/-! ## The checker -/

/-- A position map: each position's image after a step (`none` = overwritten or discarded). -/
abbrev PMap := Pos → Option Pos

/-- A tainted byte of store memory `mi` in `[a, a + n)`. -/
def hitBytes (ps : List Pos) (mi a n : Nat) : Bool :=
  ps.any fun
    | .byte mi' x => mi' == mi && a ≤ x && x < a + n
    | _ => false

/-- Bytes `[a, a + n)` of store memory `mi` overwritten. -/
def killBytes (mi a n : Nat) : PMap
  | .byte mi' x => bif mi' == mi && a ≤ x && x < a + n then none else some (.byte mi' x)
  | p => some p

/-- A tainted operand saved in entry `k`. -/
def hitSaved (ps : List Pos) (k : Nat) : Bool :=
  ps.any fun
    | .saved k' _ => k' == k
    | _ => false

/-- Every control entry from `k` up popped; with `frame`, entry `k`'s caller frame runs again
(its locals become the running frame's, the running frame's die). -/
def popTo (k : Nat) (frame : Bool) : PMap
  | .byte mi a => some (.byte mi a)
  | .top i => bif frame then none else some (.top i)
  | .loc k' i => bif k' == k then (bif frame then some (.top i) else none)
    else bif k < k' then none else some (.loc k' i)
  | .saved k' j => bif k ≤ k' then none else some (.saved k' j)

/-- The bottom index of the target label of `br l` (handlers skipped), `none` past a frame. -/
def brTarget : Nat → List Ctl → Option Nat
  | 0, .label .. :: ctl => some ctl.length
  | l + 1, .label .. :: ctl => brTarget l ctl
  | l, .handler .. :: ctl => brTarget l ctl
  | _, _ => none

/-- The bottom index of the innermost frame entry. -/
def frameAt : List Ctl → Option Nat
  | .label .. :: ctl | .handler .. :: ctl => frameAt ctl
  | .frame .. :: ctl => some ctl.length
  | [] => none

/-- A read of `[ea, ea + n)` from the running frame's memory 0: rejected when it succeeds over a
tainted byte (an out-of-bounds read traps without reading). -/
def memRead (ps : List Pos) (m : MState) (ea n : Nat) : Option PMap :=
  match m.mem0 with
  | some (mi, mm) => bif Nat.blt mm.size (ea + n) then some some
    else bif hitBytes ps mi ea n then none else some some
  | none => some some

/-- A write of `[ea, ea + n)` into the running frame's memory 0: kills exactly the written bytes
(an out-of-bounds write traps without writing). -/
def memWrite (m : MState) (ea n : Nat) : PMap :=
  match m.mem0 with
  | some (mi, mm) => bif Nat.blt mm.size (ea + n) then some else killBytes mi ea n
  | none => some

/-- `throwPop`'s position map for exception `a` alone in the innermost block. -/
def throwMap (ps : List Pos) (m : MState) (a : Nat) : Option PMap :=
  let k := m.ctl.length - 1
  match m.ctl with
  | [] => none
  | .label .. :: _ => bif hitSaved ps k then none else some (popTo k false)
  | .frame .. :: _ => bif hitSaved ps k then none else some (popTo k true)
  | .handler _ cs _ _ :: _ => match cs with
    | [] => bif hitSaved ps k then none else some (popTo k false)
    | c :: _ => match Ref.catchStep m.store.abs m.frame a c with
      | some _ => bif hitSaved ps k then none else some (popTo k false)
      | none => some some

/-- The plain instructions `MState.stepPlain` hands to `Ref.instrStep` that the checker admits:
each reads locals by `local.get` alone and memory bytes never (`instrStep_generic`). Every other
fallthrough instruction fails closed. -/
def Generic : Instr → Bool
  | .localGet _ | .localSet _ | .localTee _ | .call _ | .callIndirect .. | .globalGet _
  | .globalSet _ | .ibinop .. | .iunop .. | .irelop .. | .itestEqz _ | .cvtop _ | .brIf _
  | .brTable .. | .select _ | .drop | .throw _ => true
  | _ => false

/-- The running frame's local `x` overwritten, every other position kept. -/
def killTop (x : Nat) : PMap := fun p => bif p == .top x then none else some p

/-- The position map of generic instruction `i` on operands `stk`: `local.get` of a live local
is a read; `local.set` overwrites its local (`local.tee` keeps it: the stepper emits
`[v, v, local.set x]`, killed at that later `local.set`). -/
def genMap (ps : List Pos) (i : Instr) (stk : List Val) : Option PMap :=
  match i, stk with
  | .localGet x, _ => bif ps.contains (.top x) then none else some some
  | .localSet x, _ :: _ => some (killTop x)
  | _, _ => some some

/-- The position map of plain instruction `i` before `rest` (mirrors `MState.stepPlain`). -/
def plainMap (ps : List Pos) (m : MState) (i : Instr) (rest : List AInstr) : Option PMap :=
  match i, m.stack with
  | .block .., _ | .loop .., _ | .tryTable .., _ => some some
  | .br l, _ => match brTarget l m.ctl with
    | some k => bif hitSaved ps k then none else some (popTo k false)
    | none => none
  | .return_, _ => match frameAt m.ctl with
    | some k => bif hitSaved ps k then none else some (popTo k true)
    | none => none
  | .load t ma, .i32 a :: _ => memRead ps m (a.toNat + ma.offset) t.bytes
  | .loadPacked _ p _ ma, .i32 a :: _ => memRead ps m (a.toNat + ma.offset) (p.bits / 8)
  | .store t ma, _ :: .i32 a :: _ => some (memWrite m (a.toNat + ma.offset) t.bytes)
  | .storePacked _ p ma, _ :: .i32 a :: _ => some (memWrite m (a.toNat + ma.offset) (p.bits / 8))
  | .memoryFill, .i32 n :: _ :: .i32 d :: _ => some (memWrite m d.toNat n.toNat)
  | .throwRef, .ref (.exn a) :: stk =>
    bif stk.isEmpty && rest.isEmpty then throwMap ps m a else some some
  | i, stk => bif Generic i then genMap ps i stk else none

/-- The position map of the machine step from `m`, or `none` when it reads a position of `ps` (or
leaves the admitted step kinds: traps, tail calls). -/
def tstep (ps : List Pos) (m : MState) : Option PMap :=
  match m.code with
  | e :: rest => match Ref.toVal e with
    | some _ => some some
    | none => match e with
      | .plain i => plainMap ps m i rest
      | .invoke a => match m.store.base.funcs[a]? with
        | some (.wasm ..) => some fun
          | .top i => some (.loc m.ctl.length i)
          | p => some p
        | _ => none
      | _ => none
  | [] => match m.ctl with
    | [] => none
    | .label .. :: _ | .handler .. :: _ =>
      bif hitSaved ps (m.ctl.length - 1) then none else some (popTo (m.ctl.length - 1) false)
    | .frame .. :: _ =>
      bif hitSaved ps (m.ctl.length - 1) then none else some (popTo (m.ctl.length - 1) true)

/-- The position map of host call `id` of module `md` on arguments `vs` under the executable WASI
host with memory `mem`: `environ_sizes_get` alone (no guest-memory input; its successful writes
kill exactly the bytes they cover). -/
def hostMap (md : Module) (mem : Nat) (σ : State) (id : Nat) (ms : MStore) (vs : List Val) :
    Option PMap := do
  let c ← bind md id
  guard (c = .environSizesGet)
  let mm ← ms.mems[mem]?
  let a ← c.args vs
  guard (inProfile σ c ms.abs mem vs)
  match step σ (decode c mm.abs a) { bytes := [] } with
  | (_, .ok ws) =>
    pure fun p => ws.foldl (fun q w => q.bind (killBytes mem w.1 w.2.length)) (some p)
  | _ => pure some

/-- Position `p` exists in `m`: a byte inside its store memory, a control entry below the top. -/
def posOK (m : MState) : Pos → Bool
  | .byte mi a => match m.store.mems[mi]? with
    | some mm => Nat.blt a mm.size
    | none => false
  | .loc k _ | .saved k _ => Nat.blt k m.ctl.length
  | .top _ => true

/-- The positions `ps` followed through `n` admitted transitions of `sysRun` with the executable
WASI host of `md` (memory `mem`): each one's final image (`none` = overwritten or discarded), or
`none` when a transition reads a live position, a live position leaves the state (`posOK`), the
run stops early or leaves the admitted kinds. -/
def trun (md : Module) (mem : Nat) : List (Option Pos) → Nat → State × MState →
    Option (List (Option Pos))
  | ps, 0, _ => some ps
  | ps, n + 1, (σ, m) =>
    match σ.exited with
    | some _ => none
    | none =>
      let live := ps.filterMap id
      bif !(live.all (posOK m)) then none else
      match m.hostCall with
      | some (id, k, rest) =>
        let vs := (m.stack.take k).reverse
        match hostMap md mem σ id m.store vs, wasiHost md mem none σ id m.store vs with
        | some f, some (τ, ms, r) =>
          trun md mem (ps.map (·.bind f)) n (τ, m.hostResume ms r.out rest k)
        | _, _ => none
      | none =>
        bif m.uniq true || m.admin then
          match tstep live m, m.step with
          | some f, some m' => trun md mem (ps.map (·.bind f)) n (σ, m')
          | _, _ => none
        else none

/-! ## Patches by component -/

/-- The byte patches of `ts` on store memories `ms`, in order. -/
def putMems : List (Pos × TVal) → List MMem → List MMem
  | [], ms => ms
  | (.byte mi a, .byte b) :: ts, ms => putMems ts (modifyAt (fun mm => mm.writeBytes a [b]) mi ms)
  | _ :: ts, ms => putMems ts ms

/-- The running frame's local patches of `ts`, in order. -/
def putLocals : List (Pos × TVal) → List (Option Val) → List (Option Val)
  | [], L => L
  | (.top i, .val v) :: ts, L => putLocals ts (L.set i (some v))
  | _ :: ts, L => putLocals ts L

/-- The control-stack patches of `ts` (saved caller locals, saved operands), in order. -/
def putCtl : List (Pos × TVal) → List Ctl → List Ctl
  | [], ctl => ctl
  | (.loc k i, .val v) :: ts, ctl => putCtl ts (modifyAt (setCallerLocal i v) (ctlAt ctl k) ctl)
  | (.saved k j, .val v) :: ts, ctl => putCtl ts (modifyAt (setSaved j v) (ctlAt ctl k) ctl)
  | _ :: ts, ctl => putCtl ts ctl

/-- `put` patches the memories, the running frame's locals and the control stack apart. -/
theorem put_eq (ts : List (Pos × TVal)) (m : MState) :
    put ts m = { m with
      store := { m.store with mems := putMems ts m.store.mems }
      frame := { m.frame with locals := putLocals ts m.frame.locals }
      ctl := putCtl ts m.ctl } := by
  induction ts generalizing m with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p, v⟩ := t
    show put ts (put1 m (p, v)) = _
    rw [ih]
    cases p <;> cases v <;> rfl

/-- Patches moved by a position map: each follows its position's image; a position mapped to
`none` drops its patch. -/
def move (f : PMap) (ts : List (Pos × TVal)) : List (Pos × TVal) :=
  ts.filterMap fun (p, v) => (f p).map (·, v)

theorem move_some (ts : List (Pos × TVal)) : move some ts = ts := by
  simp [move]

theorem move_killTop_cons (x : Nat) (p : Pos) (v : TVal) (ts : List (Pos × TVal)) :
    move (killTop x) ((p, v) :: ts) =
      bif p == .top x then move (killTop x) ts else (p, v) :: move (killTop x) ts := by
  simp only [move, killTop, List.filterMap_cons]
  cases p == .top x <;> rfl

theorem length_putLocals (ts : List (Pos × TVal)) (L : List (Option Val)) :
    (putLocals ts L).length = L.length := by
  induction ts generalizing L with
  | nil => rfl
  | cons t ts ih => obtain ⟨p, v⟩ := t; cases p <;> cases v <;> simp [putLocals, ih]

theorem putLocals_getElem? {ts : List (Pos × TVal)} {x : Nat} (hx : ∀ t ∈ ts, t.1 ≠ .top x)
    (L : List (Option Val)) : (putLocals ts L)[x]? = L[x]? := by
  induction ts generalizing L with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p, v⟩ := t
    have hx' : ∀ t ∈ ts, t.1 ≠ .top x := fun t ht => hx t (List.mem_cons_of_mem _ ht)
    have h0 : p ≠ .top x := hx (p, v) List.mem_cons_self
    cases p <;> cases v <;> simp_all [putLocals]

theorem putLocals_set (ts : List (Pos × TVal)) (L : List (Option Val)) (x : Nat)
    (w : Option Val) : (putLocals ts L).set x w = putLocals (move (killTop x) ts) (L.set x w) := by
  induction ts generalizing L with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p, v⟩ := t
    rw [move_killTop_cons]
    by_cases hp : p = .top x
    · subst hp
      cases v <;> simp [putLocals, ih, List.set_set]
    · have hb : (p == .top x) = false := by simpa using hp
      rw [hb, Bool.cond_false]
      cases p <;> cases v <;> simp only [putLocals, ih]
      case top.val i u =>
        have hix : i ≠ x := fun h => hp (h ▸ rfl)
        rw [List.set_comm _ _ hix]

theorem putMems_killTop (ts : List (Pos × TVal)) (x : Nat) (ms : List MMem) :
    putMems (move (killTop x) ts) ms = putMems ts ms := by
  induction ts generalizing ms with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p, v⟩ := t
    rw [move_killTop_cons]
    by_cases hp : p = .top x
    · subst hp; cases v <;> simp only [beq_self_eq_true, Bool.cond_true, ih] <;> rfl
    · have hb : (p == .top x) = false := by simpa using hp
      rw [hb, Bool.cond_false]
      cases p <;> cases v <;> simp only [putMems, ih]

theorem putCtl_killTop (ts : List (Pos × TVal)) (x : Nat) (ctl : List Ctl) :
    putCtl (move (killTop x) ts) ctl = putCtl ts ctl := by
  induction ts generalizing ctl with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨p, v⟩ := t
    rw [move_killTop_cons]
    by_cases hp : p = .top x
    · subst hp; cases v <;> simp only [beq_self_eq_true, Bool.cond_true, ih] <;> rfl
    · have hb : (p == .top x) = false := by simpa using hp
      rw [hb, Bool.cond_false]
      cases p <;> cases v <;> simp only [putCtl, ih]

/-! ## Fallthrough congruence (contract F1: the generic kinds) -/

/-- The locals after generic instruction `i` on operands `stk`: `local.set x` writes local `x`. -/
def relocal (i : Instr) (stk : List Val) (L : List (Option Val)) : List (Option Val) :=
  match i, stk with
  | .localSet x, v :: _ => L.set x (some v)
  | _, _ => L

/-- `Ref.instrStep` on a generic instruction reads neither memories nor locals but `local.get`'s
and writes locals by `relocal` alone: other memories and same-length locals agreeing at
`local.get`'s index give the same step, its frame's locals rewritten by `relocal`. -/
theorem instrStep_generic {S S' : Store} {f f' : Frame} {i : Instr} {stk stk' : List Val}
    {out : List AInstr} (hg : Generic i = true)
    (h : Ref.instrStep S f i stk = some (S', f', stk', out)) (M : List MemInst)
    (L : List (Option Val)) (hL : L.length = f.locals.length)
    (hget : ∀ x, i = .localGet x → L[x]? = f.locals[x]?) :
    Ref.instrStep { S with mems := M } { f with locals := L } i stk =
      some ({ S' with mems := M }, { f' with locals := relocal i stk L }, stk', out) := by
  fun_cases Ref.instrStep S f i stk <;> (try simp only [Generic, Bool.false_eq_true] at hg) <;>
    simp_all [Ref.instrStep, relocal, Ref.callTarget, Ref.tableAt]
  all_goals first
    | (obtain ⟨_, _, rfl, rfl, rfl, rfl⟩ := h; simp_all)
    | (obtain ⟨rfl, rfl, rfl, rfl⟩ := h; simp_all)
    | (obtain ⟨ft, hft, h⟩ := Option.bind_eq_some_iff.mp h
       simp only [hft, Option.bind_some] at h ⊢
       split at h <;> simp_all
       obtain ⟨rfl, rfl, rfl, rfl⟩ := h
       simp)

/-- The frame a generic step leaves: its locals rewritten by `relocal`. -/
theorem instrStep_generic_locals {S S' : Store} {f f' : Frame} {i : Instr}
    {stk stk' : List Val} {out : List AInstr} (hg : Generic i = true)
    (h : Ref.instrStep S f i stk = some (S', f', stk', out)) :
    f'.locals = relocal i stk f.locals := by
  have := instrStep_generic hg h S.mems f.locals rfl (fun _ _ => rfl)
  rw [show ({ S with mems := S.mems } : Store) = S from rfl,
    show ({ f with locals := f.locals } : Frame) = f from rfl, h] at this
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact congrArg Frame.locals this.2.1

/-- A generic instruction is no value. -/
theorem toVal_generic {i : Instr} (hg : Generic i = true) : Ref.toVal (.plain i) = none := by
  cases i <;> simp_all [Generic, Ref.toVal]

/-- The machine runs a generic instruction by `Ref.instrStep` on the abstract store. -/
theorem stepPlain_generic (m : MState) {i : Instr} (rest : List AInstr)
    (hg : Generic i = true) :
    m.stepPlain i rest = (Ref.instrStep m.store.abs m.frame i m.stack).map
      fun (s', f', stk', out) =>
        { m with store := { m.store with base := s' }, frame := f', stack := stk',
                 code := out ++ rest } := by
  cases i <;> simp only [Generic, Bool.false_eq_true] at hg <;> rfl

/-- `plainMap` on a generic instruction is `genMap`. -/
theorem plainMap_generic (ps : List Pos) (m : MState) {i : Instr} (rest : List AInstr)
    (hg : Generic i = true) : plainMap ps m i rest = genMap ps i m.stack := by
  cases i <;> simp only [Generic, Bool.false_eq_true] at hg <;> rfl

/-- `genMap`'s two shapes: `local.set` on an operand overwrites its local, every other generic
step keeps every position (and every local). -/
theorem genMap_cases {ps : List Pos} {i : Instr} {stk : List Val} {F : PMap}
    (h : genMap ps i stk = some F) :
    (F = some ∧ ∀ L, relocal i stk L = L) ∨
      ∃ x v stk₀, i = .localSet x ∧ stk = v :: stk₀ ∧ F = killTop x := by
  unfold genMap at h
  split at h
  · rename_i x
    left
    refine ⟨?_, fun L => rfl⟩
    cases hc : ps.contains (.top x) <;> simp_all
  · exact .inr ⟨_, _, _, rfl, rfl, (Option.some.inj h).symm⟩
  · left
    refine ⟨(Option.some.inj h).symm, fun L => ?_⟩
    unfold relocal
    split <;> simp_all

/-! ## Alike states (contract F1 `Eqv`) -/

/-- Memories alike: equal pages, maximum, depth and bytes. -/
def MemEqv (m₁ m₂ : MMem) : Prop :=
  m₁.pages = m₂.pages ∧ m₁.max = m₂.max ∧ m₁.depth = m₂.depth ∧ ∀ a, m₁.byte a = m₂.byte a

/-- `m` without memories (store memories, `store.base.mems`). -/
def eraseMems (m : MState) : MState :=
  { m with store := { base := { m.store.base with mems := [] }, mems := [] } }

/-- Alike states: memories pairwise `MemEqv`, every other component equal (`store.base.mems`,
never read, aside). -/
def Eqv (m₁ m₂ : MState) : Prop :=
  List.Forall₂ MemEqv m₁.store.mems m₂.store.mems ∧ eraseMems m₁ = eraseMems m₂

theorem eqv_iff {m₁ m₂ : MState} : Eqv m₁ m₂ ↔
    List.Forall₂ MemEqv m₁.store.mems m₂.store.mems ∧
      ({ m₁.store.base with mems := [] } : Store) = { m₂.store.base with mems := [] } ∧
      m₁.frame = m₂.frame ∧ m₁.stack = m₂.stack ∧ m₁.code = m₂.code ∧ m₁.ctl = m₂.ctl := by
  obtain ⟨⟨b₁, ms₁⟩, f₁, s₁, c₁, k₁⟩ := m₁
  obtain ⟨⟨b₂, ms₂⟩, f₂, s₂, c₂, k₂⟩ := m₂
  simp only [Eqv, eraseMems, MState.mk.injEq, MStore.mk.injEq, and_true]

theorem base_congr {b₁ b₂ : Store} (h : ({ b₁ with mems := [] } : Store) = { b₂ with mems := [] })
    (M : List MemInst) : ({ b₁ with mems := M } : Store) = { b₂ with mems := M } := by
  cases b₁; cases b₂; simp_all

/-- `step_put` on a generic instruction (contract F1), from any state `P` alike the patched one:
`P` steps, alike the patched successor. -/
theorem step_put_generic {m m' P : MState} {ps : List Pos} {ts : List (Pos × TVal)} {F : PMap}
    {i : Instr} {rest : List AInstr} (hP : Eqv P (put ts m)) (hc : m.code = .plain i :: rest)
    (hg : Generic i = true) (hsup : ∀ t ∈ ts, t.1 ∈ ps) (hF : genMap ps i m.stack = some F)
    (h : m.step = some m') : ∃ P', P.step = some P' ∧ Eqv P' (put (move F ts) m') := by
  have hv := toVal_generic hg
  simp only [MState.step, hc, hv, stepPlain_generic m rest hg, Option.map_eq_some_iff] at h
  obtain ⟨⟨S', f', stk', out⟩, hs, rfl⟩ := h
  rw [put_eq, eqv_iff] at hP
  obtain ⟨hPm, hPb, hPf, hPs, hPc, hPk⟩ := hP
  have hget : ∀ x, i = .localGet x → (putLocals ts m.frame.locals)[x]? = m.frame.locals[x]? := by
    rintro x rfl
    apply putLocals_getElem?
    intro t ht h'
    have := hsup t ht
    rw [h'] at this
    simp only [genMap] at hF
    cases hc' : ps.contains (.top x) <;> simp_all
  have hS := instrStep_generic hg hs (P.store.mems.map MMem.abs) (putLocals ts m.frame.locals)
    (length_putLocals ..) hget
  have hf' := instrStep_generic_locals hg hs
  have habs : P.store.abs = { m.store.abs with mems := P.store.mems.map MMem.abs } :=
    base_congr hPb _
  refine ⟨{ P with
      store := { P.store with base := { S' with mems := P.store.mems.map MMem.abs } }
      frame := { f' with locals := relocal i m.stack (putLocals ts m.frame.locals) }
      stack := stk'
      code := out ++ rest }, ?_, ?_⟩
  · simp only [MState.step, hPc, hc, hv, stepPlain_generic _ rest hg]
    rw [habs, hPf, hPs, hS]
    rfl
  · rw [put_eq, eqv_iff]
    rcases genMap_cases hF with ⟨rfl, hid⟩ | ⟨x, v, stk₀, rfl, hstk, rfl⟩
    · simp only [move_some, hid, hf']
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | exact trivial | assumption
    · simp only [putMems_killTop, putCtl_killTop, hf', hstk, relocal, putLocals_set]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | exact trivial | assumption

end FVA.Wasm.Exec.Machine.Oblivious
