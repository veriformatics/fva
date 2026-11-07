import FVA.Proof.Exec.MachineSys

/-!
# Process claims on toy hosts (contract U27 T6)

Each theorem goes through the system layer the way D28's claim does: machine segments of unique
steps (`machineSegment_sysMust`, `machineRun_sysMust`), host calls over every allowed outcome
(`sysMust_host`), and the finishing rules. `pokeGrow`: a host writes any byte at `L` that the
code never reads again, fitting growth succeeds, the code stores into the new page and returns
42 — for all 256 bytes, the byte kept symbolic through the machine run (no read of its 64-byte
leaf). `exitSeven`: `proc_exit`'s encoding ends the process before the continuation runs.
`hostTrap`: a trapping host call with a live world finishes abnormally. `diverges`: an allowed
divergence refutes `SysMust`.
-/

namespace FVA.Wasm.Exec.SysExamples

open FVA.Wasm FVA.Wasm.Exec Machine

/-- `[] → []`. -/
def unitT : FuncType := ⟨[], []⟩
/-- `[] → [i32]`. -/
def mainT : FuncType := ⟨[], [.num .i32]⟩

/-- An instance of host function 0 (`unitT`) + module function 1 (`mainT`) + memory 0. -/
def inst : ModuleInst := { types := [unitT, mainT], funcs := [0, 1, 2], mems := [0] }

/-- The process's store: host functions 0 and 2 (host ids 0, 1), module function 1 running
`body`, one page of memory, at most 2. -/
def store (body : Expr) (ty : FuncType) : MStore :=
  { base := { funcs := [.host unitT 0, .wasm ty inst ⟨1, [], body⟩, .host unitT 1] },
    mems := [MMem.alloc 1 (some 2)] }

theorem store_inv (body : Expr) (ty : FuncType) : (store body ty).Inv := by
  intro mm hm
  simp only [store, List.mem_singleton] at hm
  subst hm
  exact MMem.alloc_inv 1 (some 2) (by norm_num)

/-! ## Growth + a host with 256 outcomes -/

/-- Where `poke` writes. -/
def L : Nat := 100

/-- Call `poke`, grow by one page, store 7 at the new page's first byte, return 42. -/
def pokeBody : Expr :=
  [.call 0, .iconst .w32 1, .memoryGrow, .drop, .iconst .w32 65536, .iconst .w32 7,
    .storePacked .w32 .p8 ⟨0, 0⟩, .iconst .w32 42]

/-- Every memory with byte `L` set to `b`. -/
def poked (s : Store) (b : Nat) : Store := { s with mems := s.mems.map (·.write L 1 b) }

/-- A call counter; host 0 (`poke`) on no arguments writes any byte at `L` and counts. -/
abbrev pokeWorld : World where
  St := Nat
  host σ τ id s vs o := id = 0 ∧ vs = [] ∧ τ = σ + 1 ∧ ∃ b < 256, o = .returned (poked s b) []
  exited _ := none
  stay h := by
    obtain ⟨-, -, -, b, -, h⟩ := h
    cases h

/-- Returned 42, one host call made. -/
def pokeQ : SysOutcome Nat → Prop
  | .returned σ _ vs => σ = 1 ∧ vs = [.i32 42]
  | _ => False

/-- The run to the host call. -/
def m₁ : MState := ((MState.ofInvoke (store pokeBody mainT) 1 []).runU true 8).1

/-- The machine store after `poke` wrote `b`. -/
def pokedStore (b : Nat) : MStore := { m₁.store with mems := m₁.store.mems.map (·.write L 1 b) }

theorem pokedStore_abs {b : Nat} : (pokedStore b).abs = poked m₁.abs.store b := by
  show _ = poked m₁.store.abs b
  have hm : m₁.store.mems = [MMem.alloc 1 (some 2)] := rfl
  simp only [pokedStore, poked, MStore.abs, hm, List.map_cons, List.map_nil]
  rw [MMem.abs_write (MMem.alloc_inv 1 (some 2) (by norm_num)).1 (by decide)]

/-- The machine has finished with `42` alone. -/
def done42 (m : MState) : Bool :=
  m.code.isEmpty && m.ctl.isEmpty && match m.stack with
    | [.i32 v] => v.toNat == 42
    | _ => false

theorem done42_abs {m : MState} (h : done42 m = true) : m.abs.instrs = vals [.i32 42] := by
  rcases m with ⟨st, f, stk, code, ctl⟩
  simp only [done42, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  match stk, h with
  | [.i32 v], h =>
    have hv : v = 42 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst hv
    rfl

/-- The machine after `poke` wrote `b`. -/
def m₂ (b : Nat) : MState :=
  m₁.hostResume (pokedStore b) [] ((pokeBody.drop 1).map .plain) unitT.params.length

/-- Every byte: the rest of the run returns 42 (the kernel runs the machine per byte; a byte
kept symbolic stalls elaboration at the first trie write after it, the `store8` into the grown
page — U29e states its framing on `MMem` instead). -/
theorem pokeRest : ∀ b < 256, done42 (MState.runU true 12 (m₂ b)).1 = true := by
  decide +kernel

theorem pokeGrow :
    SysMust pokeWorld true pokeQ (0, invokeConfig (store pokeBody mainT).abs 1 []) := by
  rw [← abs_ofInvoke]
  refine machineSegment_sysMust (m' := m₁) (b := ((MState.ofInvoke (store pokeBody mainT) 1
    []).runU true 8).2) (store_inv _ _) rfl rfl ?_
  have hc : m₁.code = .invoke 0 :: (pokeBody.drop 1).map .plain := rfl
  have hf : m₁.store.base.funcs[0]? = some (.host unitT 0) := rfl
  obtain ⟨K, hq, hcont⟩ := abs_host hc hf (Nat.zero_le _)
  refine sysMust_host hq hf rfl ⟨1, .returned (poked m₁.store.abs 0) [], rfl, rfl, rfl, 0,
    by norm_num, rfl⟩ fun τ o hW => ?_
  obtain ⟨-, -, rfl, b, hb, rfl⟩ := hW
  have hk := hcont (pokedStore b) []
  simp only [Ref.hostStore, Ref.HCtx.result, vals, List.map_nil]
  rw [← pokedStore_abs, ← hk]
  refine machineSegment_sysMust (n := 12) (m' := ((m₂ b).runU true 12).1)
    (b := ((m₂ b).runU true 12).2) ?_ rfl rfl ?_
  · intro mm hm
    simp only [MState.hostResume, pokedStore, List.mem_map] at hm
    obtain ⟨mm₀, hm₀, rfl⟩ := hm
    have hm₁ : m₁.store.mems = [MMem.alloc 1 (some 2)] := rfl
    rw [hm₁, List.mem_singleton] at hm₀
    subst hm₀
    exact MMem.write_inv (MMem.alloc_inv 1 (some 2) (by norm_num)) (by decide) b
  · exact sysMust_returned rfl (done42_abs (pokeRest b hb)) ⟨rfl, rfl⟩

/-! ## Exit, host trap, divergence -/

/-- A call counter and an exit; host 0 counts, host 1 = `proc_exit 7` (trap carrier, exit
marked). -/
abbrev exitWorld : World where
  St := Nat × Option Nat
  host σ τ id s vs o :=
    (id = 0 ∧ vs = [] ∧ τ = (σ.1 + 1, σ.2) ∧ o = .returned s []) ∨
      (id = 1 ∧ vs = [] ∧ τ = (σ.1, some 7) ∧ o = .trapped s)
  exited σ := σ.2
  stay h := by
    rcases h with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> cases h

/-- The executable host of `exitWorld`. -/
def exitHost (σ : Nat × Option Nat) (id : Nat) (s : MStore) (vs : List Val) :
    Option ((Nat × Option Nat) × MStore × MHostOut) :=
  if vs = [] then
    if id = 0 then some ((σ.1 + 1, σ.2), s, .returned [])
    else if id = 1 then some ((σ.1, some 7), s, .trapped) else none
  else none

theorem exitHost_ok : HostOK exitWorld exitHost := by
  intro σ id s args τ ms r hx hi
  unfold exitHost at hx
  split at hx
  · next hv =>
    subst hv
    split at hx
    · next h0 =>
      subst h0
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      refine ⟨hi, .inl ⟨rfl, rfl, rfl, rfl⟩, fun τ' o h => ?_⟩
      rcases h with ⟨-, -, h1, h2⟩ | ⟨h, -⟩
      · exact ⟨h1, h2⟩
      · cases h
    · next h0 =>
      split at hx
      · next h1 =>
        subst h1
        simp only [Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl, rfl⟩ := hx
        refine ⟨hi, .inr ⟨rfl, rfl, rfl, rfl⟩, fun τ' o h => ?_⟩
        rcases h with ⟨h, -⟩ | ⟨-, -, h1, h2⟩
        · cases h
        · exact ⟨h1, h2⟩
      · cases hx
  · cases hx

/-- Count, exit 7, then a count + `unreachable` that never run. -/
def exitBody : Expr := [.call 0, .iconst .w32 0, .drop, .call 2, .call 0, .unreachable]

/-- Exited 7 after exactly one count: the continuation never ran. -/
def exitQ : SysOutcome (Nat × Option Nat) → Prop
  | .exited σ _ k => σ = (1, some 7) ∧ k = 7
  | _ => False

theorem exitSeven :
    SysMust exitWorld true exitQ ((0, none), invokeConfig (store exitBody unitT).abs 1 []) := by
  rw [← abs_ofInvoke]
  refine machineRun_sysMust (n := 20) exitHost_ok (σ' := (1, some 7))
    (m' := (sysRun exitWorld.exited exitHost 20 ((0, none),
      MState.ofInvoke (store exitBody unitT) 1 [])).2.1)
    (b := (sysRun exitWorld.exited exitHost 20 ((0, none),
      MState.ofInvoke (store exitBody unitT) 1 [])).2.2) (store_inv _ _) rfl ?_
  exact sysMust_exited rfl ⟨rfl, rfl⟩

/-- An exited process takes no step, even at a `nop`. -/
theorem exited_nop (s : Store) (f : Frame) (y : exitWorld.St × Config) (fits : Bool) :
    ¬ SysStep exitWorld fits ((0, some 7), ⟨s, f, [.plain .nop]⟩) y :=
  exited_no_step (k := 7) rfl

/-- Host 0 traps, the world live. -/
abbrev trapWorld : World where
  St := Unit
  host _ _ id s vs o := id = 0 ∧ vs = [] ∧ o = .trapped s
  exited _ := none
  stay h := by
    obtain ⟨-, -, h⟩ := h
    cases h

/-- The executable host of `trapWorld`. -/
def trapHost (_ : Unit) (id : Nat) (s : MStore) (vs : List Val) :
    Option (Unit × MStore × MHostOut) :=
  if id = 0 ∧ vs = [] then some ((), s, .trapped) else none

theorem trapHost_ok : HostOK trapWorld trapHost := by
  intro σ id s args τ ms r hx hi
  unfold trapHost at hx
  split at hx
  · next h =>
    obtain ⟨rfl, rfl⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl, rfl⟩ := hx
    exact ⟨hi, ⟨rfl, rfl, rfl⟩, fun τ' o h => ⟨rfl, h.2.2⟩⟩
  · cases hx

/-- Finished abnormally. -/
def trapQ : SysOutcome Unit → Prop
  | .abnormal _ _ => True
  | _ => False

theorem hostTrap :
    SysMust trapWorld true trapQ ((), invokeConfig (store [.call 0] unitT).abs 1 []) := by
  rw [← abs_ofInvoke]
  refine machineRun_sysMust (n := 6) trapHost_ok
    (m' := (sysRun trapWorld.exited trapHost 6 ((),
      MState.ofInvoke (store [.call 0] unitT) 1 [])).2.1)
    (b := (sysRun trapWorld.exited trapHost 6 ((),
      MState.ofInvoke (store [.call 0] unitT) 1 [])).2.2) (store_inv _ _) rfl ?_
  exact sysMust_trap rfl rfl trivial

/-- Host 0 may diverge. -/
abbrev divergeWorld : World where
  St := Unit
  host σ τ id _ vs o := id = 0 ∧ vs = [] ∧ τ = σ ∧ o = .diverged
  exited _ := none
  stay h := h.2.2.1

theorem diverges (Q : SysOutcome Unit → Prop) (fits : Bool) :
    ¬ SysMust divergeWorld fits Q ((), invokeConfig (store [] unitT).abs 0 []) :=
  host_diverged_not_must (W := divergeWorld) (σ := ()) (τ := ()) (a := 0) (args := [])
    (k := .seq [] .hole []) (ft := unitT) (id := 0) rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩

-- contract U27 E1: the standard three axioms alone, through every layer each theorem uses
#print axioms pokeGrow
#print axioms exitSeven
#print axioms hostTrap
#print axioms diverges
#print axioms machineRun_must
#print axioms sysStep_restrict_total
#print axioms host_free_iff

end FVA.Wasm.Exec.SysExamples
