import FVA.Proof.Wasi.Host
import FVA.Proof.Exec.Process

/-!
# Launch canonicalization + the run bridge (contract U29b T3, public API)

`launch_canonical` (T3): where `instantiateU` succeeds on `hostMStore m`, every `Launch` of `m` at
an export starts from its store and uses its exported memory. `launch_of_instantiateU` (T3(iii))
builds a `Launch` from that run. `launch_sysMust` = the endpoint → `SysMust` bridge consumers
use: a machine run of the launched export under `wasiHost m mem none` (`sysRun`) transfers
`SysMust` under `E` from the state it stops in to every launch of `m`.
-/

namespace FVA.Wasi

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine

theorem hostMStore_inv (m : Module) : (hostMStore m).Inv := fun _ h => by
  simp [hostMStore] at h

theorem hostMStore_abs (m : Module) : (hostMStore m).abs = hostStore m := rfl

/-- T3: where `instantiateU` succeeds, every launch of `m` at `name` is its configuration, with its
exported memory. -/
theorem launch_canonical {m : Module} {fuel : Nat} {ms : MStore} {inst : ModuleInst}
    (h : instantiateU fuel (hostMStore m) m (hostImports m) = some (ms, inst)) {name : String}
    {a : Nat} (ha : inst.exportFunc name = some a) {args : List Val} {c : Config} {mem : Nat}
    (hl : Launch m name args c mem) :
    c = invokeConfig ms.abs a args ∧ inst.exportMem "memory" = some mem := by
  obtain ⟨hv, -, -, -, -, s, inst', a', hI, hmem, ha', -, rfl⟩ := hl
  obtain ⟨rfl, rfl⟩ := instantiateU_unique (hostMStore_inv m) hv h hI
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  exact ⟨rfl, hmem⟩

/-- T3(iii): `instantiateU`'s result launches `m` at `name` once `Launch`'s static conditions and
the call's argument conditions hold. -/
theorem launch_of_instantiateU {m : Module} {fuel : Nat} {ms : MStore} {inst : ModuleInst}
    (h : instantiateU fuel (hostMStore m) m (hostImports m) = some (ms, inst))
    (hv : Valid.ModuleValid m) (hs : m.start = none)
    (hinit : ∀ ex ∈ m.exports, ex.name ≠ "_initialize")
    (hfun : ∀ im ∈ m.imports, ∃ x, im.desc = .func x)
    (hbind : ∀ id im, m.imports[id]? = some im → im.module = "wasi_snapshot_preview1" →
      (Call.ofName im.name).isSome → (bind m id).isSome)
    (hm : ImportsMatch (hostStore m) m (hostImports m)) {name : String} {a : Nat}
    (ha : inst.exportFunc name = some a) {mem : Nat} (hmem : inst.exportMem "memory" = some mem)
    {args : List Val} (hok : InvokeOK ms.abs a args) :
    Launch m name args (invokeConfig ms.abs a args) mem :=
  ⟨hv, hs, hinit, hfun, hbind, ms.abs, inst, a,
    instantiate_sound (H := NoHost) (hostMStore_inv m) (mems_fit hv) hm
      (instantiateU_instantiate h),
    hmem, ha, hok, rfl⟩

/-- The run bridge: a machine run of the export `instantiateU` launches, under the WASI host
without random bytes, transfers `SysMust` under `E` from where it stops to every launch. -/
theorem launch_sysMust {m : Module} {fuel : Nat} {ms : MStore} {inst : ModuleInst}
    (h : instantiateU fuel (hostMStore m) m (hostImports m) = some (ms, inst)) {name : String}
    {a : Nat} (ha : inst.exportFunc name = some a) {mem : Nat}
    (hmem : inst.exportMem "memory" = some mem) {args : List Val}
    {Q : SysOutcome State → Prop} {n : Nat} {σ σ' : State} {m' : MState} {b : Bool}
    (hrun : sysRun State.exited (wasiHost m mem none) n (σ, MState.ofInvoke ms a args) =
      (σ', m', b))
    (hend : SysMust ((world m mem).restrict (E m mem)) true Q (σ', m'.abs)) :
    ∀ c mem', Launch m name args c mem' →
      SysMust ((world m mem').restrict (E m mem')) true Q (σ, c) := by
  intro c mem' hl
  obtain ⟨rfl, hmem'⟩ := launch_canonical h ha hl
  obtain rfl : mem = mem' := Option.some.inj (hmem.symm.trans hmem')
  have hi : (MState.ofInvoke ms a args).Inv :=
    instantiateU_inv (hostMStore_inv m) (mems_fit hl.1) h
  rw [← abs_ofInvoke]
  exact machineRun_sysMust (wasiHost_ok m mem) n hi hrun hend

end FVA.Wasi
