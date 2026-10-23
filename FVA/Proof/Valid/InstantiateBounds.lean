import FVA.Proof.Valid.InstantiateLists

namespace FVA.Wasm.Valid.BoundsWitness

open FVA.Wasm FVA.Wasm.Exec

/-- A symbolic payload size exposes the vector bound without allocating an oversized list. -/
def module (n : Nat) : Module :=
  { mems := [⟨0, none⟩]
    datas := [⟨List.replicate n 0, .active 0 [.iconst .w32 0]⟩] }

/-- Oversized active segments fail validity before allocation synthesizes their lengths. -/
theorem invalid (n : Nat) (hn : 2 ^ 32 ≤ n) : ¬ModuleValid (module n) := by
  intro hm
  have hl := hm.dataLengths ⟨List.replicate n 0, .active 0 [.iconst .w32 0]⟩ (by simp [module])
  exact Nat.not_lt.mpr hn (by simpa using hl)

theorem untypable (C : Context) (st : StackType) (n : Nat) (hn : 2 ^ 32 ≤ n) :
    ¬SeqT C (initCode (module n)) st := by
  intro h
  have hm : Instr.iconst .w32 n ∈ initCode (module n) := by
    simp [module, initCode, runData]
  obtain ⟨_, hi⟩ := InitProof.seq_member h _ hm
  cases hi with
  | iconst hb => exact Nat.not_lt.mpr hn hb

end FVA.Wasm.Valid.BoundsWitness
