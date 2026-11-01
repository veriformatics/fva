import FVATest.Subjects.Lz4C.Accept

/-! # One-clause R1 mutation: exclude the last byte of the destination's write range -/

namespace Subjects.Lz4C.Refute.LastWrite

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref Accept

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
attribute [local irreducible] alloc initConfig store0

/-- R1 with only the destination write bound changed from `< dst + length` to
`< dst + length - 1`; the last destination byte is wrongly excluded. -/
def Mutant : Prop :=
  ∀ (src dst : Nat) (input initDst : List UInt8),
    131072 ≤ src → src + input.length ≤ 2097152 →
    131072 ≤ dst → dst + initDst.length ≤ 2097152 →
    input.length < 2 ^ 31 → initDst.length < 2 ^ 31 →
    (input = [] ∨ initDst = [] ∨ src + input.length ≤ dst ∨ dst + initDst.length ≤ src) →
    let ps := [Prep.write src input, .write dst initDst]
    let args := [Val.i32 (BitVec.ofNat 32 src), .i32 (BitVec.ofNat 32 dst),
      .i32 (BitVec.ofNat 32 input.length), .i32 (BitVec.ofNat 32 initDst.length)]
    (∀ H, ∃ s inst, Prepared Lifted.module H ps s inst) ∧
      ∀ H s inst, Prepared Lifted.module H ps s inst →
        CallWithin H s inst "LZ4_decompress_safe" args
          (fun _ a => a < 131072 ∨ 2097152 ≤ a ∨
            (src ≤ a ∧ a < src + input.length) ∨ (dst ≤ a ∧ a < dst + initDst.length))
          (fun _ a => a < 131072 ∨ 2097152 ≤ a ∨ (dst ≤ a ∧ a < dst + initDst.length - 1)) ∧
        CallReturns H s inst "LZ4_decompress_safe" args
          (fun _ vs => ∃ result : BitVec 32, vs = [.i32 result])

theorem write_reached : (walk 457 matched.config).isSome := by decide +kernel

noncomputable def atWrite : Config := (walk 457 matched.config).get write_reached

/-- The reachable store writes address 196620, the last byte of the 13-byte destination. -/
theorem access_write : access atWrite = some ⟨true, 0, 196620, 1⟩ := by kernel_rfl

theorem writes_last : Writes atWrite 0 (matched.dst + matched.initDst.length - 1) :=
  writes_iff.mpr ⟨⟨true, 0, 196620, 1⟩, access_write, rfl, rfl, by decide, by decide⟩

/-- A concrete run of the shipped decoder writes the byte the mutant excludes. -/
theorem refuted : ¬ Mutant := by
  intro hm
  let H : HostSem := fun _ _ _ _ => False
  have h := (hm matched.src matched.dst matched.input matched.initDst
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    H matched.store alloc.2 (matched.prepared matched_prep H)
  obtain ⟨a, ha, -, hth⟩ := h.1
  have he : alloc.2.exportFunc "LZ4_decompress_safe" = some 2 := by decide +kernel
  have ha2 : a = 2 := Option.some.inj (ha.symm.trans he)
  subst a
  have hs : Steps H matched.config atWrite :=
    steps_of_walk (Option.some_get write_reached).symm
  have hw := (hth atWrite hs).2 0 (matched.dst + matched.initDst.length - 1) writes_last
  exact (by decide : ¬ (matched.dst + matched.initDst.length - 1 < 131072 ∨
    2097152 ≤ matched.dst + matched.initDst.length - 1 ∨
      (matched.dst ≤ matched.dst + matched.initDst.length - 1 ∧
        matched.dst + matched.initDst.length - 1 < matched.dst + matched.initDst.length - 1))) hw

end Subjects.Lz4C.Refute.LastWrite
