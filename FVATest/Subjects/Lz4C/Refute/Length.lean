import FVATest.Subjects.Lz4C.Accept

/-! # One-clause R2 mutation: return `c.length + 1` instead of `c.length` -/

namespace Subjects.Lz4C.Refute.Length

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref Accept

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
attribute [local irreducible] alloc initConfig store0

/-- R2 with only the returned-length clause changed to `c.length + 1`. -/
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
        ∀ c, Lz4.Valid input c → c.length ≤ initDst.length →
          (1 ≤ initDst.length ∨ input = [0]) →
          CallReturns H s inst "LZ4_decompress_safe" args
            (fun s' vs => vs = [.i32 (BitVec.ofNat 32 (c.length + 1))] ∧ Holds s' dst c)

/-- The literal block returns 1 on the shipped bytes, not the mutant's 2. -/
theorem refuted : ¬ Mutant := by
  intro hm
  let H : HostSem := fun _ _ _ _ => False
  have h := (hm literal.src literal.dst literal.input literal.initDst
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    H literal.store alloc.2 (literal.prepared literal_prep H) [0x61]
    literal_valid (by decide) (by decide)
  obtain ⟨a, ha, -, hm⟩ := h
  have he : alloc.2.exportFunc "LZ4_decompress_safe" = some 2 := by decide +kernel
  have ha2 : a = 2 := Option.some.inj (ha.symm.trans he)
  subst a
  have hs : Steps H literal.config literalFinal :=
    steps_of_runDet (Option.some_get literal_run).symm literal_result
  have ho := hm.outcome hs (o := .returned literalFinal.store [.i32 1]) ⟨rfl, literal_result⟩
  exact (by decide : ([Val.i32 1] : List Val) ≠ [.i32 2]) ho.1

end Subjects.Lz4C.Refute.Length
