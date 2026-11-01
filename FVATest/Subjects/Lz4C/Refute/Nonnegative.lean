import FVATest.Subjects.Lz4C.Accept

/-! # One-clause R3 mutation: require its conclusion even for negative error results -/

namespace Subjects.Lz4C.Refute.Nonnegative

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref Accept

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
attribute [local irreducible] alloc initConfig store0

/-- R3 with only the `0 ≤ result.toInt` premise removed. -/
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
        CallReturns H s inst "LZ4_decompress_safe" args (fun s' vs =>
          ∃ result : BitVec 32, vs = [.i32 result] ∧
            (result.toInt ≤ (initDst.length : Int) ∧
              ∃ ss last content, Lz4.ParsesAny input ss last ∧
                (Lz4.decode ss []).map (· ++ last) = some content ∧
                content.length = result.toInt.toNat ∧ Holds s' dst content))

/-- A token for one literal without that literal cannot parse, even with offset 0 allowed. -/
theorem malformed_not_parses (ss : List Lz4.Seq) (last : List UInt8) :
    ¬ Lz4.ParsesAny malformed.input ss last := by
  rintro ⟨low, hlo, hbytes, -⟩
  change [0x10] = ss.flatMap Lz4.Seq.bytes ++ Lz4.head last low at hbytes
  have hlen := congrArg List.length hbytes
  cases ss with
  | nil =>
    have hlast : last = [] := by
      cases last with
      | nil => rfl
      | cons b bs =>
        simp only [List.flatMap_nil, List.nil_append, Lz4.head, List.length_cons,
          List.length_append, List.length_nil] at hlen
        omega
    subst last
    have ht : (0x10 : UInt8) = UInt8.ofNat low := by
      simpa [Lz4.head, Lz4.ext] using hbytes
    have hn := congrArg UInt8.toNat ht
    change (16 : Nat) = low % 256 at hn
    have hl : low % 256 = low := Nat.mod_eq_of_lt (by omega)
    omega
  | cons s ss =>
    simp only [List.flatMap_cons, List.length_append, Lz4.Seq.bytes, Lz4.head,
      List.length_cons, List.length_nil] at hlen
    omega

/-- The malformed input returns −2; applying R3 without its sign guard would make it parse. -/
theorem refuted : ¬ Mutant := by
  intro hm
  let H : HostSem := fun _ _ _ _ => False
  have h := (hm malformed.src malformed.dst malformed.input malformed.initDst
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    H malformed.store alloc.2 (malformed.prepared malformed_prep H)
  obtain ⟨a, ha, -, hm⟩ := h
  have he : alloc.2.exportFunc "LZ4_decompress_safe" = some 2 := by decide +kernel
  have ha2 : a = 2 := Option.some.inj (ha.symm.trans he)
  subst a
  have hs : Steps H malformed.config malformedFinal :=
    steps_of_runDet (Option.some_get malformed_run).symm malformed_result
  obtain ⟨result, -, -, ss, last, content, hp, -⟩ :=
    hm.outcome hs (o := .returned malformedFinal.store [.i32 (-2)]) ⟨rfl, malformed_result⟩
  exact malformed_not_parses ss last hp

end Subjects.Lz4C.Refute.Nonnegative
