import FVATest.Subjects.EdgerCpm.LoaderData

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

-- Infer the lifted constant; direct quotients avoid the data list's repeated division chain.
noncomputable def dataPacking : {v : Nat // dataBytes = Binary.leBytes 20236 v} := by
  exact ⟨_, rfl⟩

noncomputable def dataByte (i : Nat) : UInt8 :=
  if i < 20236 then UInt8.ofNat (dataPacking.val / 256 ^ i) else 0

theorem leBytes_getElem? (n v i : Nat) :
    (Binary.leBytes n v)[i]? =
      if i < n then some (UInt8.ofNat (v / 256 ^ i)) else none := by
  induction n generalizing v i with
  | zero => simp [Binary.leBytes]
  | succ n ih =>
    cases i with
    | zero =>
      simp only [Binary.leBytes, List.getElem?_cons_zero, Nat.zero_lt_succ, ite_true,
        Nat.pow_zero, Nat.div_one, Option.some.injEq]
      exact UInt8.ofNat_mod_size
    | succ i =>
      simpa [Binary.leBytes, Nat.pow_succ', Nat.div_div_eq_div_mul] using ih (v / 256) i

theorem dataByte_eq (i : Nat) : dataBytes[i]! = dataByte i := by
  rw [dataPacking.property, List.getElem!_eq_getElem?_getD, leBytes_getElem?]
  by_cases hi : i < 20236
  · simp [hi, dataByte]
  · simp only [ite_eq_right hi, Option.getD_none, dataByte]
    rfl

end Subjects.EdgerCpm.Existence
