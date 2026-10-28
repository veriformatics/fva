import Proofs.Artifact

namespace Artifact

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem zeroCapacity (m : Memory) (src dst size : Nat)
    (hsrc : src ≠ 0) (hbound : src < 2097152) :
    execute decoder m src dst size 0 =
      some (if size = 1 then (if byte m src = 0 then 0 else word - 1) else word - 1,
            m, if size = 1 then [src] else []) := by
  by_cases hn : size = 1
  · subst size
    by_cases hb : byte m src = 0
    · simp [execute, decoder, run, primitive, initial, finish, flag, signed,
        word, hsrc, hbound, hb]
    · simp [execute, decoder, run, primitive, initial, finish, flag, signed,
        word, hsrc, hbound, hb]
  · simp [execute, decoder, run, primitive, initial, finish, flag, signed,
      word, hsrc, hn]

theorem zeroInput (m : Memory) (src dst cap : Nat)
    (hsrc : src ≠ 0) (hcap : cap < 2147483648) (hne : cap ≠ 0) :
    execute decoder m src dst 0 cap = some (word - 1, m, []) := by
  simp [execute, decoder, run, primitive, initial, finish, flag, signed,
    word, hsrc, hcap, hne]

theorem emptyBlock (m : Memory) (src dst : Nat)
    (hsrc : src ≠ 0) (hbound : src < 2097152) (hbyte : byte m src = 0) :
    execute decoder m src dst 1 0 = some (0, m, [src]) := by
  simpa [hbyte] using zeroCapacity m src dst 1 hsrc hbound

theorem zeroCapacityConverse (m finalMemory : Memory) (reads : List Nat)
    (src dst size r : Nat)
    (hsrc : src ≠ 0) (hbound : src < 2097152)
    (hr : r < 2147483648)
    (hexec : execute decoder m src dst size 0 =
      some (r, finalMemory, reads)) :
    size = 1 ∧ byte m src = 0 ∧ r = 0 ∧ finalMemory = m ∧ reads = [src] := by
  rw [zeroCapacity m src dst size hsrc hbound] at hexec
  by_cases hn : size = 1
  · simp only [hn, ↓reduceIte] at hexec
    by_cases hb : byte m src = 0
    · simp only [hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hexec
      exact ⟨hn, hb, hexec.1.symm, hexec.2.1.symm, hexec.2.2.symm⟩
    · simp only [hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hexec
      have he : r = word - 1 := hexec.1.symm
      subst r
      contradiction
  · simp only [hn, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hexec
    have he : r = word - 1 := hexec.1.symm
    subst r
    contradiction

end Artifact
