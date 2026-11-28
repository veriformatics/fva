import FVA.Proof.Exec.Seam

/-! Seams of `eh` (contract U28g F2): one run equation per instruction shape the input crosses.
Each takes the seam's start state `M` as a variable with facts about its projections, so the
kernel unfolds no twin state; a twin instantiates `M` with kernel-checked facts (`Twin`). -/

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasm.Exec.Machine.Oblivious FVA.Wasi

namespace Subjects.CppEH

theorem sysRun_succ_elim {St : Type} {exited : St → Option Nat}
    {X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut)} (n : Nat)
    (s : St × MState) :
    sysRun exited X (n + 1) s =
      (sysNext exited X s).elim (s.1, s.2, false) (sysRun exited X n) := by
  rw [sysRun_succ]; cases sysNext exited X s <;> rfl

@[simp] theorem abs_withBase (s : MStore) : ({ s with base := s.abs } : MStore).abs = s.abs := by
  obtain ⟨b, ms⟩ := s
  simp [MStore.abs]

@[simp] theorem abs_funcs (s : MStore) : s.abs.funcs = s.base.funcs := rfl

variable {St : Type} {exited : St → Option Nat}
  {X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut)} {σ : St}

/-- G3 (S2): `local.get 0; i32.store` with the payload address on the stack. -/
theorem runG3 (he : exited σ = none) {M : MState} {L : List (Option Val)} {v : BitVec 32}
    {mm : MMem} {C : List AInstr}
    (hc : M.code = .plain (.localGet 0) :: .plain (.store .i32 ⟨2, 0⟩) :: C)
    (hs : M.stack = [.i32 70448]) (hl : M.frame.locals = some (.i32 v) :: L)
    (hI : M.frame.inst.mems = [0]) (hm : M.store.mems = [mm]) (hb : 70452 ≤ mm.size) :
    sysRun exited X 3 (σ, M) =
      (σ, { M with
        store := ⟨M.store.abs, [mm.write 70448 4 v.toNat]⟩
        stack := []
        code := C }, true) := by
  have hx : v.toNat < 4294967296 := v.isLt
  have hb' : ¬ mm.size < 70452 := by omega
  simp [he, MState.hostCall, MState.uniq, MState.admin, Ref.toVal, Val.instr, hx,
    Ref.instrUnique, MState.step, MState.stepPlain, Ref.instrStep, MState.mem0, hI, MState.setMem,
    MState.cont, Val.numBits, NumType.bytes, hb', sysRun, hc, hs, hl, hm]

/-- The simp set every seam run unfolds with. -/
macro "seam_simp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [sysRun_succ_elim, sysNext, MState.hostCall, MState.uniq, MState.admin, Ref.toVal,
    Val.instr, Ref.instrUnique, MState.step, MState.stepPlain, Ref.instrStep, Ref.numStep, numOut,
    MState.mem0, MState.setMem, MState.cont, MState.invoke, Val.numBits, NumType.bytes, NumType.val,
    retPop, brPop, sysRun, $hs,*])

/-- G1 (S1a): the launch `invoke 133` of the wrapper (`local.get 0; call 7; call 132`) through
`call 7`'s invoke: the input moves from the operand stack into eh's local 0 and the wrapper's. -/
theorem runG1 (he : exited σ = none) {S : MStore} {x : BitVec 32} {dtW dtE : DefType}
    {IW IE : ModuleInst} {cW cE : Func}
    (hfW : S.base.funcs[133]? = some (.wasm dtW IW cW))
    (htW : dtW.expand = some ⟨[.num .i32], [.num .i32]⟩) (hdW : cW.localDefaults = [])
    (hbW : cW.body = [.localGet 0, .call 7, .call 132]) (hiW : IW.funcs[7]? = some 7)
    (hfE : S.base.funcs[7]? = some (.wasm dtE IE cE))
    (htE : dtE.expand = some ⟨[.num .i32], [.num .i32]⟩)
    (hdE : cE.localDefaults = [some (.i32 0), some (.i32 0), some (.ref .null)]) :
    sysRun exited X 5 (σ, MState.ofInvoke S 133 [.i32 x]) =
      (σ, { store := { S with base := S.abs }
            frame := ⟨[some (.i32 x), some (.i32 0), some (.i32 0), some (.ref .null)], IE⟩
            stack := []
            code := cE.body.map .plain
            ctl := [.label 1 [] [] [], .frame 1 ⟨[some (.i32 x)], IW⟩ [] [.plain (.call 132)],
              .label 1 [] [] [], .frame 1 ⟨[], {}⟩ [] []] }, true) := by
  have hx : x.toNat < 4294967296 := x.isLt
  seam_simp [MState.ofInvoke, he, hx, hfW, htW, hdW, hbW, hiW, hfE, htE, hdE]

/-- G2 (S1c): `local.get 0; i32.const 1; i32.and` → the parity as the next code value. -/
theorem runG2 (he : exited σ = none) {M : MState} {L : List (Option Val)} {v r : BitVec 32}
    {C : List AInstr}
    (hc : M.code = .plain (.localGet 0) :: .plain (.iconst .w32 1) ::
      .plain (.ibinop .w32 .and) :: C)
    (hs : M.stack = []) (hl : M.frame.locals = some (.i32 v) :: L)
    (hop : ibinop .and v (BitVec.ofNat 32 1) = some r) :
    sysRun exited X 4 (σ, M) =
      (σ, { M with
        store := { M.store with base := M.store.abs }
        stack := []
        code := (Val.i32 r).instr :: C }, true) := by
  have hx : v.toNat < 4294967296 := v.isLt
  seam_simp [he, hx, hc, hs, hl, hop]

/-- G4 (S3): `i32.load` from the payload, `local.set 0`. -/
theorem runG4 (he : exited σ = none) {M : MState} {w : Option Val} {L : List (Option Val)}
    {mm : MMem} {C : List AInstr} {n : Nat}
    (hc : M.code = .plain (.load .i32 ⟨2, 0⟩) :: .plain (.localSet 0) :: C)
    (hs : M.stack = [.i32 70448]) (hl : M.frame.locals = w :: L)
    (hI : M.frame.inst.mems = [0]) (hm : M.store.mems = [mm]) (hb : 70452 ≤ mm.size)
    (hr : mm.read 70448 4 = n) :
    sysRun exited X 2 (σ, M) =
      (σ, { M with
        store := { M.store with base := M.store.abs }
        frame := { M.frame with locals := some (.i32 (BitVec.ofNat 32 n)) :: L }
        stack := []
        code := C }, true) := by
  have hb' : ¬ mm.size < 70452 := by omega
  seam_simp [he, hc, hs, hl, hI, hm, hb', hr]

/-- G5 (S4a, S4′a): `local.get 0; i32.const k; <op>; local.set 0`. -/
theorem runG5 (he : exited σ = none) {M : MState} {L : List (Option Val)} {v r : BitVec 32}
    {k : Nat} {op : IBinOp} {C : List AInstr} (hk : k < 4294967296)
    (hc : M.code = .plain (.localGet 0) :: .plain (.iconst .w32 k) :: .plain (.ibinop .w32 op) ::
      .plain (.localSet 0) :: C)
    (hs : M.stack = []) (hl : M.frame.locals = some (.i32 v) :: L)
    (hop : ibinop op v (BitVec.ofNat 32 k) = some r) :
    sysRun exited X 6 (σ, M) =
      (σ, { M with
        store := { M.store with base := M.store.abs }
        frame := { M.frame with locals := some (.i32 r) :: L }
        stack := []
        code := C }, true) := by
  have hx : v.toNat < 4294967296 := v.isLt
  have hr : r.toNat < 4294967296 := r.isLt
  seam_simp [he, hx, hr, hk, hc, hs, hl, hop]

/-- G6 (S4b, S4′b): `local.get 0; return` to the wrapper, its `call 132` + invoke: the result
lands in the wrapper frame entry's saved operands. -/
theorem runG6 (he : exited σ = none) {M : MState} {L : List (Option Val)} {r : BitVec 32}
    {n₁ n₂ : Nat} {c₁ c₂ : List Instr} {s₁ s₂ : List Val} {r₁ r₂ : List AInstr} {FW : Frame}
    {K : List Ctl} {a : Nat} {dt : DefType} {I : ModuleInst} {cf : Func}
    (hc : M.code = [.plain (.localGet 0), .plain .return_]) (hs : M.stack = [])
    (hl : M.frame.locals = some (.i32 r) :: L)
    (hk : M.ctl = .label n₁ c₁ s₁ r₁ :: .label n₂ c₂ s₂ r₂ ::
      .frame 1 FW [] [.plain (.call 132)] :: K)
    (hiW : FW.inst.funcs[132]? = some a) (hf : M.store.base.funcs[a]? = some (.wasm dt I cf))
    (ht : dt.expand = some ⟨[], []⟩) (hd : cf.localDefaults = []) :
    sysRun exited X 5 (σ, M) =
      (σ, { M with
        store := { M.store with base := M.store.abs }
        frame := ⟨[], I⟩
        stack := []
        code := cf.body.map .plain
        ctl := .label 0 [] [] [] :: .frame 0 FW [.i32 r] [] :: K }, true) := by
  have hx : r.toNat < 4294967296 := r.isLt
  seam_simp [he, hx, hc, hs, hl, hk, hiW, hf, ht, hd]

/-- G7 (S6): the dtors frame exit, the wrapper's label + frame exits: the saved result returns. -/
theorem runG7 (he : exited σ = none) {M : MState} {v : Val} {FW FD : Frame}
    (hc : M.code = []) (hs : M.stack = [])
    (hk : M.ctl = [.frame 0 FW [v] [], .label 1 [] [] [], .frame 1 FD [] []]) :
    sysRun exited X 3 (σ, M) =
      (σ, { M with frame := FD, stack := [v], code := [], ctl := [] }, true) := by
  seam_simp [he, hc, hs, hk]

end Subjects.CppEH
