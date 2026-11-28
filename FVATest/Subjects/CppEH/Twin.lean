import FVATest.Subjects.CppEH.Core

/-! The twin runs of `eh` (contract U28g F2/F3): the instantiated subject, the process run of
`eh x0` for the twin inputs 1 (odd) and 0 (even), and the kernel-checked facts at every cut + the
`trun` certificate of every oblivious segment. Each fact re-runs its twin prefix in the kernel. -/

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasm.Exec.Machine.Oblivious FVA.Wasi
  FVA.Wasm.Num

set_option maxRecDepth 100000

namespace Subjects.CppEH

theorem instU : (instantiateU 100000 (hostMStore md) md (hostImports md)).isSome = true := by
  decide +kernel

/-- The machine store + instance every launch starts from. -/
@[irreducible] noncomputable def inst : MStore × ModuleInst :=
  (instantiateU 100000 (hostMStore md) md (hostImports md)).get instU

theorem inst_eq :
    instantiateU 100000 (hostMStore md) md (hostImports md) = some (inst.1, inst.2) := by
  unfold inst; simp

theorem mems_ok : ∀ lim ∈ md.mems, lim.min ≤ 2 ^ 16 := by decide +kernel

theorem inst_inv : inst.1.Inv := instantiateU_inv (hostMStore_inv md) mems_ok inst_eq

/-- `n` transitions of the process calling `eh x`. -/
noncomputable def run (n : Nat) (x : BitVec 32) : State × MState × Bool :=
  sysRun State.exited Xh n (start, MState.ofInvoke inst.1 133 [.i32 x])

theorem run_inv (n : Nat) (x : BitVec 32) : (run n x).2.1.Inv := by
  have h : sysRun Wd.exited Xh n (start, MState.ofInvoke inst.1 133 [.i32 x]) =
      ((run n x).1, (run n x).2.1, (run n x).2.2) := by rw [wd_exited]; rfl
  exact sysRun_inv (wasiHost_ok md 0) n (s := (start, MState.ofInvoke inst.1 133 [.i32 x]))
    (show (MState.ofInvoke inst.1 133 [.i32 x]).Inv from inst_inv) h

/-- A twin run continued from a cut where it used all its fuel. -/
theorem run_add {a : Nat} (b : Nat) {x : BitVec 32} {σ : State} {m : MState}
    (h : run a x = (σ, m, true)) : run (a + b) x = sysRun State.exited Xh b (σ, m) :=
  sysRun_add a b h

/-- A cut's twin facts make the next cut's run equation: `run (a + b)` = the seam's twin end. -/
theorem run_seam {a b : Nat} {x : BitVec 32} {σ : State} {m m' : MState}
    (h : run a x = (σ, m, true)) (hs : sysRun State.exited Xh b (σ, m) = (σ, m', true)) :
    run (a + b) x = (σ, m', true) :=
  (run_add b h).trans hs

/-! ## F links -/

/-- An F segment: a `trun` certificate on the twin carries `SysMust` from its patched end back
to its patched start. -/
theorem linkF {Q : SysOutcome State → Prop} {a n : Nat} {x0 : BitVec 32} {σ σ' : State}
    {ps qs : List (Option Pos)} {vs : List TVal}
    (ht : trun md 0 ps n (σ, (run a x0).2.1) = some qs) (hv : ValsOK vs)
    (hok : BytesOK (ride ps vs) (run a x0).2.1.store.mems)
    (hra : run a x0 = (σ, (run a x0).2.1, true))
    (hrb : run (a + n) x0 = (σ', (run (a + n) x0).2.1, true))
    (hend : SysMust Wd true Q (σ', (put (ride qs vs) (run (a + n) x0).2.1).abs)) :
    SysMust Wd true Q (σ, (put (ride ps vs) (run a x0).2.1).abs) :=
  sysMust_put ht (run_inv a x0) hv hok ((run_add n hra).symm.trans hrb) hend

/-! ## Twin facts (kernel) -/

/-- A function instance's parts (defaults off a wasm function). -/
def fwasm : Option FuncInst → DefType × ModuleInst × Func
  | some (.wasm d i c) => (d, i, c)
  | _ => (⟨[], 0⟩, {}, ⟨0, [], []⟩)

/-- A label's leftover code (defaults off a label). -/
def labRest : Ctl → List AInstr
  | .label _ _ _ r => r
  | _ => []

/-- A frame entry's caller instance (defaults off a frame). -/
def frmInst : Ctl → ModuleInst
  | .frame _ f _ _ => f.inst
  | _ => {}

theorem instF :
    (inst.1.base.funcs[133]?, (fwasm inst.1.base.funcs[133]?).1.expand,
      (fwasm inst.1.base.funcs[133]?).2.2.localDefaults, (fwasm inst.1.base.funcs[133]?).2.2.body,
      (fwasm inst.1.base.funcs[133]?).2.1.funcs[7]?, inst.1.base.funcs[7]?,
      (fwasm inst.1.base.funcs[7]?).1.expand, (fwasm inst.1.base.funcs[7]?).2.2.localDefaults) =
    (some (.wasm (fwasm inst.1.base.funcs[133]?).1 (fwasm inst.1.base.funcs[133]?).2.1
        (fwasm inst.1.base.funcs[133]?).2.2), some ⟨[.num .i32], [.num .i32]⟩, [],
      [.localGet 0, .call 7, .call 132], some 7,
      some (.wasm (fwasm inst.1.base.funcs[7]?).1 (fwasm inst.1.base.funcs[7]?).2.1
        (fwasm inst.1.base.funcs[7]?).2.2), some ⟨[.num .i32], [.num .i32]⟩,
      [some (.i32 0), some (.i32 0), some (.ref .null)]) := by
  kernel_rfl

theorem tw11 (x0 : BitVec 32) (hx0 : x0 = 1 ∨ x0 = 0) :
    ((run 11 x0).1, (run 11 x0).2.2, (run 11 x0).2.1.code, (run 11 x0).2.1.stack,
      (run 11 x0).2.1.frame.locals) =
    (start, true, .plain (.localGet 0) :: .plain (.iconst .w32 1) :: .plain (.ibinop .w32 .and) ::
        (run 11 x0).2.1.code.drop 3, [], some (.i32 x0) :: (run 11 x0).2.1.frame.locals.tail) := by
  rcases hx0 with rfl | rfl <;> kernel_rfl

/-- Cut 1233 (S2's start). -/
theorem tw1233 :
    ((run 1233 1).1, (run 1233 1).2.2, (run 1233 1).2.1.code, (run 1233 1).2.1.stack,
      (run 1233 1).2.1.frame.locals, (run 1233 1).2.1.frame.inst.mems, (run 1233 1).2.1.store.mems,
      decide (70452 ≤ (run 1233 1).2.1.store.mems.head!.size)) =
    (start, true,
      .plain (.localGet 0) :: .plain (.store .i32 ⟨2, 0⟩) :: (run 1233 1).2.1.code.drop 2,
      [.i32 70448], some (.i32 1) :: (run 1233 1).2.1.frame.locals.tail, [0],
      [(run 1233 1).2.1.store.mems.head!], true) := by
  kernel_rfl

/-- Cut 3264 (S3's start, past the host call). -/
theorem tw3264 :
    (State.exited (run 3264 1).1, (run 3264 1).2.2, (run 3264 1).2.1.code, (run 3264 1).2.1.stack,
      (run 3264 1).2.1.frame.locals, (run 3264 1).2.1.frame.inst.mems, (run 3264 1).2.1.store.mems,
      decide (70452 ≤ (run 3264 1).2.1.store.mems.head!.size ∧
        (run 3264 1).2.1.store.mems.head!.read 70448 4 = 1)) =
    (none, true, .plain (.load .i32 ⟨2, 0⟩) :: .plain (.localSet 0) :: (run 3264 1).2.1.code.drop 2,
      [.i32 70448], (run 3264 1).2.1.frame.locals.head! :: (run 3264 1).2.1.frame.locals.tail, [0],
      [(run 3264 1).2.1.store.mems.head!], true) := by
  kernel_rfl

/-- Cut 3526 (S4a's start). -/
theorem tw3526 :
    (State.exited (run 3526 1).1, (run 3526 1).2.2, (run 3526 1).2.1.code, (run 3526 1).2.1.stack,
      (run 3526 1).2.1.frame.locals, (run 3526 1).2.1.store.mems,
      decide (70452 ≤ (run 3526 1).2.1.store.mems.head!.size)) =
    (none, true, .plain (.localGet 0) :: .plain (.iconst .w32 2779096485) ::
        .plain (.ibinop .w32 .xor) :: .plain (.localSet 0) :: (run 3526 1).2.1.code.drop 4,
      [], some (.i32 1) :: (run 3526 1).2.1.frame.locals.tail,
      [(run 3526 1).2.1.store.mems.head!], true) := by
  kernel_rfl

/-- Cut 3533 (S4b's start). -/
theorem tw3533 :
    (State.exited (run 3533 1).1, (run 3533 1).2.2, (run 3533 1).2.1.code, (run 3533 1).2.1.stack,
      (run 3533 1).2.1.frame.locals, (run 3533 1).2.1.ctl,
      (frmInst ((run 3533 1).2.1.ctl.getD 2 (.label 0 [] [] []))).funcs[132]?,
      (run 3533 1).2.1.store.base.funcs[132]?,
      (fwasm (run 3533 1).2.1.store.base.funcs[132]?).1.expand,
      (fwasm (run 3533 1).2.1.store.base.funcs[132]?).2.2.localDefaults,
      (run 3533 1).2.1.store.mems, decide (70452 ≤ (run 3533 1).2.1.store.mems.head!.size)) =
    (none, true, [.plain (.localGet 0), .plain .return_], [],
      some (.i32 2779096484) :: (run 3533 1).2.1.frame.locals.tail,
      [.label 0 [] [] (labRest ((run 3533 1).2.1.ctl.getD 0 (.label 0 [] [] []))),
        .label 1 [] [] [],
        .frame 1 ⟨[some (.i32 1)], frmInst ((run 3533 1).2.1.ctl.getD 2 (.label 0 [] [] []))⟩ []
          [.plain (.call 132)], .label 1 [] [] [], .frame 1 ⟨[], {}⟩ [] []],
      some 132,
      some (.wasm (fwasm (run 3533 1).2.1.store.base.funcs[132]?).1
        (fwasm (run 3533 1).2.1.store.base.funcs[132]?).2.1
        (fwasm (run 3533 1).2.1.store.base.funcs[132]?).2.2),
      some ⟨[], []⟩, [], [(run 3533 1).2.1.store.mems.head!], true) := by
  kernel_rfl

/-- Cut 3741 (S6's start). -/
theorem tw3741 :
    (State.exited (run 3741 1).1, (run 3741 1).2.2, (run 3741 1).2.1.code, (run 3741 1).2.1.stack,
      (run 3741 1).2.1.ctl, (run 3741 1).2.1.store.mems,
      decide (70452 ≤ (run 3741 1).2.1.store.mems.head!.size),
      (run 3741 1).2.1.store.base.exns.length) =
    (none, true, [], [],
      [.frame 0 ⟨[some (.i32 1)], frmInst ((run 3741 1).2.1.ctl.getD 0 (.label 0 [] [] []))⟩
          [.i32 2779096484] [], .label 1 [] [] [], .frame 1 ⟨[], {}⟩ [] []],
      [(run 3741 1).2.1.store.mems.head!], true, 1) := by
  kernel_rfl

/-! ## Certificates (kernel) -/

theorem cert5 : trun md 0 ps1 6 (start, (run 5 1).2.1) = some ps1 := by kernel_rfl
theorem cert15 : trun md 0 ps1 1218 (start, (run 15 1).2.1) = some ps1 := by kernel_rfl
theorem cert1236 : trun md 0 (ps1 ++ pb) 2028 (start, (run 1236 1).2.1) = some (psL ++ pb) := by
  kernel_rfl
theorem cert3266 :
    trun md 0 (ps1 ++ pb) 260 ((run 3264 1).1, (run 3266 1).2.1) = some (ps1 ++ pb) := by kernel_rfl
theorem cert3532 :
    trun md 0 (ps1 ++ pb) 1 ((run 3526 1).1, (run 3532 1).2.1) = some (ps1 ++ pb) := by kernel_rfl
theorem cert3538 :
    trun md 0 (ps2 ++ pb) 203 ((run 3533 1).1, (run 3538 1).2.1) = some (ps2 ++ pb) := by kernel_rfl


theorem run_cut {k : Nat} {x0 : BitVec 32} {σ : State} (h1 : (run k x0).1 = σ)
    (h2 : (run k x0).2.2 = true) : run k x0 = (σ, (run k x0).2.1, true) := by
  rw [← h1, ← h2]

/-- A seam's twin run fixes the twin at the seam's end. -/
theorem twinEnd {a b : Nat} {x0 : BitVec 32} {σ : State} {m R : MState}
    (h : run a x0 = (σ, m, true)) (hs : sysRun State.exited Xh b (σ, m) = (σ, R, true)) :
    sysRun State.exited Xh b (σ, m) = (σ, (run (a + b) x0).2.1, true) ∧
      run (a + b) x0 = (σ, (run (a + b) x0).2.1, true) ∧ (run (a + b) x0).2.1 = R := by
  have e := run_seam h hs
  rw [e]; exact ⟨hs, rfl, rfl⟩

/-! ## The even chain (twin x = 0) -/

/-- Cut 20 (S4′a's start, even twin). -/
theorem tw20 :
    ((run 20 0).1, (run 20 0).2.2, (run 20 0).2.1.code, (run 20 0).2.1.stack,
      (run 20 0).2.1.frame.locals) =
    (start, true, .plain (.localGet 0) :: .plain (.iconst .w32 1) :: .plain (.ibinop .w32 .or) ::
        .plain (.localSet 0) :: (run 20 0).2.1.code.drop 4, [],
      some (.i32 0) :: (run 20 0).2.1.frame.locals.tail) := by
  kernel_rfl

/-- Cut 27 (S4′b's start, even twin). -/
theorem tw27 :
    ((run 27 0).1, (run 27 0).2.2, (run 27 0).2.1.code, (run 27 0).2.1.stack,
      (run 27 0).2.1.frame.locals, (run 27 0).2.1.ctl,
      (frmInst ((run 27 0).2.1.ctl.getD 2 (.label 0 [] [] []))).funcs[132]?,
      (run 27 0).2.1.store.base.funcs[132]?,
      (fwasm (run 27 0).2.1.store.base.funcs[132]?).1.expand,
      (fwasm (run 27 0).2.1.store.base.funcs[132]?).2.2.localDefaults) =
    (start, true, [.plain (.localGet 0), .plain .return_], [],
      some (.i32 1) :: (run 27 0).2.1.frame.locals.tail,
      [.label 0 [] [] (labRest ((run 27 0).2.1.ctl.getD 0 (.label 0 [] [] []))), .label 1 [] [] [],
        .frame 1 ⟨[some (.i32 0)], frmInst ((run 27 0).2.1.ctl.getD 2 (.label 0 [] [] []))⟩ []
          [.plain (.call 132)], .label 1 [] [] [], .frame 1 ⟨[], {}⟩ [] []],
      some 132,
      some (.wasm (fwasm (run 27 0).2.1.store.base.funcs[132]?).1
        (fwasm (run 27 0).2.1.store.base.funcs[132]?).2.1
        (fwasm (run 27 0).2.1.store.base.funcs[132]?).2.2),
      some ⟨[], []⟩, []) := by
  kernel_rfl

/-- Cut 235 (S6′'s start, even twin). -/
theorem tw235 :
    ((run 235 0).1, (run 235 0).2.2, (run 235 0).2.1.code, (run 235 0).2.1.stack,
      (run 235 0).2.1.ctl, (run 235 0).2.1.store.base.exns.length) =
    (start, true, [], [],
      [.frame 0 ⟨[some (.i32 0)], frmInst ((run 235 0).2.1.ctl.getD 0 (.label 0 [] [] []))⟩
          [.i32 1] [], .label 1 [] [] [], .frame 1 ⟨[], {}⟩ [] []], 0) := by
  kernel_rfl

theorem cert5e : trun md 0 ps1 6 (start, (run 5 0).2.1) = some ps1 := by kernel_rfl
theorem cert15e : trun md 0 ps1 5 (start, (run 15 0).2.1) = some ps1 := by kernel_rfl
theorem cert26e : trun md 0 ps1 1 (start, (run 26 0).2.1) = some ps1 := by kernel_rfl
theorem cert32e : trun md 0 ps2 203 (start, (run 32 0).2.1) = some ps2 := by kernel_rfl

end Subjects.CppEH
