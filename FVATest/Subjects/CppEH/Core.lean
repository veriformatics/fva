import FVATest.Subjects.CppEH.Links

/-! The chains of `eh` (contract U28g F3), generic in every twin state: the twin runs enter as
hypotheses (`Proof` supplies them by kernel facts), so checking a chain unfolds no run. -/

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasm.Exec.Machine.Oblivious FVA.Wasi
  FVA.Wasm.Num

namespace Subjects.CppEH

/-- An F segment over twin states given as variables. -/
theorem linkFg {Q : SysOutcome State → Prop} {n : Nat} {σ σ' : State} {T T' : MState}
    {ps qs : List (Option Pos)} {vs : List TVal} (ht : trun md 0 ps n (σ, T) = some qs)
    (hi : T.Inv) (hv : ValsOK vs) (hok : BytesOK (ride ps vs) T.store.mems)
    (hr : sysRun State.exited Xh n (σ, T) = (σ', T', true))
    (hend : SysMust Wd true Q (σ', (put (ride qs vs) T').abs)) :
    SysMust Wd true Q (σ, (put (ride ps vs) T).abs) :=
  sysMust_put ht hi hv hok hr hend

/-- The invariant along a twin run. -/
theorem invOf {n : Nat} {σ σ' : State} {T T' : MState} {b : Bool} (hi : T.Inv)
    (h : sysRun State.exited Xh n (σ, T) = (σ', T', b)) : T'.Inv :=
  sysRun_inv (W := Wd) (wasiHost_ok md 0) n (s := (σ, T)) hi h

theorem valsOK_vv (a b : BitVec 32) : ValsOK (vv a b) := by
  intro b h; simp [vv] at h

theorem valsOK_vvb (a b x : BitVec 32) : ValsOK (vv a b ++ vb x) := by
  intro b h; simp only [vv, vb, List.cons_append, List.nil_append, List.mem_cons, TVal.byte.injEq,
    List.not_mem_nil, or_false, reduceCtorEq, false_or] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ (by norm_num)

theorem bytesOK_pb {ts : List (Pos × TVal)} (hts : ∀ t ∈ ts, ∀ mi a, t.1 ≠ .byte mi a)
    (x : BitVec 32) {mm : MMem} (hb : 70452 ≤ mm.size) : BytesOK (ts ++ ride pb (vb x)) [mm] := by
  refine bytesOK_slots hts ?_
  intro mi a b hmem
  simp only [ride, pb, vb, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
    Pos.byte.injEq, TVal.byte.injEq] at hmem
  rcases hmem with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
    exact ⟨Nat.mod_lt _ (by norm_num), mm, rfl, by omega⟩

theorem size_write_ge {n : Nat} {mm : MMem} (h : n ≤ mm.size) (ea k v : Nat) :
    n ≤ (mm.write ea k v).size := by
  simp only [MMem.size, (MMem.write_fields ..).1]; exact h

/-- The odd chain over abstract twin states: S1a F0 S1c F1a S2 F1b S3 F1c S4a Fbr S4b F1d S6. -/
theorem oddCore {Q : SysOutcome State → Prop} (x : BitVec 32) (hx : x.toNat % 2 = 1)
    (hQ : ∀ σ (s : Store), s.exns.length = 1 →
      Q (.returned σ s [.i32 (ixor x (BitVec.ofNat 32 2779096485))]))
    {S : MStore} {dtW dtE : DefType} {IW IE : ModuleInst} {cW cE : Func}
    (hfW : S.base.funcs[133]? = some (.wasm dtW IW cW))
    (htW : dtW.expand = some ⟨[.num .i32], [.num .i32]⟩) (hdW : cW.localDefaults = [])
    (hbW : cW.body = [.localGet 0, .call 7, .call 132]) (hiW : IW.funcs[7]? = some 7)
    (hfE : S.base.funcs[7]? = some (.wasm dtE IE cE))
    (htE : dtE.expand = some ⟨[.num .i32], [.num .i32]⟩)
    (hdE : cE.localDefaults = [some (.i32 0), some (.i32 0), some (.ref .null)]) (hSi : S.Inv)
    {T5 T11 T15 T1233 T1236 T3264 T3266 T3526 T3532 T3533 T3538 T3741 : MState}
    {σB σC σD σE : State}
    -- S1a + F0
    (h5 : sysRun State.exited Xh 5 (start, MState.ofInvoke S 133 [.i32 1]) = (start, T5, true))
    (c5 : trun md 0 ps1 6 (start, T5) = some ps1)
    (f5 : sysRun State.exited Xh 6 (start, T5) = (start, T11, true))
    -- S1c + F1a
    {C11 : List AInstr} {L11 : List (Option Val)}
    (hc11 : T11.code = .plain (.localGet 0) :: .plain (.iconst .w32 1) ::
      .plain (.ibinop .w32 .and) :: C11)
    (hs11 : T11.stack = []) (hl11 : T11.frame.locals = some (.i32 1) :: L11)
    (s11 : sysRun State.exited Xh 4 (start, T11) = (start, T15, true))
    (c15 : trun md 0 ps1 1218 (start, T15) = some ps1)
    (f15 : sysRun State.exited Xh 1218 (start, T15) = (start, T1233, true))
    -- S2 + F1b
    {C1233 : List AInstr} {L1233 : List (Option Val)} {mm1233 : MMem}
    (hc1233 : T1233.code = .plain (.localGet 0) :: .plain (.store .i32 ⟨2, 0⟩) :: C1233)
    (hs1233 : T1233.stack = [.i32 70448]) (hl1233 : T1233.frame.locals = some (.i32 1) :: L1233)
    (hI1233 : T1233.frame.inst.mems = [0]) (hm1233 : T1233.store.mems = [mm1233])
    (hz1233 : 70452 ≤ mm1233.size)
    (s1233 : sysRun State.exited Xh 3 (start, T1233) = (start, T1236, true))
    (c1236 : trun md 0 (ps1 ++ pb) 2028 (start, T1236) = some (psL ++ pb))
    (f1236 : sysRun State.exited Xh 2028 (start, T1236) = (σB, T3264, true))
    -- S3 + F1c
    (he3264 : State.exited σB = none) {C3264 : List AInstr} {w3264 : Option Val}
    {L3264 : List (Option Val)} {mm3264 : MMem}
    (hc3264 : T3264.code = .plain (.load .i32 ⟨2, 0⟩) :: .plain (.localSet 0) :: C3264)
    (hs3264 : T3264.stack = [.i32 70448]) (hl3264 : T3264.frame.locals = w3264 :: L3264)
    (hI3264 : T3264.frame.inst.mems = [0]) (hm3264 : T3264.store.mems = [mm3264])
    (hz3264 : 70452 ≤ mm3264.size) (hr3264 : mm3264.read 70448 4 = 1)
    (s3264 : sysRun State.exited Xh 2 (σB, T3264) = (σB, T3266, true))
    (c3266 : trun md 0 (ps1 ++ pb) 260 (σB, T3266) = some (ps1 ++ pb))
    (f3266 : sysRun State.exited Xh 260 (σB, T3266) = (σC, T3526, true))
    -- S4a + Fbr
    (he3526 : State.exited σC = none) {C3526 : List AInstr} {L3526 : List (Option Val)}
    {mm3526 : MMem}
    (hc3526 : T3526.code = .plain (.localGet 0) :: .plain (.iconst .w32 2779096485) ::
      .plain (.ibinop .w32 .xor) :: .plain (.localSet 0) :: C3526)
    (hs3526 : T3526.stack = []) (hl3526 : T3526.frame.locals = some (.i32 1) :: L3526)
    (hm3526 : T3526.store.mems = [mm3526]) (hz3526 : 70452 ≤ mm3526.size)
    (s3526 : sysRun State.exited Xh 6 (σC, T3526) = (σC, T3532, true))
    (c3532 : trun md 0 (ps1 ++ pb) 1 (σC, T3532) = some (ps1 ++ pb))
    (f3532 : sysRun State.exited Xh 1 (σC, T3532) = (σD, T3533, true))
    -- S4b + F1d
    (he3533 : State.exited σD = none) {L3533 : List (Option Val)} {r₁ : List AInstr}
    {IW' : ModuleInst} {a : Nat} {dt : DefType} {I : ModuleInst} {cf : Func} {mm3533 : MMem}
    (hc3533 : T3533.code = [.plain (.localGet 0), .plain .return_]) (hs3533 : T3533.stack = [])
    (hl3533 : T3533.frame.locals = some (.i32 2779096484) :: L3533)
    (hk3533 : T3533.ctl = [.label 0 [] [] r₁, .label 1 [] [] [],
      .frame 1 ⟨[some (.i32 1)], IW'⟩ [] [.plain (.call 132)], .label 1 [] [] [],
      .frame 1 ⟨[], {}⟩ [] []])
    (hiW3533 : IW'.funcs[132]? = some a)
    (hf3533 : T3533.store.base.funcs[a]? = some (.wasm dt I cf))
    (ht3533 : dt.expand = some ⟨[], []⟩) (hd3533 : cf.localDefaults = [])
    (hm3533 : T3533.store.mems = [mm3533]) (hz3533 : 70452 ≤ mm3533.size)
    (s3533 : sysRun State.exited Xh 5 (σD, T3533) = (σD, T3538, true))
    (c3538 : trun md 0 (ps2 ++ pb) 203 (σD, T3538) = some (ps2 ++ pb))
    (f3538 : sysRun State.exited Xh 203 (σD, T3538) = (σE, T3741, true))
    -- S6
    (he3741 : State.exited σE = none) {IW'' : ModuleInst}
    (hc3741 : T3741.code = []) (hs3741 : T3741.stack = [])
    (hk3741 : T3741.ctl = [.frame 0 ⟨[some (.i32 1)], IW''⟩ [.i32 2779096484] [],
      .label 1 [] [] [], .frame 1 ⟨[], {}⟩ [] []]) {mm3741 : MMem}
    (hm3741 : T3741.store.mems = [mm3741]) (hz3741 : 70452 ≤ mm3741.size)
    (hn3741 : T3741.store.base.exns.length = 1) :
    SysMust Wd true Q (start, (MState.ofInvoke S 133 [.i32 x]).abs) := by
  -- invariants along the twin
  have i5 := invOf (T := MState.ofInvoke S 133 [.i32 1]) hSi h5
  have i11 := invOf i5 f5
  have i15 := invOf i11 s11
  have i1233 := invOf i15 f15
  have i1236 := invOf i1233 s1233
  have i3264 := invOf i1236 f1236
  have i3266 := invOf i3264 s3264
  have i3526 := invOf i3266 f3266
  have i3532 := invOf i3526 s3526
  have i3533 := invOf i3532 f3532
  have i3538 := invOf i3533 s3533
  have i3741 := invOf i3538 f3538
  -- the twin seams' ends, explicitly (memories for the byte patches)
  have e1236 := runG3 (X := Xh) start_exited hc1233 hs1233 hl1233 hI1233 hm1233 hz1233
  rw [s1233] at e1236
  have hm1236 : T1236.store.mems = [mm1233.write 70448 4 (BitVec.toNat (1 : BitVec 32))] := by
    simp only [Prod.mk.injEq, true_and, and_true] at e1236; rw [e1236]
  have e3266 := runG4 (X := Xh) he3264 hc3264 hs3264 hl3264 hI3264 hm3264 hz3264 hr3264
  rw [s3264] at e3266
  have hm3266 : T3266.store.mems = [mm3264] := by
    simp only [Prod.mk.injEq, true_and, and_true] at e3266; rw [e3266]; exact hm3264
  have e3532 := runG5 (X := Xh) he3526 (by norm_num) hc3526 hs3526 hl3526
    (r := ixor 1 (BitVec.ofNat 32 2779096485)) rfl
  rw [s3526] at e3532
  have hm3532 : T3532.store.mems = [mm3526] := by
    simp only [Prod.mk.injEq, true_and, and_true] at e3532; rw [e3532]; exact hm3526
  have e3538 := runG6 (X := Xh) he3533 hc3533 hs3533 hl3533 hk3533 hiW3533 hf3533 ht3533 hd3533
  rw [s3533] at e3538
  have hm3538 : T3538.store.mems = [mm3533] := by
    simp only [Prod.mk.injEq, true_and, and_true] at e3538; rw [e3538]; exact hm3533
  -- the chain
  refine linkG1 x 1 hfW htW hdW hbW hiW hfE htE hdE hSi h5 ?_
  refine linkFg c5 i5 (valsOK_vv x x) (by simp [BytesOK, ride, ps1, vv]) f5 ?_
  refine linkG2 x 1 (by simp [hx]) hc11 hs11 hl11 i11 s11 ?_
  refine linkFg c15 i15 (valsOK_vv x x) (by simp [BytesOK, ride, ps1, vv]) f15 ?_
  refine linkG3 x hc1233 hs1233 hl1233 hI1233 hm1233 hz1233 i1233 s1233 ?_
  rw [← ride_append ps1 pb (vv x x) (vb x) rfl]
  refine linkFg c1236 i1236 (valsOK_vvb x x x)
    (by rw [ride_append ps1 pb (vv x x) (vb x) rfl, hm1236]
        exact bytesOK_pb (slots_ps1 x x) x (size_write_ge hz1233 _ _ _)) f1236 ?_
  rw [ride_append psL pb (vv x x) (vb x) rfl]
  refine linkG4 x he3264 hc3264 hs3264 hl3264 hI3264 hm3264 hz3264 hr3264 i3264 s3264 ?_
  rw [← ride_append ps1 pb (vv x x) (vb x) rfl]
  refine linkFg c3266 i3266 (valsOK_vvb x x x)
    (by rw [ride_append ps1 pb (vv x x) (vb x) rfl, hm3266]
        exact bytesOK_pb (slots_ps1 x x) x hz3264) f3266 ?_
  rw [ride_append ps1 pb (vv x x) (vb x) rfl]
  refine linkG5 x 1 (by norm_num) (r := ixor x (BitVec.ofNat 32 2779096485)) rfl rfl
    (byteOnly_pb x) he3526 hc3526 hs3526 hl3526 i3526
    (by rw [hm3526]; simpa using bytesOK_pb (ts := []) (by simp) x hz3526) s3526 ?_
  rw [← ride_append ps1 pb (vv _ x) (vb x) rfl]
  refine linkFg c3532 i3532 (valsOK_vvb _ x x)
    (by rw [ride_append ps1 pb (vv _ x) (vb x) rfl, hm3532]
        exact bytesOK_pb (slots_ps1 _ x) x hz3526) f3532 ?_
  rw [ride_append ps1 pb (vv _ x) (vb x) rfl]
  refine linkG6 x 1 _ _ (byteOnly_pb x) he3533 hc3533 hs3533 hl3533 hk3533 hiW3533 hf3533
    ht3533 hd3533 i3533 (by rw [hm3533]; simpa using bytesOK_pb (ts := []) (by simp) x hz3533)
    s3533 ?_
  rw [← ride_append ps2 pb (vv x _) (vb x) rfl]
  refine linkFg c3538 i3538 (valsOK_vvb x _ x)
    (by rw [ride_append ps2 pb (vv x _) (vb x) rfl, hm3538]
        exact bytesOK_pb (slots_ps2 x _) x hz3533) f3538 ?_
  rw [ride_append ps2 pb (vv x _) (vb x) rfl]
  exact linkG7 x _ (byteOnly_pb x) he3741 hc3741 hs3741 hk3741 i3741
    (by rw [hm3741]; simpa using bytesOK_pb (ts := []) (by simp) x hz3741)
    (fun s hs => hQ _ s (by rw [hs]; exact hn3741))

end Subjects.CppEH
