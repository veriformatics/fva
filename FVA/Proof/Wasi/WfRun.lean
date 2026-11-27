import FVA.Proof.Wasi.Wf

/-!
# T7: every call keeps `Wf` (U29a)

`run_wf`: on a well-formed state, every successful `run` under an admissible choice yields a
well-formed state; `exec_wf` lifts it to `exec` (failures + `proc_exit` keep the descriptors,
nodes and clocks).
-/

namespace FVA.Wasi

open FVA.Wasm FVA.Wasm.Exec

theorem nextIno_fresh (σ : State) : σ.nextIno ∉ σ.nodes.map (·.ino) := by
  intro h
  unfold State.nextIno at h
  cases hm : (σ.nodes.map (·.ino)).max? with
  | none => simp_all
  | some m =>
    rw [hm] at h
    have := List.le_max?_getD_of_mem (l := σ.nodes.map (·.ino)) h (k := 0)
    rw [hm] at this
    simp at this

theorem nextFd_fresh {σ : State} (hw : σ.Wf) : σ.nextFd ∉ σ.fds.map (·.1) := by
  intro h
  unfold State.nextFd at h
  cases hf : σ.free.max? with
  | some f =>
    rw [hf] at h
    simp only [Option.getD_some] at h
    obtain ⟨⟨k, d⟩, hk, rfl⟩ := List.mem_map.mp h
    exact (hw.2.2.1 _ hk).2.1 (List.max?_mem hf)
  | none =>
    rw [hf] at h
    simp only [Option.getD_none] at h
    cases hm : (σ.fds.map (·.1)).max? with
    | none => simp_all
    | some m =>
      rw [hm] at h
      have := List.le_max?_getD_of_mem (l := σ.fds.map (·.1)) h (k := 0)
      rw [hm] at this
      simp at this

theorem isDir_of_dirDesc {σ : State} (hw : σ.Wf) {fd n : Nat} {pre : Option Bytes}
    {fl b i : Nat} (h : σ.desc fd = some ⟨.dir n pre, fl, b, i⟩) : σ.isDir n = true :=
  desc_ok hw h

/-- The directory a path call's descriptor names. -/
theorem dirOf_ok {σ : State} (hw : σ.Wf) {fd bit dn : Nat}
    (h : (match σ.desc fd with
      | some ⟨.dir n _, _, b, _⟩ => if has b bit then .ok n else .error Errno.notcapable
      | _ => .error Errno.badf : Except Nat Nat) = .ok dn) : σ.isDir dn = true := by
  split at h
  · rename_i n pre fl b i hd
    split at h
    · cases h; exact isDir_of_dirDesc hw hd
    · simp at h
  · simp at h

theorem head_mem {st : List Nat} (h : st ≠ []) : st.headD 0 ∈ st := by
  cases st <;> simp_all

/-- A new descriptor over a well-formed state with the same descriptors as `σ`. -/
theorem open_wf {σ σ' : State} (hw' : σ'.Wf) (hfds : σ'.fds = σ.fds) (hfree : σ'.free = σ.free)
    {ch : Choice} {r : Req} (hc : ChoiceOK σ r ch) {k : Kind} (hk : Desc.Ok σ' ⟨k, 0, 0, 0⟩)
    {rb ri ff : Nat} {τ : State} {ws : List (Nat × Bytes)} (out : Nat)
    (h : (let fd := ch.fd.getD σ.nextFd
      if 2 ^ 31 ≤ fd then .error Errno.mfile else
      let (b, i) := ch.rights.getD (rb, ri)
      .ok ({ σ' with fds := (fd, ⟨k, ff, b, i⟩) :: σ'.fds, free := σ'.free.erase fd },
        [(out, le 4 fd)]) : Except Nat (State × List (Nat × Bytes))) = .ok (τ, ws)) : τ.Wf := by
  have hn : σ.nextFd = σ'.nextFd := by simp only [State.nextFd, hfds, hfree]
  rw [hn] at h
  simp only at h
  split at h
  · simp at h
  · rename_i hlt
    rw [ok_fst h]
    refine wf_open hw' ?_ (by omega) hk
    cases hf : ch.fd with
    | none => simpa using nextFd_fresh hw'
    | some f => simpa [hfds, hf] using (hc.2.2.1 f hf).2

theorem run_wf {σ : State} (hw : σ.Wf) {r : Req} {ch : Choice} (hc : ChoiceOK σ r ch)
    {τ : State} {ws : List (Nat × Bytes)} (h : run σ r ch = .ok (τ, ws)) : τ.Wf := by
  have hc' := hc
  obtain ⟨-, hcount, -, htime, hino, -, -⟩ := hc'
  rcases r with ⟨call, a, iovs, data, path⟩
  cases call <;> simp only [run] at h
  case argsGet => rw [ok_fst h]; exact hw
  case environGet => rw [ok_fst h]; exact hw
  case argsSizesGet | environSizesGet =>
    simp only [run.sizes] at h
    split at h
    · simp at h
    · rw [ok_fst h]; exact hw
  case clockTimeGet =>
    split at h
    · rename_i t ht
      rw [ok_fst h]; exact wf_clock hw _ t (htime t ht).1
    · split at h
      · rw [ok_fst h]; exact hw
      · simp at h
  case fdClose =>
    split at h
    · rename_i d hd
      rw [ok_fst h]; exact wf_close hw (desc_key hd)
    · simp at h
  case fdFdstatGet | fdPrestatGet | fdPrestatDirName | randomGet | procExit =>
    repeat (first | (rw [ok_fst h]; exact hw) | simp at h | split at h)
  case fdFdstatSetFlags =>
    cases hd : σ.desc (a.getD 0 0) with
    | none => rw [hd] at h; simp at h
    | some d =>
      rcases d with ⟨kind, flg, b, inh⟩
      cases kind with
      | stream k t => rw [hd] at h; simp at h
      | dir n p => rw [hd] at h; simp at h
      | file n pos =>
        simp only [hd] at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · rw [ok_fst h]; have hok := desc_ok hw hd; exact wf_setDesc hw hok
  case fdRead =>
    cases hd : σ.desc (a.getD 0 0) with
    | none => rw [hd] at h; simp at h
    | some d =>
      rcases d with ⟨kind, flg, b, inh⟩
      cases kind with
      | stream k t =>
        rcases k with _ | k
        · simp only [hd] at h
          split at h
          · simp at h
          · split at h
            · simp at h
            · rw [ok_fst h]; exact wf_streams hw rfl rfl rfl rfl rfl
        · rw [hd] at h; simp at h
      | dir n p => rw [hd] at h; simp at h
      | file n pos =>
        simp only [hd] at h
        split at h
        · simp at h
        split at h
        · simp at h
        · rw [ok_fst h]
          have hok := desc_ok hw hd
          have hL := data_len hw n
          have hk : ch.count.getD (min (firstLen iovs) ((σ.data n).length - pos)) ≤
              (σ.data n).length - pos := by
            cases hcc : ch.count with
            | none => simp
            | some k =>
              have := (hcount k hcc).1
              simp only [maxCount, hd] at this
              simp only [Option.getD_some]; omega
          exact wf_setDesc hw ⟨hok.1, by have := hok.2; omega⟩
  case fdSeek =>
    cases hd : σ.desc (a.getD 0 0) with
    | none => rw [hd] at h; simp at h
    | some d =>
      rcases d with ⟨kind, flg, b, inh⟩
      cases kind with
      | stream k t => rw [hd] at h; simp at h
      | dir n p => rw [hd] at h; simp at h
      | file n pos =>
        simp only [hd] at h
        repeat' (first | (simp at h; done) | split at h)
        all_goals (rw [ok_fst h]; exact wf_setDesc hw ⟨(desc_ok hw hd).1, by omega⟩)
  case fdWrite =>
    cases hd : σ.desc (a.getD 0 0) with
    | none => rw [hd] at h; simp at h
    | some d =>
      rcases d with ⟨kind, flg, b, inh⟩
      cases kind with
      | stream k t =>
        simp only [hd] at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · rw [ok_fst h]
            split <;> exact wf_streams hw rfl rfl rfl rfl rfl
      | dir n p => rw [hd] at h; simp at h
      | file n pos =>
        simp only [hd] at h
        have hok := desc_ok hw hd
        have hL := data_len hw n
        have hpos := hok.2
        have hmax : ∀ k, ch.count = some k → k ≤ 2 ^ 64 - 1 -
            (if flag flg Fdflags.append = true then (σ.data n).length else pos) := by
          intro k hk
          have := (hcount k hk).1
          simp only [maxCount, hd] at this
          omega
        by_cases hf : flag flg Fdflags.append = true <;>
          simp only [hf, ↓reduceIte, Bool.false_eq_true] at h hmax
        -- three error branches (rights, E's append limit, E's positioned limit); the `if c = 0`
        -- inside the success state stays for the size bound
        all_goals
          split at h
          · simp at h
          split at h
          · simp at h
          split at h
          · simp at h
          rw [ok_fst h]
          refine wf_setDesc (wf_setFile hw hok.1 _ ?_) ⟨?_, ?_⟩
          · split
            · exact hL
            · simp only [List.length_append, List.length_take, List.length_replicate,
                List.length_drop]
              cases hcc : ch.count with
              | none => simp only [Option.getD_none, fileMax]; omega
              | some k => simp only [Option.getD_some]; have := hmax k hcc; omega
          · rw [(setBody_file σ hok.1 _ n).2.2]; exact hok.1
          · cases hcc : ch.count with
            | none => simp only [Option.getD_none, fileMax]; omega
            | some k => simp only [Option.getD_some]; have := hmax k hcc; omega
  case pathCreateDirectory =>
    obtain ⟨dn, hdn, h⟩ := bind_ok h
    obtain ⟨⟨st, c, sl⟩, hres, h⟩ := bind_ok h
    obtain ⟨tg, htg, h⟩ := bind_ok h
    cases tg with
    | some _ => simp at h
    | none =>
      obtain ⟨σ'', hcr, h⟩ := bind_ok h
      rw [ok_fst h]
      obtain ⟨hst, hdirs, hc0, h47, hnul⟩ := resolve_spec hres (dirOf_ok hw hdn)
      obtain ⟨hc1, hc2, hnot⟩ := target_none htg
      split at hcr
      · simp at hcr
      split at hcr
      · simp at hcr
      rename_i hex
      obtain rfl := Except.ok.inj hcr
      refine wf_create hw (hdirs _ (head_mem hst)) ⟨hc0, h47, hnul, hc1, hc2⟩ hnot ?_ ?_
        (Or.inr rfl)
      · cases hi : ch.ino with
        | none => simpa using nextIno_fresh σ
        | some i => simpa using (hino i hi).2
      · cases hi : ch.ino with
        | none => simp only [hi, true_and, not_le] at hex; simpa using hex
        | some i => simpa using (hino i hi).1
  case pathRemoveDirectory | pathUnlinkFile =>
    obtain ⟨dn, hdn, h⟩ := bind_ok h
    obtain ⟨⟨st, c, sl⟩, hres, h⟩ := bind_ok h
    obtain ⟨hst, hdirs, -, -, -⟩ := resolve_spec hres (dirOf_ok hw hdn)
    obtain ⟨tg, -, h⟩ := bind_ok h
    repeat' (first | (simp at h; done) | split at h)
    all_goals
      rw [ok_fst h]
      exact wf_setDir hw (hdirs _ (head_mem hst)) (List.filter_sublist)
  case pathFilestatGet =>
    obtain ⟨dn, -, h⟩ := bind_ok h
    obtain ⟨⟨st, c, sl⟩, -, h⟩ := bind_ok h
    obtain ⟨tg, -, h⟩ := bind_ok h
    cases tg with
    | none => simp at h
    | some n =>
      simp only at h
      split at h
      · simp at h
      · rw [ok_fst h]; exact hw
  case pathOpen =>
    cases hd : σ.desc (a.getD 0 0) with
    | none => rw [hd] at h; simp at h
    | some d =>
      rcases d with ⟨kind, flg, b, inh⟩
      cases kind with
      | stream k t => rw [hd] at h; simp at h
      | file n pos => rw [hd] at h; simp at h
      | dir dn pre =>
        simp only [hd] at h
        have hdn : σ.isDir dn = true := desc_ok hw hd
        split at h
        · simp at h
        · split at h
          · simp at h
          split at h
          · simp at h
          · obtain ⟨⟨st, c, sl⟩, hres, h⟩ := bind_ok h
            obtain ⟨hst, hdirs, hc0, h47, hnul⟩ := resolve_spec hres hdn
            obtain ⟨tg, htg, h⟩ := bind_ok h
            cases tg with
            | some n =>
              obtain ⟨hn, -⟩ := target_some hw htg hst hdirs
              simp only at h
              split at h
              · simp at h
              · split at h
                · rename_i hdir
                  split at h
                  · simp at h
                  · exact open_wf (σ := σ) (σ' := σ) (k := .dir n none) hw rfl rfl hc hdir _ h
                · rename_i hdir
                  have hfile := isFile_of_not_isDir hn (by simpa using hdir)
                  split at h
                  · simp at h
                  · by_cases ht : flag (a.getD 4 0) Oflags.trunc = true
                    · simp only [ht, ↓reduceIte] at h
                      exact open_wf (σ := σ) (σ' := σ.setBody n (.file [])) (k := .file n 0)
                        (wf_setFile hw hfile [] (by simp)) rfl rfl hc
                        ⟨by rw [(setBody_file σ hfile [] n).2.2]; exact hfile, by simp⟩ _ h
                    · simp only [ht, ↓reduceIte, Bool.false_eq_true] at h
                      exact open_wf (σ := σ) (σ' := σ) (k := .file n 0) hw rfl rfl hc
                        ⟨hfile, by simp⟩
                        _ h
            | none =>
              obtain ⟨hc1, hc2, hnot⟩ := target_none htg
              simp only at h
              split at h
              · simp at h
              · split at h
                · simp at h
                · obtain ⟨σ'', hcr, h⟩ := bind_ok h
                  have hp := hdirs _ (head_mem hst)
                  split at hcr
                  · simp at hcr
                  split at hcr
                  · simp at hcr
                  rename_i hex
                  obtain rfl := Except.ok.inj hcr
                  have hino' : ch.ino.getD σ.nextIno ∉ σ.nodes.map (·.ino) := by
                    cases hi : ch.ino with
                    | none => simpa using nextIno_fresh σ
                    | some i => simpa using (hino i hi).2
                  have hino64 : ch.ino.getD σ.nextIno < 2 ^ 64 := by
                    cases hi : ch.ino with
                    | none => simp only [hi, true_and, not_le] at hex; simpa using hex
                    | some i => simpa using (hino i hi).1
                  have hw' := wf_create hw hp ⟨hc0, h47, hnul, hc1, hc2⟩ hnot hino' hino64
                    (b := .file []) (Or.inl rfl)
                  refine open_wf (σ := σ) (k := .file σ.nodes.length 0) hw' rfl rfl hc ?_ _ h
                  refine ⟨?_, by simp⟩
                  simp [State.isFile, setBody_length]

/-- T7: on a well-formed state every `exec` outcome under an admissible choice is well formed
(failures and `proc_exit` keep descriptors, nodes, roots and clocks). -/
theorem exec_wf {σ : State} (hw : σ.Wf) (c : Call) (s : Store) (mem : Nat) (vs : List Val)
    (ch : Choice) (hc : ChoiceOK σ (reqOf c s mem vs) ch) : (exec σ c s mem vs ch).1.Wf := by
  unfold exec
  split
  · rename_i m a hm ha
    have hreq : reqOf c s mem vs = decode c m a := by simp [reqOf, hm, ha]
    rw [hreq] at hc
    have hstep : (step σ (decode c m a) ch).1.Wf := by
      unfold step
      split
      · exact wf_streams hw rfl rfl rfl rfl rfl
      · split
        · exact hw
        · split
          · rename_i τ ws hr; exact run_wf hw hc hr
          · exact hw
    split
    · next τ ws heq => rw [heq] at hstep; exact hstep
    · next τ e heq => rw [heq] at hstep; exact hstep
    · next τ k heq => rw [heq] at hstep; exact hstep
  · exact hw

theorem initFds_mem {roots : List (Bytes × Nat)} {e : Nat × Desc} (he : e ∈ initFds roots) :
    (e.1 < 3 ∧ ∃ k t b i, e.2 = ⟨.stream k t, 0, b, i⟩ ∧ k < 3) ∨
      ∃ i, ∃ h : i < roots.length, e.1 = 3 + i ∧ e.2.kind = .dir roots[i].2 (some roots[i].1) := by
  simp only [initFds, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_mapIdx] at he
  rcases he with (rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  · exact Or.inl ⟨by decide, _, _, _, _, rfl, by decide⟩
  · exact Or.inl ⟨by decide, _, _, _, _, rfl, by decide⟩
  · exact Or.inl ⟨by decide, _, _, _, _, rfl, by decide⟩
  · exact Or.inr ⟨i, hi, rfl, rfl⟩

theorem initFds_keys_nodup (roots : List (Bytes × Nat)) : ((initFds roots).map (·.1)).Nodup := by
  simp only [initFds, List.map_append, List.map_cons, List.map_nil]
  rw [List.nodup_append]
  refine ⟨by decide, ?_, ?_⟩
  · rw [List.nodup_iff_injective_getElem]
    intro i j hij
    simp only [List.getElem_map, List.getElem_mapIdx] at hij
    exact Fin.ext (by omega)
  · intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [List.mem_map, List.mem_mapIdx] at hy
    obtain ⟨_, ⟨i, -, rfl⟩, rfl⟩ := hy
    omega

/-- T7: the next process of a pipeline is well formed (fresh descriptors over the same roots). -/
theorem spawn_wf {σ : State} (hw : σ.Wf) (args : List Bytes) (hr : σ.roots.length + 3 < 2 ^ 31) :
    (σ.spawn args).Wf := by
  obtain ⟨-, -, -, -, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  refine ⟨initFds_keys_nodup _, List.nodup_nil, ?_, by simp [State.spawn], h5, h6, h7, h8, h9,
    h10, h11, by simpa [State.spawn] using h12, ?_⟩
  · intro e he
    rcases initFds_mem he with ⟨hk, k, t, b, i, hd, hk3⟩ | ⟨i, hi, hk, hd⟩
    · refine ⟨by omega, by simp [State.spawn], ?_⟩
      unfold Desc.Ok; rw [hd]; exact hk3
    · refine ⟨by omega, by simp [State.spawn], ?_⟩
      unfold Desc.Ok; rw [hd]; exact h5 _ (List.getElem_mem _)
  · intro x hx
    simp only [State.spawn] at hx
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact h13 x hx
      · exact Nat.two_pow_pos 64
    · exact Nat.two_pow_pos 64

instance (σ : State) (d : Desc) : Decidable (d.Ok σ) := by
  unfold Desc.Ok; split <;> infer_instance

instance (n : Bytes) : Decidable (Name.Ok n) := by unfold Name.Ok; infer_instance

set_option synthInstance.maxSize 512 in
set_option synthInstance.maxHeartbeats 200000 in
instance (σ : State) : Decidable σ.Wf := by unfold State.Wf; infer_instance

end FVA.Wasi
