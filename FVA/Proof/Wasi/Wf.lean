import FVA.Spec.Wasi.World

/-!
# `State.Wf` is preserved (U29a T7)

On a well-formed state, every outcome of an in-profile call under any admissible choice is well
formed. `Wf` reads five fields alone (descriptors, free numbers, nodes, roots, clocks), so each
call reduces to a few state changes: a descriptor's offset or flags, a closed descriptor, a clock
reading, a file's contents, a directory losing entries, a new node, a new descriptor.
-/

namespace FVA.Wasi

open FVA.Wasm FVA.Wasm.Exec

/-! ## Frame: `Wf` reads five fields -/

theorem wf_congr {σ τ : State} (h1 : τ.fds = σ.fds) (h2 : τ.free = σ.free)
    (h3 : τ.nodes = σ.nodes) (h4 : τ.roots = σ.roots) (h5 : τ.clocks = σ.clocks) :
    τ.Wf ↔ σ.Wf := by
  cases σ; cases τ
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  exact Iff.rfl

/-! ## Node-level facts -/

theorem entries_of_mem {σ : State} {n : Nat} {e : Bytes × Nat} (h : e ∈ σ.entries n) :
    n < σ.nodes.length := by
  unfold State.entries at h
  split at h
  · rename_i heq
    exact (List.getElem?_eq_some_iff.mp heq).1
  · simp at h

theorem isDir_lt {σ : State} {n : Nat} (h : σ.isDir n = true) : n < σ.nodes.length := by
  unfold State.isDir at h
  split at h
  · rename_i heq; exact (List.getElem?_eq_some_iff.mp heq).1
  · simp at h

theorem isFile_lt {σ : State} {n : Nat} (h : σ.isFile n = true) : n < σ.nodes.length := by
  unfold State.isFile at h
  split at h
  · rename_i heq; exact (List.getElem?_eq_some_iff.mp heq).1
  · simp at h

/-- A node below the length is a file or a directory. -/
theorem isFile_of_not_isDir {σ : State} {n : Nat} (hn : n < σ.nodes.length)
    (h : σ.isDir n = false) : σ.isFile n = true := by
  unfold State.isDir at h; unfold State.isFile
  rcases hx : σ.nodes[n]? with _ | ⟨i, _ | _⟩
  · simp at hx; omega
  · rfl
  · rw [hx] at h; simp at h

theorem not_isFile_of_isDir {σ : State} {n : Nat} (h : σ.isDir n = true) : σ.isFile n = false := by
  unfold State.isDir at h; unfold State.isFile
  split at h
  · rename_i heq; rw [heq]
  · simp at h

theorem desc_ok_congr {σ τ : State} (h : τ.nodes = σ.nodes) (d : Desc) : d.Ok τ ↔ d.Ok σ := by
  unfold Desc.Ok State.isFile State.isDir; rw [h]

/-! ## State changes that keep `Wf` -/

theorem wf_setDesc {σ : State} (hw : σ.Wf) {fd : Nat} {d : Desc} (hd : d.Ok σ) :
    (σ.setDesc fd d).Wf := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  have hk : (σ.setDesc fd d).fds.map (·.1) = σ.fds.map (·.1) := by
    simp only [State.setDesc, List.map_map]
    congr 1; funext e; by_cases he : e.1 = fd <;> simp [he]
  refine ⟨hk ▸ h1, h2, ?_, h4, h5⟩
  intro e he
  simp only [State.setDesc, List.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  obtain ⟨hf, hfr, hok⟩ := h3 e' he'
  by_cases hx : e'.1 = fd
  · simp only [hx, ↓reduceIte]
    exact ⟨hx ▸ hf, hx ▸ hfr, (desc_ok_congr rfl d).mpr hd⟩
  · simp only [hx, ↓reduceIte]
    exact ⟨hf, hfr, (desc_ok_congr rfl _).mpr hok⟩

theorem wf_clock {σ : State} (hw : σ.Wf) (id t : Nat) (ht : t < 2 ^ 64) :
    ({ σ with clocks := σ.clocks.set id t } : State).Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by simpa using h12, ?_⟩
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h13 x hx
  · exact ht

theorem wf_close {σ : State} (hw : σ.Wf) {fd : Nat} (hfd : fd ∈ σ.fds.map (·.1)) :
    ({ σ with fds := σ.fds.filter (·.1 ≠ fd), free := fd :: σ.free } : State).Wf := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  obtain ⟨⟨f, d⟩, hfd', rfl⟩ := List.mem_map.mp hfd
  obtain ⟨hlt, hnf, -⟩ := h3 _ hfd'
  refine ⟨?_, List.nodup_cons.mpr ⟨hnf, h2⟩, ?_, ?_, h5⟩
  · exact (List.filter_sublist.map _).nodup h1
  · intro e he
    simp only [List.mem_filter, decide_eq_true_eq] at he
    obtain ⟨hl, hfr, hok⟩ := h3 e he.1
    refine ⟨hl, ?_, hok⟩
    simp only [List.mem_cons, not_or]
    exact ⟨he.2, hfr⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hlt
    · exact h4 x hx

/-! ## Replacing a node's body -/

theorem setBody_get (σ : State) (n : Nat) (b : Body) (q : Nat) :
    (σ.setBody n b).nodes[q]? =
      if q = n then (σ.nodes[q]?).map (fun nd => { nd with body := b }) else σ.nodes[q]? := by
  simp only [State.setBody, List.getElem?_mapIdx]
  by_cases h : q = n <;> simp [h]

theorem setBody_length (σ : State) (n : Nat) (b : Body) :
    (σ.setBody n b).nodes.length = σ.nodes.length := by simp [State.setBody]

theorem setBody_inos (σ : State) (n : Nat) (b : Body) :
    (σ.setBody n b).nodes.map (·.ino) = σ.nodes.map (·.ino) := by
  apply List.ext_getElem (by simp [State.setBody])
  intro i h₁ h₂
  simp only [State.setBody, List.getElem_map, List.getElem_mapIdx]
  split <;> rfl

theorem entries_setBody_ne (σ : State) {n q : Nat} (b : Body) (h : q ≠ n) :
    (σ.setBody n b).entries q = σ.entries q := by
  simp only [State.entries, setBody_get, h, ↓reduceIte]

theorem isDir_setBody_ne (σ : State) {n q : Nat} (b : Body) (h : q ≠ n) :
    (σ.setBody n b).isDir q = σ.isDir q := by
  simp only [State.isDir, setBody_get, h, ↓reduceIte]

theorem isFile_setBody_ne (σ : State) {n q : Nat} (b : Body) (h : q ≠ n) :
    (σ.setBody n b).isFile q = σ.isFile q := by
  simp only [State.isFile, setBody_get, h, ↓reduceIte]

/-- A file keeps being a file under new contents: kinds + entries unchanged. -/
theorem setBody_file (σ : State) {n : Nat} (hn : σ.isFile n = true) (d : Bytes) (q : Nat) :
    (σ.setBody n (.file d)).entries q = σ.entries q ∧
      (σ.setBody n (.file d)).isDir q = σ.isDir q ∧
      (σ.setBody n (.file d)).isFile q = σ.isFile q := by
  by_cases h : q = n
  · subst h
    unfold State.isFile at hn
    simp only [State.entries, State.isDir, State.isFile, setBody_get, ↓reduceIte]
    split at hn
    · rename_i heq; simp [heq]
    · simp at hn
  · exact ⟨entries_setBody_ne σ _ h, isDir_setBody_ne σ _ h, isFile_setBody_ne σ _ h⟩

theorem wf_setFile {σ : State} (hw : σ.Wf) {n : Nat} (hn : σ.isFile n = true) (d : Bytes)
    (hd : d.length < 2 ^ 64) : (σ.setBody n (.file d)).Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  have hk := setBody_file σ hn d
  have hl := setBody_length σ n (.file d)
  have hok : ∀ x : Desc, x.Ok (σ.setBody n (.file d)) ↔ x.Ok σ := by
    intro x; unfold Desc.Ok; split <;> simp [(hk _).2.1, (hk _).2.2]
  refine ⟨h1, h2, fun e he => ?_, h4, fun r hr => ?_, fun q hq => ?_, ?_, h8, ?_,
    (setBody_inos σ n _) ▸ h10, ?_, h12, h13⟩
  · obtain ⟨a, b, c⟩ := h3 e he; exact ⟨a, b, (hok _).mpr c⟩
  · rw [(hk _).2.1]; exact h5 r hr
  · rw [(hk q).1, hl]; exact h6 q (hl ▸ hq)
  · intro p hp q hq e he f hf; rw [(hk p).1] at he; rw [(hk q).1] at hf
    exact h7 p (hl ▸ hp) q (hl ▸ hq) e he f hf
  · intro r hr p hp e he; rw [(hk p).1] at he; exact h9 r hr p (hl ▸ hp) e he
  · intro x hx
    simp only [State.setBody, List.mem_mapIdx] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    split
    · exact ⟨(h11 _ (List.getElem_mem _)).1, hd⟩
    · exact h11 _ (List.getElem_mem _)

/-- A directory losing entries stays a directory: kinds unchanged, its entries a sublist. -/
theorem setBody_dir (σ : State) {n : Nat} (hn : σ.isDir n = true) (es : List (Bytes × Nat))
    (q : Nat) :
    (σ.setBody n (.dir es)).entries q = (if q = n then es else σ.entries q) ∧
      (σ.setBody n (.dir es)).isDir q = σ.isDir q ∧
      (σ.setBody n (.dir es)).isFile q = σ.isFile q := by
  by_cases h : q = n
  · subst h
    unfold State.isDir at hn
    simp only [State.entries, State.isDir, State.isFile, setBody_get, ↓reduceIte]
    split at hn
    · rename_i heq; simp [heq]
    · simp at hn
  · simp only [h, ↓reduceIte]
    exact ⟨entries_setBody_ne σ _ h, isDir_setBody_ne σ _ h, isFile_setBody_ne σ _ h⟩

theorem wf_setDir {σ : State} (hw : σ.Wf) {n : Nat} (hn : σ.isDir n = true)
    {es : List (Bytes × Nat)} (hs : es.Sublist (σ.entries n)) : (σ.setBody n (.dir es)).Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  have hk := setBody_dir σ hn es
  have hl := setBody_length σ n (.dir es)
  have hsub : ∀ q e, e ∈ (σ.setBody n (.dir es)).entries q → e ∈ σ.entries q := by
    intro q e he; rw [(hk q).1] at he; split at he
    · rename_i h; subst h; exact hs.subset he
    · exact he
  have hok : ∀ x : Desc, x.Ok (σ.setBody n (.dir es)) ↔ x.Ok σ := by
    intro x; unfold Desc.Ok; split <;> simp [(hk _).2.1, (hk _).2.2]
  refine ⟨h1, h2, fun e he => ?_, h4, fun r hr => ?_, fun q hq => ?_, ?_, h8, ?_,
    (setBody_inos σ n _) ▸ h10, ?_, h12, h13⟩
  · obtain ⟨a, b, c⟩ := h3 e he; exact ⟨a, b, (hok _).mpr c⟩
  · rw [(hk _).2.1]; exact h5 r hr
  · rw [hl] at hq ⊢
    obtain ⟨hnd, hall⟩ := h6 q hq
    refine ⟨?_, fun e he => hall e (hsub q e he)⟩
    rw [(hk q).1]; split
    · rename_i h; subst h; exact (hs.map _).nodup hnd
    · exact hnd
  · intro p hp q hq e he f hf
    exact h7 p (hl ▸ hp) q (hl ▸ hq) e (hsub p e he) f (hsub q f hf)
  · intro r hr p hp e he; exact h9 r hr p (hl ▸ hp) e (hsub p e he)
  · intro x hx
    simp only [State.setBody, List.mem_mapIdx] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    split
    · exact ⟨(h11 _ (List.getElem_mem _)).1, Nat.two_pow_pos 64⟩
    · exact h11 _ (List.getElem_mem _)

/-- A new descriptor `fd` (unused, below 2^31) naming a node of its kind. -/
theorem wf_open {σ : State} (hw : σ.Wf) {fd : Nat} {d : Desc} (hfd : fd ∉ σ.fds.map (·.1))
    (hlt : fd < 2 ^ 31) (hd : d.Ok σ) :
    ({ σ with fds := (fd, d) :: σ.fds, free := σ.free.erase fd } : State).Wf := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  refine ⟨List.nodup_cons.mpr ⟨hfd, h1⟩, h2.erase fd, fun e he => ?_,
    fun x hx => h4 x (List.mem_of_mem_erase hx), h5⟩
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨hlt, h2.not_mem_erase, (desc_ok_congr rfl _).mpr hd⟩
  · obtain ⟨a, b, c⟩ := h3 e he
    exact ⟨a, fun h => b (List.mem_of_mem_erase h), (desc_ok_congr rfl _).mpr c⟩

/-! ## A new node -/

section Append

variable (σ : State) (nd : Node)

/-- `σ` with node `nd` appended. -/
abbrev State.push : State := { σ with nodes := σ.nodes ++ [nd] }

theorem push_get_lt {q : Nat} (h : q < σ.nodes.length) : (σ.push nd).nodes[q]? = σ.nodes[q]? :=
  List.getElem?_append_left h

theorem push_get_self : (σ.push nd).nodes[σ.nodes.length]? = some nd := by
  simp

theorem push_get_gt {q : Nat} (h : σ.nodes.length < q) : (σ.push nd).nodes[q]? = none := by
  simp only [List.getElem?_eq_none_iff, List.length_append, List.length_singleton]
  omega

theorem push_entries_lt {q : Nat} (h : q < σ.nodes.length) :
    (σ.push nd).entries q = σ.entries q := by
  simp only [State.entries, push_get_lt σ nd h]

theorem push_isDir_lt {q : Nat} (h : q < σ.nodes.length) : (σ.push nd).isDir q = σ.isDir q := by
  simp only [State.isDir, push_get_lt σ nd h]

theorem push_isFile_lt {q : Nat} (h : q < σ.nodes.length) :
    (σ.push nd).isFile q = σ.isFile q := by
  simp only [State.isFile, push_get_lt σ nd h]

end Append

theorem wf_create {σ : State} (hw : σ.Wf) {p : Nat} (hp : σ.isDir p = true) {c : Bytes}
    (hc : Name.Ok c) (hnot : c ∉ (σ.entries p).map (·.1)) {ino : Nat}
    (hino : ino ∉ σ.nodes.map (·.ino)) (hino64 : ino < 2 ^ 64) {b : Body}
    (hb : b = .file [] ∨ b = .dir []) :
    ((σ.setBody p (.dir (σ.entries p ++ [(c, σ.nodes.length)]))).push ⟨ino, b⟩).Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  set N := σ.nodes.length with hN
  set σ' := σ.setBody p (.dir (σ.entries p ++ [(c, N)])) with hσ'
  have hl' : σ'.nodes.length = N := setBody_length σ p _
  have hk := setBody_dir σ hp (σ.entries p ++ [(c, N)])
  -- entries of the result: below N as in σ' (p gains (c, N)); N and above: none
  have hent : ∀ q e, e ∈ (σ'.push ⟨ino, b⟩).entries q →
      (q < N ∧ e ∈ σ.entries q) ∨ (q = p ∧ e = (c, N)) := by
    intro q e he
    by_cases hq : q < N
    · rw [push_entries_lt σ' _ (hl' ▸ hq), (hk q).1] at he
      split at he
      · rename_i h; subst h
        rcases List.mem_append.mp he with he | he
        · exact Or.inl ⟨hq, he⟩
        · exact Or.inr ⟨rfl, List.mem_singleton.mp he⟩
      · exact Or.inl ⟨hq, he⟩
    · exfalso
      unfold State.entries at he
      by_cases hqN : q = N
      · subst hqN; rw [← hl', push_get_self] at he
        rcases hb with rfl | rfl <;> simp at he
      · rw [push_get_gt σ' _ (by omega)] at he; simp at he
  have hpN : p < N := isDir_lt hp
  have hkind : ∀ q, q < N → (σ'.push ⟨ino, b⟩).isDir q = σ.isDir q ∧
      (σ'.push ⟨ino, b⟩).isFile q = σ.isFile q := fun q hq =>
    ⟨(push_isDir_lt σ' _ (hl' ▸ hq)).trans (hk q).2.1,
     (push_isFile_lt σ' _ (hl' ▸ hq)).trans (hk q).2.2⟩
  have hok : ∀ x : Desc, x.Ok σ → x.Ok (σ'.push ⟨ino, b⟩) := by
    intro x hx; unfold Desc.Ok at hx ⊢; split at hx
    · exact hx
    · rename_i n pos _; rw [(hkind n (isFile_lt hx.1)).2]; exact hx
    · rename_i n _ _; rw [(hkind n (isDir_lt hx)).1]; exact hx
  have hlen : (σ'.push ⟨ino, b⟩).nodes.length = N + 1 := by simp [hl']
  have hi' : σ'.nodes.map (·.ino) = σ.nodes.map (·.ino) := by rw [hσ']; exact setBody_inos σ p _
  refine ⟨h1, h2, fun e he => ?_, h4, fun r hr => ?_, fun q hq => ?_, ?_, h8, ?_, ?_, ?_, h12,
    h13⟩
  · obtain ⟨a, b', c'⟩ := h3 e he; exact ⟨a, b', hok _ c'⟩
  · rw [(hkind _ (isDir_lt (h5 r hr))).1]; exact h5 r hr
  · rw [hlen] at hq ⊢
    by_cases hqN : q < N
    · rw [push_entries_lt σ' _ (hl' ▸ hqN), (hk q).1]
      obtain ⟨hnd, hall⟩ := h6 q hqN
      split
      · rename_i h; subst h
        refine ⟨?_, fun e he => ?_⟩
        · rw [List.map_append, List.nodup_append]
          refine ⟨hnd, by simp, fun a ha b hb => ?_⟩
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          subst hb; exact fun h => hnot (h ▸ ha)
        · rcases List.mem_append.mp he with he | he
          · exact ⟨(hall e he).1, by have := (hall e he).2; omega⟩
          · rw [List.mem_singleton.mp he]; exact ⟨hc, by omega⟩
      · exact ⟨hnd, fun e he => ⟨(hall e he).1, by have := (hall e he).2; omega⟩⟩
    · have : (σ'.push ⟨ino, b⟩).entries q = [] := by
        unfold State.entries
        by_cases hqe : q = N
        · subst hqe; rw [← hl', push_get_self]; rcases hb with rfl | rfl <;> rfl
        · rw [push_get_gt σ' _ (by omega)]
      simp [this]
  · intro p₁ _ q₁ _ e he f hf hef
    rcases hent p₁ e he with ⟨hp₁, he'⟩ | ⟨rfl, rfl⟩ <;>
      rcases hent q₁ f hf with ⟨hq₁, hf'⟩ | ⟨rfl, rfl⟩
    · exact h7 p₁ hp₁ q₁ hq₁ e he' f hf' hef
    · have := (h6 p₁ hp₁).2 e he'; simp at hef; omega
    · have := (h6 q₁ hq₁).2 f hf'; simp at hef; omega
    · exact ⟨rfl, rfl⟩
  · intro r hr p₁ _ e he
    have hrN := isDir_lt (h5 r hr)
    rcases hent p₁ e he with ⟨hp₁, he'⟩ | ⟨rfl, rfl⟩
    · exact h9 r hr p₁ hp₁ e he'
    · simp; omega
  · simp only [List.map_append, hi', List.map_singleton]
    refine List.nodup_append.mpr ⟨h10, by simp, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb; exact fun h => hino (h ▸ ha)
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · simp only [hσ', State.setBody, List.mem_mapIdx] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      split
      · exact ⟨(h11 _ (List.getElem_mem _)).1, Nat.two_pow_pos 64⟩
      · exact h11 _ (List.getElem_mem _)
    · rcases hb with rfl | rfl <;> exact ⟨hino64, Nat.two_pow_pos 64⟩

/-! ## Paths -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact absurd h (by intro h'; cases h')
  | ok a => exact ⟨a, rfl, h⟩

theorem splitSlash_spec : ∀ (path : Bytes), ∀ c ∈ splitSlash path, 47 ∉ c ∧ ∀ x ∈ c, x ∈ path
  | [] => by simp [splitSlash]
  | b :: bs => by
    have ih := splitSlash_spec bs
    unfold splitSlash
    split
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp
      · exact ⟨(ih c hc).1, fun x hx => List.mem_cons_of_mem _ ((ih c hc).2 x hx)⟩
    · rename_i hb
      split
      · rename_i c' cs heq
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · have := ih c' (heq ▸ List.mem_cons_self ..)
          refine ⟨?_, ?_⟩
          · simp only [List.mem_cons, not_or]; exact ⟨fun h => hb h.symm, this.1⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (this.2 x hx)
        · have := ih c (heq ▸ List.mem_cons_of_mem _ hc)
          exact ⟨this.1, fun x hx => List.mem_cons_of_mem _ (this.2 x hx)⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨fun h => hb h.symm, fun x hx => by simp_all⟩
        · simp at hc

theorem walk_dirs (σ : State) : ∀ (st : List Nat) (cs : List Bytes) (st' : List Nat),
    σ.walk st cs = .ok st' → st ≠ [] → (∀ x ∈ st, σ.isDir x = true) →
      st' ≠ [] ∧ ∀ x ∈ st', σ.isDir x = true
  | st, [], st', h, hne, hd => by
    simp only [State.walk, Except.ok.injEq] at h; subst h; exact ⟨hne, hd⟩
  | st, c :: cs, st', h, hne, hd => by
    unfold State.walk at h
    split at h
    · exact walk_dirs σ st cs st' h hne hd
    · split at h
      · split at h
        · rename_i a d st''
          exact walk_dirs σ (d :: st'') cs st' h (by simp)
            (fun x hx => hd x (List.mem_cons_of_mem _ hx))
        · simp at h
      · split at h
        · simp at h
        · rename_i n _
          split at h
          · rename_i hn
            exact walk_dirs σ (n :: st) cs st' h (by simp) (fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hn
              · exact hd x hx)
          · simp at h

/-- A resolved path: a stack of directories ending at the walk's start, a valid component. -/
theorem resolve_spec {σ : State} {d : Nat} {path : Bytes} {st : List Nat} {c : Bytes}
    {slash : Bool} (h : σ.resolve d path = .ok (st, c, slash)) (hd : σ.isDir d = true) :
    st ≠ [] ∧ (∀ x ∈ st, σ.isDir x = true) ∧ c ≠ [] ∧ 47 ∉ c ∧ 0 ∉ c := by
  unfold State.resolve at h
  split at h
  · simp at h
  · rename_i hnul
    split at h
    · simp at h
    · set L := (splitSlash path).filter (· ≠ []) with hL
      cases hLc : L with
      | nil => rw [hLc] at h; simp at h
      | cons c₀ cs₀ =>
        rw [hLc] at h
        obtain ⟨st₀, hw, h⟩ := bind_ok h
        have h' := Except.ok.inj h
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl, -⟩ := h'
        obtain ⟨hne, hdirs⟩ := walk_dirs σ [d] _ _ hw (by simp) (by simpa using hd)
        have hmem : (c₀ :: cs₀).getLastD [] ∈ L := by
          rw [hLc, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (by simp)]
          exact List.getLast_mem _
        obtain ⟨hin, hne'⟩ := List.mem_filter.mp (hL ▸ hmem)
        obtain ⟨h47, hsub⟩ := splitSlash_spec path _ hin
        exact ⟨hne, hdirs, by simpa using hne', h47, fun h0 => hnul (hsub 0 h0)⟩

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      have : a = k := by simpa using hk
      subst this; cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_none {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α}, l.lookup a = none → a ∉ l.map (·.1)
  | [], _, _ => by simp
  | (k, v) :: l, a, h => by
    simp only [List.lookup] at h
    split at h
    · simp at h
    · rename_i hk
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun h' => by subst h'; simp at hk, lookup_none h⟩

theorem target_some {σ : State} (hw : σ.Wf) {st : List Nat} {c : Bytes} {n : Nat}
    (h : σ.target st c = .ok (some n)) (hst : st ≠ []) (hd : ∀ x ∈ st, σ.isDir x = true) :
    n < σ.nodes.length ∧ ((c = [46] ∨ c = [46, 46]) → σ.isDir n = true) := by
  unfold State.target at h
  split at h
  · rename_i hc
    cases h
    have : st.headD 0 ∈ st := by cases st <;> simp_all
    exact ⟨isDir_lt (hd _ this), fun _ => hd _ this⟩
  · split at h
    · match st, hd, h with
      | a :: d :: st', hd, h =>
        obtain rfl : d = n := by simpa using h
        have : d ∈ a :: d :: st' := by simp
        exact ⟨isDir_lt (hd _ this), fun _ => hd _ this⟩
      | [_], _, h => simp at h
      | [], _, h => simp at h
    · rename_i h1 h2
      have hl := lookup_mem (Except.ok.inj h)
      have hp : st.headD 0 ∈ st := by cases st <;> simp_all
      have hpl := isDir_lt (hd _ hp)
      exact ⟨((hw.2.2.2.2.2.1 _ hpl).2 _ hl).2, fun h' => (h'.elim h1 h2).elim⟩

theorem target_none {σ : State} {st : List Nat} {c : Bytes} (h : σ.target st c = .ok none) :
    c ≠ [46] ∧ c ≠ [46, 46] ∧ c ∉ (σ.entries (st.headD 0)).map (·.1) := by
  unfold State.target at h
  split at h
  · simp at h
  · split at h
    · split at h <;> simp at h
    · rename_i h1 h2
      exact ⟨h1, h2, lookup_none (Except.ok.inj h)⟩

/-! ## Descriptors + contents on a well-formed state -/

theorem desc_mem {σ : State} {fd : Nat} {d : Desc} (h : σ.desc fd = some d) : (fd, d) ∈ σ.fds :=
  lookup_mem h

theorem desc_ok {σ : State} (hw : σ.Wf) {fd : Nat} {d : Desc} (h : σ.desc fd = some d) :
    d.Ok σ := (hw.2.2.1 _ (desc_mem h)).2.2

theorem desc_key {σ : State} {fd : Nat} {d : Desc} (h : σ.desc fd = some d) :
    fd ∈ σ.fds.map (·.1) := List.mem_map.mpr ⟨_, desc_mem h, rfl⟩

theorem data_len {σ : State} (hw : σ.Wf) (n : Nat) : (σ.data n).length < 2 ^ 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := hw
  unfold State.data
  split
  · rename_i i d heq
    exact (h11 ⟨i, .file d⟩ (List.mem_of_getElem? heq)).2
  · exact Nat.two_pow_pos 64

theorem ok_fst {x τ : State} {w w' : List (Nat × Bytes)}
    (h : (Except.ok (x, w) : Except Nat (State × List (Nat × Bytes))) = .ok (τ, w')) : τ = x := by
  cases h; rfl

/-- `σ` with its streams, arguments or exit changed. -/
theorem wf_streams {σ τ : State} (hw : σ.Wf) (h1 : τ.fds = σ.fds) (h2 : τ.free = σ.free)
    (h3 : τ.nodes = σ.nodes) (h4 : τ.roots = σ.roots) (h5 : τ.clocks = σ.clocks) : τ.Wf :=
  (wf_congr h1 h2 h3 h4 h5).mpr hw

end FVA.Wasi
