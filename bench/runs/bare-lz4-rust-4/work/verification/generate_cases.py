#!/usr/bin/env python3
"""Regenerate transparent Lean case data and proof modules from cases.json."""
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
cases = json.loads((root / "verification/cases.json").read_text())
header = ("\n\nnamespace LZ4Verification\n\n"
          "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n")
text = "import Proofs.Checks" + header
for i, c in enumerate(cases):
    output = "none" if c["output"] is None else "some " + str(c["output"])
    text += (f'def case_{i} : Case :=\n'
             f'  ⟨{json.dumps(c["name"])}, {c["input"]}, {c["cap"]}, '
             f'{output}, {c["src"]}, {c["dst"]}⟩\n\n')
text += "def cases : List Case := [" + ", ".join(
    f"case_{i}" for i in range(len(cases))) + "]\n\nend LZ4Verification\n"
(root / "Proofs/Cases.lean").write_text(text)

modules = []
for start in range(0, len(cases), 6):
    name = f"CaseProofs{start // 6}"
    modules.append(name)
    text = "import Proofs.Cases" + header
    for i in range(start, min(start + 6, len(cases))):
        text += (f"theorem case_{i}_checked : checkedCase case_{i} = true := "
                 "by decide +kernel\n\n")
    text += "end LZ4Verification\n"
    (root / f"Proofs/{name}.lean").write_text(text)

text = "\n".join(f"import Proofs.{m}" for m in modules) + header
text += "theorem cases_checked : ∀ c ∈ cases, checkedCase c = true := by\n"
text += "  intro c hc\n"
text += "  simp only [cases, List.mem_cons, List.not_mem_nil, or_false] at hc\n"
text += "  rcases hc with " + " | ".join("rfl" for _ in cases) + "\n"
text += "".join(f"  · exact case_{i}_checked\n" for i in range(len(cases))) + "\n"
text += f"theorem cases_count : cases.length = {len(cases)} := by decide +kernel\n\n"
text += '''theorem cases_R1 : ∀ c ∈ cases, checkR1 c = true := by
  intro c hc
  have h := cases_checked c hc
  simp only [checkedCase, Bool.and_eq_true] at h
  exact h.1.1.2

theorem cases_R2 : ∀ c ∈ cases, checkR2 c = true := by
  intro c hc
  have h := cases_checked c hc
  simp only [checkedCase, Bool.and_eq_true] at h
  exact h.1.2

theorem cases_R3 : ∀ c ∈ cases, checkR3 c = true := by
  intro c hc
  have h := cases_checked c hc
  simp only [checkedCase, Bool.and_eq_true] at h
  exact h.2

theorem cases_R1_trace (c : Case) (hc : c ∈ cases) :
    ∃ r s, runCase c = some (r, s) ∧
      ∀ a ∈ s.trace, safeAccess c a = true := by
  have h := cases_R1 c hc
  cases hr : runCase c with
  | none => simp [checkR1, hr] at h
  | some p =>
    rcases p with ⟨r, s⟩
    exact ⟨r, s, rfl, List.all_eq_true.mp (by simpa only [checkR1, hr] using h)⟩

theorem cases_R2_content (c : Case) (hc : c ∈ cases) (d : Decoded)
    (hd : decode c.input = some d) (he : endConditions d = true)
    (hcap : d.output.length ≤ c.cap) :
    ∃ r s, runCase c = some (r, s) ∧ correctOutput c r s d.output = true := by
  have h := cases_R2 c hc
  cases hr : runCase c with
  | none => simp [checkR2, hd, he, hcap, hr] at h
  | some p =>
    rcases p with ⟨r, s⟩
    exact ⟨r, s, rfl, by simpa only [checkR2, hd, he, hcap, hr, Bool.true_and, decide_true, ite_true] using h⟩

theorem cases_R3_content (c : Case) (hc : c ∈ cases) (r : Nat) (s : State)
    (hr : runCase c = some (r, s)) (hn : r < 2147483648) :
    ∃ d, decode c.input = some d ∧ correctOutput c r s d.output = true := by
  have h := cases_R3 c hc
  cases hd : decode c.input with
  | none => simp [checkR3, hr, hn, hd] at h
  | some d => exact ⟨d, rfl, by simpa only [checkR3, hr, hn, hd, ite_true] using h⟩

'''
text += "end LZ4Verification\n"
(root / "Proofs/Results.lean").write_text(text)
