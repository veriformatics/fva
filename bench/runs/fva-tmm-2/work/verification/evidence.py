#!/usr/bin/env python3
"""Untrusted generator of kernel-checkable evidence, using generate.py's data."""
from pathlib import Path
import json

root = Path(__file__).resolve().parent.parent
v = json.loads((root / 'verification/numerical.json').read_text())
libs = v['libraries']
calc = root / 'Proofs/Calc'
calc.mkdir(exist_ok=True)
header = ['import Proofs.Data', 'import FVA.Lifted', '', 'namespace Proofs',
     'open Bounds Model', 'set_option maxRecDepth 100000',
     'set_option maxHeartbeats 0', '']
for j, lib in enumerate(libs):
    q = header + [f'theorem lib_{j} : lib Data.counts {j} = {lib} := by kernel_rfl',
          f'theorem sort_{j} : (col (active Data.counts) {j}).mergeSort (· ≤ ·) = Data.sorted{j} := by',
          f'  have hp : Data.sorted{j}.Perm (col (active Data.counts) {j}) := by decide +kernel',
          f'  have hs : Data.sorted{j}.SortedLE := by decide +kernel',
          f'  exact ((List.mergeSort_perm _ _).trans hp.symm).eq_of_pairwise\' ',
          '    (List.pairwise_mergeSort\' (· ≤ ·) _) hs.pairwise',
          f'theorem uq_{j} : uq Data.counts {j} = ({[4,2,2,3,5,3,3][j]} / {lib} : ℚ) := by',
          '  unfold uq',
          f'  rw [sort_{j}, lib_{j}]',
          '  kernel_rfl', '', 'end Proofs', '']
    (calc / f'Q{j}.lean').write_text('\n'.join(q))
    if j != 3:
        t = header + [f'theorem kept_{j} : kept Data.counts {j} 3 = Data.kept{j} := by kernel_rfl',
                      '', 'end Proofs', '']
        (calc / f'Trim{j}.lean').write_text('\n'.join(t))
    else:
        (calc / 'Trim3.lean').unlink(missing_ok=True)
s = [f'import Proofs.Calc.Q{j}' for j in range(7)] + [
    f'import Proofs.Calc.Trim{j}' for j in range(7) if j != 3] + header[2:]
s += ['theorem reference_eq : reference Data.counts = 3 := by',
      '  unfold reference',
      '  rw [show List.range 7 = [0, 1, 2, 3, 4, 5, 6] by decide]',
      '  norm_num [List.foldl_cons, List.foldl_nil, ' + ', '.join(f'uq_{j}' for j in range(7)) + ']',
      '', 'end Proofs', '']
(calc / 'Selection.lean').write_text('\n'.join(s))
p = ['import Proofs.LogChecks', 'import Proofs.Calc.Selection'] + header[2:]
p += ['theorem raw_self (m : Matrix) (r : Nat) : rawLog m r r = 0 := by',
      '  have heq : ∀ p ∈ kept m r r, p.1 = p.2 := by',
      '    intro p hp',
      '    have hp1 : p ∈ pairs m r r := (List.mem_filter.mp hp).1',
      '    have hp2 := (List.mem_filter.mp hp1).1',
      '    obtain ⟨row, _, hrow⟩ := List.mem_map.mp hp2',
      '    cases hrow', '    rfl',
      '  unfold rawLog', '  dsimp only',
      '  have hz : ((kept m r r).map (fun p => (weight (lib m r) (lib m r) p : ℝ) *',
      '      logRatio (lib m r) (lib m r) p)).sum = 0 := by',
      '    apply List.sum_eq_zero', '    intro v hv',
      '    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv',
      '    simp [logRatio, heq p hp]',
      '  rw [hz]', '  simp', '']
p += ['def rb (j : Nat) : I := Data.rawBounds[j]?.getD I.zero', '']
for j, lib in enumerate(libs):
    if j == 3:
        p += ['theorem raw_3 : (rb 3).Holds (rawLog Data.counts 3 3) := by',
              '  rw [raw_self]', '  norm_num [rb, Data.rawBounds, I.Holds]', '']
        continue
    p += [f'theorem raw_{j} : (rb {j}).Holds (rawLog Data.counts {j} 3) := by',
          f'  have hn : ∀ p ∈ Data.kept{j}, p.1 ∈ Data.logged ∧ p.2 ∈ Data.logged := by decide +kernel',
          f'  have hp : ∀ p ∈ Data.kept{j}, (Data.logI p.1).Holds (Real.log p.1) ∧',
          '      (Data.logI p.2).Holds (Real.log p.2) := by',
          '    intro p h',
          '    exact ⟨log_valid p.1 (hn p h).1, log_valid p.2 (hn p h).2⟩',
          f'  have hw : ∀ p ∈ Data.kept{j}, 0 ≤ weight {lib} 1097 p := by decide +kernel',
          f'  have h := raw_sound Data.logI {lib} 1097 Data.kept{j} log_{lib} log_1097 hp hw',
          f'  unfold rawLog',
          f'  rw [kept_{j}, lib_{j}' + ('' if j == 3 else ', lib_3') + ']',
          '  exact holds_weaken h (by decide +kernel) (by decide +kernel)', '']
p += ['theorem raw_valid (j : Nat) (hj : j ∈ List.range 7) :',
      '    (rb j).Holds (rawLog Data.counts j 3) := by',
      '  have hj7 : j < 7 := List.mem_range.mp hj',
      '  interval_cases j', *[f'  · exact raw_{j}' for j in range(7)], '',
      'def centerI (j : Nat) : I :=',
      '  (rb j).sub ((isum ((List.range 7).map rb)).div 7)', '',
      'theorem center_sound (j : Nat) (hj : j ∈ List.range 7) :',
      '    (centerI j).Holds (rawLog Data.counts j 3 -',
      '      ((List.range 7).map (fun k => rawLog Data.counts k 3)).sum / 7) := by',
      '  exact holds_sub (raw_valid j hj)',
      '    (holds_div (by norm_num) (holds_sum (List.range 7) rb',
      '      (fun k => rawLog Data.counts k 3) raw_valid))', '']
for j, (a, b) in enumerate(v['brackets']):
    p += [f'theorem factor_{j} : ({a} / 1000000 : ℚ) ≤ factor Data.counts {j} ∧',
          f'    factor Data.counts {j} ≤ ({b} / 1000000 : ℚ) := by',
          '  unfold factor', '  rw [reference_eq]',
          f'  have hl := log_quotient {a} 1000000 (by decide) (by decide) log_{a} log_1000000',
          f'  have hh := log_quotient {b} 1000000 (by decide) (by decide) log_{b} log_1000000',
          f'  exact exp_enclose (center_sound {j} (by decide)) hl hh',
          '    (by decide +kernel) (by decide +kernel)',
          '    (by decide +kernel) (by decide +kernel)', '']
for name, tolerance in [('edge', '23 / 1000'), ('rna', '21 / 1000')]:
    p += [f'theorem {name}_errors (j : Fin 7) :',
          f'    |((Data.{name}[j.val]?.getD ⟨0, []⟩).value : ℝ) - factor Data.counts j| ≤',
          f'      ({tolerance} : ℚ) := by',
          '  fin_cases j']
    p += [f'  · exact abs_error factor_{j} (by decide +kernel) (by decide +kernel)' for j in range(7)]
    p += ['']
p += ['end Proofs', '']
(root / 'Proofs/Evidence.lean').write_text('\n'.join(p))
print('Generated Evidence.lean; acceptance requires lake build and fva trust.')
