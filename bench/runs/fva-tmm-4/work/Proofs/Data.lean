import Proofs.Raw
namespace Proofs.Data
theorem es_eq : Model.samples Counts.blob.data = es := by
  unfold Model.samples
  rw [rows_eq, nonzero]
  dsimp only
  rw [columns_eq, ref_eq, cs_eq]
  change [Model.entries c0 c3, Model.entries c1 c3, Model.entries c2 c3, Model.entries c3 c3, Model.entries c4 c3, Model.entries c5 c3, Model.entries c6 c3] = es
  rw [e0_eq, e1_eq, e2_eq, e3_eq, e4_eq, e5_eq, e6_eq]
  rfl
end Proofs.Data
