import Proofs.Spec
namespace Verification
-- Statement-only roots for measuring the complete transitive review closure.
def R1_statement : Prop := ¬ Compatible Artifact.edge (retained 1 20)
def R2_statement : Prop := ¬ Compatible Artifact.rna (retained 1 20)
def R2_literal_statement : Prop := ¬ Compatible Artifact.rna (retained 6 20)
def R3_statement : Prop := ¬ Agree10
def R3_witness_statement : Prop :=
  (9/1000 : ℚ) < |Artifact.edge.getD 0 0 - Artifact.rna.getD 0 0|
end Verification
