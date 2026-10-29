import Proofs.Checks
namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private theorem p0 : program[0]? = some .block := by decide
private theorem p1 : program[1]? = some (.get 2) := by decide
private theorem p2 : program[2]? = some (.brIf 0) := by decide
private theorem p3 : program[3]? = some (.const 4294967295) := by decide
private theorem p4 : program[4]? = some .ret := by decide
private theorem e0 : findEnd program program.size 1 0 = some 5 := by decide
attribute [local irreducible] program
theorem empty_input_no_access (src dst cap : Nat) (mem : Memory) :
    match run program 5 (initialState src dst 0 cap mem) with
    | .returned r s => r = 4294967295 ∧ s.mem.writes = mem.writes ∧ s.accesses = []
    | _ => False := by
  simp [run, step, p0, p1, p2, p3, p4, e0, initialState]
end Verification
