import Proofs.Decoder
namespace Verification
set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- Uniform in addresses, capacity and all initial memory bytes.
theorem empty_input (src dst cap : Nat) (initial : Nat → Nat) :
    let s := run decoder initial 5 (start src dst 0 cap)
    (s.result, s.accesses, s.stores, s.failed) = (some 4294967295, [], [], false) := by
  cbv

end Verification
