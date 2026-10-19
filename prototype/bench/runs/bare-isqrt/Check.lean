import Machine

/-!
Always elaborate this file afresh (see verify.sh): include_str reads isqrt.c.
The equality pins the proof to the exact reviewed source, but is not a C parser
or a proof of correctness of the manual C-to-Lean translation.
-/
namespace Isqrt

/-- A stale source/model pairing must fail, even if Lake has cached other modules. -/
theorem source_matches : (include_str "isqrt.c") =
    "/* Integer square root. */\nunsigned isqrt(unsigned n) {\n  unsigned lo = 0, hi = 65536;\n  while (hi - lo > 1) {\n    unsigned mid = lo + (hi - lo) / 2;\n    if ((unsigned long long)mid * mid <= n) lo = mid; else hi = mid;\n  }\n  return lo;\n}\n" := rfl

end Isqrt

#print axioms Isqrt.source_matches
#print axioms Isqrt.reachable_arithmetic_safe
#print axioms Isqrt.Machine.step_refines
#print axioms Isqrt.Machine.no_overflow
#print axioms Isqrt.Machine.verified
