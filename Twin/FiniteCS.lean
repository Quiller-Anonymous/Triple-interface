/-
  Twin/FiniteCS.lean
  ------------------
  Compatibility shim: finite-window Cauchy–Schwarz lemmas backed by Mathlib.
  Formerly these were axioms; we now simply re-export the proved lemmas from
  `Twin.WindowCS`.
-/
import Twin.WindowCS

noncomputable section

namespace Twin
namespace FiniteCS

export Twin.WindowCS
  ( window_l1_le_sqrt_span_mul_window_l2
    sqrt_span_mul_sqrt_span_div9
    sqrt_span_div9 )

end FiniteCS
end Twin
