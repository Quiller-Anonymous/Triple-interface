import Goldbach.Cert.ExplicitPNTinAP_BMOR_Consequences

/-!
`MajorArcModules/BMOR` collects the *effective*, explicit PNT-in-AP input (BMOR Corollary 1.7)
and the repo’s derived bounds on the SW deviation `E(x)`.

This is intended for the offline/turnkey major-arc certificate work: it keeps the proof boundary
explicit and numeric, but still “conventional math” (published theorem + standard consequences).
-/

namespace Goldbach.Cert.MajorArcModules.BMOR

open Goldbach.Cert.ExplicitPNTinAP_BMOR
open Goldbach.Cert.ExplicitPNTinAP_BMOR.Consequences

noncomputable section

-- Re-export the canonical constants (paper-facing, not project params).
abbrev Xmin : ℕ := Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin
abbrev Qmax : ℕ := Goldbach.Cert.ExplicitPNTinAP_BMOR.Qmax
abbrev Cψ : ℝ := Goldbach.Cert.ExplicitPNTinAP_BMOR.Cψ

lemma Cψ_nonneg : 0 ≤ Cψ := Goldbach.Cert.ExplicitPNTinAP_BMOR.Cψ_nonneg

end

end Goldbach.Cert.MajorArcModules.BMOR

