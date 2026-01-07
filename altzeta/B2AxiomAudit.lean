import AltZeta.B2RealBound

/-!
AltZeta/B2AxiomAudit.lean
=========================

Quick audit file for the B2 “windowed Chebyshev/ψ error bound” entrypoint.

This is not part of the default build (`All.lean` does not import AltZeta).  It exists
to make it easy to inspect exactly which explicit axioms the canonical B2 theorem
depends on, via `#print axioms`.
-/

namespace AltZeta
namespace B2

#check b2_bound0_on_window
#print axioms b2_bound0_on_window

end B2
end AltZeta

