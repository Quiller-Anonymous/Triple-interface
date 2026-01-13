import Goldbach.Cert.SiegelWalfiszAxioms

/-!
Effective PNT in arithmetic progressions (explicit ψ-bound).

This file records an *effective*, fully explicit bound for Chebyshev `ψ(x; q, a)` in arithmetic
progressions in a fixed modulus range. The intent is to use it as a conventional-math boundary
input for the major-arc bookkeeping when one wants *numeric* constants (as opposed to the
ineffective “Siegel–Walfisz” family in `Goldbach.Cert.SiegelWalfiszAxioms`).

We phrase the input directly in terms of `Goldbach.Cert.SiegelWalfisz.psi` to avoid duplicating
definitions.

Source (as provided by the user’s mathematician): Bennett–Martin–O’Bryant–Rechnitzer (2018),
a uniform explicit bound for `ψ(x; q, a)` valid for `x ≥ 10^6`, `q ≤ 10^5`.

Note: the constant below is recorded as the rational `11/1000` (i.e. `0.011`).
-/

namespace Goldbach.Cert.ExplicitPNTinAP_BMOR

open Goldbach.Cert.SiegelWalfisz

noncomputable section

/-! ### Constants (paper-facing, not project parameters) -/

-- Lower cutoff for the explicit bound.
def Xmin : ℕ := 10 ^ 6

-- Uniform modulus range covered by the explicit bound.
def Qmax : ℕ := 10 ^ 5

-- Explicit constant `0.011` as a rational.
def Cψ : ℝ := (11 : ℝ) / 1000

lemma Cψ_nonneg : 0 ≤ Cψ := by
  norm_num [Cψ]

/-!
### Explicit ψ-bound axiom

We record the bound in the “`x / log x`” form (as suggested by the mathematician’s
`A = 1, C = 0.011` interpretation).

This is a *conventional* (published, project-neutral) analytic input, but it is **not** imported
by default entry points; downstream files should decide explicitly whether they want the “ineffective
SW family” or this “effective explicit bound”.
-/

axiom psi_bound :
  ∀ ⦃x q a : ℕ⦄,
    Xmin ≤ x →
    1 ≤ q →
    q ≤ Qmax →
    Nat.Coprime a q →
    |psi x q a - (x : ℝ) / (Nat.totient q : ℝ)|
      ≤ Cψ * (x : ℝ) / Real.log (x : ℝ)

end

end Goldbach.Cert.ExplicitPNTinAP_BMOR

