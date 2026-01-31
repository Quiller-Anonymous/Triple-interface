import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle

/-!
`MajorArcModules/Q0MinorInterzoneDyadicTTStar` provides **deterministic TT*/Gram-expansion
lemmas** for the ε₁ dyadic interzone route.

This file does **not** prove any analytic decay; it only rewrites the Gram matrix entries

`⟪dyadicV X Δ i, dyadicV X Δ j⟫`

into explicit finite sums over `N : EvenIn X H` of the zone-restricted minor statistics.

These expansions are intended as the “Layer 1” bridge for later SSU/interzone work:
they make the exact object to be bounded explicit, without changing the pipeline interfaces.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicTTStar

open scoped BigOperators Interval

open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels

noncomputable section

/-- The `N`-level Gram entry for dyadic zones `i,j`: the product appearing in the `ℓ²` inner
product after expanding `dyadicV`. -/
def dyadicGramEntry (X : ℕ) (Δ : ℝ) (i j : ℕ) (N : EvenIn X H) : ℂ :=
  corr_integral_minor_zone X (N : ℕ) Δ j * star (corr_integral_minor_zone X (N : ℕ) Δ i)

/-- The Gram inner product `⟪dyadicV i, dyadicV j⟫` as an explicit finite sum over the window. -/
def dyadicGramSum (X : ℕ) (Δ : ℝ) (i j : ℕ) : ℂ :=
  Finset.sum Finset.univ (dyadicGramEntry (X := X) (Δ := Δ) (i := i) (j := j))

@[simp] lemma dyadicGramSum_def (X : ℕ) (Δ : ℝ) (i j : ℕ) :
    dyadicGramSum (X := X) (Δ := Δ) i j
      =
    Finset.sum Finset.univ (dyadicGramEntry (X := X) (Δ := Δ) (i := i) (j := j)) := rfl

@[simp] lemma dyadicGramEntry_def (X : ℕ) (Δ : ℝ) (i j : ℕ) (N : EvenIn X H) :
    dyadicGramEntry (X := X) (Δ := Δ) i j N
      =
    corr_integral_minor_zone X (N : ℕ) Δ j * star (corr_integral_minor_zone X (N : ℕ) Δ i) := rfl

/-!
### Gram / TT* expansion (finite-dimensional ℓ²)
-/

theorem inner_dyadicV_eq_dyadicGramSum (X : ℕ) (Δ : ℝ) (i j : ℕ) :
    inner ℂ (dyadicV X Δ i) (dyadicV X Δ j) = dyadicGramSum (X := X) (Δ := Δ) i j := by
  classical
  -- Use the explicit inner-product formula for `toLp 2` in `EuclideanSpace`.
  -- This expands `⟪toLp 2 x, toLp 2 y⟫` as a dot product with conjugation.
  -- Then unfold the definitions and rewrite as the desired finite sum.
  -- `EuclideanSpace.inner_toLp_toLp` expands the inner product as a dot product with `star`.
  simp [dyadicV, dyadicGramSum, dyadicGramEntry, EuclideanSpace.inner_toLp_toLp, dotProduct]

end

end Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicTTStar
