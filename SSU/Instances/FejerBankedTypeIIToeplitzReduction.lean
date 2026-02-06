import SSU.Instances.FejerBankedPartition
import SSU.Engines.BGToeplitzReduction
import SSU.Engines.TypeIIToeplitz

/-!
TeX-faithful interface: Fejér-banked packet Grams → BG Toeplitz Type–II form.

This file does **not** prove the SSU heart. Instead, it isolates the application-specific
“Toeplitz Type–II reduction” step from `05_BG.tex`:

1. choose a Type–II tube set `tube : Finset (ℤ×ℤ)`;
2. choose coefficient sequences `α_d(i,j,f)` and `β_n(i,j,f)` and a cutoff `W(d,n)`;
3. prove the Gram identity for packet operators against the TeX Toeplitz quadratic form.

Once an application supplies that identity (and an energy comparison), the deterministic constructor
`BGToeplitzReduction.TeX.mkReductionToTubeFormProd` converts it into a
`SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd`, which plugs into the SSU Type-II Toeplitz
bridge.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzReduction

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII
open SSU.Engines.TypeIIToeplitz
open SSU.Engines.BGToeplitzReduction

variable {κ : Type*} [DecidableEq κ]

/--
Application-facing hypothesis for the BG Toeplitz Type–II reduction, specialized to the
Fejér-banked packet operators on the torus.

The torus-side packet operators are the *unnormalized multipliers*
`f ↦ ψ_j • f` coming from `FejerBankedPartition.Data`.
-/
structure Hypothesis where
  D : SSU.Instances.FejerBankedPartition.Data κ
  /-- The Toeplitz kernel `K_H` in the product shift variable `k' - k` (TeX `K_H(k'-k)`). -/
  K : ℤ → ℝ
  /-- TeX coefficient factorization `F(d,n) = α_d β_n W(d,n)` on a tube. -/
  C : SSU.Engines.BGToeplitzReduction.TeX.CoeffFactorization (H := SSU.Torus.L2)
  /-- Energy comparison constant for `tubeEnergy` vs packet norms. -/
  Cenergy : ℝ
  Cenergy_nonneg : 0 ≤ Cenergy
  /--
  The “Toeplitz Type–II reduction” identity:
  Gram entries of the packet operators equal the Toeplitz tube form built from `α,β,W`.
  -/
  inner_eq_toeplitzForm :
    ∀ f : SSU.Torus.L2, ∀ i ∈ D.J, ∀ j ∈ D.J,
      inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) f)
          (((D.toMultiplierModel).packetOpUnnormalized j) f)
        =
      (C.toeplitzForm K f i j)
  /--
  Energy comparison for the coefficient array on the tube:
  this is the `ReductionToTubeFormProd.energy_le` input in TeX factorized form.
  -/
  energy_le :
    ∀ f : SSU.Torus.L2, ∀ i ∈ D.J, ∀ j ∈ D.J,
      tubeEnergy C.tube (C.F f i j) ≤ Cenergy * ‖((D.toMultiplierModel).packetOpUnnormalized i) f‖
        * ‖((D.toMultiplierModel).packetOpUnnormalized j) f‖

namespace Hypothesis

variable (h : Hypothesis (κ := κ))

noncomputable def reductionTorus :
    SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd
      (H := SSU.Torus.L2)
      (J := h.D.J)
      (T := (h.D.toMultiplierModel).packetOpUnnormalized)
      h.D.X h.D.H h.K h.C.tube :=
by
  classical
  exact
    SSU.Engines.BGToeplitzReduction.TeX.mkReductionToTubeFormProd
      (H := SSU.Torus.L2)
      (J := h.D.J)
      (T := (h.D.toMultiplierModel).packetOpUnnormalized)
      (X := h.D.X) (Hpar := h.D.H) (K := h.K)
      (C := h.C) (Cenergy := h.Cenergy) (Cenergy_nonneg := h.Cenergy_nonneg)
      (inner_eq_toeplitzForm := h.inner_eq_toeplitzForm)
      (energy_le := by
        intro f i hi j hj
        simpa using (h.energy_le f i hi j hj))

end Hypothesis

/--
TeX-faithful variant of `Hypothesis`:

Instead of assuming `inner = tubeFormProd` directly, assume `inner` equals the *TeX-displayed*
`k,k'` Toeplitz form (05_BG.tex line 37), and include evenness of the kernel `K`.

Conversion to `Hypothesis` is deterministic via
`BGToeplitzReduction.TeX.CoeffFactorization.toeplitzFormTeX_eq_toeplitzForm`.
-/
structure HypothesisTeX where
  D : SSU.Instances.FejerBankedPartition.Data κ
  K : ℤ → ℝ
  K_even : ∀ t : ℤ, K (-t) = K t
  C : SSU.Engines.BGToeplitzReduction.TeX.CoeffFactorization (H := SSU.Torus.L2)
  Cenergy : ℝ
  Cenergy_nonneg : 0 ≤ Cenergy
  /-- The TeX-displayed `k,k'` quadratic form identity. -/
  inner_eq_toeplitzFormTeX :
    ∀ f : SSU.Torus.L2, ∀ i ∈ D.J, ∀ j ∈ D.J,
      inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) f)
          (((D.toMultiplierModel).packetOpUnnormalized j) f)
        =
      (C.toeplitzFormTeX K f i j)
  energy_le :
    ∀ f : SSU.Torus.L2, ∀ i ∈ D.J, ∀ j ∈ D.J,
      tubeEnergy C.tube (C.F f i j) ≤ Cenergy * ‖((D.toMultiplierModel).packetOpUnnormalized i) f‖
        * ‖((D.toMultiplierModel).packetOpUnnormalized j) f‖

namespace HypothesisTeX

variable (h : HypothesisTeX (κ := κ))

/-- Convert a TeX-faithful `k,k'`-form hypothesis into the `tubeFormProd`-based hypothesis. -/
noncomputable def toHypothesis : Hypothesis (κ := κ) where
  D := h.D
  K := h.K
  C := h.C
  Cenergy := h.Cenergy
  Cenergy_nonneg := h.Cenergy_nonneg
  inner_eq_toeplitzForm := by
    intro f i hi j hj
    have hTex :
        inner ℂ (((h.D.toMultiplierModel).packetOpUnnormalized i) f)
            (((h.D.toMultiplierModel).packetOpUnnormalized j) f)
          =
        (h.C.toeplitzFormTeX h.K f i j) :=
      h.inner_eq_toeplitzFormTeX f i hi j hj
    have hEq :
        h.C.toeplitzFormTeX h.K f i j = h.C.toeplitzForm h.K f i j :=
      h.C.toeplitzFormTeX_eq_toeplitzForm (K := h.K) (hK := h.K_even) (f := f) (i := i) (j := j)
    simpa [hEq] using hTex
  energy_le := h.energy_le

end HypothesisTeX

end

end FejerBankedTypeIIToeplitzReduction
end Instances
end SSU

