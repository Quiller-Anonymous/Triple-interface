import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorVariation
import Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion

/-!
# Primitive-character mean-value interface for balanced Vaughan Type I

This module joins two independently checked ingredients:

* a maximal bound for a primitive Dirichlet-character `psi` sum; and
* the signed conductor-weight variation estimate.

The joining argument is an exact finite Stieltjes/Abel identity.  In particular, the analytic
input below is only a bound on the ordinary cumulative character sum; it does not assume the
weighted Type-I conclusion.  No explicit zero-free-region or large-sieve estimate is asserted in
this file.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveMeanValue

open scoped BigOperators
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorWeight
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorVariation

noncomputable section

/-- A finite Stieltjes sum on the integer interval `[a,b]`. -/
noncomputable def discreteStieltjesSum
    (F w : ℕ → ℂ) (a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico a (b + 1), (F n - F (n - 1)) * w n

/--
Shifted finite summation by parts.  The global cumulative function produces both endpoint terms,
which is why the conductor estimate controls `w a`, `w b`, and the variation between them.
-/
theorem discreteStieltjesSum_eq_endpoints_add_variation
    (F w : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    discreteStieltjesSum F w a b =
      F b * w b - F (a - 1) * w a +
        ∑ n ∈ Finset.Ico a b, F n * (w n - w (n + 1)) := by
  unfold discreteStieltjesSum
  induction b, hab using Nat.le_induction with
  | base =>
      simp
      ring
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih,
        Finset.sum_Ico_succ_top hab]
      simp only [Nat.add_sub_cancel]
      ring

/-- A uniform bound for `F` controls its Stieltjes sum by endpoints plus total variation. -/
theorem norm_discreteStieltjesSum_le
    (F w : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) (M : ℝ)
    (hF : ∀ n ∈ Finset.Icc (a - 1) b, ‖F n‖ ≤ M) :
    ‖discreteStieltjesSum F w a b‖ ≤
      M * (‖w a‖ + ‖w b‖ +
        ∑ n ∈ Finset.Ico a b, ‖w n - w (n + 1)‖) := by
  rw [discreteStieltjesSum_eq_endpoints_add_variation F w hab]
  have haPred : a - 1 ∈ Finset.Icc (a - 1) b := by
    rw [Finset.mem_Icc]
    omega
  have hb : b ∈ Finset.Icc (a - 1) b := by
    rw [Finset.mem_Icc]
    omega
  have hInterior : ∀ n ∈ Finset.Ico a b, ‖F n‖ ≤ M := by
    intro n hn
    apply hF
    rw [Finset.mem_Icc]
    have hnData := Finset.mem_Ico.mp hn
    omega
  calc
    ‖F b * w b - F (a - 1) * w a +
        ∑ n ∈ Finset.Ico a b, F n * (w n - w (n + 1))‖ ≤
        ‖F b * w b‖ + ‖F (a - 1) * w a‖ +
          ‖∑ n ∈ Finset.Ico a b, F n * (w n - w (n + 1))‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ M * ‖w b‖ + M * ‖w a‖ +
          ∑ n ∈ Finset.Ico a b, M * ‖w n - w (n + 1)‖ := by
      apply add_le_add
      · apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hF b hb) (norm_nonneg _)
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hF (a - 1) haPred) (norm_nonneg _)
      · calc
          ‖∑ n ∈ Finset.Ico a b, F n * (w n - w (n + 1))‖ ≤
              ∑ n ∈ Finset.Ico a b, ‖F n * (w n - w (n + 1))‖ :=
            norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.Ico a b, M * ‖w n - w (n + 1)‖ := by
            apply Finset.sum_le_sum
            intro n hn
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hInterior n hn) (norm_nonneg _)
    _ = M * (‖w a‖ + ‖w b‖ +
          ∑ n ∈ Finset.Ico a b, ‖w n - w (n + 1)‖) := by
      rw [← Finset.mul_sum]
      ring

/-- The cumulative primitive-character sum twisted by the fixed center. -/
noncomputable def twistedPrimitivePsi
    (N r : ℕ) (χ : DirichletCharacter ℂ r) (t : ℕ) : ℂ :=
  χ ((N : ZMod r)⁻¹) * dirichletPsi t r χ

/-- One step of `dirichletPsi` is its von Mangoldt character summand. -/
theorem dirichletPsi_sub_pred
    {r p : ℕ} (χ : DirichletCharacter ℂ r) (hp : 0 < p) :
    dirichletPsi p r χ - dirichletPsi (p - 1) r χ =
      (ΛVM p : ℂ) * χ (p : ZMod r) := by
  unfold dirichletPsi
  have hPred : p - 1 + 1 = p := by omega
  rw [hPred, Finset.sum_range_succ]
  ring

/-- The twisted cumulative sum has the expected pointwise increment. -/
theorem twistedPrimitivePsi_sub_pred
    {N r p : ℕ} (χ : DirichletCharacter ℂ r) (hp : 0 < p) :
    twistedPrimitivePsi N r χ p - twistedPrimitivePsi N r χ (p - 1) =
      χ ((N : ZMod r)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod r)) := by
  unfold twistedPrimitivePsi
  rw [← mul_sub, dirichletPsi_sub_pred χ hp]

/-- A single primitive character weighted by the complete signed conductor lift. -/
noncomputable def primitiveCharacterConductorSum
    (N u r a b : ℕ) (χ : DirichletCharacter ℂ r) : ℂ :=
  ∑ p ∈ Finset.Ico a (b + 1),
    χ ((N : ZMod r)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod r)) *
      (balancedVaughanTypeIConductorWeight N u r p : ℂ)

/-- The character-weighted conductor sum is exactly a finite Stieltjes sum. -/
theorem primitiveCharacterConductorSum_eq_discreteStieltjesSum
    {N u r a b : ℕ} (χ : DirichletCharacter ℂ r)
    (ha : 0 < a) :
    primitiveCharacterConductorSum N u r a b χ =
      discreteStieltjesSum (twistedPrimitivePsi N r χ)
        (fun t => (balancedVaughanTypeIConductorWeight N u r t : ℂ)) a b := by
  unfold primitiveCharacterConductorSum discreteStieltjesSum
  apply Finset.sum_congr rfl
  intro p hp
  have hpData := Finset.mem_Ico.mp hp
  rw [twistedPrimitivePsi_sub_pred χ (by omega)]

/-- The complex variation of the real conductor weight is the previously defined real variation. -/
theorem sum_norm_conductorWeight_diff_eq_variation
    (N u r a b : ℕ) :
    (∑ t ∈ Finset.Ico a b,
        ‖(balancedVaughanTypeIConductorWeight N u r t : ℂ) -
          (balancedVaughanTypeIConductorWeight N u r (t + 1) : ℂ)‖) =
      balancedVaughanTypeIConductorVariation N u r a b := by
  unfold balancedVaughanTypeIConductorVariation
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/--
A maximal bound for one ordinary primitive-character `psi` sum gives the corresponding weighted
conductor estimate.  This is the exact analytic interface required before summing over primitive
characters and conductors.
-/
theorem norm_primitiveCharacterConductorSum_le
    {N u r a b : ℕ} (χ : DirichletCharacter ℂ r) (M : ℝ)
    (hN : 0 < N) (hr : 0 < r) (hNr : Nat.Coprime N r)
    (ha : 0 < a) (hab : a ≤ b) (hbN : b < N)
    (hM : 0 ≤ M)
    (hPsi : ∀ t ∈ Finset.Icc (a - 1) b, ‖dirichletPsi t r χ‖ ≤ M) :
    ‖primitiveCharacterConductorSum N u r a b χ‖ ≤
      M * (2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
        (Nat.totient r : ℝ)) * Real.log (N : ℝ)) := by
  have hTwisted : ∀ t ∈ Finset.Icc (a - 1) b,
      ‖twistedPrimitivePsi N r χ t‖ ≤ M := by
    intro t ht
    unfold twistedPrimitivePsi
    calc
      ‖χ ((N : ZMod r)⁻¹) * dirichletPsi t r χ‖ =
          ‖χ ((N : ZMod r)⁻¹)‖ * ‖dirichletPsi t r χ‖ := norm_mul _ _
      _ ≤ 1 * ‖dirichletPsi t r χ‖ :=
        mul_le_mul_of_nonneg_right
          (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
      _ ≤ M := by simpa using hPsi t ht
  rw [primitiveCharacterConductorSum_eq_discreteStieltjesSum χ ha]
  calc
    ‖discreteStieltjesSum (twistedPrimitivePsi N r χ)
        (fun t => (balancedVaughanTypeIConductorWeight N u r t : ℂ)) a b‖ ≤
        M * (|balancedVaughanTypeIConductorWeight N u r a| +
          |balancedVaughanTypeIConductorWeight N u r b| +
          balancedVaughanTypeIConductorVariation N u r a b) := by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        sum_norm_conductorWeight_diff_eq_variation] using
        (norm_discreteStieltjesSum_le
          (twistedPrimitivePsi N r χ)
          (fun t => (balancedVaughanTypeIConductorWeight N u r t : ℂ))
          hab M hTwisted)
    _ ≤ M * (2 * (6 * ((r * N : ℕ) : ℝ) /
          (Nat.totient (r * N) : ℝ) / (Nat.totient r : ℝ)) *
          Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (conductorWeight_endpoints_add_variation_le_two_mul_log
          hN hr hNr hab hbN) hM

/-- The primitive characters at one exact conductor. -/
noncomputable def primitiveCharacters
    (r : ℕ) : Finset (DirichletCharacter ℂ r) := by
  classical
  exact Finset.univ.filter fun χ => χ.IsPrimitive

@[simp]
theorem mem_primitiveCharacters_iff
    {r : ℕ} {χ : DirichletCharacter ℂ r} :
    χ ∈ primitiveCharacters r ↔ χ.IsPrimitive := by
  classical
  simp [primitiveCharacters]

/-- The complete primitive-character contribution at one conductor. -/
noncomputable def primitiveCharacterFamilyConductorSum
    (N u r a b : ℕ) : ℂ :=
  ∑ χ ∈ primitiveCharacters r,
    primitiveCharacterConductorSum N u r a b χ

/--
The fixed-conductor family costs the sum of the individual maximal `psi` bounds.  This is the
finite form expected from an explicit primitive-character mean-value theorem.
-/
theorem norm_primitiveCharacterFamilyConductorSum_le
    {N u r a b : ℕ}
    (M : DirichletCharacter ℂ r → ℝ)
    (hN : 0 < N) (hr : 0 < r) (hNr : Nat.Coprime N r)
    (ha : 0 < a) (hab : a ≤ b) (hbN : b < N)
    (hM : ∀ χ ∈ primitiveCharacters r, 0 ≤ M χ)
    (hPsi : ∀ χ ∈ primitiveCharacters r, ∀ t ∈ Finset.Icc (a - 1) b,
      ‖dirichletPsi t r χ‖ ≤ M χ) :
    ‖primitiveCharacterFamilyConductorSum N u r a b‖ ≤
      (∑ χ ∈ primitiveCharacters r, M χ) *
        (2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) * Real.log (N : ℝ)) := by
  let C : ℝ :=
    2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
      (Nat.totient r : ℝ)) * Real.log (N : ℝ)
  unfold primitiveCharacterFamilyConductorSum
  calc
    ‖∑ χ ∈ primitiveCharacters r,
        primitiveCharacterConductorSum N u r a b χ‖ ≤
        ∑ χ ∈ primitiveCharacters r,
          ‖primitiveCharacterConductorSum N u r a b χ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ χ ∈ primitiveCharacters r, M χ * C := by
      apply Finset.sum_le_sum
      intro χ hχ
      simpa [C] using
        (norm_primitiveCharacterConductorSum_le χ (M χ) hN hr hNr ha hab hbN
          (hM χ hχ) (hPsi χ hχ))
    _ = (∑ χ ∈ primitiveCharacters r, M χ) * C := by
      rw [Finset.sum_mul]
    _ = (∑ χ ∈ primitiveCharacters r, M χ) *
        (2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) * Real.log (N : ℝ)) := by
      rfl

/-- A supplied bound for the total maximal primitive-character mass at conductor `r`. -/
theorem norm_primitiveCharacterFamilyConductorSum_le_of_mass
    {N u r a b : ℕ}
    (M : DirichletCharacter ℂ r → ℝ) (B : ℝ)
    (hN : 0 < N) (hr : 0 < r) (hNr : Nat.Coprime N r)
    (ha : 0 < a) (hab : a ≤ b) (hbN : b < N)
    (hM : ∀ χ ∈ primitiveCharacters r, 0 ≤ M χ)
    (hPsi : ∀ χ ∈ primitiveCharacters r, ∀ t ∈ Finset.Icc (a - 1) b,
      ‖dirichletPsi t r χ‖ ≤ M χ)
    (hMass : (∑ χ ∈ primitiveCharacters r, M χ) ≤ B) :
    ‖primitiveCharacterFamilyConductorSum N u r a b‖ ≤
      B * (2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
        (Nat.totient r : ℝ)) * Real.log (N : ℝ)) := by
  have hLogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hTotientRN : (0 : ℝ) < Nat.totient (r * N) := by
    exact_mod_cast Nat.totient_pos.2 (Nat.mul_pos hr hN)
  have hTotientR : (0 : ℝ) < Nat.totient r := by
    exact_mod_cast Nat.totient_pos.2 hr
  calc
    ‖primitiveCharacterFamilyConductorSum N u r a b‖ ≤
        (∑ χ ∈ primitiveCharacters r, M χ) *
          (2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
            (Nat.totient r : ℝ)) * Real.log (N : ℝ)) :=
      norm_primitiveCharacterFamilyConductorSum_le M hN hr hNr ha hab hbN hM hPsi
    _ ≤ B * (2 * (6 * ((r * N : ℕ) : ℝ) /
          (Nat.totient (r * N) : ℝ) / (Nat.totient r : ℝ)) *
          Real.log (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right hMass
      positivity

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveMeanValue
