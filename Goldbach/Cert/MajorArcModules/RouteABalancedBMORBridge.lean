import Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
import Goldbach.Cert.MajorArcStep13RealToCircle
import Goldbach.Cert.MajorArcStep5ExpSumApproxBMOR

/-!
# BMOR exponential-sum bridge for the balanced Route A prototype

The balanced support is an actual interval, not an arithmetic bank. This module identifies its
circle exponential sum with the real-frequency interval sum used by the existing explicit BMOR
theorem, then restates that theorem directly on the balanced support.

This is the first reusable part of the old major-arc chain on the corrected exact-center route. It
does not yet integrate the pointwise approximation over all major arcs.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedBMORBridge

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex AddCircle

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep13RealToCircle
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype

noncomputable section

theorem balancedCandidateSupport_subset_primeCandidateSupport
    {L N : ℕ} (hL : 2 ≤ L) :
    balancedCandidateSupport L N ⊆ primeCandidateSupport N := by
  intro n hn
  have hBounds := Finset.mem_Icc.mp hn
  rw [primeCandidateSupport, Finset.mem_Icc]
  constructor <;> omega

theorem balancedCandidateSupport_eq_Ico (L N : ℕ) :
    balancedCandidateSupport L N = Finset.Ico L (N - L + 1) := by
  ext n
  simp only [balancedCandidateSupport, Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- The balanced von Mangoldt sum in the real-frequency notation used by Steps 2--5. -/
noncomputable def balancedVonMangoldtRealExpSum
    (L N : ℕ) (alpha : ℝ) : ℂ :=
  ∑ n ∈ balancedCandidateSupport L N,
    (broadVonMangoldtWeight n : ℂ) * gExp alpha n

/-- The corresponding exponential sum as it occurs in the generic circle integrand. -/
noncomputable def balancedVonMangoldtCircleExpSum
    (L N : ℕ) (alpha : UC) : ℂ :=
  finiteWeightExponentialSum (balancedVonMangoldtWeight L N) N alpha

/-- Exact real-to-circle identification on the balanced support. -/
theorem balancedVonMangoldtCircleExpSum_coe_eq_real
    {L N : ℕ} (hL : 2 ≤ L) (alpha : ℝ) :
    balancedVonMangoldtCircleExpSum L N (alpha : UC)
      = balancedVonMangoldtRealExpSum L N alpha := by
  classical
  let f : ℕ → ℂ := fun n =>
    (balancedVonMangoldtWeight L N n : ℂ)
      * fourier (T := (1 : ℝ)) (n : ℤ) (alpha : UC)
  have hsub : balancedCandidateSupport L N ⊆ primeCandidateSupport N :=
    balancedCandidateSupport_subset_primeCandidateSupport hL
  have hsum :
      (∑ n ∈ balancedCandidateSupport L N, f n)
        = ∑ n ∈ primeCandidateSupport N, f n := by
    apply Finset.sum_subset hsub
    intro n hnPrime hnBalanced
    simp [f, balancedVonMangoldtWeight, balancedRestrictedWeight, hnBalanced]
  unfold balancedVonMangoldtCircleExpSum finiteWeightExponentialSum
  rw [← hsum]
  unfold balancedVonMangoldtRealExpSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hfour :
      (fourier (T := (1 : ℝ)) (n : ℤ) (alpha : UC) : ℂ)
        = e ((n : ℝ) * alpha) :=
    fourier_coe_eq_e (k := (n : ℤ)) (x := alpha)
  calc
    f n = (broadVonMangoldtWeight n : ℂ) * e ((n : ℝ) * alpha) := by
      dsimp [f]
      rw [show balancedVonMangoldtWeight L N n = broadVonMangoldtWeight n by
        simp [balancedVonMangoldtWeight, balancedRestrictedWeight, hn]]
      exact congrArg (fun z : ℂ => (broadVonMangoldtWeight n : ℂ) * z) hfour
    _ = (broadVonMangoldtWeight n : ℂ) * gExp alpha n := by
      simp only [gExp]
      rw [mul_comm (n : ℝ) alpha]

/--
The published BMOR exponential-sum estimate, now stated directly for the balanced support.

Choosing `L = ExplicitPNTinAP_BMOR.Xmin + 1` discharges the lower-cutoff hypothesis while leaving
the support width free to grow with `N`.
-/
theorem norm_balancedVonMangoldtRealExpSum_sub_muMainTerm_le_of_BMOR
    {q a L N : ℕ}
    (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {beta : ℝ} (hbeta : |2 * Real.pi * beta| ≤ 1) :
    let V : ℂ := ∑ n ∈ balancedCandidateSupport L N, gExp beta n
    ‖balancedVonMangoldtRealExpSum L N (beta + (a : ℝ) / (q : ℝ))
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
      ≤
      (q : ℝ) *
        ((Goldbach.Cert.ExplicitPNTinAP_BMOR.Cψ * ((N - L : ℕ) : ℝ)
              / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (2 + (((N - L) - (L - 1) : ℕ) : ℝ)
              * (4 * Real.pi * |beta|))))
        +
      (((q + 1) * (Nat.log 2 (N - L) + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
  intro V
  have h :=
    Goldbach.Cert.MajorArcStep5ExpSumApproxBMOR.norm_expSum_sub_muMainTerm_le_of_BMOR
      (q := q) (a := a) (L := L) (U := N - L)
      hLU hL hXmin hq ha hqQ0 (β := beta) hbeta
  simpa [balancedVonMangoldtRealExpSum, balancedCandidateSupport_eq_Ico, V] using h

private lemma norm_sq_sub_sq_le_of_norm_sub_le
    {S M : ℂ} {E : ℝ} (h : ‖S - M‖ ≤ E) :
    ‖S ^ 2 - M ^ 2‖ ≤ E * (2 * ‖M‖ + E) := by
  have hE : 0 ≤ E := le_trans (norm_nonneg _) h
  have hS : ‖S‖ ≤ ‖M‖ + E := by
    calc
      ‖S‖ = ‖(S - M) + M‖ := by ring_nf
      _ ≤ ‖S - M‖ + ‖M‖ := norm_add_le _ _
      _ ≤ E + ‖M‖ := add_le_add_right h _
      _ = ‖M‖ + E := by ring
  have hfactor : S ^ 2 - M ^ 2 = (S - M) * (S + M) := by ring
  calc
    ‖S ^ 2 - M ^ 2‖ = ‖(S - M) * (S + M)‖ := by rw [hfactor]
    _ = ‖S - M‖ * ‖S + M‖ := norm_mul _ _
    _ ≤ E * (‖S‖ + ‖M‖) := by
      calc
        ‖S - M‖ * ‖S + M‖ ≤ E * ‖S + M‖ :=
          mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ ≤ E * (‖S‖ + ‖M‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hE
    _ ≤ E * (2 * ‖M‖ + E) := by
      apply mul_le_mul_of_nonneg_left _ hE
      linarith

/-- Quadratic major-arc approximation for the balanced exact-circle integrand. -/
theorem norm_balancedVonMangoldtRealExpSum_sq_sub_muMainTerm_sq_le_of_BMOR
    {q a L N : ℕ}
    (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {beta : ℝ} (hbeta : |2 * Real.pi * beta| ≤ 1) :
    let V : ℂ := ∑ n ∈ balancedCandidateSupport L N, gExp beta n
    let S : ℂ :=
      balancedVonMangoldtRealExpSum L N (beta + (a : ℝ) / (q : ℝ))
    let M : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V
    let E : ℝ :=
      (q : ℝ) *
          ((Goldbach.Cert.ExplicitPNTinAP_BMOR.Cψ * ((N - L : ℕ) : ℝ)
                / Real.log ((L - 1 : ℕ) : ℝ))
            * (2 * (2 + (((N - L) - (L - 1) : ℕ) : ℝ)
                * (4 * Real.pi * |beta|))))
        +
        (((q + 1) * (Nat.log 2 (N - L) + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
    ‖S ^ 2 - M ^ 2‖ ≤ E * (2 * ‖M‖ + E) := by
  intro V S M E
  have hSM : ‖S - M‖ ≤ E := by
    simpa [V, S, M, E] using
      (norm_balancedVonMangoldtRealExpSum_sub_muMainTerm_le_of_BMOR
        (q := q) (a := a) (L := L) (N := N)
        hLU hL hXmin hq ha hqQ0 (beta := beta) hbeta)
  exact norm_sq_sub_sq_le_of_norm_sub_le hSM

end

end Goldbach.Cert.MajorArcModules.RouteABalancedBMORBridge
