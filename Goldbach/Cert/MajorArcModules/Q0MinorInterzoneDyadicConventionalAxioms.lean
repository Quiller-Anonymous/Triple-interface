import Goldbach.Cert.MajorArcModules.Q0MinorCrow
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerFromInterzone
import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
import Mathlib.Analysis.PSeries

/-!
`MajorArcModules/Q0MinorInterzoneDyadicConventionalAxioms` records a **project-neutral**
“conventional math” axiom schema for the ε₁ interzone route, specialized to the canonical
dyadic level decomposition (`JX`, `zoneSet`, `corr_integral_minor_zone`) from
`Q0MinorInterzoneDyadicLevels`.

The intent is:

* deterministic pieces (dyadic partition and the identity `∑ v_j = f_X`) are proved in-repo;
* the analytic heart (Gram decay + diagonal sum ledger) is packaged as an axiom for now (3B);
* later we try to prove the same statement from SSU/Type–I/dispersion technology (3A).

This file does **not** pin any constants; it is purely an interface brick.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.Q0MinorCrow
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerFromInterzone
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
open Goldbach.Cert.MajorArcStep17MajorMinorSplit

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- Canonical Crow constant associated to a summable decay profile `a`. -/
def CrowOf (a : ℕ → ℝ) : ℝ :=
  a 0 + 2 * (∑' d : ℕ, a (d + 1))

lemma CrowOf_nonneg {a : ℕ → ℝ} (ha : ∀ d : ℕ, 0 ≤ a d) :
    0 ≤ CrowOf a := by
  have htsum : 0 ≤ (∑' d : ℕ, a (d + 1)) := by
    exact tsum_nonneg (fun d => ha (d + 1))
  have : 0 ≤ a 0 + 2 * (∑' d : ℕ, a (d + 1)) := by
    exact add_nonneg (ha 0) (mul_nonneg (by linarith : (0 : ℝ) ≤ 2) htsum)
  simpa [CrowOf] using this

/-!
## Conventional analytic heart (3B): dyadic Gram decay + diagonal ledger

This is the missing “Gram decay” brick for the canonical dyadic level vectors
`dyadicV X Δ j` and diagonal weights `dyadicD X Δ j := ‖dyadicV X Δ j‖^2`.

It is stated in a **textbook** Hilbert-space form (no Goldbach-specific constants),
but specialized to the canonical `JX X` index set.
-/

structure Q0MinorDyadicGramDecay (Δ : ℝ) (a : ℕ → ℝ) (C2 C3 : ℝ) : Prop where
  a_nonneg : ∀ k : ℕ, 0 ≤ a k
  a_summable : Summable (fun d : ℕ => a (d + 1))
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  gram_bound :
    ∀ {X : ℕ}, X0 ≤ X →
      ∀ i ∈ (JX X : Finset ℕ), ∀ j ∈ (JX X : Finset ℕ),
        ‖inner ℂ (dyadicV X Δ i) (dyadicV X Δ j)‖
          ≤ a (Nat.dist i j) * Real.sqrt (dyadicD X Δ i) * Real.sqrt (dyadicD X Δ j)
  sumD_bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ j ∈ (JX X : Finset ℕ), dyadicD X Δ j)
        ≤ C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)

/-!
## A polynomial-template variant of the Gram decay interface

For the ε₁ certificate route, it is useful to pin the decay profile to a textbook p-series:

`a(d) = C / (d+1)^p` with `1 < p`.

This avoids a “mystery function `a`” and makes the Crow row-sum constant explicit.
-/

/-- Polynomial p-series decay profile on `ℕ`: `a(d) = C / (d+1)^p`. -/
def aPoly (C : ℝ) (p : ℕ) (d : ℕ) : ℝ :=
  C / (((d : ℝ) + 1) ^ p)

lemma aPoly_nonneg {C : ℝ} {p : ℕ} (hC : 0 ≤ C) : ∀ d : ℕ, 0 ≤ aPoly C p d := by
  intro d
  have hbase : 0 ≤ (d : ℝ) + 1 := by
    exact add_nonneg (Nat.cast_nonneg d) (by linarith)
  have hpow : 0 ≤ (((d : ℝ) + 1) ^ p) := pow_nonneg hbase p
  exact div_nonneg hC hpow

lemma aPoly_summable_shift {C : ℝ} {p : ℕ} (hp : 1 < p) :
    Summable (fun d : ℕ => aPoly C p (d + 1)) := by
  -- Reduce to the standard p-series `∑ 1 / n^p` via shifting.
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ p)) := by
    exact (Real.summable_one_div_nat_pow (p := p)).2 hp
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℝ) ^ p)) := by
    -- Shift by `2` to avoid any endpoint conventions; summability is invariant under shifts.
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
      ((_root_.summable_nat_add_iff 2 (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ p))).2 h0)
  -- Multiply by `C` and rewrite `aPoly C p (d+1)` as `C * (1 / (d+2)^p)`.
  have h2' : Summable (fun n : ℕ => C * ((1 : ℝ) / (((n + 2 : ℕ) : ℝ) ^ p))) := h2.mul_left C
  -- `aPoly C p (d+1) = C / ((d+2)^p)` in the `ℝ`-cast normalization.
  simpa [aPoly, div_eq_mul_inv, Nat.cast_add, add_assoc, add_comm, add_left_comm,
    one_add_one_eq_two] using h2'

structure Q0MinorDyadicGramDecayPoly (Δ : ℝ) (C : ℝ) (p : ℕ) (C2 C3 : ℝ) : Prop where
  C_nonneg : 0 ≤ C
  p_gt_one : 1 < p
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  gram_bound :
    ∀ {X : ℕ}, X0 ≤ X →
      ∀ i ∈ (JX X : Finset ℕ), ∀ j ∈ (JX X : Finset ℕ),
        ‖inner ℂ (dyadicV X Δ i) (dyadicV X Δ j)‖
          ≤ aPoly C p (Nat.dist i j) * Real.sqrt (dyadicD X Δ i) * Real.sqrt (dyadicD X Δ j)
  sumD_bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ j ∈ (JX X : Finset ℕ), dyadicD X Δ j)
        ≤ C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)

theorem Q0MinorDyadicGramDecayPoly.to_Q0MinorDyadicGramDecay
    {Δ : ℝ} {C : ℝ} {p : ℕ} {C2 C3 : ℝ}
    (h : Q0MinorDyadicGramDecayPoly Δ C p C2 C3) :
    Q0MinorDyadicGramDecay Δ (aPoly C p) C2 C3 := by
  refine ⟨aPoly_nonneg (C := C) (p := p) h.C_nonneg, ?_, h.C2_nonneg, h.C3_nonneg, ?_, ?_⟩
  · -- summable tail of the p-series
    simpa using (aPoly_summable_shift (C := C) (p := p) h.p_gt_one)
  · intro X hX i hi j hj
    simpa using h.gram_bound (X := X) hX i hi j hj
  · intro X hX
    simpa using h.sumD_bound (X := X) hX

/-!
### (3B) Axiom: the dyadic Gram-decay brick exists

This is the “stable axiom route” requested by the user.  It is project-neutral and does not pin
any values for `a`, `C2`, or `C3`.
-/

axiom q0MinorDyadicGramDecay_exists :
  ∀ Δ : ℝ, ∃ (a : ℕ → ℝ) (C2 C3 : ℝ), Q0MinorDyadicGramDecay Δ a C2 C3

/-!
### (3B, polynomial template) Axiom: dyadic Gram decay with p-series decay

This version pins the decay profile to the standard textbook form `C/(d+1)^p` with `1 < p`.
-/

axiom q0MinorDyadicGramDecayPoly_exists :
  ∀ Δ : ℝ, ∃ (C : ℝ) (p : ℕ) (C2 C3 : ℝ), Q0MinorDyadicGramDecayPoly Δ C p C2 C3

theorem q0MinorDyadicGramDecay_exists_of_poly :
    ∀ Δ : ℝ, ∃ (a : ℕ → ℝ) (C2 C3 : ℝ), Q0MinorDyadicGramDecay Δ a C2 C3 := by
  intro Δ
  rcases q0MinorDyadicGramDecayPoly_exists (Δ := Δ) with ⟨C, p, C2, C3, h⟩
  refine ⟨aPoly C p, C2, C3, ?_⟩
  exact h.to_Q0MinorDyadicGramDecay

/-!
## Packaging: dyadic Gram-decay ⇒ `Q0MinorLeverBundle`

This lemma wires the deterministic dyadic decomposition (`JX`, `dyadicV`, `dyadicD`) together with
the purely combinatorial Crow lemma, leaving only the analytic Gram-decay input as a hypothesis.
-/

theorem leverBundle_of_dyadicGramDecay
    {Δ : ℝ} {a : ℕ → ℝ} {C2 C3 : ℝ}
    (hDy : Q0MinorDyadicGramDecay Δ a C2 C3)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
                  (fun α : ℝ => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ.indicator
                  (fun α : ℝ => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterZone :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ j ∈ (JX X : Finset ℕ),
          IntervalIntegrable
            (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (zoneSet X Δ j).indicator (fun α : ℝ => innerIntegrand X N β α) α))
            volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorLeverBundle Δ a (CrowOf a) C2 C3 := by
  classical
  refine ⟨hDy.a_nonneg, CrowOf_nonneg (a := a) hDy.a_nonneg, hDy.C2_nonneg, hDy.C3_nonneg,
    hInner, hOuterMaj, hOuterMin, ?_⟩
  intro X hX
  refine ⟨JX X, dyadicV X Δ, dyadicD X Δ, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact dyadicD_nonneg (X := X) (Δ := Δ) (j := j)
  · -- decomposition `∑ v_j = toLp corr_integral_minor_Q0`
    have hInner' :
        ∀ N : ℕ, N ∈ EvenIn X H →
          ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ) := by
      intro N hN β
      exact hInner (X := X) (N := N) hX hN β
    have hOuterZone' :
        ∀ N : ℕ, N ∈ EvenIn X H →
          ∀ j ∈ (JX X : Finset ℕ),
            IntervalIntegrable
              (fun β : ℝ =>
                Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
                  (∫ α in (0 : ℝ)..(1 : ℝ),
                    (zoneSet X Δ j).indicator (fun α : ℝ => innerIntegrand X N β α) α))
              volume (0 : ℝ) (1 : ℝ) := by
      intro N hN j hj
      exact hOuterZone (X := X) (N := N) hX hN j hj
    simpa using
      (toLp_corr_integral_minor_Q0_eq_sum_dyadicV (X := X) (Δ := Δ) hX hInner' hOuterZone')
  · -- Gram bound: supplied by the dyadic Gram-decay axiom.
    intro i hi j hj
    exact hDy.gram_bound (X := X) hX i hi j hj
  · -- Row-sum bound: purely combinatorial Crow lemma from summable decay.
    intro i hi
    -- The Crow lemma is uniform over all `i : ℕ`, so we can ignore `hi`.
    simpa [CrowOf] using
      sum_dist_le_crow_of_summable (a := a) hDy.a_nonneg hDy.a_summable (J := (JX X : Finset ℕ)) i
  · -- Diagonal ledger bound: supplied by the dyadic Gram-decay axiom.
    simpa using hDy.sumD_bound (X := X) hX

theorem leverBundle_of_dyadicGramDecayPoly
    {Δ : ℝ} {C : ℝ} {p : ℕ} {C2 C3 : ℝ}
    (hDy : Q0MinorDyadicGramDecayPoly Δ C p C2 C3)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
                  (fun α : ℝ => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ.indicator
                  (fun α : ℝ => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterZone :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ j ∈ (JX X : Finset ℕ),
          IntervalIntegrable
            (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (zoneSet X Δ j).indicator (fun α : ℝ => innerIntegrand X N β α) α))
            volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorLeverBundle Δ (aPoly C p) (CrowOf (aPoly C p)) C2 C3 := by
  refine leverBundle_of_dyadicGramDecay (Δ := Δ) (a := aPoly C p) (C2 := C2) (C3 := C3)
    (hDy := hDy.to_Q0MinorDyadicGramDecay) hInner hOuterMaj hOuterMin hOuterZone

theorem leverBundle_exists_of_dyadicGramDecayPoly
    (Δ : ℝ)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
                  (fun α : ℝ => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ.indicator
                  (fun α : ℝ => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterZone :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ j ∈ (JX X : Finset ℕ),
          IntervalIntegrable
            (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (zoneSet X Δ j).indicator (fun α : ℝ => innerIntegrand X N β α) α))
            volume (0 : ℝ) (1 : ℝ)) :
    ∃ (C : ℝ) (p : ℕ) (C2 C3 : ℝ),
      Q0MinorLeverBundle Δ (aPoly C p) (CrowOf (aPoly C p)) C2 C3 := by
  rcases q0MinorDyadicGramDecayPoly_exists (Δ := Δ) with ⟨C, p, C2, C3, hDy⟩
  refine ⟨C, p, C2, C3, ?_⟩
  exact leverBundle_of_dyadicGramDecayPoly (Δ := Δ) (C := C) (p := p) (C2 := C2) (C3 := C3)
    hDy hInner hOuterMaj hOuterMin hOuterZone

end

end Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
