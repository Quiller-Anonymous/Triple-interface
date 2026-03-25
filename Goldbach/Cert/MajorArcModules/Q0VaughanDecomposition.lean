import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXCoreCollapse
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.VonMangoldt

/-!
Elementary Vaughan-type decomposition scaffolding for the packet-orthogonality interface.

This file does not prove the full analytic Vaughan identity. It packages the coefficient sequences,
their basic divisor-style bounds, a dyadic shell wrapper, and a theorem-shaped smooth-cutoff
boundary corresponding to the paper's Lemma 6.32.
-/

namespace Goldbach.Cert.MajorArcModules.Q0VaughanDecomposition

open scoped BigOperators ArithmeticFunction.Moebius

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXCoreCollapse

noncomputable section

/-- `τ(n)` as the positive-divisor count, reused from the existing TT* route. -/
abbrev tau (n : ℕ) : ℕ := Q0MajorTailTTStarStep5LXCoreCollapse.tau n

/-- Vaughan's medium-range Möbius coefficient. -/
noncomputable def vaughanAlpha (d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℤ)

/-- Vaughan's medium/large von Mangoldt coefficient. -/
noncomputable def vaughanBeta (m : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt m

/-- Raw Type-II aggregate at level `k`. -/
noncomputable def vaughanTypeII (k U V X : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc U (X / V), ∑ m ∈ Finset.Ioc V (X / d),
    if d * m = k then vaughanAlpha d * vaughanBeta m else 0

/-- Dyadic shell restriction of the Type-II aggregate. -/
noncomputable def vaughanTypeIIShell (k A B : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc A (2 * A), ∑ m ∈ Finset.Icc B (2 * B),
    if d * m = k then vaughanAlpha d * vaughanBeta m else 0

/-- Explicit finite support set for a dyadic Vaughan shell. -/
noncomputable def vaughanShellSupport (A B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc A (2 * A)).product (Finset.Icc B (2 * B))

/-- Coarse dyadic shell index set; its cardinality is `O(log^2 X)` in the usual heuristic sense. -/
noncomputable def dyadicShellPairs (X : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (Nat.log2 X + 1)).product (Finset.range (Nat.log2 X + 1))

/-- The theorem-shaped smooth-cutoff boundary corresponding to Lemma 6.32 in the paper. -/
axiom smoothApproximationErrorOnDyadicShell
    (A B U V X : ℕ) :
    Prop

theorem abs_vaughanAlpha_le_one (d : ℕ) :
    |vaughanAlpha d| ≤ 1 := by
  change |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

private theorem one_mem_divisors {n : ℕ} (hn : n ≠ 0) :
    1 ∈ Nat.divisors n :=
  Nat.mem_divisors.2 ⟨one_dvd n, hn⟩

private theorem self_mem_divisors {n : ℕ} (hn : n ≠ 0) :
    n ∈ Nat.divisors n :=
  Nat.mem_divisors.2 ⟨dvd_rfl, hn⟩

theorem two_le_tau_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ tau n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hsubset : ({1, n} : Finset ℕ) ⊆ Nat.divisors n := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact one_mem_divisors hn0
    · exact self_mem_divisors hn0
  have hcard : ({1, n} : Finset ℕ).card = 2 := by
    have hne : n ≠ 1 := by omega
    exact Finset.card_pair (by simpa [eq_comm] using hne)
  have hle := Finset.card_le_card hsubset
  simpa [tau, hcard] using hle

theorem abs_vaughanAlpha_le_tau_pow {d C : ℕ} (hd : 2 ≤ d) :
    |vaughanAlpha d| ≤ (tau d : ℝ) ^ C := by
  have h1 : |vaughanAlpha d| ≤ 1 := abs_vaughanAlpha_le_one d
  have htau : (1 : ℝ) ≤ (tau d : ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) (two_le_tau_of_two_le hd))
  have hpow : (1 : ℝ) ≤ (tau d : ℝ) ^ C := by
    induction C with
    | zero =>
        simp
    | succ C ih =>
        have htau_nonneg : 0 ≤ (tau d : ℝ) := by positivity
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (tau d : ℝ) ^ C * (tau d : ℝ) := by
              exact mul_le_mul ih htau (by positivity) (by positivity)
          _ = (tau d : ℝ) ^ (C + 1) := by simp [pow_succ]
  exact le_trans h1 hpow

theorem vaughanBeta_nonneg (m : ℕ) :
    0 ≤ vaughanBeta m := by
  exact ArithmeticFunction.vonMangoldt_nonneg (n := m)

theorem vaughanBeta_le_logX_quarter_tau_sq
    {X m : ℕ} (hX : 2 ≤ X) (hm : 2 ≤ m) (hmX : m ≤ X) :
    vaughanBeta m ≤ (Real.log X / 4) * (tau m : ℝ) ^ 2 := by
  have hlogm : vaughanBeta m ≤ Real.log m := by
    simpa [vaughanBeta] using (ArithmeticFunction.vonMangoldt_le_log (n := m))
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hX)
  have hlog_le : Real.log m ≤ Real.log X := Real.log_le_log hm_pos (by exact_mod_cast hmX)
  have htau2 : (4 : ℝ) ≤ (tau m : ℝ) ^ 2 := by
    have htau : (2 : ℝ) ≤ (tau m : ℝ) := by
      exact_mod_cast two_le_tau_of_two_le hm
    nlinarith
  have hscale_nonneg : 0 ≤ Real.log X / 4 := by
    have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ 2) hX
    have hlog_nonneg : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX1)
    positivity
  have hscale :
      Real.log X ≤ (Real.log X / 4) * (tau m : ℝ) ^ 2 := by
    calc
      Real.log X = (Real.log X / 4) * 4 := by
        ring
      _ ≤ (Real.log X / 4) * (tau m : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left htau2 hscale_nonneg
  exact le_trans (le_trans hlogm hlog_le) hscale

theorem mem_vaughanShellSupport_iff
    {A B d m : ℕ} :
    (d, m) ∈ vaughanShellSupport A B
      ↔ d ∈ Finset.Icc A (2 * A) ∧ m ∈ Finset.Icc B (2 * B) := by
  simp [vaughanShellSupport]

theorem vaughanTypeIIShell_has_dyadic_support
    {A B d m : ℕ}
    (hmem : (d, m) ∈ vaughanShellSupport A B) :
    d ∈ Finset.Icc A (2 * A) ∧ m ∈ Finset.Icc B (2 * B) :=
  mem_vaughanShellSupport_iff.mp hmem

theorem dyadicShellPairs_card_eq_logSq (X : ℕ) :
    (dyadicShellPairs X).card = (Nat.log2 X + 1) ^ 2 := by
  simp [dyadicShellPairs, pow_two]

theorem dyadicShellPairs_card_le_logSqSucc (X : ℕ) :
    (dyadicShellPairs X).card ≤ (Nat.log2 X + 1) ^ 2 := by
  rw [dyadicShellPairs_card_eq_logSq]

end

end Goldbach.Cert.MajorArcModules.Q0VaughanDecomposition
