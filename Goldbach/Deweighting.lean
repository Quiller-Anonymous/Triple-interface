import Mathlib.NumberTheory.VonMangoldt
import Goldbach.BG_Identity
import Goldbach.Rep
import Goldbach.Windows

/-!
`Goldbach/Deweighting.lean`

Phase D (deweighting prep): this file is *not* wired into the main pipeline yet.
It exists to hold a clean, compilation-stable interface for the eventual
“weights bridge” proof (deweighting + contamination control), plus a few
elementary lemmas we will reuse in that development.

No bespoke axioms are introduced here; the bridge itself is packaged as a
hypothesis/record so downstream wiring stays explicit.
-/

namespace Goldbach.Deweighting

open Real
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open scoped BigOperators
open scoped ArithmeticFunction

/-- Elementary: for `n ≥ 2`, the normalized von Mangoldt weight has magnitude at most `1`. -/
lemma abs_vonMangoldt_div_log_le_one {n : ℕ} (hn : 2 ≤ n) :
    |(Λ n) / Real.log (n : ℝ)| ≤ 1 := by
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
  have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos h1
  have hlog_ne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hlog_pos
  have hΛ_le : (Λ n) ≤ Real.log (n : ℝ) := by
    simpa using (ArithmeticFunction.vonMangoldt_le_log (n := n))
  have hdiv_le :
      (Λ n) / Real.log (n : ℝ) ≤ 1 := by
    have h :=
      div_le_div_of_nonneg_right hΛ_le (le_of_lt hlog_pos)
    simpa [div_self hlog_ne] using h
  have hnonneg : 0 ≤ (Λ n) / Real.log (n : ℝ) := by
    exact div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (le_of_lt hlog_pos)
  simpa [abs_of_nonneg hnonneg] using hdiv_le

/--
Deweighting bridge (to be proved later): a uniform bound on the gap between the
raw representation count and the BG full convolution on the canonical window.

This is deliberately a *record* rather than an instance, so the project cannot
silently assume it.
-/
structure DeweightingBridge (δ : ℝ) : Prop where
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N| ≤ δ

end Goldbach.Deweighting
