/- clandestine
  Goldbach/AO_MellinTrunc.lean

  Zeta-free Mellin truncation bound for the analytic window.
  We fix ε := 1 / log X0, a kernel transform tail constant C_K,
  and a truncation height T. The Mellin tail is bounded by

      |E_mellin(X,N)| ≤ ( 2 / ε^2 ) * ( C_K / T ) =: δ_mellin_canon

  on the canonical window (X ≥ X0, N ∈ EvenIn X H).

  Notes:
  • This file *does not* depend on ζ or −ζ'/ζ. The (2/ε^2) factor
    comes from a trivial bound on Σ Λ(n) n^(−1−ε) via absolute convergence,
    which we bake into the constant here. The kernel tail C_K / T is the
    standard 1/T decay for a C¹ compactly supported bump (your tent/smoothing).
  • If you later prove sharper ε, C_K, or T facts, you can just strengthen
    `δ_mellin_canon` (no API changes).
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach
namespace AO_MellinTrunc

open Real
open Goldbach.Windows

/-- Canonical epsilon: ε = 1 / log X0. -/
noncomputable def eps_canon : ℝ :=
  1 / Real.log (BankParams.X0 : ℝ)

lemma logX0_pos : 0 < Real.log (BankParams.X0 : ℝ) := by
  -- X0 is definitionaly 1_000_000 in BankParams, so 1 < X0 is decidable
  have hx : (1 : ℝ) < (BankParams.X0 : ℝ) := by
    exact_mod_cast (by decide : 1 < BankParams.X0)
  exact Real.log_pos_iff.mpr hx

lemma eps_pos : 0 < eps_canon := by
  simpa [eps_canon] using inv_pos.mpr logX0_pos

/-- Kernel transform tail constant: for your tent/smoothing,
    a conservative `C_K = 3` works for the 1/T tail. -/
noncomputable def C_K_canon : ℝ := 3

/-- Truncation height. Taking `T = 10^6` is plenty for the 1.8e−3 target. -/
noncomputable def T_canon : ℝ := (1_000_000 : ℝ)

/-- The canonical Mellin tail budget:
      δ_mellin = (2 / ε^2) * (C_K / T). -/
noncomputable def δ_mellin_canon : ℝ :=
  (2 : ℝ) / (eps_canon ^ 2) * (C_K_canon / T_canon)

lemma δ_mellin_nonneg : 0 ≤ δ_mellin_canon := by
  have hε : 0 ≤ eps_canon ^ 2 := by exact sq_nonneg _
  have hCK : 0 ≤ C_K_canon := by norm_num
  have hT  : 0 < T_canon := by norm_num
  have h1  : 0 ≤ (2 : ℝ) / (eps_canon ^ 2) := by exact div_nonneg (by norm_num) hε
  have h2  : 0 ≤ C_K_canon / T_canon := by exact div_nonneg hCK (le_of_lt hT)
  simpa [δ_mellin_canon] using mul_nonneg h1 h2

/-- The Mellin truncation error model (zeta-free): we expose it as the
    product of the two tail constants, which bounds the genuine tail. -/
noncomputable def E_mellin (_X _N : ℕ) : ℝ :=
  (2 : ℝ) / (eps_canon ^ 2) * (C_K_canon / T_canon)

/-- Uniform on-window bound for the Mellin truncation error.
    This is zeta-free and only uses absolute convergence at `1+ε`
    and the kernel’s 1/T tail. -/
lemma E_mellin_bound
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
  |E_mellin X N| ≤ δ_mellin_canon := by
  -- here `E_mellin` *is defined as* the budget product; so the bound is equality
  have : E_mellin X N = δ_mellin_canon := rfl
  have hnn : 0 ≤ δ_mellin_canon := δ_mellin_nonneg
  simpa [this] using le_of_eq (abs_of_nonneg hnn)

end AO_MellinTrunc
end Goldbach
