import Goldbach.Cert.ExplicitPNTinAP_BMOR
import Goldbach.Cert.SiegelWalfiszWeighted
import Goldbach.AO_OffDiag.TailBlock

/-!
Consequences of the explicit PNT-in-AP ψ-bound (`ExplicitPNTinAP_BMOR.psi_bound`).

The goal of this file is to provide “drop-in” bounds on the SW deviation

`E(x) = ψ(x; q, a) - x/φ(q)`

in the forms that later major-arc bookkeeping typically consumes: a pointwise bound and a uniform
bound over an interval `x ∈ [X,U]`.

This file does **not** attempt to rerun the whole major-arc chain; it just exposes the algebraic
pieces needed to do so later (or to build a certificate/checker that uses the explicit constants).
-/

namespace Goldbach.Cert
namespace ExplicitPNTinAP_BMOR
namespace Consequences

open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.SiegelWalfiszWeighted
open Goldbach.AO_OffDiag.TailBlock

noncomputable section

variable (q a : ℕ)

lemma Q0_le_Qmax : (Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) ≤ Qmax := by
  -- `30000 ≤ 100000`
  norm_num [Goldbach.AO_OffDiag.TailBlock.Q0, Qmax]

private lemma log_pos_of_Xmin_le {X : ℕ} (hX : Xmin ≤ X) : 0 < Real.log (X : ℝ) := by
  have hX2 : (2 : ℕ) ≤ X := le_trans (by
      -- `2 ≤ 10^6`
      norm_num [Xmin]) hX
  have hX2' : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have h1X : (1 : ℝ) < (X : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hX2'
  exact Real.log_pos h1X

/-- Pointwise bound for the SW deviation `E(x)` from the explicit ψ(AP) estimate. -/
theorem abs_E_le_of_psi_bound
    {x : ℕ} (hx : Xmin ≤ x) (hq : 1 ≤ q) (hqQ : q ≤ Qmax) (hcop : Nat.Coprime a q) :
    |E (q := q) (a := a) x| ≤ Cψ * (x : ℝ) / Real.log (x : ℝ) := by
  -- `E x` is definitionally `psi x q a - x/φ(q)`.
  simpa [SiegelWalfiszWeighted.E] using (psi_bound (x := x) (q := q) (a := a) hx hq hqQ hcop)

/--
Uniform `E`-bound on an interval `x ∈ [X,U]`, in the “`U / log X`” form.

This uses only monotonicity of `log` on `x ≥ 2` and the trivial monotonicity `x ≤ U`.
-/
theorem abs_E_le_uniform_on_Icc
    {X U : ℕ} (hX : Xmin ≤ X)
    (hq : 1 ≤ q) (hqQ : q ≤ Qmax) (hcop : Nat.Coprime a q) :
    ∀ {x : ℕ}, x ∈ Finset.Icc X U →
      |E (q := q) (a := a) x| ≤ Cψ * (U : ℝ) / Real.log (X : ℝ) := by
  intro x hx
  have hxX : X ≤ x := (Finset.mem_Icc.mp hx).1
  have hxU : x ≤ U := (Finset.mem_Icc.mp hx).2
  have hx' : Xmin ≤ x := le_trans hX hxX

  have hlogX_pos : 0 < Real.log (X : ℝ) := log_pos_of_Xmin_le (X := X) hX
  have hlogx_pos : 0 < Real.log (x : ℝ) := log_pos_of_Xmin_le (X := x) hx'
  have hlog_mono : Real.log (X : ℝ) ≤ Real.log (x : ℝ) := by
    have hXpos : 0 < (X : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by
      -- `0 < 10^6`
      norm_num [Xmin]) hX)
    exact Real.log_le_log hXpos (by exact_mod_cast hxX)
  have hpow_inv :
      (Real.log (x : ℝ))⁻¹ ≤ (Real.log (X : ℝ))⁻¹ :=
    (inv_le_inv₀ hlogx_pos hlogX_pos).2 hlog_mono

  have hxU_real : (x : ℝ) ≤ (U : ℝ) := by exact_mod_cast hxU
  have hdiv :
      (x : ℝ) / Real.log (x : ℝ) ≤ (U : ℝ) / Real.log (X : ℝ) := by
    -- `x/log x = x * (log x)⁻¹ ≤ U * (log X)⁻¹`
    calc
      (x : ℝ) / Real.log (x : ℝ) = (x : ℝ) * (Real.log (x : ℝ))⁻¹ := by
        simp [div_eq_mul_inv]
      _ ≤ (U : ℝ) * (Real.log (x : ℝ))⁻¹ := by
        exact mul_le_mul_of_nonneg_right hxU_real (by positivity)
      _ ≤ (U : ℝ) * (Real.log (X : ℝ))⁻¹ := by
        exact mul_le_mul_of_nonneg_left hpow_inv (by positivity)
      _ = (U : ℝ) / Real.log (X : ℝ) := by simp [div_eq_mul_inv]

  have hEx := abs_E_le_of_psi_bound (q := q) (a := a) (x := x) hx' hq hqQ hcop
  have hC_nonneg : 0 ≤ Cψ := Cψ_nonneg
  have := mul_le_mul_of_nonneg_left hdiv hC_nonneg
  exact le_trans hEx (by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this)

/-! Convenience specialization: the project’s `Q0 = 30000` lies inside BMOR’s `Qmax = 100000`. -/

theorem abs_E_le_uniform_on_Icc_Q0
    {X U : ℕ} (hX : Xmin ≤ X)
    (hq : 1 ≤ q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0) (hcop : Nat.Coprime a q) :
    ∀ {x : ℕ}, x ∈ Finset.Icc X U →
      |E (q := q) (a := a) x| ≤ Cψ * (U : ℝ) / Real.log (X : ℝ) := by
  intro x hx
  have hqQ : q ≤ Qmax :=
    le_trans hqQ0 (Q0_le_Qmax : (Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) ≤ Qmax)
  exact abs_E_le_uniform_on_Icc (q := q) (a := a) (X := X) (U := U) hX hq hqQ hcop hx

end

end Consequences
end ExplicitPNTinAP_BMOR
end Goldbach.Cert
