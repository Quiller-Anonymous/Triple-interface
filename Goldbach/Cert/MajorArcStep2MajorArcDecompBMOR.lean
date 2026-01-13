import Goldbach.Cert.MajorArcStep2MajorArcDecomp
import Goldbach.Cert.MajorArcStep2ExpSumsBMOR

/-!
Major arcs (Step 2b, BMOR-effective variant): coprime-residue decomposition bound.

This is a drop-in replacement for
`Goldbach.Cert.MajorArcStep2MajorArcDecomp.norm_sum_coprimeResidues_sub_mainTerm_le_of_PsiBound`
in the “turnkey/certificate” setting where:

- moduli are *fixed* (`q ≤ Q0 = 30000`), and
- prime distribution in AP is provided via the explicit BMOR ψ-bound (`x ≥ 10^6`),
  rather than the (ineffective) Siegel–Walfisz family `x / (log x)^A`.

Nothing here is sigma-specific; we only repackage Step-2 exponential-sum control plus
`‖∑‖ ≤ ∑‖·‖`.
-/

namespace Goldbach.Cert
namespace MajorArcStep2MajorArcDecompBMOR

open scoped BigOperators

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.ExplicitPNTinAP_BMOR

noncomputable section

variable {q a : ℕ}

theorem norm_sum_coprimeResidues_sub_mainTerm_le_of_BMOR
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hXmin : Xmin ≤ (L - 1))
    (hq : 1 ≤ q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let Rcop : Finset ℕ := (Finset.range q).filter (fun r => Nat.Coprime r q)
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β n
    let Sres (r : ℕ) : ℂ :=
      ∑ n ∈ Finset.Ico L (U + 1), (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ) * gExp β n
    ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
      ≤
      (q : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)))) := by
  classical
  intro Rcop V Sres
  set c : ℂ := (Nat.totient q : ℂ)⁻¹ with hc_def
  -- Rewrite the difference as a sum of residue-class errors.
  have hrewrite :
      (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
        - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V
        =
      ∑ r ∈ Rcop,
        e ((a : ℝ) * (r : ℝ) / q)
          * (Sres r - c * V) := by
    have :
        (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V))
          =
        (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V := by
      calc
        (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V))
            =
          (∑ r ∈ Rcop,
            ((e ((a : ℝ) * (r : ℝ) / q) * Sres r) -
              (e ((a : ℝ) * (r : ℝ) / q) * (c * V)))) := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                simp [mul_sub]
        _ =
          (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - ∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * (c * V) := by
              simp [Finset.sum_sub_distrib]
        _ =
          (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * (c * V) := by
              rw [← Finset.sum_mul (s := Rcop) (f := fun r => e ((a : ℝ) * (r : ℝ) / q)) (a := c * V)]
        _ =
          (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V := by
              simp [mul_assoc, mul_left_comm, mul_comm]
    simpa using this.symm

  have hnorm_sum :
      ‖∑ r ∈ Rcop,
          e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖
        ≤
      ∑ r ∈ Rcop, ‖e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖ := by
    simpa using (norm_sum_le (s := Rcop) (f := fun r =>
      e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)))

  have hterm_norm :
      ∀ r ∈ Rcop,
        ‖e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖
          =
        ‖Sres r - c * V‖ := by
    intro r hr
    simp [norm_e]

  have hbound_each :
      ∀ r ∈ Rcop,
        ‖Sres r - c * V‖
          ≤
          (Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
            * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))) := by
    intro r hr
    have hcop : Nat.Coprime r q := (Finset.mem_filter.mp hr).2
    have hstep :=
      Goldbach.Cert.MajorArcStep2ExpSumsBMOR.norm_sum_aTerm_gExp_Ico_sub_mainTerm_le_of_BMOR
        (q := q) (a := r) (L := L) (U := U) hLU hL hXmin hq hqQ0 hcop (β := β) hβ
    -- Unfold `Sres` and `V`, and rewrite the scalar `c`.
    simpa [Sres, V, hc_def, one_div] using hstep

  have hsum_bound :
      (∑ r ∈ Rcop, ‖Sres r - c * V‖)
        ≤
      (Rcop.card : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)))) := by
    have := Finset.sum_le_sum (fun r hr => hbound_each r hr)
    simpa using this

  have hcard_le : (Rcop.card : ℝ) ≤ (q : ℝ) := by
    have : Rcop.card ≤ q := by
      dsimp [Rcop]
      simpa using
        (Finset.card_filter_le (s := Finset.range q) (p := fun r => Nat.Coprime r q))
    exact_mod_cast this

  have hmain :
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
        ≤
      (Rcop.card : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)))) := by
    calc
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
          = ‖∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖ := by
              simpa using congrArg (fun z : ℂ => ‖z‖) hrewrite
      _ ≤ ∑ r ∈ Rcop, ‖e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖ := hnorm_sum
      _ = ∑ r ∈ Rcop, ‖Sres r - c * V‖ := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              exact hterm_norm r hr
      _ ≤ (Rcop.card : ℝ) *
            ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
              * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)))) := hsum_bound

  have hnonneg :
      0 ≤
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)))) := by
    have hlog_pos : 0 < Real.log ((L - 1 : ℕ) : ℝ) := by
      have h2 : (2 : ℕ) ≤ (L - 1 : ℕ) := le_trans (by
        norm_num [Xmin]) hXmin
      have h2' : (2 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast h2
      have h1 : (1 : ℝ) < ((L - 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2'
      exact Real.log_pos h1
    have hC : 0 ≤ Cψ := Cψ_nonneg
    have hfrac_nonneg : 0 ≤ Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ) :=
      div_nonneg (mul_nonneg hC (by positivity)) (le_of_lt hlog_pos)
    have hfac_nonneg :
        0 ≤ (2 : ℝ) * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)) := by
      have : 0 ≤ (1 : ℝ) + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|) := by
        have : 0 ≤ ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|) := by
          have : 0 ≤ (1 : ℝ) + 4 * Real.pi * |β| := by nlinarith [Real.pi_pos, abs_nonneg β]
          exact mul_nonneg (by positivity) this
        linarith
      nlinarith [this]
    exact mul_nonneg hfrac_nonneg hfac_nonneg

  -- Replace `Rcop.card` by `q`.
  have hfinal :
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
        ≤
      (q : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)))) := by
    have := le_trans hmain (by
      -- multiply both sides by the nonnegative RHS factor.
      exact mul_le_mul_of_nonneg_right hcard_le hnonneg)
    simpa [mul_assoc] using this

  -- Replace `c` by the explicit real scalar and finish.
  have hc :
      c = ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) := by
    simp [hc_def, one_div]
  simpa [hc, mul_assoc, mul_left_comm, mul_comm] using hfinal

end

end MajorArcStep2MajorArcDecompBMOR
end Goldbach.Cert

