import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.Interval.Finset.Nat
import Twin.PaperParams
import Twin.ChecklistModel
import Twin.ChecklistIntegrability
import Twin.MajorArc.MajMass
import Twin.MajorArc.GateBookkeeping
import Twin.CLSL2
import Twin.AnalyticCore
import Twin.Bridge
import Twin.Ledger

/-
  Twin/ChecklistAxioms.lean

  Single place to collect the remaining “conventional analytic” assumptions for the
  checklist-route Twin pipeline, specialized to the frozen model (`Twin.ChecklistModel`)
  and the concrete paper parameters `Twin.PaperParams.P`.

  These are the objects you will progressively replace by real Lean proofs.
-/

namespace Twin.ChecklistAxioms

noncomputable section

open Twin
open scoped ComplexConjugate

private lemma norm_chi_add (t : ℝ) : ‖Twin.SW.χ_add t‖ = 1 := by
  simp [Twin.SW.χ_add, Complex.norm_exp]

abbrev P : Twin.GoalAPI.Params := Twin.PaperParams.P
abbrev SS : ℝ := Twin.fullTruncSingularSeries P.S

/-!
## Error channels (paper-faithful definitions)

We define **global** error channels `emin, eds : ℕ → ℝ` from window-level analytic quantities
by distributing each window error across the `H+1` lattice points it touches, using a local
`sup` over the possible window-start indices.

These are designed so that, for every window start `X`, one has purely by definition:

* `|minorMass X| ≤ windowSum X H emin`,
* `|fullMass X - localizedTwinMass X H| ≤ windowSum X H eds`.

The *budgets* for `emin` and `eds` (`/9` and `/3`) remain paper-facing analytic obligations.
-/

abbrev A : ℝ := Twin.ChecklistModel.A
abbrev B : ℝ := Twin.ChecklistModel.B
abbrev Lambda : ℕ → ℝ := Twin.ChecklistModel.Λ
abbrev Wwin : ℝ → ℝ := Twin.ChecklistModel.W
abbrev What : ℝ → ℝ := Twin.ChecklistModel.W_hat

variable (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)

def N : ℝ := (P.H : ℝ) + 1

private lemma N_pos : 0 < N := by
  have hH : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
  simpa [N] using add_pos_of_nonneg_of_pos hH (by norm_num)

noncomputable def fullMassAt (X : ℕ) : ℝ :=
  Twin.MajorArc.fullMass (Λ := Lambda) (W := Wwin) X P.H

noncomputable def minorMassAt (X : ℕ) : ℝ :=
  Twin.MajorArc.minorMass (sme := sme) X P.H

noncomputable def dsMassAt (X : ℕ) : ℝ :=
  |fullMassAt X - Twin.Bridge.localizedTwinMass X P.H|

private lemma dsMassAt_nonneg (X : ℕ) : 0 ≤ dsMassAt X := by
  simp [dsMassAt]

private lemma minorMassAt_nonneg (X : ℕ) : 0 ≤ |minorMassAt (sme := sme) X| := abs_nonneg _

noncomputable def emin (n : ℕ) : ℝ :=
  (Finset.Icc (n - P.H) n).sup' (by
    refine ⟨n, ?_⟩
    exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩) (fun X => |minorMassAt (sme := sme) X| / N)

noncomputable def eds (n : ℕ) : ℝ :=
  (Finset.Icc (n - P.H) n).sup' (by
    refine ⟨n, ?_⟩
    exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩) (fun X => dsMassAt X / N)

/-!
### Budget reductions (pure bookkeeping)

The definitions of `emin`/`eds` distribute each window-level error across the `H+1` lattice points
it touches via a local `sup`.  The resulting window inequalities can be reduced to bounds on
the *window-level* masses `minorMassAt` and `dsMassAt` over a slightly enlarged index set.

These lemmas are purely finitary inequalities (no analytic number theory).
-/

private lemma emin_le_sum_local (n : ℕ) :
    emin (sme := sme) n
      ≤ (Finset.Icc (n - P.H) n).sum (fun X => |minorMassAt (sme := sme) X| / N) := by
  classical
  -- `sup ≤ sum` since each summand is nonnegative and bounded by the total sum.
  unfold emin
  refine Finset.sup'_le (by
      refine ⟨n, ?_⟩
      exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩)
    (fun X : ℕ => |minorMassAt (sme := sme) X| / N) ?_
  intro X hX
  exact
    Finset.single_le_sum
      (f := fun Y : ℕ => |minorMassAt (sme := sme) Y| / N)
      (fun Y _ => div_nonneg (minorMassAt_nonneg (sme := sme) Y) (le_of_lt N_pos))
      hX

private lemma eds_le_sum_local (n : ℕ) :
    eds n
      ≤ (Finset.Icc (n - P.H) n).sum (fun X => dsMassAt X / N) := by
  classical
  unfold eds
  refine Finset.sup'_le (by
      refine ⟨n, ?_⟩
      exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩)
    (fun X : ℕ => dsMassAt X / N) ?_
  intro X hX
  exact
    Finset.single_le_sum
      (f := fun Y : ℕ => dsMassAt Y / N)
      (fun Y _ => div_nonneg (dsMassAt_nonneg Y) (le_of_lt N_pos))
      hX

private lemma emin_sq_le_card_mul_sum_sq_local (n : ℕ) :
    (emin (sme := sme) n) ^ 2
      ≤ ((Finset.Icc (n - P.H) n).card : ℝ)
        * (Finset.Icc (n - P.H) n).sum (fun X => (|minorMassAt (sme := sme) X| / N) ^ 2) := by
  classical
  -- Compare to the square of the sum, then use the `sq_sum_le_card_mul_sum_sq` inequality.
  have hle :
      emin (sme := sme) n
        ≤ (Finset.Icc (n - P.H) n).sum (fun X => |minorMassAt (sme := sme) X| / N) :=
    emin_le_sum_local (sme := sme) (n := n)
  have hsum_nonneg :
      0 ≤ (Finset.Icc (n - P.H) n).sum (fun X => |minorMassAt (sme := sme) X| / N) := by
    refine Finset.sum_nonneg ?_
    intro X hX
    exact div_nonneg (minorMassAt_nonneg (sme := sme) X) (le_of_lt N_pos)
  have hem_nonneg : 0 ≤ emin (sme := sme) n := by
    -- `emin` is a supremum of nonnegative terms.
    have hn_mem : n ∈ Finset.Icc (n - P.H) n := (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩
    have h0 : 0 ≤ |minorMassAt (sme := sme) n| / N :=
      div_nonneg (minorMassAt_nonneg (sme := sme) n) (le_of_lt N_pos)
    have h1 : |minorMassAt (sme := sme) n| / N ≤ emin (sme := sme) n := by
      unfold emin
      exact Finset.le_sup' (s := Finset.Icc (n - P.H) n)
        (f := fun X : ℕ => |minorMassAt (sme := sme) X| / N) hn_mem
    exact le_trans h0 h1
  have hsq :
      (emin (sme := sme) n) ^ 2
        ≤ ((Finset.Icc (n - P.H) n).sum (fun X => |minorMassAt (sme := sme) X| / N)) ^ 2 := by
    -- monotonicity of squaring on nonnegative reals
    nlinarith [hle, hem_nonneg, hsum_nonneg]
  have hcs :
      ((Finset.Icc (n - P.H) n).sum (fun X => |minorMassAt (sme := sme) X| / N)) ^ 2
        ≤ ((Finset.Icc (n - P.H) n).card : ℝ)
            * (Finset.Icc (n - P.H) n).sum (fun X => (|minorMassAt (sme := sme) X| / N) ^ 2) := by
    -- Cauchy–Schwarz / Chebyshev special case.
    exact
      (sq_sum_le_card_mul_sum_sq (s := Finset.Icc (n - P.H) n)
        (f := fun X : ℕ => |minorMassAt (sme := sme) X| / N))
  exact le_trans hsq hcs

/-- Canonical “buffered window” index set around `X`: `[X-H, X+H]`.

This is the index set on which the paper-facing minor-arc and desmoothing budgets are stated. -/
def bigIcc (X : ℕ) : Finset ℕ :=
  Finset.Icc (X - P.H) (X + P.H)

private lemma localIcc_subset_bigIcc (X k : ℕ) (hk : k ≤ P.H) :
    Finset.Icc ((X + k) - P.H) (X + k) ⊆ bigIcc (X := X) := by
  intro Y hY
  rcases (Finset.mem_Icc).1 hY with ⟨hlow, hhigh⟩
  refine (Finset.mem_Icc).2 ?_
  constructor
  · have hX : X - P.H ≤ (X + k) - P.H := by
      exact Nat.sub_le_sub_right (Nat.le_add_right X k) P.H
    exact le_trans hX hlow
  · have hXk : X + k ≤ X + P.H := Nat.add_le_add_left hk X
    exact le_trans hhigh hXk

private lemma card_localIcc_le_span (n : ℕ) :
    (Finset.Icc (n - P.H) n).card ≤ P.H + 1 := by
  -- `card (Icc a b) = b + 1 - a`, then finish by cases on `H ≤ n`.
  have hcard : (Finset.Icc (n - P.H) n).card = n + 1 - (n - P.H) := by
    simpa using (Nat.card_Icc (a := n - P.H) (b := n))
  by_cases hH : P.H ≤ n
  · -- In this case the interval has length exactly `H+1`.
    set m : ℕ := n - P.H with hm
    have hm_add : m + P.H = n := by
      -- `n - H + H = n`, then rewrite `n - H` as `m`.
      simpa [hm] using (Nat.sub_add_cancel hH)
    have hEq : n + 1 - (n - P.H) = P.H + 1 := by
      -- rewrite the subterm as `m` so rewriting `n` does not re-enter subtraction
      rw [← hm]
      -- now `n + 1 - m`
      rw [hm_add.symm]
      -- now `(m + H) + 1 - m = H + 1`
      calc
        (m + P.H) + 1 - m = m + (P.H + 1) - m := by
          simpa [Nat.add_assoc]
        _ = P.H + 1 := Nat.add_sub_cancel_left _ _
    have hcardEq : (Finset.Icc (n - P.H) n).card = P.H + 1 := by
      calc
        (Finset.Icc (n - P.H) n).card = n + 1 - (n - P.H) := hcard
        _ = P.H + 1 := hEq
    exact hcardEq.le
  · -- Here `n < H`, so the interval is `[0,n]` and has size `n+1 ≤ H+1`.
    have h0 : n - P.H = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hH)
    have hnle : n + 1 ≤ P.H + 1 := Nat.succ_le_succ (le_of_not_ge hH)
    -- rewrite the card formula and reduce to `n+1 ≤ H+1`
    simpa [hcard, h0] using hnle

private lemma windowSum_emin_sq_le_big_sum_minor_sq (X : ℕ) :
    Twin.Ledger.windowSum X P.H (fun n => (emin (sme := sme) n) ^ 2)
      ≤ (P.H + 1 : ℝ) ^ 2
        * (bigIcc (X := X)).sum (fun Y => (|minorMassAt (sme := sme) Y| / N) ^ 2) := by
  classical
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
  set g : ℕ → ℝ := fun Y => (|minorMassAt (sme := sme) Y| / N) ^ 2 with hg
  have g_nonneg : ∀ Y, 0 ≤ g Y := by intro Y; exact sq_nonneg _
  set bigSum : ℝ := (bigIcc (X := X)).sum g
  have bigSum_nonneg : 0 ≤ bigSum := by
    exact Finset.sum_nonneg (fun Y _ => g_nonneg Y)

  have hterm :
      ∀ k ∈ Finset.range (P.H + 1),
        (emin (sme := sme) (X + k)) ^ 2 ≤ (P.H + 1 : ℝ) * bigSum := by
    intro k hk
    have hk_le : k ≤ P.H := by
      have : k < P.H + 1 := Finset.mem_range.1 hk
      exact Nat.lt_succ_iff.1 this
    have hlocal := emin_sq_le_card_mul_sum_sq_local (sme := sme) (n := X + k)
    have hcard :
        ((Finset.Icc ((X + k) - P.H) (X + k)).card : ℝ) ≤ (P.H + 1 : ℝ) := by
      exact_mod_cast (card_localIcc_le_span (n := X + k))
    have hsub : Finset.Icc ((X + k) - P.H) (X + k) ⊆ bigIcc (X := X) :=
      localIcc_subset_bigIcc (X := X) (k := k) hk_le
    have hsum_le :
        (Finset.Icc ((X + k) - P.H) (X + k)).sum g ≤ bigSum := by
      simpa [bigSum] using
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun Y _ _ => g_nonneg Y))
    have hsum_nonneg : 0 ≤ (Finset.Icc ((X + k) - P.H) (X + k)).sum g := by
      exact Finset.sum_nonneg (fun Y _ => g_nonneg Y)
    have hlocal' :
        (emin (sme := sme) (X + k)) ^ 2
          ≤ ((Finset.Icc ((X + k) - P.H) (X + k)).card : ℝ)
              * (Finset.Icc ((X + k) - P.H) (X + k)).sum g := by
      -- rewrite the `sum g` target to the explicit square-summand used by `hlocal`
      have hsum :
          (Finset.Icc ((X + k) - P.H) (X + k)).sum g
            =
            (Finset.Icc ((X + k) - P.H) (X + k)).sum
              (fun X => (|minorMassAt (sme := sme) X| / N) ^ 2) :=
        congrArg (fun f : ℕ → ℝ => (Finset.Icc ((X + k) - P.H) (X + k)).sum f) hg
      -- avoid `simp`/`simpa` here to prevent recursion-depth blowups
      rw [hsum]
      exact hlocal
    have h1 :
        (emin (sme := sme) (X + k)) ^ 2
          ≤ (P.H + 1 : ℝ) * (Finset.Icc ((X + k) - P.H) (X + k)).sum g := by
      exact le_trans hlocal' (mul_le_mul_of_nonneg_right hcard hsum_nonneg)
    have h2 :
        (P.H + 1 : ℝ) * (Finset.Icc ((X + k) - P.H) (X + k)).sum g
          ≤ (P.H + 1 : ℝ) * bigSum := by
      have hH_nonneg : 0 ≤ (P.H + 1 : ℝ) := by
        exact_mod_cast Nat.zero_le (P.H + 1)
      exact mul_le_mul_of_nonneg_left hsum_le hH_nonneg
    exact le_trans h1 h2

  have hsum :
      (Finset.range (P.H + 1)).sum (fun k => (emin (sme := sme) (X + k)) ^ 2)
        ≤ (Finset.range (P.H + 1)).sum (fun _k => (P.H + 1 : ℝ) * bigSum) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hterm k hk

  have hconst :
      (Finset.range (P.H + 1)).sum (fun _k => (P.H + 1 : ℝ) * bigSum)
        = (P.H + 1 : ℝ) ^ 2 * bigSum := by
    -- Use `sum_const` + `card_range`, then rewrite `nsmul` and reassociate.
    have h1 :
        (Finset.range (P.H + 1)).sum (fun _k => (P.H + 1 : ℝ) * bigSum)
          = (Finset.range (P.H + 1)).card • ((P.H + 1 : ℝ) * bigSum) := by
      simpa using (Finset.sum_const (s := Finset.range (P.H + 1)) ((P.H + 1 : ℝ) * bigSum))
    -- `card (range (H+1)) = H+1`
    have h2 :
        (Finset.range (P.H + 1)).card • ((P.H + 1 : ℝ) * bigSum)
          = (P.H + 1 : ℝ) * ((P.H + 1 : ℝ) * bigSum) := by
      -- convert `nsmul` to multiplication on `ℝ`
      simp [Finset.card_range, nsmul_eq_mul, mul_assoc]
    -- fold into `(H+1)^2 * bigSum`
    calc
      (Finset.range (P.H + 1)).sum (fun _k => (P.H + 1 : ℝ) * bigSum)
          = (P.H + 1 : ℝ) * ((P.H + 1 : ℝ) * bigSum) := by simpa [h1] using congrArg id h2
      _ = (P.H + 1 : ℝ) ^ 2 * bigSum := by
          simp [pow_two, mul_assoc]

  have hfinal :
      (Finset.range (P.H + 1)).sum (fun k => (emin (sme := sme) (X + k)) ^ 2)
        ≤ (P.H + 1 : ℝ) ^ 2 * bigSum := by
    exact le_trans hsum (le_of_eq hconst)

  simpa [bigSum, g] using hfinal

private lemma windowSum_eds_le_big_sum_dsMassAt (X : ℕ) :
    Twin.Ledger.windowSum X P.H eds
      ≤ (bigIcc (X := X)).sum dsMassAt := by
  classical
  -- Expand the window sum and bound each term by its local Icc sum.
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
  have h1 :
      (Finset.range (P.H + 1)).sum (fun k => eds (X + k))
        ≤ (Finset.range (P.H + 1)).sum (fun k =>
            (Finset.Icc ((X + k) - P.H) (X + k)).sum (fun Y => dsMassAt Y / N)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact eds_le_sum_local (n := X + k)
  -- Enlarge each local Icc to the big Icc, using nonnegativity of the summand.
  have h2 :
      (Finset.range (P.H + 1)).sum (fun k =>
          (Finset.Icc ((X + k) - P.H) (X + k)).sum (fun Y => dsMassAt Y / N))
        ≤ (Finset.range (P.H + 1)).sum (fun _k =>
            (bigIcc (X := X)).sum (fun Y => dsMassAt Y / N)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hk_le : k ≤ P.H := by
      have : k < P.H + 1 := Finset.mem_range.1 hk
      exact Nat.lt_succ_iff.1 this
    refine Finset.sum_le_sum_of_subset_of_nonneg (localIcc_subset_bigIcc (X := X) (k := k) hk_le) ?_
    intro Y _hY _hY'
    exact div_nonneg (dsMassAt_nonneg Y) (le_of_lt N_pos)
  -- Compute the constant sum and cancel the `N = H+1` normalization.
  have h3 :
      (Finset.range (P.H + 1)).sum (fun _k => (bigIcc (X := X)).sum (fun Y => dsMassAt Y / N))
        = ((P.H + 1 : ℝ) / N) * (bigIcc (X := X)).sum dsMassAt := by
    -- `∑_{k=0}^H c = (H+1) * c`, then pull the constant `1/N` out of the inner sum.
    have hconst :
        (Finset.range (P.H + 1)).sum (fun _k => (bigIcc (X := X)).sum (fun Y => dsMassAt Y / N))
          = (P.H + 1) • ((bigIcc (X := X)).sum (fun Y => dsMassAt Y / N)) := by
      simpa [Finset.sum_const]
    -- pull `1/N` through the sum
    have hinner :
        (bigIcc (X := X)).sum (fun Y => dsMassAt Y / N)
          = (1 / N) * (bigIcc (X := X)).sum dsMassAt := by
      -- Pull a constant factor out of the finite sum.
      have hmul :
          (1 / N) * (bigIcc (X := X)).sum dsMassAt
            = (bigIcc (X := X)).sum (fun Y => (1 / N) * dsMassAt Y) := by
        simpa [Finset.mul_sum] using
          (Finset.mul_sum (s := bigIcc (X := X)) (f := dsMassAt) (a := (1 / N)))
      -- rewrite `(1/N) * dsMassAt Y` as `dsMassAt Y / N`
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul.symm
    -- combine and rewrite `nsmul` as multiplication on `ℝ`
    calc
      (Finset.range (P.H + 1)).sum (fun _k => (bigIcc (X := X)).sum (fun Y => dsMassAt Y / N))
          = (P.H + 1) • ((1 / N) * (bigIcc (X := X)).sum dsMassAt) := by
              simpa [hinner] using hconst
      _ = ((P.H + 1 : ℝ) * (1 / N)) * (bigIcc (X := X)).sum dsMassAt := by
              -- `n • x = (n:ℝ) * x` for `ℝ`
              simp [nsmul_eq_mul, mul_assoc]
      _ = ((P.H + 1 : ℝ) / N) * (bigIcc (X := X)).sum dsMassAt := by
              simp [div_eq_mul_inv, mul_assoc]
  -- put together
  have hN : ((P.H + 1 : ℝ) / N) = 1 := by
    have hN_eq : (N : ℝ) = (P.H + 1 : ℝ) := by
      simp [N, Nat.cast_add, Nat.cast_one]
    have hne : (P.H + 1 : ℝ) ≠ 0 := by
      exact ne_of_gt (by exact_mod_cast Nat.succ_pos P.H)
    calc
      (P.H + 1 : ℝ) / N = (P.H + 1 : ℝ) / (P.H + 1 : ℝ) := by simp [hN_eq]
      _ = 1 := by simpa [hne] using (div_self (P.H + 1 : ℝ))
  -- Evaluate the constant sum.
  have hconst_eval :
      (Finset.range (P.H + 1)).sum (fun _k => (bigIcc (X := X)).sum (fun Y => dsMassAt Y / N))
        = (bigIcc (X := X)).sum dsMassAt := by
    calc
      (Finset.range (P.H + 1)).sum (fun _k => (bigIcc (X := X)).sum (fun Y => dsMassAt Y / N))
          = ((P.H + 1 : ℝ) / N) * (bigIcc (X := X)).sum dsMassAt := h3
      _ = 1 * (bigIcc (X := X)).sum dsMassAt := by simp [hN]
      _ = (bigIcc (X := X)).sum dsMassAt := by simp
  have h2' :
      (Finset.range (P.H + 1)).sum (fun k =>
          (Finset.Icc ((X + k) - P.H) (X + k)).sum (fun Y => dsMassAt Y / N))
        ≤ (bigIcc (X := X)).sum dsMassAt := by
    exact le_trans h2 (le_of_eq hconst_eval)
  have hfinal :
      (Finset.range (P.H + 1)).sum (fun k => eds (X + k))
        ≤ (bigIcc (X := X)).sum dsMassAt := le_trans h1 h2'
  simpa [Twin.Ledger.windowSum, Twin.Ledger.windowSumN, bigIcc] using hfinal

/-!
The `/9` (L² minor) and `/3` (L¹ desmoothing) budgets are still paper-facing analytic
obligations.  We record them in their **raw window-inequality** form (the shape that
appears in the paper / in `Twin.ChecklistTargets.ObligationsExplicit`), and then derive
the record-valued interfaces from these inequalities.
-/

/-!
As with desmoothing, we state the L² minor budget at the level of the window-masses
`minorMassAt` and then derive the corresponding `emin` window-inequality by bookkeeping.
-/

/-
Minor-arc L² budget (decomposition)
-----------------------------------

The previous bespoke axiom `minorMassAt_sq_sum_bigIcc_core_raw` bounded the square-sum of the
window-level minor masses `|minorMassAt Y|^2` over `bigIcc(X) = [X-H, X+H]`.

We now split this into two conventional components and package the remaining analytic input
as the typeclass `MinorMassAtSqSumBudget`:

1. **Cauchy–Schwarz on the torus**: for each `Y`, the squared minor mass is controlled by the
   `L²`-energy of the minor-arc integrand on `[0,1]`.
2. A single **analytic** axiom bounding the total of these `L²` energies over `bigIcc(X)`.

This matches the paper: the analytic input is an `L²`-type (large-sieve / Type-II) minor-arc
estimate; the rest is standard measure theory.
-/

/-- `L²` energy of the minor-arc integrand (on `[0,1]`) for the window centered at `Y`. -/
noncomputable def minorMassAt_L2At (Y : ℕ) : ℝ :=
  ∫ α in Set.Icc (0 : ℝ) 1,
    |Twin.MajorArc.minorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
        (X := (Y : ℝ)) (H := (P.H : ℝ)) α| ^ 2

/-- Conventional Cauchy–Schwarz: the squared minor mass is controlled by the `L²` energy
of the minor-arc integrand (since `volume (Icc 0 1) = 1`). -/
theorem minorMassAt_sq_le_L2At_raw :
  ∀ Y : ℕ, |minorMassAt (sme := sme) Y| ^ 2 ≤ minorMassAt_L2At (sme := sme) Y := by
  intro Y
  classical
  -- Work on the restricted Lebesgue measure `volume` on `[0,1]`.
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  haveI : MeasureTheory.IsFiniteMeasure μ := by
    -- `μ univ = volume (Icc 0 1) = 1`.
    refine ⟨?_⟩
    simpa [μ] using (show μ Set.univ < (⊤ : ENNReal) by simp [Measure.restrict_apply])

  -- The minor-arc integrand for this `Y`.
  let f0 : ℝ → ℝ :=
    fun α =>
      Twin.MajorArc.minorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
        (X := (Y : ℝ)) (H := (P.H : ℝ)) α

  -- `|∫ f0| ≤ ∫ |f0|`.
  have h_abs :
      |∫ α, f0 α ∂μ| ≤ ∫ α, |f0 α| ∂μ :=
    MeasureTheory.abs_integral_le_integral_abs (μ := μ) (f := f0)

  -- A uniform bound on `‖sumValue‖`, hence on `|f0|`.
  let u : ℕ → ℝ :=
    fun n =>
      ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (Y : ℝ)) / (P.H : ℝ)))‖
  have hu : Summable u := by
    -- This is proven in `Twin/ChecklistIntegrability.lean` for the frozen model.
    simpa [u, Twin.ChecklistIntegrability.Lambda, Twin.ChecklistIntegrability.Wwin,
      Twin.ChecklistIntegrability.P, Lambda, Wwin, P] using
      (Twin.ChecklistIntegrability.summable_sumValue_bound (X := Y))
  let Su : ℝ := ∑' n : ℕ, u n

  have hSbound :
      ∀ α : ℝ, ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ≤ Su := by
    intro α
    -- Direct comparison test via `norm_tsum_le_tsum_norm`.
    let term : ℕ → ℂ :=
      fun n =>
        Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (Y : ℝ)) / (P.H : ℝ)))
          * Twin.SW.χ_add (α * (n : ℝ))
    have hterm : Summable (fun n : ℕ => ‖term n‖) := by
      -- `‖term n‖ = u n` since `‖χ_add‖ = 1`.
      have : (fun n : ℕ => ‖term n‖) = u := by
        funext n
        simp [term, u, norm_chi_add]
      simpa [this] using hu
    have hnorm :
        ‖∑' n : ℕ, term n‖ ≤ ∑' n : ℕ, ‖term n‖ :=
      norm_tsum_le_tsum_norm hterm
    -- Rewrite `tsum term` as `sumValue` and `tsum ‖term‖` as `Su`.
    simpa [Twin.SW.sumValue, term, Su, u, norm_chi_add] using hnorm

  have hf0_bound : ∀ α : ℝ, |f0 α| ≤ Su ^ 2 := by
    intro α
    -- First bound the correlation core by `‖S‖^2`.
    set S : ℂ := Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α
    have hCorr :
        |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| ≤ Su ^ 2 := by
      -- `|re z| ≤ ‖z‖` and `‖(S*conj S)*χ‖ = ‖S‖^2`.
      have hre :
          |((S * conj S) * Twin.SW.χ_add (-2 * α)).re| ≤ ‖(S * conj S) * Twin.SW.χ_add (-2 * α)‖ := by
        simpa using Complex.abs_re_le_norm ((S * conj S) * Twin.SW.χ_add (-2 * α))
      have hnormχ : ‖Twin.SW.χ_add (-2 * α)‖ = 1 := by
        simpa using norm_chi_add (-2 * α)
      have hnorm :
          ‖(S * conj S) * Twin.SW.χ_add (-2 * α)‖ ≤ Su ^ 2 := by
        have hS : ‖S‖ ≤ Su := by
          simpa [S] using hSbound α
        -- `‖(S*conj S)*χ‖ = ‖S‖^2` since `‖conj S‖ = ‖S‖` and `‖χ‖ = 1`.
        have hEq :
            ‖(S * conj S) * Twin.SW.χ_add (-2 * α)‖ = ‖S‖ ^ 2 := by
          set χ : ℂ := Twin.SW.χ_add (-2 * α)
          have hχ : ‖χ‖ = 1 := by simpa [χ] using hnormχ
          have h1 : ‖S * conj S‖ = ‖S‖ * ‖conj S‖ := by
            simpa using (norm_mul S (conj S))
          have h2 : ‖S * conj S‖ * ‖χ‖ = (‖S‖ * ‖conj S‖) * ‖χ‖ :=
            congrArg (fun t => t * ‖χ‖) h1
          calc
            ‖(S * conj S) * χ‖
                = ‖S * conj S‖ * ‖χ‖ := by simpa using (norm_mul (S * conj S) χ)
            _ = (‖S‖ * ‖conj S‖) * ‖χ‖ := h2
            _ = (‖S‖ * ‖S‖) * 1 := by simp [Complex.norm_conj, hχ, mul_assoc]
            _ = ‖S‖ ^ 2 := by simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
        -- Use `‖S‖ ≤ Su` to get `‖S‖^2 ≤ Su^2`.
        have hSq : ‖S‖ ^ 2 ≤ Su ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg S) hS 2
        -- Finish via `‖(S*conj S)*χ‖ = ‖S‖^2` and `‖S‖ ≤ Su`.
        calc
          ‖(S * conj S) * Twin.SW.χ_add (-2 * α)‖ = ‖S‖ ^ 2 := hEq
          _ ≤ Su ^ 2 := hSq
      -- Finish: `|twinCorrIntegrand| = |re z| ≤ ‖z‖ ≤ Su^2`.
      simpa [Twin.MajorArc.twinCorrIntegrand, S] using le_trans hre hnorm

    -- Now insert the minor-arc indicator (which is `0` or `1`).
    have hind : |Twin.MajorArc.minorArcInd (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α| ≤ 1 := by
      classical
      by_cases h : Twin.MajorArc.IsMajorArc (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α <;>
        simp [Twin.MajorArc.minorArcInd, h]
    calc
      |f0 α|
          = |Twin.MajorArc.minorArcInd (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α
                * Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| := by
              simp [f0, Twin.MajorArc.minorArcTwinIntegrand]
      _ = |Twin.MajorArc.minorArcInd (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α|
            * |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| := by
              simp [abs_mul]
      _ ≤ 1 * |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| := by
            gcongr
      _ = |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| := by simp
      _ ≤ Su ^ 2 := hCorr

  -- Use Hölder with `p=q=2` and the fact that `μ` has total mass `1` to get `∫ |f0| ≤ √(∫ |f0|^2)`.
  have hf_mem : MeasureTheory.MemLp (fun α : ℝ => |f0 α|) (ENNReal.ofReal (2 : ℝ)) μ := by
    -- `f0` is integrable on `[0,1]` (from full integrability of the frozen model).
    have hFull :
        MeasureTheory.IntegrableOn
          (fun α =>
            Twin.MajorArc.fullTwinIntegrand (Λ := Lambda) (W := Wwin)
              (X := (Y : ℝ)) (H := (P.H : ℝ)) α)
          (Set.Icc (0 : ℝ) 1) :=
      by
        -- `Twin.ChecklistIntegrability.fullIntegrable` is stated with `X : ℕ`.
        simpa [Twin.ChecklistIntegrability.Lambda, Twin.ChecklistIntegrability.Wwin,
          Twin.ChecklistIntegrability.P, Lambda, Wwin, P] using
          (Twin.ChecklistIntegrability.fullIntegrable (X := Y))
    have hMinor :
        MeasureTheory.IntegrableOn
          (fun α =>
            Twin.MajorArc.minorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
              (X := (Y : ℝ)) (H := (P.H : ℝ)) α)
          (Set.Icc (0 : ℝ) 1) :=
      Twin.MajorArc.integrableOn_minorArcTwinIntegrand_of_full
        (sme := sme) (Λ := Lambda) (W := Wwin) (X := (Y : ℝ)) (H := (P.H : ℝ)) hFull
    have hMinor_int : MeasureTheory.Integrable (fun α => f0 α) μ := by
      simpa [MeasureTheory.IntegrableOn, μ, f0] using hMinor
    have hf_meas : MeasureTheory.AEStronglyMeasurable (fun α : ℝ => |f0 α|) μ := by
      have : MeasureTheory.AEStronglyMeasurable (fun α : ℝ => ‖f0 α‖) μ :=
        MeasureTheory.AEStronglyMeasurable.norm hMinor_int.aestronglyMeasurable
      simpa [Real.norm_eq_abs] using this
    have hfC : ∀ᵐ α ∂μ, ‖|f0 α|‖ ≤ Su ^ 2 := by
      exact Filter.Eventually.of_forall (fun α => by simpa using hf0_bound α)
    exact MeasureTheory.MemLp.of_bound (μ := μ) (p := ENNReal.ofReal (2 : ℝ)) hf_meas (Su ^ 2) hfC

  have hg_mem : MeasureTheory.MemLp (fun _α : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (MeasureTheory.memLp_const (μ := μ) (c := (1 : ℝ)) (p := ENNReal.ofReal (2 : ℝ)))

  have hHolder :
      (∫ α, |f0 α| ∂μ) ≤ Real.sqrt (∫ α, |f0 α| ^ 2 ∂μ) := by
    have hf_nonneg : 0 ≤ᵐ[μ] fun α : ℝ => |f0 α| := by
      exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
    have hg_nonneg : 0 ≤ᵐ[μ] fun _α : ℝ => (1 : ℝ) := by
      exact Filter.Eventually.of_forall (fun _ => by norm_num)
    have hMul :
        (∫ α, (fun α : ℝ => |f0 α|) α * (fun _α : ℝ => (1 : ℝ)) α ∂μ)
          ≤ (∫ α, (|f0 α|) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
              * (∫ α, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
        hf_nonneg hg_nonneg hf_mem hg_mem
    have hμreal : μ.real Set.univ = (1 : ℝ) := by
      -- `μ` is `volume` restricted to `Icc 0 1`, so `μ univ = 1`.
      simp [μ]
    have hMul' :
        (∫ α, |f0 α| ∂μ)
          ≤ (∫ α, |f0 α| ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
      -- `integral_mul_le_Lp_mul_Lq_of_nonneg` specializes to Cauchy–Schwarz with the factor
      -- `μ.real univ^(1/2)`, and here `μ.real univ = 1`.
      simpa [mul_one, Real.rpow_two, hμreal] using hMul
    -- `x ^ (1/2) = sqrt x`
    simpa [Real.sqrt_eq_rpow] using hMul'

  -- Combine and square.
  have hMain :
      |∫ α, f0 α ∂μ| ≤ Real.sqrt (∫ α, |f0 α| ^ 2 ∂μ) :=
    le_trans h_abs hHolder
  have hx_nonneg' : 0 ≤ ∫ α, (f0 α) ^ 2 ∂μ := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    exact Filter.Eventually.of_forall (fun α => by simpa using (sq_nonneg (f0 α)))
  have hsq :
      |∫ α, f0 α ∂μ| ^ 2 ≤ (Real.sqrt (∫ α, |f0 α| ^ 2 ∂μ)) ^ 2 := by
    -- square both sides (both are nonnegative)
    have h0 : 0 ≤ |∫ α, f0 α ∂μ| := abs_nonneg _
    have h1 : 0 ≤ Real.sqrt (∫ α, |f0 α| ^ 2 ∂μ) := Real.sqrt_nonneg _
    simpa [pow_two] using (mul_self_le_mul_self h0 hMain)
  -- `sqrt` cancels because the integral is nonnegative.
  have hsq' :
      |∫ α, f0 α ∂μ| ^ 2 ≤ ∫ α, |f0 α| ^ 2 ∂μ := by
    -- `|f0|^2` and `(f0)^2` coincide pointwise.
    have hsq0 : |∫ α, f0 α ∂μ| ^ 2 ≤ ∫ α, (f0 α) ^ 2 ∂μ := by
      simpa [Real.sq_sqrt hx_nonneg'] using hsq
    simpa using hsq0

  -- Rewrite back to the checklist names and set-integrals on `[0,1]`.
  -- LHS: `minorMassAt`; RHS: `minorMassAt_L2At`.
  simpa [minorMassAt, Twin.MajorArc.minorMass, Twin.MajorArc.minorMassReal, μ, f0,
    minorMassAt_L2At] using hsq'

/-- Raw L² minor budget, stated on the window-level minor masses `minorMassAt`.

For the checklist route we only use the *summed* square-mass inequality below; it is the
canonical “paper-facing” minor-arc input at the `/9` scale.

Paper anchor: the minor-arc `L²` estimate (large sieve / Type-II) feeding the gate. -/
class MinorMassAtSqSumBudget
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) : Prop where
  /-- The summed square-mass inequality on the enlarged index set `bigIcc(X)`. -/
  budget :
    ∀ X, P.X0 ≤ X →
      (bigIcc (X := X)).sum (fun Y => |minorMassAt (sme := sme) Y| ^ 2)
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9

private lemma minorMassAt_sq_sum_bigIcc_scaled_eq (X : ℕ) :
    (P.H + 1 : ℝ) ^ 2
        * (bigIcc (X := X)).sum (fun Y => (|minorMassAt (sme := sme) Y| / N) ^ 2)
      =
    (bigIcc (X := X)).sum (fun Y => |minorMassAt (sme := sme) Y| ^ 2) := by
  classical
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt N_pos
  -- rewrite the outer scaling as `N^2` and push it inside the sum
  have hN : (P.H + 1 : ℝ) = N := by
    simp [N, Nat.cast_add, Nat.cast_one, add_assoc]
  -- Now each summand satisfies `N^2 * (|m|/N)^2 = |m|^2`.
  have hterm :
      ∀ Y : ℕ, (N : ℝ) ^ 2 * (|minorMassAt (sme := sme) Y| / N) ^ 2
        = |minorMassAt (sme := sme) Y| ^ 2 := by
    intro Y
    -- Clear the division by `N`.
    have hN0' : (N : ℝ) ≠ 0 := hN0
    field_simp [hN0', pow_two]
  -- Convert the LHS to `N^2 * sum ...` then distribute.
  calc
    (P.H + 1 : ℝ) ^ 2
        * (bigIcc (X := X)).sum (fun Y => (|minorMassAt (sme := sme) Y| / N) ^ 2)
        =
      (N : ℝ) ^ 2
        * (bigIcc (X := X)).sum (fun Y => (|minorMassAt (sme := sme) Y| / N) ^ 2) := by
          simpa [hN]
    _ =
      (bigIcc (X := X)).sum (fun Y => (N : ℝ) ^ 2 * (|minorMassAt (sme := sme) Y| / N) ^ 2) := by
          simp [Finset.mul_sum]
    _ =
      (bigIcc (X := X)).sum (fun Y => |minorMassAt (sme := sme) Y| ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro Y hY
          simp [hterm Y]

theorem minorMassAt_sq_sum_bigIcc_raw
  [MinorMassAtSqSumBudget (sme := sme)] :
  ∀ X, P.X0 ≤ X →
    (P.H + 1 : ℝ) ^ 2
      * (bigIcc (X := X)).sum (fun Y => (|minorMassAt (sme := sme) Y| / N) ^ 2)
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9 := by
  intro X hX
  -- reduce to the core (more conventional) square-sum statement
  have hcore := (MinorMassAtSqSumBudget.budget (sme := sme) X hX)
  simpa [minorMassAt_sq_sum_bigIcc_scaled_eq (sme := sme) (X := X)] using hcore

theorem l2_minor_onWindow_raw
  [MinorMassAtSqSumBudget (sme := sme)] :
  ∀ X, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H (fun n => (emin (sme := sme) n)^2)
      ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9 := by
  intro X hX
  have h1 :
      Twin.Ledger.windowSum X P.H (fun n => (emin (sme := sme) n) ^ 2)
        ≤ (P.H + 1 : ℝ) ^ 2
          * (bigIcc (X := X)).sum (fun Y => (|minorMassAt (sme := sme) Y| / N) ^ 2) :=
    windowSum_emin_sq_le_big_sum_minor_sq (sme := sme) (X := X)
  exact le_trans h1 (minorMassAt_sq_sum_bigIcc_raw (sme := sme) X hX)

/-!
We make the desmoothing budget *less bespoke* by stating it at the window-level
`dsMassAt` and then deriving the `eds`-window inequality by bookkeeping.
-/

/-!
Raw desmoothing budget (paper-facing), stated on the window-level masses `dsMassAt`.

This is the analytic input: show that the total desmoothing discrepancy over the enlarged
index set `bigIcc(X) = [X-H, X+H]` stays within the canonical `/3` budget.

### Desmoothing decomposition (conventional components)

We split the discrepancy `dsMassAt X = |fullMassAt X - localizedTwinMass X H|` using an
intermediate window-sum built from the von Mangoldt function:

* `lambdaTwinMassAt X` is the sharp-window (kernel `J`) ΛΛ-correlation;
* `dsFourierAt X` is the Fourier/smoothing discrepancy between `fullMassAt` (defined by an
  integral of `|S_X(α)|^2 e(-2α)`) and the sharp ΛΛ window sum;
* `dsPrimePowerAt X` is the prime-power disposal discrepancy between ΛΛ and the log-indicator
  `twinIndicator` used by `localizedTwinMass`.

Both pieces are “conventional analytic” in the sense of being standard harmonic-analysis /
prime-power bookkeeping steps; the only paper-specific input is elsewhere (pinned majors, minor arcs).
-/

/-- Sharp-window ΛΛ-correlation on `[X, X+H]`. -/
noncomputable def lambdaTwinMassAt (X : ℕ) : ℝ :=
  (Finset.range (P.H + 1)).sum (fun k =>
    Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))

/-!
We split the Fourier/smoothing discrepancy into two conventional pieces:

* a **Fourier inversion** step turning `fullMassAt` into an explicit ΛΛ-correlation with the
  smooth window profile `Wwin`,
* a **window comparison** step comparing that smooth ΛΛ-correlation to the sharp window sum
  `lambdaTwinMassAt` (kernel `J`).

This lets us isolate which part is “analysis on the torus” versus “window bookkeeping”.
-/

/-- Smooth ΛΛ-correlation modeled directly by the window profile `Wwin`. -/
noncomputable def smoothLambdaTwinMassAt (X : ℕ) : ℝ :=
  let Xr : ℝ := (X : ℝ)
  let Hr : ℝ := (P.H : ℝ)
  ∑' n : ℕ,
    (Lambda n) * Wwin (((n : ℝ) - Xr) / Hr)
      * (Lambda (n + 2)) * Wwin ((((n + 2 : ℕ) : ℝ) - Xr) / Hr)

/-!
Fourier inversion (conventional)
--------------------------------

Paper anchor: standard orthogonality on `∫_{0}^{1} e(kα)dα` plus justified exchange of
`∑∑` with `∫` (Fubini/Tonelli under absolute convergence from the Gaussian window).

This is **conventional analytic** (textbook Fourier inversion for a Schwartz window).
For the checklist route we only use it through the *summed budget* axiom
`dsMassAt_sum_bigIcc_raw` below, rather than a pointwise identity.
-/

/-|
Fourier inversion discrepancy: `fullMassAt` (integral definition) versus the explicit smooth ΛΛ sum.

Paper anchor: standard orthogonality on `∫_{0}^{1} e(kα)dα` plus justified exchange of
`∑∑` with `∫` (Fubini/Tonelli under absolute convergence from the Gaussian window).
-/
noncomputable def dsFourierInvAt (X : ℕ) : ℝ :=
  |fullMassAt X - smoothLambdaTwinMassAt X|

/-|
Window comparison discrepancy: smooth ΛΛ sum versus sharp-window ΛΛ sum.

Paper anchor: smooth-vs-sharp window comparison / truncation, plus the rapid decay of the Gaussian.
-/
noncomputable def dsFourierWindowAt (X : ℕ) : ℝ :=
  |smoothLambdaTwinMassAt X - lambdaTwinMassAt X|

/-!
Window comparison (conventional decomposition)
---------------------------------------------

The smooth ΛΛ sum `smoothLambdaTwinMassAt X` is an infinite sum over `n : ℕ`.  The sharp-window
sum `lambdaTwinMassAt X` only sees the `H+1` integers `n = X, …, X+H`.

It is convenient (and paper-faithful) to split the window comparison into:

* a **tail** term: the contribution of `n ∉ [X, X+H]` to the smooth sum, and
* a **core** term: the mismatch between the smooth weights and the sharp weights on the window.

Both are conventional analytic steps (Gaussian tail control + smooth-vs-sharp window comparison).
-/

private noncomputable def smoothInsideAt (X : ℕ) : ℝ :=
  let Hr : ℝ := (P.H : ℝ)
  (Finset.range (P.H + 1)).sum (fun k =>
    (Lambda (X + k)) * Wwin (((k : ℝ)) / Hr)
      * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / Hr))

private noncomputable def dsFourierWindowTailAt (X : ℕ) : ℝ :=
  |smoothLambdaTwinMassAt X - smoothInsideAt X|

private noncomputable def dsFourierWindowCoreAt (X : ℕ) : ℝ :=
  |smoothInsideAt X - lambdaTwinMassAt X|

private noncomputable def dsFourierWindowCoreBudgetAt (X : ℕ) : ℝ :=
  let Hr : ℝ := (P.H : ℝ)
  (Finset.range (P.H + 1)).sum (fun k =>
    -- budget for `|(Λ·W·Λ₂·W₂) - (J·Λ·Λ₂)|` on the window index `k`
    |Lambda (X + k)|
      * (|Lambda (X + k + 2)|
        * |Wwin ((k : ℝ) / Hr) * Wwin (((k : ℝ) + 2) / Hr) - Twin.Kernel.J P.H k|))

private lemma dsFourierWindowCoreAt_le_budget (X : ℕ) :
    dsFourierWindowCoreAt X ≤ dsFourierWindowCoreBudgetAt X := by
  classical
  -- Write the core difference as a finite sum of termwise differences.
  have hdiff :
      smoothInsideAt X - lambdaTwinMassAt X
        =
      (Finset.range (P.H + 1)).sum (fun k =>
        (Lambda (X + k)) * Wwin (((k : ℝ)) / (P.H : ℝ))
          * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ))
          - (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))) := by
    -- difference of sums = sum of differences
    simp [smoothInsideAt, lambdaTwinMassAt, Finset.sum_sub_distrib]
  -- bound absolute value of a sum by sum of absolute values
  have hsum :=
    (Finset.abs_sum_le_sum_abs
      (s := Finset.range (P.H + 1))
      (f := fun k =>
        (Lambda (X + k)) * Wwin (((k : ℝ)) / (P.H : ℝ))
          * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ))
          - (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))))
  have hsum' :
      dsFourierWindowCoreAt X
        ≤ (Finset.range (P.H + 1)).sum (fun k =>
            |(Lambda (X + k)) * Wwin (((k : ℝ)) / (P.H : ℝ))
                * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ))
              - (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))|) := by
    -- unfold and rewrite using `hdiff`
    have habs :
        |smoothInsideAt X - lambdaTwinMassAt X|
          = |(Finset.range (P.H + 1)).sum (fun k =>
                (Lambda (X + k)) * Wwin (((k : ℝ)) / (P.H : ℝ))
                  * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ))
                  - (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2))))| := by
      simpa [hdiff] using congrArg (fun t : ℝ => |t|) hdiff
    simpa [dsFourierWindowCoreAt, habs] using hsum
  -- rewrite each term into the budget form
  have hterm :
      ∀ k : ℕ,
        |(Lambda (X + k)) * Wwin (((k : ℝ)) / (P.H : ℝ))
            * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ))
          - (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))|
          =
        |Lambda (X + k)|
          * (|Lambda (X + k + 2)|
            * |Wwin ((k : ℝ) / (P.H : ℝ)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ)) - Twin.Kernel.J P.H k|) := by
    intro k
    -- factor out `Λ·Λ₂` and take abs:
    -- `(Λ*W*Λ₂*W₂) - (J*Λ*Λ₂) = (Λ*Λ₂) * (W*W₂ - J)`
    have hfac :
        (Lambda (X + k)) * Wwin (((k : ℝ)) / (P.H : ℝ))
            * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ))
          - (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))
          =
        ((Lambda (X + k)) * (Lambda (X + k + 2)))
          * (Wwin ((k : ℝ) / (P.H : ℝ)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ)) - Twin.Kernel.J P.H k) := by
      ring
    have habs_fac :
        |(Lambda (X + k)) * Wwin (((k : ℝ)) / (P.H : ℝ))
              * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ))
            - (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))|
          =
          |(Lambda (X + k) * Lambda (X + k + 2))
              * (Wwin ((k : ℝ) / (P.H : ℝ)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ)) - Twin.Kernel.J P.H k)| := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t : ℝ => |t|) hfac
    calc
      |(Lambda (X + k)) * Wwin (((k : ℝ)) / (P.H : ℝ))
            * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ))
          - (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))|
          =
          |(Lambda (X + k) * Lambda (X + k + 2))
              * (Wwin ((k : ℝ) / (P.H : ℝ)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ)) - Twin.Kernel.J P.H k)| := by
            exact habs_fac
      _ =
          |(Lambda (X + k) * Lambda (X + k + 2))|
            * |Wwin ((k : ℝ) / (P.H : ℝ)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ)) - Twin.Kernel.J P.H k| := by
        simp [abs_mul]
      _ =
          (|Lambda (X + k)| * |Lambda (X + k + 2)|)
            * |Wwin ((k : ℝ) / (P.H : ℝ)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ)) - Twin.Kernel.J P.H k| := by
        simp [abs_mul]
      _ =
          |Lambda (X + k)|
            * (|Lambda (X + k + 2)|
              * |Wwin ((k : ℝ) / (P.H : ℝ)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ)) - Twin.Kernel.J P.H k|) := by
        simp [mul_assoc]
  have hrepl :
      (Finset.range (P.H + 1)).sum (fun k =>
            |(Lambda (X + k)) * Wwin (((k : ℝ)) / (P.H : ℝ))
                * (Lambda (X + k + 2)) * Wwin (((k : ℝ) + 2) / (P.H : ℝ))
              - (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))|)
        = dsFourierWindowCoreBudgetAt X := by
    unfold dsFourierWindowCoreBudgetAt
    refine Finset.sum_congr rfl ?_
    intro k hk
    -- keep the exact association used in the definition
    simpa using (hterm k)
  exact le_trans hsum' (le_of_eq hrepl)

private lemma dsFourierWindowAt_le_tail_add_core (X : ℕ) :
    dsFourierWindowAt X ≤ dsFourierWindowTailAt X + dsFourierWindowCoreAt X := by
  classical
  -- split through the inside approximation
  have hsplit :
      smoothLambdaTwinMassAt X - lambdaTwinMassAt X
        =
      (smoothLambdaTwinMassAt X - smoothInsideAt X)
        + (smoothInsideAt X - lambdaTwinMassAt X) := by
    ring
  have habs0 :
      |(smoothLambdaTwinMassAt X - smoothInsideAt X)
          + (smoothInsideAt X - lambdaTwinMassAt X)|
        ≤ |smoothLambdaTwinMassAt X - smoothInsideAt X|
          + |smoothInsideAt X - lambdaTwinMassAt X| :=
    abs_add_le _ _
  have habs :
      |smoothLambdaTwinMassAt X - lambdaTwinMassAt X|
        ≤ |smoothLambdaTwinMassAt X - smoothInsideAt X|
          + |smoothInsideAt X - lambdaTwinMassAt X| := by
    have habs_eq :
        |smoothLambdaTwinMassAt X - lambdaTwinMassAt X|
          =
        |(smoothLambdaTwinMassAt X - smoothInsideAt X)
            + (smoothInsideAt X - lambdaTwinMassAt X)| :=
      congrArg (fun t => |t|) hsplit
    exact habs_eq.trans_le habs0
  dsimp [dsFourierWindowAt, dsFourierWindowTailAt, dsFourierWindowCoreAt] at habs ⊢
  exact habs

/-- Fourier/smoothing discrepancy: `fullMassAt` versus the sharp ΛΛ window sum. -/
noncomputable def dsFourierAt (X : ℕ) : ℝ :=
  |fullMassAt X - lambdaTwinMassAt X|

/-- Prime-power disposal discrepancy: ΛΛ window sum versus `localizedTwinMass`. -/
noncomputable def dsPrimePowerAt (X : ℕ) : ℝ :=
  |lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H|

private lemma dsFourierAt_le_inv_add_window (X : ℕ) :
    dsFourierAt X ≤ dsFourierInvAt X + dsFourierWindowAt X := by
  classical
  have hsplit :
      fullMassAt X - lambdaTwinMassAt X
        =
      (fullMassAt X - smoothLambdaTwinMassAt X)
        + (smoothLambdaTwinMassAt X - lambdaTwinMassAt X) := by
    ring
  have habs0 :
      |(fullMassAt X - smoothLambdaTwinMassAt X)
          + (smoothLambdaTwinMassAt X - lambdaTwinMassAt X)|
        ≤ |fullMassAt X - smoothLambdaTwinMassAt X|
          + |smoothLambdaTwinMassAt X - lambdaTwinMassAt X| :=
    abs_add_le _ _
  have habs :
      |fullMassAt X - lambdaTwinMassAt X|
        ≤ |fullMassAt X - smoothLambdaTwinMassAt X|
          + |smoothLambdaTwinMassAt X - lambdaTwinMassAt X| := by
    have habs_eq :
        |fullMassAt X - lambdaTwinMassAt X|
          =
          |(fullMassAt X - smoothLambdaTwinMassAt X)
            + (smoothLambdaTwinMassAt X - lambdaTwinMassAt X)| :=
      congrArg (fun t => |t|) hsplit
    exact habs_eq.trans_le habs0
  dsimp [dsFourierAt, dsFourierInvAt, dsFourierWindowAt] at habs ⊢
  exact habs

/-!
Prime-power disposal split
-------------------------

The discrepancy between the ΛΛ sharp-window correlation and `localizedTwinMass` is entirely due
to **prime powers** (`p^m` with `m ≥ 2`): on twin primes we have `Λ(p)=log p` and the two
weights match exactly.

We make this precise by introducing the “prime-only” weight `LambdaPrime`, for which the
sharp-window correlation matches `localizedTwinMass` by definition; the remaining discrepancy
is then split into a left/right prime-power contribution.
-/

private def LambdaPrime (n : ℕ) : ℝ :=
  if Nat.Prime n then Real.log (n : ℝ) else 0

private lemma LambdaPrime_mul_shift_eq_twinIndicator (n : ℕ) :
    LambdaPrime n * LambdaPrime (n + 2) = Twin.Bridge.twinIndicator n := by
  classical
  by_cases h1 : Nat.Prime n
  · by_cases h2 : Nat.Prime (n + 2)
    · have ht : Twin.TwinPairAt n := ⟨h1, h2⟩
      simp [LambdaPrime, Twin.Bridge.twinIndicator, h1, h2, ht]
    · have ht : ¬ Twin.TwinPairAt n := by
        intro ht
        exact h2 ht.2
      simp [LambdaPrime, Twin.Bridge.twinIndicator, h1, h2, ht]
  · have ht : ¬ Twin.TwinPairAt n := by
      intro ht
      exact h1 ht.1
    simp [LambdaPrime, Twin.Bridge.twinIndicator, h1, ht]

private noncomputable def lambdaPrimeTwinMassAt (X : ℕ) : ℝ :=
  (Finset.range (P.H + 1)).sum (fun k =>
    Twin.Kernel.J P.H k * (LambdaPrime (X + k)) * (LambdaPrime (X + k + 2)))

private lemma lambdaPrimeTwinMassAt_eq_localized (X : ℕ) :
    lambdaPrimeTwinMassAt X = Twin.Bridge.localizedTwinMass X P.H := by
  classical
  unfold lambdaPrimeTwinMassAt Twin.Bridge.localizedTwinMass
  refine Finset.sum_congr rfl ?_
  intro k hk
  -- `J * (Λp·Λp₂) = J * twinIndicator`
  have : (LambdaPrime (X + k)) * (LambdaPrime (X + k + 2)) = Twin.Bridge.twinIndicator (X + k) := by
    simpa [Nat.add_assoc] using LambdaPrime_mul_shift_eq_twinIndicator (n := X + k)
  calc
    Twin.Kernel.J P.H k * (LambdaPrime (X + k)) * (LambdaPrime (X + k + 2))
        = Twin.Kernel.J P.H k * ((LambdaPrime (X + k)) * (LambdaPrime (X + k + 2))) := by
            ring
    _ = Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k) := by
            simpa [this]

noncomputable def dsPrimePowerLeftAt (X : ℕ) : ℝ :=
  |(Finset.range (P.H + 1)).sum (fun k =>
      Twin.Kernel.J P.H k
        * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2))))|

noncomputable def dsPrimePowerRightAt (X : ℕ) : ℝ :=
  |(Finset.range (P.H + 1)).sum (fun k =>
      Twin.Kernel.J P.H k
        * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2))))|

/-!
Prime-power budget (more “textbook”)
-----------------------------------

To bound the prime-power discrepancy, it is convenient to upper bound `|∑ f|` by `∑ |f|`.
We introduce nonnegative “budget” versions of the left/right prime-power errors where the
absolute values are pushed inside the finite sum.

These are closer to the conventional analytic bookkeeping one would prove (no cancellation needed),
and allow the window-sum axioms to be phrased in terms of explicit nonnegative sums.
-/

noncomputable def dsPrimePowerLeftBudgetAt (X : ℕ) : ℝ :=
  (Finset.range (P.H + 1)).sum (fun k =>
    Twin.Kernel.J P.H k
      * |Lambda (X + k) - LambdaPrime (X + k)|
      * |Lambda (X + k + 2)|)

noncomputable def dsPrimePowerRightBudgetAt (X : ℕ) : ℝ :=
  (Finset.range (P.H + 1)).sum (fun k =>
    Twin.Kernel.J P.H k
      * |LambdaPrime (X + k)|
      * |Lambda (X + k + 2) - LambdaPrime (X + k + 2)|)

private lemma dsPrimePowerLeftAt_le_budget (X : ℕ) :
    dsPrimePowerLeftAt X ≤ dsPrimePowerLeftBudgetAt X := by
  classical
  -- `|∑ f| ≤ ∑ |f|`
  have hsum :=
    (Finset.abs_sum_le_sum_abs
      (s := Finset.range (P.H + 1))
      (f := fun k =>
        Twin.Kernel.J P.H k
          * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2)))))
  -- rewrite each `|f k|` into the budget term
  have hterm :
      ∀ k : ℕ,
        |Twin.Kernel.J P.H k
            * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2)))|
          =
        Twin.Kernel.J P.H k
          * |Lambda (X + k) - LambdaPrime (X + k)|
          * |Lambda (X + k + 2)| := by
    intro k
    have hJ : 0 ≤ Twin.Kernel.J P.H k := Twin.Kernel.J_nonneg
    -- `|J * (A * B)| = |J|*|A|*|B| = J*|A|*|B|`
    simp [abs_mul, abs_of_nonneg hJ, mul_assoc, mul_left_comm, mul_comm]
  have hsum' :
      dsPrimePowerLeftAt X
        ≤ (Finset.range (P.H + 1)).sum (fun k =>
            |Twin.Kernel.J P.H k
                * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2)))|) := by
    simpa [dsPrimePowerLeftAt] using hsum
  have hrepl :
      (Finset.range (P.H + 1)).sum (fun k =>
            |Twin.Kernel.J P.H k
                * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2)))|)
        = dsPrimePowerLeftBudgetAt X := by
    unfold dsPrimePowerLeftBudgetAt
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact hterm k
  exact le_trans hsum' (le_of_eq hrepl)

private lemma dsPrimePowerRightAt_le_budget (X : ℕ) :
    dsPrimePowerRightAt X ≤ dsPrimePowerRightBudgetAt X := by
  classical
  have hsum :=
    (Finset.abs_sum_le_sum_abs
      (s := Finset.range (P.H + 1))
      (f := fun k =>
        Twin.Kernel.J P.H k
          * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2)))))
  have hterm :
      ∀ k : ℕ,
        |Twin.Kernel.J P.H k
            * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2)))|
          =
        Twin.Kernel.J P.H k
          * |LambdaPrime (X + k)|
          * |Lambda (X + k + 2) - LambdaPrime (X + k + 2)| := by
    intro k
    have hJ : 0 ≤ Twin.Kernel.J P.H k := Twin.Kernel.J_nonneg
    simp [abs_mul, abs_of_nonneg hJ, mul_assoc, mul_left_comm, mul_comm]
  have hsum' :
      dsPrimePowerRightAt X
        ≤ (Finset.range (P.H + 1)).sum (fun k =>
            |Twin.Kernel.J P.H k
                * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2)))|) := by
    simpa [dsPrimePowerRightAt] using hsum
  have hrepl :
      (Finset.range (P.H + 1)).sum (fun k =>
            |Twin.Kernel.J P.H k
                * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2)))|)
        = dsPrimePowerRightBudgetAt X := by
    unfold dsPrimePowerRightBudgetAt
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact hterm k
  exact le_trans hsum' (le_of_eq hrepl)

private lemma dsPrimePowerAt_le_left_add_right (X : ℕ) :
    dsPrimePowerAt X ≤ dsPrimePowerLeftAt X + dsPrimePowerRightAt X := by
  classical
  -- replace `localizedTwinMass` by the prime-only ΛpΛp correlation
  have hLoc : Twin.Bridge.localizedTwinMass X P.H = lambdaPrimeTwinMassAt X :=
    (lambdaPrimeTwinMassAt_eq_localized (X := X)).symm
  have hRewrite :
      lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H
        =
      lambdaTwinMassAt X - lambdaPrimeTwinMassAt X := by
    simpa [hLoc]
  -- expand both masses as finite sums, then split the difference termwise
  have hDiff :
      lambdaTwinMassAt X - lambdaPrimeTwinMassAt X
        =
      (Finset.range (P.H + 1)).sum (fun k =>
        Twin.Kernel.J P.H k
          * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2))))
      +
      (Finset.range (P.H + 1)).sum (fun k =>
        Twin.Kernel.J P.H k
          * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2)))) := by
    -- `ΛΛ - ΛpΛp = (Λ-Λp)·Λ₂ + Λp·(Λ₂-Λp₂)`
    unfold lambdaTwinMassAt lambdaPrimeTwinMassAt
    -- turn the difference of sums into the sum of differences
    have :
        (Finset.range (P.H + 1)).sum (fun k =>
          Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))
        -
        (Finset.range (P.H + 1)).sum (fun k =>
          Twin.Kernel.J P.H k * (LambdaPrime (X + k)) * (LambdaPrime (X + k + 2)))
          =
        (Finset.range (P.H + 1)).sum (fun k =>
          (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))
            - (Twin.Kernel.J P.H k * (LambdaPrime (X + k)) * (LambdaPrime (X + k + 2)))) := by
      simpa [Finset.sum_sub_distrib]
    -- now rewrite each summand
    -- and then split termwise using the ring identity.
    -- (Do this with `Finset.sum_congr` to avoid simp recursion.)
    calc
      lambdaTwinMassAt X - lambdaPrimeTwinMassAt X
          =
        (Finset.range (P.H + 1)).sum (fun k =>
          (Twin.Kernel.J P.H k * (Lambda (X + k)) * (Lambda (X + k + 2)))
            - (Twin.Kernel.J P.H k * (LambdaPrime (X + k)) * (LambdaPrime (X + k + 2)))) := by
              exact this
      _ =
        (Finset.range (P.H + 1)).sum (fun k =>
          Twin.Kernel.J P.H k
            * (((Lambda (X + k)) * (Lambda (X + k + 2)))
                - (LambdaPrime (X + k) * LambdaPrime (X + k + 2)))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
      _ =
        (Finset.range (P.H + 1)).sum (fun k =>
          Twin.Kernel.J P.H k
            * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2))
                + (LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2)))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
      _ =
        (Finset.range (P.H + 1)).sum (fun k =>
          Twin.Kernel.J P.H k
            * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2))))
        +
        (Finset.range (P.H + 1)).sum (fun k =>
          Twin.Kernel.J P.H k
            * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2)))) := by
              -- distribute `sum` across the internal `+`
              simp [mul_add, Finset.sum_add_distrib]
  -- put it together under absolute values
  have habs0 :
      |lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H|
        ≤ dsPrimePowerLeftAt X + dsPrimePowerRightAt X := by
    -- rewrite the left side to match `hDiff`, then use triangle inequality
    have hEq :
        lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H
          =
        (Finset.range (P.H + 1)).sum (fun k =>
          Twin.Kernel.J P.H k
            * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2))))
        +
        (Finset.range (P.H + 1)).sum (fun k =>
          Twin.Kernel.J P.H k
            * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2)))) := by
      calc
        lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H
            = lambdaTwinMassAt X - lambdaPrimeTwinMassAt X := by simpa [hLoc]
        _ = _ := hDiff
    have hAbs :
        |lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H|
          =
        |(Finset.range (P.H + 1)).sum (fun k =>
            Twin.Kernel.J P.H k
              * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2))))
          +
          (Finset.range (P.H + 1)).sum (fun k =>
            Twin.Kernel.J P.H k
              * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2))))| := by
      simpa using congrArg (fun t : ℝ => |t|) hEq
    -- triangle inequality now
    let A : ℝ :=
      (Finset.range (P.H + 1)).sum (fun k =>
        Twin.Kernel.J P.H k
          * ((Lambda (X + k) - LambdaPrime (X + k)) * (Lambda (X + k + 2))))
    let B : ℝ :=
      (Finset.range (P.H + 1)).sum (fun k =>
        Twin.Kernel.J P.H k
          * ((LambdaPrime (X + k)) * (Lambda (X + k + 2) - LambdaPrime (X + k + 2))))
    have hTri : |A + B| ≤ |A| + |B| := abs_add_le A B
    -- finish by unfolding the targets
    simpa [dsPrimePowerLeftAt, dsPrimePowerRightAt, hAbs, A, B] using hTri
  -- unwrap `dsPrimePowerAt`
  simpa [dsPrimePowerAt] using habs0

lemma dsMassAt_le_fourier_add_primePower (X : ℕ) :
    dsMassAt X ≤ dsFourierAt X + dsPrimePowerAt X := by
  classical
  -- `full - localized = (full - lambda) + (lambda - localized)`
  have hsplit :
      fullMassAt X - Twin.Bridge.localizedTwinMass X P.H
        =
      (fullMassAt X - lambdaTwinMassAt X)
        + (lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H) := by
    ring
  -- Triangle inequality on `abs`.
  have habs0 :
      |(fullMassAt X - lambdaTwinMassAt X)
          + (lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H)|
        ≤ |fullMassAt X - lambdaTwinMassAt X|
          + |lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H| :=
    abs_add_le _ _
  have habs :
      |fullMassAt X - Twin.Bridge.localizedTwinMass X P.H|
        ≤ |fullMassAt X - lambdaTwinMassAt X|
          + |lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H| := by
    -- avoid `simp` recursion: rewrite by `congrArg abs` and apply `habs0`.
    have habs_eq : |fullMassAt X - Twin.Bridge.localizedTwinMass X P.H|
        =
        |(fullMassAt X - lambdaTwinMassAt X)
            + (lambdaTwinMassAt X - Twin.Bridge.localizedTwinMass X P.H)| :=
      congrArg (fun t => |t|) hsplit
    -- now use triangle inequality
    exact habs_eq.trans_le habs0
  -- unfold the definitions (avoid `simp` recursion depth explosions)
  dsimp [dsMassAt, dsFourierAt, dsPrimePowerAt] at habs ⊢
  exact habs

/-!
#### Conventional axioms (to be proved later)

For the checklist route, we need a *window-summed* desmoothing budget at `/3` for
`dsMassAt = |fullMassAt - localizedTwinMass|`.

We make this less bespoke by splitting the discrepancy using the fully formal lemma
`dsMassAt ≤ dsFourierAt + dsPrimePowerAt`:

* `dsFourierAt = |fullMassAt - lambdaTwinMassAt|` packages Fourier inversion + smooth/sharp
  window comparison (harmonic analysis).
* `dsPrimePowerAt = |lambdaTwinMassAt - localizedTwinMass|` is the prime-power disposal step
  (ΛΛ versus prime-only log-indicator).

Both are “conventional analytic” in the sense of being textbook steps; the only paper-specific
inputs live elsewhere (pinned majors, minor arcs).  We postulate separate `/6` budgets for the
two pieces, from which the `/3` budget follows.
-/

class DsFourierAtSumBudget : Prop where
  /-- `/6` budget for the Fourier/smoothing discrepancy, summed on `bigIcc(X)`. -/
  budget :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      (bigIcc (X := X)).sum dsFourierAt
        ≤ P.eps * SS * (P.H + 1) / 6

class DsPrimePowerAtSumBudget : Prop where
  /-- `/6` budget for the prime-power disposal discrepancy, summed on `bigIcc(X)`. -/
  budget :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      (bigIcc (X := X)).sum dsPrimePowerAt
        ≤ P.eps * SS * (P.H + 1) / 6

theorem dsMassAt_sum_bigIcc_raw
  [DsFourierAtSumBudget] [DsPrimePowerAtSumBudget] :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsMassAt
      ≤ P.eps * SS * (P.H + 1) / 3 := by
  intro X hX
  classical
  have hsplit :
      (bigIcc (X := X)).sum dsMassAt
        ≤ (bigIcc (X := X)).sum (fun Y => dsFourierAt Y + dsPrimePowerAt Y) := by
    refine Finset.sum_le_sum ?_
    intro Y hY
    exact dsMassAt_le_fourier_add_primePower (X := Y)
  have hsum :
      (bigIcc (X := X)).sum (fun Y => dsFourierAt Y + dsPrimePowerAt Y)
        =
      (bigIcc (X := X)).sum dsFourierAt + (bigIcc (X := X)).sum dsPrimePowerAt := by
    simp [Finset.sum_add_distrib]
  have hF := DsFourierAtSumBudget.budget (X := X) hX
  have hPP := DsPrimePowerAtSumBudget.budget (X := X) hX
  have hTot :
      (bigIcc (X := X)).sum dsFourierAt + (bigIcc (X := X)).sum dsPrimePowerAt
        ≤ P.eps * SS * (P.H + 1) / 3 := by
    linarith
  exact le_trans hsplit (le_trans (le_of_eq hsum) hTot)

theorem desmooth_onWindow_raw
  [DsFourierAtSumBudget] [DsPrimePowerAtSumBudget] :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H eds
      ≤ P.eps * SS * (P.H + 1) / 3 := by
  intro X hX
  have h1 : Twin.Ledger.windowSum X P.H eds ≤ (bigIcc (X := X)).sum dsMassAt :=
    windowSum_eds_le_big_sum_dsMassAt (X := X)
  exact le_trans h1 (dsMassAt_sum_bigIcc_raw (X := X) hX)

theorem h_l2 [MinorMassAtSqSumBudget (sme := sme)] : Twin.CLSL2.Bound P (emin (sme := sme)) := by
  refine ⟨?_⟩
  intro X hX
  simpa [SS] using l2_minor_onWindow_raw (sme := sme) (X := X) hX

theorem h_desmooth
  [DsFourierAtSumBudget] [DsPrimePowerAtSumBudget] :
  Twin.AnalyticCore.DesmoothBound P eds := by
  refine ⟨?_⟩
  intro X hX
  simpa [SS, mul_assoc, mul_comm, mul_left_comm] using desmooth_onWindow_raw (X := X) hX

theorem majMass_add_minorMass_eq_fullMass (X : ℕ) :
    Twin.MajorArc.majMass (sme := sme) X P.H
      + minorMassAt (sme := sme) X
      = fullMassAt X := by
  simpa [minorMassAt, fullMassAt] using
    (Twin.MajorArc.majMass_add_minorMass_eq_fullMass_of_full
      (sme := sme) (Λ := Lambda) (W := Wwin)
      (X := X) (H := P.H) (hFull := Twin.ChecklistIntegrability.fullIntegrable (X := X)))

theorem minorMass_abs_le_windowSum_emin (X : ℕ) :
    |minorMassAt (sme := sme) X| ≤ Twin.Ledger.windowSum X P.H (emin (sme := sme)) := by
  classical
  -- each `emin (X+k)` is at least `|minorMassAt X| / N` since `X ∈ [X+k-H, X+k]`
  have hterm :
      ∀ k ∈ Finset.range (P.H + 1),
        |minorMassAt (sme := sme) X| / N ≤ emin (sme := sme) (X + k) := by
    intro k hk
    have hk_le : k ≤ P.H := by
      have : k < P.H + 1 := Finset.mem_range.mp hk
      exact Nat.lt_succ_iff.mp this
    have hmem : X ∈ Finset.Icc ((X + k) - P.H) (X + k) := by
      -- `X + k - H ≤ X` since `k ≤ H`, and `X ≤ X + k`.
      have h1 : X + k - P.H ≤ X := by
        have hk' : X + k - P.H ≤ X + k - k := by
          -- `c - b ≤ c - a` when `a ≤ b`
          exact Nat.sub_le_sub_left hk_le (X + k)
        have : X + k - k = X := by simp
        exact le_trans hk' (by simpa [this])
      have h2 : X ≤ X + k := Nat.le_add_right _ _
      exact (Finset.mem_Icc).2 ⟨h1, h2⟩
    -- `sup'` dominates the value at `X`
    have hsup :
        |minorMassAt (sme := sme) X| / N
          ≤ (Finset.Icc ((X + k) - P.H) (X + k)).sup' (by
              refine ⟨X + k, ?_⟩
              exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩) (fun X0 => |minorMassAt (sme := sme) X0| / N) := by
      exact Finset.le_sup' (f := fun X0 => |minorMassAt (sme := sme) X0| / N) hmem
    simpa [emin] using hsup
  -- sum over k = 0..H
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
  have hsum :
      (Finset.range (P.H + 1)).sum (fun _ => |minorMassAt (sme := sme) X| / N)
        ≤ (Finset.range (P.H + 1)).sum (fun k => emin (sme := sme) (X + k)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hterm k hk
  -- simplify the LHS to `|minorMassAt X|`
  have hN : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ (P.H : ℝ) := by exact_mod_cast Nat.zero_le P.H
    have : (0 : ℝ) < (P.H : ℝ) + 1 := by linarith
    simpa [N] using this
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hconst :
      (Finset.range (P.H + 1)).sum (fun _ => |minorMassAt (sme := sme) X| / N)
        = ((P.H : ℝ) + 1) * (|minorMassAt (sme := sme) X| / N) := by
    simp [Nat.cast_add, Nat.cast_one]
  have hconst' :
      ((P.H : ℝ) + 1) * (|minorMassAt (sme := sme) X| / N) = |minorMassAt (sme := sme) X| := by
    -- `N = (H:ℝ)+1`, so this is `a * (x / a) = x`.
    have ha : ((P.H : ℝ) + 1) ≠ 0 := by simpa [N] using hN0
    -- rearrange by commutativity/associativity, then cancel `a * a⁻¹`.
    simpa [N, div_eq_mul_inv] using
      (calc
        ((P.H : ℝ) + 1) * (|minorMassAt (sme := sme) X| * (((P.H : ℝ) + 1)⁻¹))
            = |minorMassAt (sme := sme) X| * (((P.H : ℝ) + 1) * (((P.H : ℝ) + 1)⁻¹)) := by ac_rfl
        _ = |minorMassAt (sme := sme) X| := by simp [ha])
  -- rewrite the LHS of `hsum` and finish
  have :
      (Finset.range (P.H + 1)).sum (fun _ => |minorMassAt (sme := sme) X| / N)
        = |minorMassAt (sme := sme) X| := by
    exact hconst.trans hconst'
  simpa [this] using hsum

theorem dsMass_le_windowSum_eds (X : ℕ) :
    dsMassAt X ≤ Twin.Ledger.windowSum X P.H eds := by
  classical
  have hterm :
      ∀ k ∈ Finset.range (P.H + 1),
        dsMassAt X / N ≤ eds (X + k) := by
    intro k hk
    have hk_le : k ≤ P.H := by
      have : k < P.H + 1 := Finset.mem_range.mp hk
      exact Nat.lt_succ_iff.mp this
    have hmem : X ∈ Finset.Icc ((X + k) - P.H) (X + k) := by
      have h1 : X + k - P.H ≤ X := by
        have hk' : X + k - P.H ≤ X + k - k := by
          exact Nat.sub_le_sub_left hk_le (X + k)
        have : X + k - k = X := by simp
        exact le_trans hk' (by simpa [this])
      have h2 : X ≤ X + k := Nat.le_add_right _ _
      exact (Finset.mem_Icc).2 ⟨h1, h2⟩
    have hsup :
        dsMassAt X / N
          ≤ (Finset.Icc ((X + k) - P.H) (X + k)).sup' (by
              refine ⟨X + k, ?_⟩
              exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩) (fun X0 => dsMassAt X0 / N) := by
      exact Finset.le_sup' (f := fun X0 => dsMassAt X0 / N) hmem
    simpa [eds] using hsup
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
  have hsum :
      (Finset.range (P.H + 1)).sum (fun _ => dsMassAt X / N)
        ≤ (Finset.range (P.H + 1)).sum (fun k => eds (X + k)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hterm k hk
  have hN : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ (P.H : ℝ) := by exact_mod_cast Nat.zero_le P.H
    have : (0 : ℝ) < (P.H : ℝ) + 1 := by linarith
    simpa [N] using this
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hconst :
      (Finset.range (P.H + 1)).sum (fun _ => dsMassAt X / N)
        = ((P.H : ℝ) + 1) * (dsMassAt X / N) := by
    simp [Nat.cast_add, Nat.cast_one]
  have hconst' :
      ((P.H : ℝ) + 1) * (dsMassAt X / N) = dsMassAt X := by
    have ha : ((P.H : ℝ) + 1) ≠ 0 := by simpa [N] using hN0
    simpa [N, div_eq_mul_inv] using
      (calc
        ((P.H : ℝ) + 1) * (dsMassAt X * (((P.H : ℝ) + 1)⁻¹))
            = dsMassAt X * (((P.H : ℝ) + 1) * (((P.H : ℝ) + 1)⁻¹)) := by ac_rfl
        _ = dsMassAt X := by simp [ha])
  have : (Finset.range (P.H + 1)).sum (fun _ => dsMassAt X / N) = dsMassAt X := by
    exact hconst.trans hconst'
  simpa [this] using hsum

theorem l2_minor_onWindow
  [MinorMassAtSqSumBudget (sme := sme)] :
  ∀ X, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H (fun n => (emin (sme := sme) n)^2)
      ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9 :=
  l2_minor_onWindow_raw (sme := sme)

theorem desmooth_onWindow
  [DsFourierAtSumBudget] [DsPrimePowerAtSumBudget] :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H eds
      ≤ P.eps * SS * (P.H + 1) / 3 :=
  desmooth_onWindow_raw

/-!
## Analytic major-arc mass

We keep two notions separate:

  * `majMassAnalytic`: the literal major-arc integral `Twin.MajorArc.majMass` (paper §11/§14 object),
  instantiated using the supplied `SmoothMajorArcEstimate` parameter `sme`.
* `majMass`: in the paper-faithful route, we take `majMass := majMassAnalytic`.
* `majMassMain`: the canonical main-term function `constMajMass`, useful as a reference target
  for pinned-major evaluations.
-/

noncomputable def majMassAnalytic : ℕ → ℝ :=
  fun X => Twin.MajorArc.majMass (sme := sme) X P.H

noncomputable def majMass : ℕ → ℝ :=
  majMassAnalytic (sme := sme)

def majMassMain : ℕ → ℝ :=
  Twin.MajorArc.MajorArcLower.constMajMass P

/-!
## Remaining major-arc assumptions (still axiomatized)

These are the two remaining paper-facing obligations on the checklist route:
  - routing/transfer inequality (Appendix A.10 / §14.2),
  - pinned majors lower bound with the `/3` tail cap (§14.2 + Lemma 14.5 + Cor 12.8).

Note on future proofs:
  With `Twin.MajorArc.fullMass` and `Twin.MajorArc.minorMass` (see `Twin/MajorArc/MajMass.lean`),
  the intended proof structure for routing is:
    1. establish a Fourier inversion identity for `fullMass` giving a smoothed twin payload;
    2. bound the minor contribution (`minorMass`) by the minor-arc error channel;
    3. dispose prime powers / desmoothing into the `eds` channel;
  and then combine `fullMass = majMass + minorMass` with triangle/budget bounds to get the
  checklist inequality.
-/

/-!
## Routing / transfer (still axiomatized)

At “gold assumptions” level, this is the remaining major-arc input:
the chosen checklist mass `majMass` must be routed/controlled by the localized twin mass
plus explicit error channels.

Paper anchor: Appendix A.10 (routing / bookkeeping), specialized to the window `[X, X+H]`.
-/

theorem h_transfer :
    Twin.MajorArc.MajorArcTransfer P (emin (sme := sme)) eds (majMass (sme := sme)) := by
  classical
  refine ⟨?_⟩
  intro X hX
  -- Split `fullMass = major + minor` and bound the minor part by the `emin` window sum.
  have hsplit :
      majMass (sme := sme) X + minorMassAt (sme := sme) X = fullMassAt X := by
    simpa [majMass, majMassAnalytic] using majMass_add_minorMass_eq_fullMass (sme := sme) (X := X)
  have hMinor :
      |minorMassAt (sme := sme) X| ≤ Twin.Ledger.windowSum X P.H (emin (sme := sme)) :=
    minorMass_abs_le_windowSum_emin (sme := sme) (X := X)
  have hDS : dsMassAt X ≤ Twin.Ledger.windowSum X P.H eds :=
    dsMass_le_windowSum_eds (X := X)
  -- `fullMass ≤ localizedTwinMass + |fullMass-localizedTwinMass|`
  set L : ℝ := Twin.Bridge.localizedTwinMass X P.H
  have hFull_le : fullMassAt X ≤ L + dsMassAt X := by
    have hsub : fullMassAt X - L ≤ dsMassAt X := by
      -- `a - b ≤ |a - b|`
      simpa [dsMassAt, L] using (le_abs_self (fullMassAt X - L))
    -- rearrange
    have := (sub_le_iff_le_add).1 hsub
    simpa [add_comm, add_left_comm, add_assoc, L] using this
  -- Now bound `majMass` using triangle inequalities:
  -- `maj = full - minor ≤ full + |minor| ≤ L + ds + windowSum emin`.
  have hMaj_le :
      majMass (sme := sme) X
        ≤ L + dsMassAt X + Twin.Ledger.windowSum X P.H (emin (sme := sme)) := by
    -- `maj = full - minor` from `hsplit`
    have hMaj_eq : majMass (sme := sme) X = fullMassAt X - minorMassAt (sme := sme) X := by
      exact eq_sub_of_add_eq hsplit
    -- `full - minor ≤ full + |minor|`
    have h1 :
        fullMassAt X - minorMassAt (sme := sme) X
          ≤ fullMassAt X + |minorMassAt (sme := sme) X| := by
      -- `x - y = x + (-y)` and `-y ≤ |y|`
      have :
          fullMassAt X + (-minorMassAt (sme := sme) X)
            ≤ fullMassAt X + |minorMassAt (sme := sme) X| := by
        exact add_le_add_left (neg_le_abs (minorMassAt (sme := sme) X)) (fullMassAt X)
      simpa [sub_eq_add_neg, add_assoc] using this
    -- combine with `full ≤ L + ds`
    have h2 :
        fullMassAt X + |minorMassAt (sme := sme) X|
          ≤ (L + dsMassAt X) + |minorMassAt (sme := sme) X| := by
      exact add_le_add_right hFull_le _
    have h3 : (L + dsMassAt X) + |minorMassAt (sme := sme) X|
        ≤ L + dsMassAt X + Twin.Ledger.windowSum X P.H (emin (sme := sme)) := by
      -- use the `emin` bound for `|minorMassAt X|`
      have := add_le_add_left (add_le_add_left hMinor (L + dsMassAt X)) 0
      -- simpler: add `L + ds` to both sides
      simpa [add_assoc, add_comm, add_left_comm] using add_le_add_left hMinor (L + dsMassAt X)
    -- chain
    have :
        fullMassAt X - minorMassAt (sme := sme) X
          ≤ L + dsMassAt X + Twin.Ledger.windowSum X P.H (emin (sme := sme)) :=
      le_trans h1 (le_trans h2 (by simpa [add_assoc, add_comm, add_left_comm] using h3))
    simpa [hMaj_eq, add_assoc, add_comm, add_left_comm] using this
  -- finish by pushing `dsMassAt` into the `eds` window sum
  have :
      majMass (sme := sme) X
        ≤ L + Twin.Ledger.windowSum X P.H (emin (sme := sme)) + Twin.Ledger.windowSum X P.H eds := by
    -- `L + ds + emin ≤ L + emin + eds`
    have hds' : L + dsMassAt X + Twin.Ledger.windowSum X P.H (emin (sme := sme))
        ≤ L + Twin.Ledger.windowSum X P.H (emin (sme := sme)) + Twin.Ledger.windowSum X P.H eds := by
      have := add_le_add_left (add_le_add_left hDS L) (Twin.Ledger.windowSum X P.H (emin (sme := sme)))
      -- rearrange
      simpa [add_assoc, add_comm, add_left_comm] using this
    exact le_trans hMaj_le hds'
  simpa [L, add_assoc, add_comm, add_left_comm] using this

theorem routing_onWindow :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass (sme := sme) X
      ≤ Twin.Bridge.localizedTwinMass X P.H
        + Twin.Ledger.windowSum X P.H (emin (sme := sme))
        + Twin.Ledger.windowSum X P.H eds :=
by
  intro X hX
  simpa using ((h_transfer (sme := sme)).bound (X := X) hX)

/-!
## Pinned majors lower (still axiomatized)

Paper anchor: §14.2 “Pinned major arcs, and closing the gate”, combined with
Lemma 14.5 (Fourier tail control) and Corollary 12.8 (orthogonality / bank margin).

We record it as the canonical `MajorArcLower` record, and also provide the rearranged
inequality form expected by `Twin.ChecklistTargets.ObligationsExplicit`.
-/

/-!
### Paper-facing pinned majors inequality (axiom, to be proved)

This is the exact “pinned majors main term with `/3` tail cap” inequality used by the checklist
route (paper §14.2 + Lemma 14.5 + Corollary 12.8).

Once we have a full major-arc evaluation proof, this axiom should be replaced by that proof.
-/

/-!
We keep the *derived* lower inequality (used by `MajorArcLower`) but phrase the remaining
paper-facing input as a more “evaluation-shaped” statement: `majMass` is close to the
main term `SS * (H+1)` with error controlled by the `/3` tail cap.
-/

/-!
Pinned majors evaluation (paper §14.2 / Thm 14.6, with the `/3` tail cap absorbed).

This is the remaining conventional analytic input for the checklist route.
-/

/-!
### Decomposed pinned majors (conventional components)

We split the pinned majors evaluation into two more “textbook shaped” components and then
derive the final `/3` cap via a triangle inequality.

Conceptually:
* `majMassMainTerm` is the **main-term** major-arc model mass, obtained by replacing
  `Twin.SW.sumValue` with the SW major-arc main term `Twin.SW.mainTerm` on each major arc.
* `pinnedMajors_SW_error_raw` is the SW error contribution (uses the major-arc SW bound +
  routine integral bookkeeping).
* `pinnedMajors_mainTerm_eval_raw` is the arithmetic main-term evaluation (singular series
  truncation aligned to `SS := truncSingularSeries P.S`).

Both bounds are budgeted at `/6`, so their sum fits the pipeline’s `/3` allowance.
-/

open MeasureTheory

  /-!
  ### Measurable selection for major-arc witnesses

  We choose a deterministic witness `(q,a)` for `IsMajorArc` by encoding pairs via
  `Nat.unpair` and taking the least code satisfying the major-arc predicate using `Nat.find`.

  This replaces the earlier `Classical.choose`-based witness, and will allow us to prove
  `pinnedMajors_mainTermValue_aestronglyMeasurable_raw` without a bespoke axiom.
  -/

  private def majorArcPredNat (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
    (X H : ℝ) (n : ℕ) (α : ℝ) : Prop :=
    let qa : ℕ × ℕ := Nat.unpair n
    let q : ℕ := qa.1
    let a : ℕ := qa.2
    1 ≤ q ∧
      (q : ℝ) ≤ Real.rpow (Real.log H) B ∧
      Nat.Coprime a q ∧
      |α - (a : ℝ) / q| ≤ sme.δ / (H + 1)

  private lemma isMajorArc_iff_existsNat (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
    (X H α : ℝ) :
      Twin.MajorArc.IsMajorArc (sme := sme) X H α ↔ ∃ n : ℕ, majorArcPredNat (sme := sme) X H n α := by
    classical
    constructor
    · intro h
      rcases h with ⟨q, a, hq1, hqB, hcop, hdist⟩
      refine ⟨Nat.pair q a, ?_⟩
      simpa [majorArcPredNat, Nat.unpair_pair] using ⟨hq1, hqB, hcop, hdist⟩
    · rintro ⟨n, hn⟩
      set qa : ℕ × ℕ := Nat.unpair n
      set q : ℕ := qa.1
      set a : ℕ := qa.2
      refine ⟨q, a, ?_⟩
      simpa [majorArcPredNat, qa, q, a] using hn

  private noncomputable def majorArcWitnessNat (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
    (X H α : ℝ) : ℕ := by
    classical
    by_cases hMaj : Twin.MajorArc.IsMajorArc (sme := sme) X H α
    ·
      have hex : ∃ n : ℕ, majorArcPredNat (sme := sme) X H n α :=
        (isMajorArc_iff_existsNat (sme := sme) (X := X) (H := H) (α := α)).1 hMaj
      exact Nat.find hex
    ·
      -- default witness off the major arcs (keeps `q=1` so we never divide by `0`)
      exact Nat.pair 1 0

  private noncomputable def majorArcWitness (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
    (X H α : ℝ) : ℕ × ℕ :=
    Nat.unpair (majorArcWitnessNat (sme := sme) X H α)

  private lemma majorArcWitness_spec_of_isMajorArc
    (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
    {X H α : ℝ} (hMaj : Twin.MajorArc.IsMajorArc (sme := sme) X H α) :
      majorArcPredNat (sme := sme) X H (majorArcWitnessNat (sme := sme) X H α) α := by
    classical
    have hex : ∃ n : ℕ, majorArcPredNat (sme := sme) X H n α :=
      (isMajorArc_iff_existsNat (sme := sme) (X := X) (H := H) (α := α)).1 hMaj
    have hEq : majorArcWitnessNat (sme := sme) X H α = Nat.find hex := by
      simp [majorArcWitnessNat, hMaj]
    simpa [hEq] using (Nat.find_spec hex)

noncomputable def mainTermValue
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) (X H α : ℝ) : ℂ :=
  let qa := majorArcWitness (sme := sme) X H α
  Twin.SW.mainTerm What X H α qa.2 qa.1

  private lemma sumValue_sub_mainTermValue_bound_of_isMajorArc
    {X H α : ℝ}
    (hX : sme.X0 ≤ X) (hH : 1 ≤ H)
    (h : Twin.MajorArc.IsMajorArc (sme := sme) X H α) :
      ‖Twin.SW.sumValue Lambda Wwin X H α - mainTermValue (sme := sme) X H α‖
        ≤ sme.C * (H / Real.rpow (Real.log X) A) := by
    classical
    -- unpack the deterministic witness and use the SW bound at that `a/q`.
    set qa : ℕ × ℕ := majorArcWitness (sme := sme) X H α
    set q : ℕ := qa.1
    set a : ℕ := qa.2
    have hqa :
        1 ≤ q ∧
          (q : ℝ) ≤ Real.rpow (Real.log H) B ∧
            Nat.Coprime a q ∧
              |α - (a : ℝ) / q| ≤ sme.δ / (H + 1) := by
      have hPred :=
        majorArcWitness_spec_of_isMajorArc (sme := sme) (X := X) (H := H) (α := α) h
      simpa [majorArcPredNat, majorArcWitness, majorArcWitnessNat, qa, q, a] using hPred
    rcases hqa with ⟨hq1, hqB, hcop, hdist⟩
    have hmt :
        mainTermValue (sme := sme) X H α = Twin.SW.mainTerm What X H α a q := by
      simp [mainTermValue, qa, q, a]
    -- apply the packaged major-arc SW bound from `sme`
    have hSW :
        ‖Twin.SW.sumValue Lambda Wwin X H α - Twin.SW.mainTerm What X H α a q‖
          ≤ sme.C * (H / Real.rpow (Real.log X) A) :=
      sme.bound (X := X) (H := H) hX hH (q := q) (a := a) hq1 hqB hcop hdist
    simpa [hmt] using hSW

private lemma norm_mul_conj_sub_le (S T : ℂ) :
    ‖S * conj S - T * conj T‖ ≤ ‖S - T‖ * (‖S‖ + ‖T‖) := by
  have hconj : conj (S - T) = conj S - conj T := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hId :
      (S - T) * conj S + T * conj (S - T) = S * conj S - T * conj T := by
    calc
      (S - T) * conj S + T * conj (S - T)
          = (S * conj S - T * conj S) + (T * conj S - T * conj T) := by
              simp [sub_mul, mul_sub, hconj, add_assoc, add_left_comm, add_comm]
      _ = S * conj S - T * conj T := by
              -- `(a - b) + (b - c) = a - c`
              simpa using sub_add_sub_cancel (S * conj S) (T * conj S) (T * conj T)
  have hnorm :
      ‖S * conj S - T * conj T‖ = ‖(S - T) * conj S + T * conj (S - T)‖ := by
    simpa using (congrArg (fun z : ℂ => ‖z‖) hId).symm
  calc
    ‖S * conj S - T * conj T‖
        = ‖(S - T) * conj S + T * conj (S - T)‖ := hnorm
    _ ≤ ‖(S - T) * conj S‖ + ‖T * conj (S - T)‖ := norm_add_le _ _
    _ = ‖S - T‖ * ‖S‖ + ‖T‖ * ‖S - T‖ := by
          -- Avoid rewriting `conj (S - T)` via `conj_sub`; rewrite norms directly.
          have h1 : ‖(S - T) * conj S‖ = ‖S - T‖ * ‖S‖ := by
            have hStarS : ‖conj S‖ = ‖S‖ := by
              -- `conj` is `star` on `ℂ`, and `‖star z‖ = ‖z‖`.
              simpa using (norm_star (x := S))
            calc
              ‖(S - T) * conj S‖ = ‖S - T‖ * ‖conj S‖ := by
                simpa using (norm_mul (S - T) (conj S))
              _ = ‖S - T‖ * ‖S‖ := by
                -- multiply the `‖conj S‖ = ‖S‖` identity by the positive constant `‖S - T‖`
                simpa using (congrArg (fun r : ℝ => ‖S - T‖ * r) hStarS)
          have h2 : ‖T * conj (S - T)‖ = ‖T‖ * ‖S - T‖ := by
            have hStarST : ‖conj (S - T)‖ = ‖S - T‖ := by
              simpa using (norm_star (x := (S - T)))
            calc
              ‖T * conj (S - T)‖ = ‖T‖ * ‖conj (S - T)‖ := by
                simpa using (norm_mul T (conj (S - T)))
              _ = ‖T‖ * ‖S - T‖ := by
                simpa using (congrArg (fun r : ℝ => ‖T‖ * r) hStarST)
          -- finish
          rw [h1, h2]
    _ = ‖S - T‖ * (‖S‖ + ‖T‖) := by ring

private lemma abs_twinCorrIntegrand_sub_le (S T : ℂ) (α : ℝ) :
    |(((S * conj S) * Twin.SW.χ_add (-2 * α)).re
        - ((T * conj T) * Twin.SW.χ_add (-2 * α)).re)|
      ≤ ‖S - T‖ * (‖S‖ + ‖T‖) := by
  set χ : ℂ := Twin.SW.χ_add (-2 * α)
  have hχ : ‖χ‖ = 1 := by
    simpa [χ] using norm_chi_add (-2 * α)
  have hRe :
      (((S * conj S) * χ).re - ((T * conj T) * χ).re)
        = (((S * conj S - T * conj T) * χ).re) := by
    -- `re` is linear and `a*c - b*c = (a-b)*c`
    calc
      ((S * conj S) * χ).re - ((T * conj T) * χ).re
          = (((S * conj S) * χ - (T * conj T) * χ).re) := by simp
      _ = (((S * conj S - T * conj T) * χ).re) := by
            simpa using (congrArg Complex.re (sub_mul (S * conj S) (T * conj T) χ)).symm
  -- reduce to a bound on the complex difference and use `Complex.abs_re_le_norm`
  have hAbs :
      |(((S * conj S) * χ).re - ((T * conj T) * χ).re)|
        = |(((S * conj S - T * conj T) * χ).re)| :=
    congrArg (fun x : ℝ => |x|) hRe
  calc
    |(((S * conj S) * χ).re - ((T * conj T) * χ).re)|
        = |(((S * conj S - T * conj T) * χ).re)| := hAbs
    _ ≤ ‖(S * conj S - T * conj T) * χ‖ := Complex.abs_re_le_norm _
    _ = ‖S * conj S - T * conj T‖ * ‖χ‖ := by simp [norm_mul]
    _ = ‖S * conj S - T * conj T‖ := by simp [hχ]
    _ ≤ ‖S - T‖ * (‖S‖ + ‖T‖) := norm_mul_conj_sub_le S T

noncomputable def twinCorrIntegrandMainTerm
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) (X H α : ℝ) : ℝ :=
  let S : ℂ := mainTermValue (sme := sme) X H α
  ((S * conj S) * Twin.SW.χ_add (-2 * α)).re

noncomputable def majorArcTwinIntegrandMainTerm
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) (X H α : ℝ) : ℝ :=
  Twin.MajorArc.majorArcInd (sme := sme) X H α * twinCorrIntegrandMainTerm (sme := sme) X H α

noncomputable def majMassMainTerm : ℕ → ℝ :=
  fun X =>
    ∫ α in Set.Icc (0 : ℝ) 1,
      majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α

/-!
### SW approximation error on pinned majors (decomposition)

We decompose the old bespoke axiom
`|majMass - majMassMainTerm| ≤ ...`
into:

1. a **conventional measurability/integrability** hypothesis for the main-term integrand
   (this is essentially a measurable-selection issue, since `majorArcWitness` is defined by choice),
2. a **conventional L¹ bound** on the *integrand-level* SW error on the major arcs,
3. a short, fully formal measure-theory wrapper deriving the desired bound on the difference of masses.

This decomposition is faithful to the paper: the analytic content is the L¹ control of the SW error
over major arcs; everything else is bookkeeping.
 -/

  /-!
  #### Main-term integrability (decomposition)

  The proof of `pinnedMajors_SW_error_raw` needs integrability of the main-term major-arc
  integrand on `[0,1]`. Since our main term is defined using a *witness* extracted from the
  major-arc predicate, the only subtlety is measurability (a measurable-selection issue).

  Once measurability is granted, integrability on a finite-measure set follows from a uniform
  pointwise bound, which we prove below from the explicit Gaussian model.
  -/

  /-!
  We now prove the measurability of `mainTermValue` (and hence a.e. strong measurability)
  from the deterministic `Nat.find`-based witness defined above.
  -/

  private lemma measurableSet_majorArcPredNat (X H : ℝ) (n : ℕ) :
      MeasurableSet {α : ℝ | majorArcPredNat (sme := sme) X H n α} := by
    classical
    -- The only α-dependent part is the distance inequality; all other conjuncts are constants.
    set qa : ℕ × ℕ := Nat.unpair n
    set q : ℕ := qa.1
    set a : ℕ := qa.2
    by_cases hc :
        1 ≤ q ∧ (q : ℝ) ≤ Real.rpow (Real.log H) B ∧ Nat.Coprime a q
    ·
      have hEq :
          {α : ℝ | majorArcPredNat (sme := sme) X H n α}
            = {α : ℝ | |α - (a : ℝ) / q| ≤ sme.δ / (H + 1)} := by
        ext α
        constructor
        · intro h
          exact h.2.2.2
        · intro hdist
          refine ⟨hc.1, ?_⟩
          refine ⟨hc.2.1, ?_⟩
          exact ⟨hc.2.2, hdist⟩
      have h1 : Measurable (fun α : ℝ => |α - (a : ℝ) / q|) := by fun_prop
      have h2 : Measurable (fun _ : ℝ => sme.δ / (H + 1)) := measurable_const
      simpa [hEq] using (measurableSet_le h1 h2)
    ·
      have hFalse : ∀ α : ℝ, ¬ majorArcPredNat (sme := sme) X H n α := by
        intro α hPred
        exact hc ⟨hPred.1, hPred.2.1, hPred.2.2.1⟩
      have hEq : {α : ℝ | majorArcPredNat (sme := sme) X H n α} = (∅ : Set ℝ) := by
        ext α
        simp [hFalse α]
      simpa [hEq] using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))

  private def majorArcMinSet (X H : ℝ) (n : ℕ) : Set ℝ :=
    {α : ℝ |
        majorArcPredNat (sme := sme) X H n α ∧
        ∀ m : ℕ, m < n → ¬ majorArcPredNat (sme := sme) X H m α}

  private lemma measurableSet_majorArcMinSet (X H : ℝ) (n : ℕ) :
      MeasurableSet (majorArcMinSet (sme := sme) X H n) := by
    classical
    have hPred :
        MeasurableSet {α : ℝ | majorArcPredNat (sme := sme) X H n α} :=
      measurableSet_majorArcPredNat (sme := sme) (X := X) (H := H) n
    have hMin :
        MeasurableSet {α : ℝ | ∀ m : ℕ, m < n → ¬ majorArcPredNat (sme := sme) X H m α} := by
      have hm : ∀ m : ℕ, Measurable fun α : ℝ => (m < n → ¬ majorArcPredNat (sme := sme) X H m α) := by
        intro m
        by_cases hmn : m < n
        ·
          have hPm : Measurable fun α : ℝ => majorArcPredNat (sme := sme) X H m α :=
            (measurableSet_setOf).1 (measurableSet_majorArcPredNat (sme := sme) (X := X) (H := H) m)
          simpa [hmn] using hPm.not
        ·
          simpa [hmn] using measurable_const
      have hForall :
          Measurable fun α : ℝ => ∀ m : ℕ, (m < n → ¬ majorArcPredNat (sme := sme) X H m α) :=
        Measurable.forall hm
      -- convert back to a measurable set
      simpa [measurableSet_setOf] using hForall.setOf
    -- combine
    simpa [majorArcMinSet, Set.setOf_and] using hPred.inter hMin

  private lemma majorArcWitnessNat_eq_iff_minSet
    {X H α : ℝ} (hMaj : Twin.MajorArc.IsMajorArc (sme := sme) X H α) (n : ℕ) :
      majorArcWitnessNat (sme := sme) X H α = n
        ↔ majorArcPredNat (sme := sme) X H n α ∧
          ∀ m : ℕ, m < n → ¬ majorArcPredNat (sme := sme) X H m α := by
    classical
    set hex : ∃ n : ℕ, majorArcPredNat (sme := sme) X H n α :=
      (isMajorArc_iff_existsNat (sme := sme) (X := X) (H := H) (α := α)).1 hMaj
    have hEq : majorArcWitnessNat (sme := sme) X H α = Nat.find hex := by
      simp [majorArcWitnessNat, hMaj, hex]
    constructor
    · intro hW
      have hSpec : majorArcPredNat (sme := sme) X H (Nat.find hex) α := Nat.find_spec hex
      have hMin : ∀ m : ℕ, m < Nat.find hex → ¬ majorArcPredNat (sme := sme) X H m α :=
        fun m hm => Nat.find_min hex hm
      -- rewrite by the equality `Nat.find hex = n`
      have hn : Nat.find hex = n := by simpa [hEq] using hW
      subst hn
      refine ⟨hSpec, ?_⟩
      intro m hm
      exact hMin m hm
    · rintro ⟨hPn, hMin⟩
      have hle : Nat.find hex ≤ n := Nat.find_min' hex hPn
      have hge : n ≤ Nat.find hex := by
        by_contra hnot
        have hnlt : Nat.find hex < n := lt_of_not_ge hnot
        have hSpec : majorArcPredNat (sme := sme) X H (Nat.find hex) α := Nat.find_spec hex
        exact (hMin (Nat.find hex) hnlt) hSpec
      have hn : Nat.find hex = n := le_antisymm hle hge
      exact hEq.trans hn

  private lemma measurableSet_majorArcWitnessNat_fiber (X H : ℝ) (n : ℕ) :
      MeasurableSet {α : ℝ | majorArcWitnessNat (sme := sme) X H α = n} := by
    classical
    let d : ℕ := Nat.pair 1 0
    by_cases hn : n = d
    ·
      have hMajSet :
          MeasurableSet {α : ℝ | Twin.MajorArc.IsMajorArc (sme := sme) X H α} :=
        Twin.MajorArc.measurableSet_majorArcSet (sme := sme) (X := X) (H := H)
      have hMin : MeasurableSet (majorArcMinSet (sme := sme) X H d) :=
        measurableSet_majorArcMinSet (sme := sme) (X := X) (H := H) d
      have hEq :
          {α : ℝ | majorArcWitnessNat (sme := sme) X H α = n}
            =
            ({α : ℝ | ¬ Twin.MajorArc.IsMajorArc (sme := sme) X H α} ∪ majorArcMinSet (sme := sme) X H d) := by
        ext α
        by_cases hMaj : Twin.MajorArc.IsMajorArc (sme := sme) X H α
        ·
          have hIff := majorArcWitnessNat_eq_iff_minSet (sme := sme) (X := X) (H := H) (α := α) hMaj d
          subst hn
          simp [majorArcMinSet, hMaj, hIff, Set.setOf_and]
        ·
          subst hn
          simp [majorArcWitnessNat, hMaj, d, majorArcMinSet]
      have hOff : MeasurableSet {α : ℝ | ¬ Twin.MajorArc.IsMajorArc (sme := sme) X H α} :=
        hMajSet.compl
      simpa [hEq] using hOff.union hMin
    ·
      have hEq :
          {α : ℝ | majorArcWitnessNat (sme := sme) X H α = n}
            = majorArcMinSet (sme := sme) X H n := by
        ext α
        by_cases hMaj : Twin.MajorArc.IsMajorArc (sme := sme) X H α
        ·
          have hIff := majorArcWitnessNat_eq_iff_minSet (sme := sme) (X := X) (H := H) (α := α) hMaj n
          simpa [majorArcMinSet] using hIff
        ·
          have hW : majorArcWitnessNat (sme := sme) X H α = d := by
            simp [majorArcWitnessNat, hMaj, d]
          have hNo : majorArcWitnessNat (sme := sme) X H α ≠ n := by
            intro hEqn
            have : n = d := by simpa [hW] using hEqn.symm
            exact hn this
          have hEmpty : ¬ (majorArcMinSet (sme := sme) X H n) α := by
            intro hmin
            have : Twin.MajorArc.IsMajorArc (sme := sme) X H α := by
              refine (isMajorArc_iff_existsNat (sme := sme) (X := X) (H := H) (α := α)).2 ?_
              exact ⟨n, hmin.1⟩
            exact hMaj this
          constructor
          · intro hEqn
            exact False.elim (hNo hEqn)
          · intro hmin
            exact False.elim (hEmpty hmin)
      simpa [hEq] using measurableSet_majorArcMinSet (sme := sme) (X := X) (H := H) n

  private lemma measurable_majorArcWitnessNat (X H : ℝ) :
      Measurable (fun α : ℝ => majorArcWitnessNat (sme := sme) X H α) := by
    classical
    intro s hs
    have hEq :
        (fun α : ℝ => majorArcWitnessNat (sme := sme) X H α) ⁻¹' s
          = ⋃ n : ℕ, if n ∈ s then {α : ℝ | majorArcWitnessNat (sme := sme) X H α = n} else (∅ : Set ℝ) := by
      ext α
      constructor
      · intro hmem
        refine Set.mem_iUnion.2 ?_
        refine ⟨majorArcWitnessNat (sme := sme) X H α, ?_⟩
        have hmem' : majorArcWitnessNat (sme := sme) X H α ∈ s := by
          simpa using hmem
        simp [hmem']
      · intro hmem
        rcases Set.mem_iUnion.1 hmem with ⟨n, hn⟩
        by_cases hns : n ∈ s
        ·
          have : majorArcWitnessNat (sme := sme) X H α = n := by
            simpa [hns] using hn
          simpa [this, hns]
        ·
          simpa [hns] using hn
    have hMeas :
        MeasurableSet (⋃ n : ℕ, if n ∈ s then {α : ℝ | majorArcWitnessNat (sme := sme) X H α = n} else (∅ : Set ℝ)) := by
      refine MeasurableSet.iUnion ?_
      intro n
      by_cases hns : n ∈ s
      · simpa [hns] using measurableSet_majorArcWitnessNat_fiber (sme := sme) (X := X) (H := H) n
      · simpa [hns] using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))
    simpa [hEq] using hMeas

  private lemma measurable_majorArcWitness (X H : ℝ) :
      Measurable (fun α : ℝ => majorArcWitness (sme := sme) X H α) := by
    classical
    have hNat : Measurable (fun α : ℝ => majorArcWitnessNat (sme := sme) X H α) :=
      measurable_majorArcWitnessNat (sme := sme) (X := X) (H := H)
    have hUnpair : Measurable (fun n : ℕ => Nat.unpair n) :=
      measurable_of_countable (fun n : ℕ => Nat.unpair n)
    simpa [majorArcWitness] using hUnpair.comp hNat

  /-- A.e. strong measurability of the chosen main-term value used on major arcs
  (proved; no bespoke axiom). -/
  theorem pinnedMajors_mainTermValue_aestronglyMeasurable_raw :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      MeasureTheory.AEStronglyMeasurable
        (fun α : ℝ => mainTermValue (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α)
        MeasureTheory.volume := by
    intro X hX
    classical
    -- Measurability of the witness `(q,a)` as a function of `α`.
    have hWit :
        Measurable (fun α : ℝ =>
          majorArcWitness (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α) :=
      measurable_majorArcWitness (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ))
    have hq : Measurable (fun α : ℝ =>
        (majorArcWitness (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α).1) :=
      hWit.fst
    have ha : Measurable (fun α : ℝ =>
        (majorArcWitness (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α).2) :=
      hWit.snd
    -- Measurable coercions `ℕ → ℝ` and `μ/φ : ℕ → ℝ`.
    have hNatCast : Measurable (fun q : ℕ => (q : ℝ)) :=
      measurable_of_countable (fun q : ℕ => (q : ℝ))
    have hMuOverPhi : Measurable (fun q : ℕ => Twin.SW.muOverPhi q) :=
      measurable_of_countable (fun q : ℕ => Twin.SW.muOverPhi q)
    -- Measurability of the additive character `χ_add`.
    have hChi : Measurable (fun t : ℝ => Twin.SW.χ_add t) := by
      have hArg : Measurable (fun t : ℝ => (2 * Real.pi * Complex.I) * t) := by fun_prop
      simpa [Twin.SW.χ_add, mul_assoc] using (Complex.measurable_exp.comp hArg)
    -- Measurability of `What` (Gaussian).
    have hWhat : Measurable What := by
      fun_prop [What, Twin.ChecklistModel.W_hat]
    -- Build measurability of `mainTermValue` by expanding `Twin.SW.mainTerm`.
    have hMeas :
        Measurable (fun α : ℝ => mainTermValue (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α) := by
      let qR : ℝ → ℝ :=
        fun α =>
          ((majorArcWitness (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α).1 : ℝ)
      let aR : ℝ → ℝ :=
        fun α =>
          ((majorArcWitness (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α).2 : ℝ)
      have hqR : Measurable qR := (hNatCast.comp hq)
      have haR : Measurable aR := (hNatCast.comp ha)
      have hMu : Measurable (fun α : ℝ =>
          Twin.SW.muOverPhi (majorArcWitness (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α).1) :=
        hMuOverPhi.comp hq
      let shift : ℝ → ℝ := fun α => α - aR α / qR α
      have hShift : Measurable shift := by
        fun_prop [shift, aR, qR]
      have hChi1 : Measurable (fun α : ℝ => Twin.SW.χ_add ((shift α) * (X : ℝ))) :=
        hChi.comp (by simpa using hShift.mul measurable_const)
      have hWhatArg : Measurable (fun α : ℝ => (P.H : ℝ) * (shift α)) :=
        measurable_const.mul hShift
      have hWhatComp : Measurable (fun α : ℝ => What ((P.H : ℝ) * (shift α))) :=
        hWhat.comp hWhatArg
      have hOfRealMu : Measurable (fun α : ℝ => Complex.ofReal (Twin.SW.muOverPhi
          (majorArcWitness (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α).1)) :=
        Complex.measurable_ofReal.comp hMu
      have hOfRealHW : Measurable (fun α : ℝ =>
          Complex.ofReal ((P.H : ℝ) * What ((P.H : ℝ) * (shift α)))) :=
        Complex.measurable_ofReal.comp (measurable_const.mul hWhatComp)
      -- Combine the factors (all measurable).
      have hProd : Measurable (fun α : ℝ =>
          Complex.ofReal (Twin.SW.muOverPhi (majorArcWitness (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α).1)
            * Twin.SW.χ_add ((shift α) * (X : ℝ))
            * Complex.ofReal ((P.H : ℝ) * What ((P.H : ℝ) * (shift α)))) := by
        exact (hOfRealMu.mul hChi1).mul hOfRealHW
      -- Match the definitional form of `mainTermValue`.
      simpa [mainTermValue, Twin.SW.mainTerm, shift, aR, qR, mul_assoc, mul_left_comm, mul_comm] using hProd
    exact hMeas.aestronglyMeasurable

  /-- Conventional measurability of the chosen main-term major-arc integrand.
  Derived from `pinnedMajors_mainTermValue_aestronglyMeasurable_raw` plus measurability of
  the major-arc indicator and algebraic operations on `ℂ`. -/
  theorem pinnedMajors_mainTerm_aestronglyMeasurable_raw :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      MeasureTheory.AEStronglyMeasurable
        (fun α : ℝ =>
          majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α)
        MeasureTheory.volume := by
    intro X hX
    classical
    -- Measurability of the major-arc indicator.
    have hMajSet :
        MeasurableSet {α : ℝ | Twin.MajorArc.IsMajorArc (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α} :=
      Twin.MajorArc.measurableSet_majorArcSet (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ))
    have hInd_meas :
        Measurable (fun α : ℝ => Twin.MajorArc.majorArcInd (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α) := by
      classical
      -- unfold the indicator and use `Measurable.ite` with the measurable major-arc set
      simpa [Twin.MajorArc.majorArcInd] using (measurable_const.ite hMajSet measurable_const)
    have hInd :
        MeasureTheory.AEStronglyMeasurable
          (fun α : ℝ => Twin.MajorArc.majorArcInd (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α)
          MeasureTheory.volume :=
      hInd_meas.aestronglyMeasurable

    -- Measurability of the main-term correlation integrand built from `mainTermValue`.
    set Sfun : ℝ → ℂ :=
      fun α => mainTermValue (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α
    have hS : MeasureTheory.AEStronglyMeasurable Sfun MeasureTheory.volume := by
      simpa [Sfun] using pinnedMajors_mainTermValue_aestronglyMeasurable_raw (sme := sme) (X := X) hX
    have hSstar : MeasureTheory.AEStronglyMeasurable (fun α => star (Sfun α)) MeasureTheory.volume :=
      hS.star
    have hMul : MeasureTheory.AEStronglyMeasurable (fun α => Sfun α * star (Sfun α)) MeasureTheory.volume :=
      hS.mul hSstar
    have hChi_meas : Measurable (fun α : ℝ => Twin.SW.χ_add (-2 * α)) := by
      -- unfold the additive character and use measurability of `Complex.exp`
      have hArg : Measurable (fun α : ℝ => (2 * Real.pi * Complex.I) * (-2 * α)) := by
        fun_prop
      -- `Complex.exp` is measurable; compose with the measurable argument map
      simpa [Twin.SW.χ_add, mul_assoc] using (Complex.measurable_exp.comp hArg)
    have hChi : MeasureTheory.AEStronglyMeasurable (fun α : ℝ => Twin.SW.χ_add (-2 * α)) MeasureTheory.volume :=
      hChi_meas.aestronglyMeasurable
    have hProd :
        MeasureTheory.AEStronglyMeasurable
          (fun α => (Sfun α * star (Sfun α)) * Twin.SW.χ_add (-2 * α))
          MeasureTheory.volume :=
      hMul.mul hChi
    have hRe :
        MeasureTheory.AEStronglyMeasurable
          (fun α => Complex.re ((Sfun α * star (Sfun α)) * Twin.SW.χ_add (-2 * α)))
          MeasureTheory.volume := by
      simpa using (Complex.continuous_re.comp_aestronglyMeasurable hProd)
    have hTwinCorr :
        MeasureTheory.AEStronglyMeasurable
          (fun α : ℝ => twinCorrIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α)
          MeasureTheory.volume := by
      -- `twinCorrIntegrandMainTerm` is just `re` of the above product.
      simpa [twinCorrIntegrandMainTerm, Sfun] using hRe

    -- Multiply by the major-arc indicator.
    simpa [majorArcTwinIntegrandMainTerm] using hInd.mul hTwinCorr

  private lemma abs_What_le_kappa (t : ℝ) : |What t| ≤ Twin.ChecklistModel.κ := by
    -- `What t = κ * exp(-π*(κ*t)^2)` is bounded by `κ`.
    have hκ : 0 ≤ (Twin.ChecklistModel.κ : ℝ) := by
      have : 0 < (Twin.ChecklistModel.κ : ℝ) := by norm_num [Twin.ChecklistModel.κ]
      exact le_of_lt this
    have hExp : -Real.pi * (Twin.ChecklistModel.κ * t) ^ 2 ≤ 0 := by
      have hs : 0 ≤ (Twin.ChecklistModel.κ * t) ^ 2 := sq_nonneg _
      nlinarith [Real.pi_pos, hs]
    have hExp_le : Real.exp (-Real.pi * (Twin.ChecklistModel.κ * t) ^ 2) ≤ 1 :=
      (Real.exp_le_one_iff.mpr hExp)
    -- unfold `What` and simplify absolute values
    have hExp_nonneg : 0 ≤ Real.exp (-Real.pi * (Twin.ChecklistModel.κ * t) ^ 2) :=
      le_of_lt (Real.exp_pos _)
    calc
      |What t|
          = |(Twin.ChecklistModel.κ : ℝ)
              * Real.exp (-Real.pi * (Twin.ChecklistModel.κ * t) ^ 2)| := by
                simp [What, Twin.ChecklistModel.W_hat]
      _ = (Twin.ChecklistModel.κ : ℝ)
            * Real.exp (-Real.pi * (Twin.ChecklistModel.κ * t) ^ 2) := by
              simp [abs_mul, abs_of_nonneg hκ, abs_of_nonneg hExp_nonneg]
      _ ≤ (Twin.ChecklistModel.κ : ℝ) * 1 := by
            gcongr
      _ = Twin.ChecklistModel.κ := by simp

    private lemma one_le_majorArcWitness_fst (X H α : ℝ) :
        1 ≤ (majorArcWitness (sme := sme) X H α).1 := by
      classical
      by_cases h : Twin.MajorArc.IsMajorArc (sme := sme) X H α
      ·
        have hPred :=
          majorArcWitness_spec_of_isMajorArc (sme := sme) (X := X) (H := H) (α := α) h
        -- `1 ≤ q` is the first conjunct of `majorArcPredNat`, after decoding the witness code.
        simpa [majorArcPredNat, majorArcWitness] using hPred.1
      ·
        -- off major arcs, the witness is `(1,0)`
        simp [majorArcWitness, majorArcWitnessNat, h]

  private lemma abs_muOverPhi_le_one {q : ℕ} (hq : 1 ≤ q) :
      |Twin.SW.muOverPhi q| ≤ (1 : ℝ) := by
    -- `|μ(q)/φ(q)| ≤ |μ(q)| ≤ 1`.
    have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ (1 : ℝ) := by
      have hμ' : |(ArithmeticFunction.moebius q : ℤ)| ≤ (1 : ℤ) := by
        simpa using (ArithmeticFunction.abs_moebius_le_one (n := q))
      have hμ'' : ((|(ArithmeticFunction.moebius q : ℤ)| : ℤ) : ℝ) ≤ (1 : ℝ) := by
        exact_mod_cast hμ'
      simpa [Int.cast_abs] using hμ''
    have hφpos : 0 < Nat.totient q :=
      (Nat.totient_pos).2 (Nat.pos_of_ne_zero (Nat.ne_of_gt hq))
    have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hφpos)
    calc
      |Twin.SW.muOverPhi q|
          = |((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ)| := by
              simp [Twin.SW.muOverPhi]
    _ = |((ArithmeticFunction.moebius q : ℤ) : ℝ)| / (Nat.totient q : ℝ) := by
            have hnonneg : 0 ≤ (Nat.totient q : ℝ) := by
              exact_mod_cast (Nat.zero_le (Nat.totient q))
            simp [abs_div, abs_of_nonneg hnonneg]
      _ ≤ |((ArithmeticFunction.moebius q : ℤ) : ℝ)| := by
            -- divide by a factor ≥ 1
            exact div_le_self (abs_nonneg _) hφ1
      _ ≤ 1 := hμ

  private lemma norm_mainTermValue_le (X H α : ℝ) :
      ‖mainTermValue (sme := sme) X H α‖ ≤ |H| * Twin.ChecklistModel.κ := by
    classical
    set qa : ℕ × ℕ := majorArcWitness (sme := sme) X H α
    set q : ℕ := qa.1
    set a : ℕ := qa.2
    have hq : 1 ≤ q := by
      simpa [q, qa] using one_le_majorArcWitness_fst (sme := sme) (X := X) (H := H) (α := α)
    have hμ : |Twin.SW.muOverPhi q| ≤ (1 : ℝ) := abs_muOverPhi_le_one (q := q) hq
    have hW : |What (H * (α - (a : ℝ) / q))| ≤ Twin.ChecklistModel.κ :=
      abs_What_le_kappa (t := (H * (α - (a : ℝ) / q)))
    -- unfold the main term and estimate its norm
    have hχ : ‖Twin.SW.χ_add ((α - (a : ℝ) / q) * X)‖ = 1 := norm_chi_add _
    calc
      ‖mainTermValue (sme := sme) X H α‖
          = ‖Twin.SW.mainTerm What X H α a q‖ := by
              simp [mainTermValue, qa, q, a]
      _ = ‖Complex.ofReal (Twin.SW.muOverPhi q)‖
            * ‖Twin.SW.χ_add ((α - (a : ℝ) / q) * X)‖
            * ‖Complex.ofReal (H * What (H * (α - (a : ℝ) / q)))‖ := by
              simp [Twin.SW.mainTerm, norm_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = |Twin.SW.muOverPhi q| * 1 * |H * What (H * (α - (a : ℝ) / q))| := by
              -- prevent unfolding `Twin.SW.muOverPhi` (it is `[simp]`), to avoid spurious goals
              simp [hχ, Complex.norm_real, -Twin.SW.muOverPhi]
      _ ≤ (1 : ℝ) * 1 * (|H| * Twin.ChecklistModel.κ) := by
            have hHW : |H * What (H * (α - (a : ℝ) / q))| ≤ |H| * Twin.ChecklistModel.κ := by
              simpa [abs_mul] using (mul_le_mul_of_nonneg_left hW (abs_nonneg H))
            gcongr
      _ = |H| * Twin.ChecklistModel.κ := by ring

  private lemma abs_twinCorrIntegrandMainTerm_le (X H α : ℝ) :
      |twinCorrIntegrandMainTerm (sme := sme) X H α| ≤ (|H| * Twin.ChecklistModel.κ) ^ 2 := by
    classical
    set S : ℂ := mainTermValue (sme := sme) X H α
    set χ : ℂ := Twin.SW.χ_add (-2 * α)
    have hχ : ‖χ‖ = 1 := by
      simpa [χ] using norm_chi_add (-2 * α)
    have hS : ‖S‖ ≤ |H| * Twin.ChecklistModel.κ := by
      simpa [S] using norm_mainTermValue_le (sme := sme) (X := X) (H := H) (α := α)
    have hRe : |(((S * conj S) * χ).re)| ≤ ‖(S * conj S) * χ‖ := Complex.abs_re_le_norm _
    have hNorm :
        ‖(S * conj S) * χ‖ = ‖S‖ ^ 2 := by
      calc
        ‖(S * conj S) * χ‖ = ‖S * conj S‖ * ‖χ‖ := by simp [norm_mul]
        _ = (‖S‖ * ‖conj S‖) * ‖χ‖ := by simp [norm_mul]
        _ = (‖S‖ * ‖S‖) * ‖χ‖ := by simp [norm_star]
        _ = ‖S‖ ^ 2 := by simp [pow_two, hχ, mul_assoc]
    calc
      |twinCorrIntegrandMainTerm (sme := sme) X H α|
          = |(((S * conj S) * χ).re)| := by
              simp [twinCorrIntegrandMainTerm, S, χ]
      _ ≤ ‖(S * conj S) * χ‖ := hRe
      _ = ‖S‖ ^ 2 := hNorm
      _ ≤ (|H| * Twin.ChecklistModel.κ) ^ 2 := by
            -- monotonicity of `t ↦ t^2` on `ℝ≥0`
            have h0 : 0 ≤ ‖S‖ := norm_nonneg _
            have h1 : 0 ≤ |H| * Twin.ChecklistModel.κ := by
              have : 0 ≤ (Twin.ChecklistModel.κ : ℝ) := by
                have : 0 < (Twin.ChecklistModel.κ : ℝ) := by norm_num [Twin.ChecklistModel.κ]
                exact le_of_lt this
              exact mul_nonneg (abs_nonneg H) this
            have hmul :
                ‖S‖ * ‖S‖ ≤ (|H| * Twin.ChecklistModel.κ) * (|H| * Twin.ChecklistModel.κ) :=
              mul_le_mul hS hS (norm_nonneg _) h1
            simpa [pow_two] using hmul

  private lemma norm_majorArcTwinIntegrandMainTerm_le (X : ℕ) (α : ℝ) :
      ‖majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α‖
        ≤ (|(P.H : ℝ)| * Twin.ChecklistModel.κ) ^ 2 := by
    classical
    set ind : ℝ := Twin.MajorArc.majorArcInd (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α
    set core : ℝ := twinCorrIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α
    have hind : ‖ind‖ ≤ (1 : ℝ) := by
      by_cases h : Twin.MajorArc.IsMajorArc (sme := sme) (X : ℝ) (P.H : ℝ) α
      · simp [ind, Twin.MajorArc.majorArcInd, h]
      · simp [ind, Twin.MajorArc.majorArcInd, h]
    have hcore : ‖core‖ ≤ (|(P.H : ℝ)| * Twin.ChecklistModel.κ) ^ 2 := by
      -- `core` is real, so `‖core‖ = |core|`.
      have h :=
        abs_twinCorrIntegrandMainTerm_le (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) (α := α)
      simpa [core, Real.norm_eq_abs] using h
    calc
      ‖majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α‖
          = ‖ind * core‖ := by simp [majorArcTwinIntegrandMainTerm, ind, core]
      _ = ‖ind‖ * ‖core‖ := by simp [norm_mul]
      _ ≤ (1 : ℝ) * (|(P.H : ℝ)| * Twin.ChecklistModel.κ) ^ 2 := by
            gcongr
      _ = (|(P.H : ℝ)| * Twin.ChecklistModel.κ) ^ 2 := by simp

  /-- Conventional integrability of the chosen main-term major-arc integrand.
  Derived from `pinnedMajors_mainTerm_aestronglyMeasurable_raw` plus a uniform bound on `[0,1]`. -/
  theorem pinnedMajors_mainTerm_integrable_raw :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      MeasureTheory.IntegrableOn
        (fun α : ℝ =>
          majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α)
        (Set.Icc (0 : ℝ) 1) := by
    intro X hX
    classical
    -- apply the boundedness criterion on a finite-measure set
    have hs : (MeasureTheory.volume (Set.Icc (0 : ℝ) 1)) ≠ (⊤ : ENNReal) := by
      have hlt : MeasureTheory.volume (Set.Icc (0 : ℝ) 1) < (⊤ : ENNReal) := by
        simpa using (MeasureTheory.measure_Icc_lt_top (0 : ℝ) (1 : ℝ))
      exact ne_of_lt hlt
    refine
      (MeasureTheory.Measure.integrableOn_of_bounded (μ := MeasureTheory.volume) (s := Set.Icc (0 : ℝ) 1)
        hs (pinnedMajors_mainTerm_aestronglyMeasurable_raw (sme := sme) (X := X) hX) (M := (|(P.H : ℝ)| * Twin.ChecklistModel.κ) ^ 2) ?_)
    -- provide the a.e. bound on the restricted measure (in fact it holds pointwise)
    refine Filter.Eventually.of_forall ?_
    intro α
    simpa using norm_majorArcTwinIntegrandMainTerm_le (sme := sme) (X := X) (α := α)

  /-!
  #### SW error on pinned majors (next decomposition)

  The remaining SW-error input is the L¹ bound `pinnedMajors_SW_error_L1_raw`.  We split this
  into:

  1. a fully formal **pointwise bound** derived from `sme.bound` and the explicit Gaussian model
     bounds on the SW main term,
  2. a single **paper-facing numeric inequality** asserting that this pointwise envelope fits
     inside the `/6` budget.

  This makes the analytic dependency explicit: the only remaining axiom is a parameter/saving
  inequality, rather than an integral statement.
  -/

  /-!
  Compatibility hypothesis used to apply the SW bound on all windows `X ≥ P.X0`.

  The `SmoothMajorArcEstimate` record comes with its own threshold `sme.X0 : ℝ`. Rather than
  axiomatizing a global relation between `sme` and the paper parameters `P`, we thread the
  compatibility `sme.X0 ≤ (P.X0 : ℝ)` as an explicit hypothesis through the pinned-major
  SW-error lemmas.

  In practice (e.g. for `Twin.ChecklistSme.sme`), this is discharged by a concrete numeric
  inequality, since `P.X0` is large and `sme.X0` is tiny.
  -/

  /-- Pointwise SW-error envelope on the major arcs (derived from the SW bound on `S - T`
  and a uniform bound on the main term `T`). -/
  noncomputable def pinnedMajors_SW_error_envelope (X : ℕ) : ℝ :=
    let Xr : ℝ := (X : ℝ)
    let Hr : ℝ := (P.H : ℝ)
    let err : ℝ := |sme.C| * (Hr / Real.rpow (Real.log Xr) A)
    err * (err + 2 * (|Hr| * Twin.ChecklistModel.κ))

    private lemma pinnedMajors_SW_error_envelope_nonneg ⦃X : ℕ⦄ (hX : P.X0 ≤ X) :
        0 ≤ pinnedMajors_SW_error_envelope (sme := sme) X := by
      -- unfold the definition and use that all factors are nonnegative
      dsimp [pinnedMajors_SW_error_envelope]
      set Xr : ℝ := (X : ℝ)
      set Hr : ℝ := (P.H : ℝ)
      have hx0 : 0 ≤ Xr := by
        -- unfold `Xr` to use `Nat.zero_le`
        simpa [Xr] using (show (0 : ℝ) ≤ (X : ℝ) from by exact_mod_cast (Nat.zero_le X))
      have hxNat : 1 ≤ X := by
        exact le_trans (by
          norm_num [P, Twin.PaperParams.P, Twin.PaperParams.X0] : (1 : ℕ) ≤ P.X0) hX
      have hx1 : (1 : ℝ) ≤ Xr := by
        -- `Xr = X` and `1 ≤ X` from the paper basepoint
        simpa [Xr] using (show (1 : ℝ) ≤ (X : ℝ) from by exact_mod_cast hxNat)
      have hlog : 0 ≤ Real.log Xr := Real.log_nonneg hx1
      have hden : 0 ≤ Real.rpow (Real.log Xr) A := Real.rpow_nonneg hlog A
      have hH0 : 0 ≤ Hr := by
        -- `Hr = H` and `H ≥ 0` for naturals
        simpa [Hr] using (show (0 : ℝ) ≤ (P.H : ℝ) from by exact_mod_cast (Nat.zero_le P.H))
      have hrat : 0 ≤ Hr / Real.rpow (Real.log Xr) A := div_nonneg hH0 hden
      have herr : 0 ≤ |sme.C| * (Hr / Real.rpow (Real.log Xr) A) :=
        mul_nonneg (abs_nonneg _) hrat
      have hk : 0 ≤ (Twin.ChecklistModel.κ : ℝ) := by
        have : 0 < (Twin.ChecklistModel.κ : ℝ) := by norm_num [Twin.ChecklistModel.κ]
        exact le_of_lt this
      have htail : 0 ≤ 2 * (|Hr| * Twin.ChecklistModel.κ) :=
        mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) hk)
      have hsum :
          0 ≤ (|sme.C| * (Hr / Real.rpow (Real.log Xr) A)) + 2 * (|Hr| * Twin.ChecklistModel.κ) :=
        add_nonneg herr htail
      exact mul_nonneg herr hsum

  /-- Conventional numeric hypothesis: the SW-error envelope is absorbed by the `/6` allowance.

  This is a **pure parameter/saving inequality** (no integrals). It should ultimately be
  discharged from the frozen analytic model (e.g. `Twin.ChecklistSme.sme`) plus a lower bound
  on the fixed truncated singular series `SS := truncSingularSeries(P.S)`.
  -/
  class PinnedMajorsSWErrorEnvelopeBudget : Prop where
    budget :
      ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
        pinnedMajors_SW_error_envelope (sme := sme) X ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6

  /-- Conventional L¹ control of the major-arc SW error at the integrand level.
  Derived from `PinnedMajorsSWErrorEnvelopeBudget` plus the pointwise envelope bound. -/
  theorem pinnedMajors_SW_error_L1_raw (hsmeX0 : sme.X0 ≤ (P.X0 : ℝ))
      [PinnedMajorsSWErrorEnvelopeBudget (sme := sme)] :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      (∫ α in Set.Icc (0 : ℝ) 1,
          |Twin.MajorArc.majorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
              (X := (X : ℝ)) (H := (P.H : ℝ)) α
            - majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α|)
        ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6 := by
    intro X hX
    classical
    -- Abbreviate the two major-arc integrands on `[0,1]`.
    let f : ℝ → ℝ :=
      fun α =>
        Twin.MajorArc.majorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
          (X := (X : ℝ)) (H := (P.H : ℝ)) α
    let g : ℝ → ℝ :=
      fun α =>
        majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α
    set env : ℝ := pinnedMajors_SW_error_envelope (sme := sme) X

    have hH : (1 : ℝ) ≤ (P.H : ℝ) := by
      -- The concrete paper parameters use `H = 10000`.
      norm_num [P, Twin.PaperParams.P, Twin.PaperParams.H]
    have hXr : sme.X0 ≤ (X : ℝ) := by
      have hPX : (P.X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      exact le_trans hsmeX0 hPX

    -- Pointwise envelope bound.
    have hpoint : ∀ α : ℝ, |f α - g α| ≤ env := by
      intro α
      by_cases hMaj : Twin.MajorArc.IsMajorArc (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α
      · -- On major arcs, reduce to the core correlation integrands and apply the SW bound.
        have hind : Twin.MajorArc.majorArcInd (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α = 1 := by
          simp [Twin.MajorArc.majorArcInd, hMaj]
        have hf' : f α = Twin.MajorArc.twinCorrIntegrand (Λ := Lambda) (W := Wwin)
            (X := (X : ℝ)) (H := (P.H : ℝ)) α := by
          simp [f, Twin.MajorArc.majorArcTwinIntegrand, hind]
        have hg' : g α = twinCorrIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α := by
          simp [g, majorArcTwinIntegrandMainTerm, hind]
        -- SW bound on `‖S - T‖`
        have hST :
            ‖Twin.SW.sumValue Lambda Wwin (X : ℝ) (P.H : ℝ) α
                - mainTermValue (sme := sme) (X : ℝ) (P.H : ℝ) α‖
              ≤ sme.C * ((P.H : ℝ) / Real.rpow (Real.log (X : ℝ)) A) :=
          sumValue_sub_mainTermValue_bound_of_isMajorArc (sme := sme)
            (X := (X : ℝ)) (H := (P.H : ℝ)) (α := α) hXr hH hMaj
        -- bound `‖T‖` and hence `‖S‖` on major arcs
        set T : ℂ := mainTermValue (sme := sme) (X : ℝ) (P.H : ℝ) α
        set S : ℂ := Twin.SW.sumValue Lambda Wwin (X : ℝ) (P.H : ℝ) α
        have hT : ‖T‖ ≤ |(P.H : ℝ)| * Twin.ChecklistModel.κ := by
          simpa [T] using
            norm_mainTermValue_le (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) (α := α)
        have hS : ‖S‖ ≤ ‖S - T‖ + ‖T‖ := by
          -- `S = (S - T) + T`
          have hEq : S = (S - T) + T := (sub_add_cancel S T).symm
          -- then triangle inequality
          have hEq' : ‖S‖ = ‖(S - T) + T‖ := by
            simpa using congrArg (fun z : ℂ => ‖z‖) hEq
          -- finish
          simpa [hEq'] using (norm_add_le (S - T) T)
        have hSum :
            (‖S - T‖) * (‖S‖ + ‖T‖) ≤
              (|sme.C| * ((P.H : ℝ) / Real.rpow (Real.log (X : ℝ)) A))
                * ((|sme.C| * ((P.H : ℝ) / Real.rpow (Real.log (X : ℝ)) A))
                    + 2 * (|(P.H : ℝ)| * Twin.ChecklistModel.κ)) := by
          set rat : ℝ := (P.H : ℝ) / Real.rpow (Real.log (X : ℝ)) A
          have hrat_nonneg : 0 ≤ rat := by
            have hH0 : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
            have hxNat : 1 ≤ X := by
              exact le_trans
                (by
                  norm_num [P, Twin.PaperParams.P, Twin.PaperParams.X0] : (1 : ℕ) ≤ P.X0)
                hX
            have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hxNat
            have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hx1
            have hden : 0 ≤ Real.rpow (Real.log (X : ℝ)) A := Real.rpow_nonneg hlog A
            exact div_nonneg hH0 hden
          have hST1 : ‖S - T‖ ≤ |sme.C| * rat := by
            have hST0 : ‖S - T‖ ≤ sme.C * rat := by
              simpa [S, T, rat, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hST
            have hC : sme.C * rat ≤ |sme.C| * rat :=
              mul_le_mul_of_nonneg_right (le_abs_self sme.C) hrat_nonneg
            exact le_trans hST0 hC
          have hS' : ‖S‖ ≤ (|sme.C| * rat) + (|(P.H : ℝ)| * Twin.ChecklistModel.κ) := by
            linarith [hS, hST1, hT]
          have hSTT :
              ‖S‖ + ‖T‖ ≤ (|sme.C| * rat) + 2 * (|(P.H : ℝ)| * Twin.ChecklistModel.κ) := by
            linarith [hS', hT]
          have hmul :=
            mul_le_mul hST1 hSTT (add_nonneg (norm_nonneg _) (norm_nonneg _))
              (mul_nonneg (abs_nonneg _) hrat_nonneg)
          simpa [rat, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hmul
        -- apply the algebraic bound on the correlation integrands
        have hCore :
            |Twin.MajorArc.twinCorrIntegrand (Λ := Lambda) (W := Wwin) (X := (X : ℝ)) (H := (P.H : ℝ)) α
                - twinCorrIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α|
              ≤ (|sme.C| * ((P.H : ℝ) / Real.rpow (Real.log (X : ℝ)) A))
                * ((|sme.C| * ((P.H : ℝ) / Real.rpow (Real.log (X : ℝ)) A))
                    + 2 * (|(P.H : ℝ)| * Twin.ChecklistModel.κ)) := by
          -- `abs_twinCorrIntegrand_sub_le` gives the bound in terms of `‖S-T‖*(‖S‖+‖T‖)`.
          have hAlg :
              |(Twin.MajorArc.twinCorrIntegrand (Λ := Lambda) (W := Wwin) (X := (X : ℝ)) (H := (P.H : ℝ)) α
                  - twinCorrIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α)|
                ≤ ‖S - T‖ * (‖S‖ + ‖T‖) := by
            -- unfold both cores and apply the pre-proved algebraic inequality
            simpa [Twin.MajorArc.twinCorrIntegrand, twinCorrIntegrandMainTerm, S, T]
              using abs_twinCorrIntegrand_sub_le S T α
          exact le_trans hAlg hSum
        -- finally, rewrite to the major-arc integrands and the envelope `env`
        simpa [hf', hg', env, pinnedMajors_SW_error_envelope] using hCore
      · -- Off the major arcs, both major-arc integrands vanish.
        have hind : Twin.MajorArc.majorArcInd (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α = 0 := by
          simp [Twin.MajorArc.majorArcInd, hMaj]
        have henv_nonneg : 0 ≤ env := by
          simpa [env] using pinnedMajors_SW_error_envelope_nonneg (sme := sme) (X := X) hX
        -- off majors, the difference is `0`, so it suffices that `env ≥ 0`
        simpa [f, g, Twin.MajorArc.majorArcTwinIntegrand, majorArcTwinIntegrandMainTerm, hind] using henv_nonneg

    -- Integrability for monotonicity of integrals.
    have hf_int : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) 1) MeasureTheory.volume := by
      simpa [f] using
        (Twin.MajorArc.integrableOn_majorArcTwinIntegrand_of_full (sme := sme) (Λ := Lambda) (W := Wwin)
          (X := (X : ℝ)) (H := (P.H : ℝ)) (hFull := Twin.ChecklistIntegrability.fullIntegrable (X := X)))
    have hg_int : MeasureTheory.IntegrableOn g (Set.Icc (0 : ℝ) 1) MeasureTheory.volume := by
      simpa [g] using (pinnedMajors_mainTerm_integrable_raw (sme := sme) (X := X) hX)
    have habs_int : MeasureTheory.IntegrableOn (fun α => |f α - g α|) (Set.Icc (0 : ℝ) 1) MeasureTheory.volume := by
      simpa using (hf_int.sub hg_int).abs

    -- Compare the set integrals using the pointwise bound, then discharge the numeric budget.
    have hI :
        (∫ α in Set.Icc (0 : ℝ) 1, |f α - g α|) ≤ (∫ _α in Set.Icc (0 : ℝ) 1, env) := by
      -- monotonicity on a measurable set
      have hs : MeasurableSet (Set.Icc (0 : ℝ) 1) := by simp
      -- `env` is integrable on a finite-measure set
      have hsμ : MeasureTheory.volume (Set.Icc (0 : ℝ) 1) ≠ (⊤ : ENNReal) := by
        -- `volume (Icc 0 1) = 1`
        simp
      have henv_int : MeasureTheory.IntegrableOn (fun _α : ℝ => env) (Set.Icc (0 : ℝ) 1) MeasureTheory.volume :=
        MeasureTheory.integrableOn_const (μ := MeasureTheory.volume) (s := Set.Icc (0 : ℝ) 1) hsμ
      refine MeasureTheory.setIntegral_mono_on (μ := MeasureTheory.volume) (s := Set.Icc (0 : ℝ) 1)
        (hf := habs_int) (hg := henv_int) hs ?_
      · intro α _hα
        simpa [f, g] using hpoint α
    have hConst : (∫ _α in Set.Icc (0 : ℝ) 1, env) = env := by
      -- `volume (Icc 0 1) = 1`
      simp [env]
    have hBudget : env ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6 :=
      PinnedMajorsSWErrorEnvelopeBudget.budget (sme := sme) (X := X) hX
    -- finish
    exact le_trans (le_trans hI (le_of_eq hConst)) hBudget

/-- SW approximation error on the major arcs (conventional; derived from `pinnedMajors_SW_error_L1_raw`). -/
theorem pinnedMajors_SW_error_raw
    [PinnedMajorsSWErrorEnvelopeBudget (sme := sme)] :
  sme.X0 ≤ (P.X0 : ℝ) →
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    |majMass (sme := sme) X - majMassMainTerm (sme := sme) X|
      ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6 := by
  intro hsmeX0 X hX
  classical
  -- Abbreviate the two major-arc integrands on `[0,1]`.
  let f : ℝ → ℝ :=
    fun α =>
      Twin.MajorArc.majorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
        (X := (X : ℝ)) (H := (P.H : ℝ)) α
  let g : ℝ → ℝ :=
    fun α =>
      majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α

  have hf : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) 1) := by
    -- `f` is the standard major-arc integrand; integrability follows from integrability of the full integrand.
    -- (The full integrand is proved integrable for the frozen Gaussian model earlier in this file.)
    simpa [f] using
      (Twin.MajorArc.integrableOn_majorArcTwinIntegrand_of_full (sme := sme) (Λ := Lambda) (W := Wwin)
        (X := (X : ℝ)) (H := (P.H : ℝ)) (hFull := Twin.ChecklistIntegrability.fullIntegrable (X := X)))

  have hg : MeasureTheory.IntegrableOn g (Set.Icc (0 : ℝ) 1) :=
    by simpa [g] using (pinnedMajors_mainTerm_integrable_raw (sme := sme) (X := X) hX)

  -- Rewrite the target as the absolute value of an integral of `f - g`.
  have hSub :
      (∫ α in Set.Icc (0 : ℝ) 1, (f α - g α))
        = (∫ α in Set.Icc (0 : ℝ) 1, f α) - (∫ α in Set.Icc (0 : ℝ) 1, g α) := by
    -- `∫ (f-g) = ∫ f - ∫ g` on the restricted measure.
    simpa [f, g] using
      (MeasureTheory.integral_sub (μ := (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
        (hf := hf) (hg := hg))

  have hAbs :
      |(∫ α in Set.Icc (0 : ℝ) 1, f α) - (∫ α in Set.Icc (0 : ℝ) 1, g α)|
        ≤ ∫ α in Set.Icc (0 : ℝ) 1, |f α - g α| := by
    -- `|∫(f-g)| ≤ ∫|f-g|` on the restricted measure, then rewrite the LHS using `integral_sub`.
    have h0 :
        |∫ α, (f α - g α) ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))|
          ≤ ∫ α, |f α - g α| ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      MeasureTheory.abs_integral_le_integral_abs
        (μ := (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
        (f := fun α => f α - g α)
    -- Convert restricted-measure integrals back into set-integrals and simplify via `hSub`.
    have h1 :
        |∫ α in Set.Icc (0 : ℝ) 1, (f α - g α)|
          ≤ ∫ α in Set.Icc (0 : ℝ) 1, |f α - g α| := by
      simpa using h0
    simpa [hSub] using h1

  -- Apply the L¹ SW-error budget.
  have hL1 : (∫ α in Set.Icc (0 : ℝ) 1, |f α - g α|)
      ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6 := by
    -- Unfolding aligns the L¹ axiom with `f` and `g`.
    simpa [f, g] using pinnedMajors_SW_error_L1_raw (sme := sme) hsmeX0 (X := X) hX

  -- Conclude.
  -- First unfold `majMass` and `majMassMainTerm` into integrals of `f` and `g`.
  have hMaj :
      majMass (sme := sme) X = ∫ α in Set.Icc (0 : ℝ) 1, f α := by
    -- `majMass` is defined via `Twin.MajorArc.majMass`, which is `majMassReal`.
    simp [majMass, majMassAnalytic, Twin.MajorArc.majMass, Twin.MajorArc.majMassReal, f]
  have hMain :
      majMassMainTerm (sme := sme) X = ∫ α in Set.Icc (0 : ℝ) 1, g α := by
    simp [majMassMainTerm, g]

  -- Now chain the inequalities.
  have :
      |majMass (sme := sme) X - majMassMainTerm (sme := sme) X|
        ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6 := by
    -- rewrite and use `hAbs` + `hL1`
    simpa [hMaj, hMain, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (le_trans (by
        -- `|a-b| = |b - a|` isn't needed; use direct form
        simpa [hMaj, hMain, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hAbs) hL1)

  simpa using this

/-!
### Main-term evaluation (decomposition)

The paper’s pinned-major main term is naturally expressed via a finite Euler-product attached to
the fixed truncation set `P.S`, i.e. `SS := Twin.truncSingularSeries P.S`.

For the checklist route we only need the *numeric* major-arc main-term evaluation at this scale.
We record it directly in terms of `SS` (rather than an internal powerset expansion), so it is
easy to treat as a conventional analytic axiom and later replace by a proof.
-/

/-- Arithmetic evaluation of the main-term major-arc model (conventional; singular series
truncation).

Paper anchor: §14.2 “Pinned major arcs, and closing the gate”.
-/
class PinnedMajorsMainTermEval : Prop where
  eval :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      |majMassMainTerm (sme := sme) X - SS * ((P.H : ℝ) + 1)|
        ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6

theorem pinnedMajors_eval_raw
    [PinnedMajorsSWErrorEnvelopeBudget (sme := sme)]
    [PinnedMajorsMainTermEval (sme := sme)] :
  sme.X0 ≤ (P.X0 : ℝ) →
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    |majMass (sme := sme) X - SS * ((P.H : ℝ) + 1)|
      ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 3 := by
  intro hsmeX0 X hX
  set main : ℝ := SS * ((P.H : ℝ) + 1)
  set tailHalf : ℝ := (P.eps * SS) * ((P.H : ℝ) + 1) / 6
  have hSW : |majMass (sme := sme) X - majMassMainTerm (sme := sme) X| ≤ tailHalf := by
    simpa [tailHalf] using pinnedMajors_SW_error_raw (sme := sme) hsmeX0 (X := X) hX
  have hMT : |majMassMainTerm (sme := sme) X - main| ≤ tailHalf := by
    simpa [main, tailHalf] using PinnedMajorsMainTermEval.eval (sme := sme) (X := X) hX
  have hSplit :
      majMass (sme := sme) X - main
        = (majMass (sme := sme) X - majMassMainTerm (sme := sme) X)
          + (majMassMainTerm (sme := sme) X - main) := by
    ring
  have hTri :
      |majMass (sme := sme) X - main|
        ≤ |majMass (sme := sme) X - majMassMainTerm (sme := sme) X|
          + |majMassMainTerm (sme := sme) X - main| := by
    -- triangle inequality, after splitting the difference through the intermediate main term
    have hAbs :
        |majMass (sme := sme) X - main|
          =
          |(majMass (sme := sme) X - majMassMainTerm (sme := sme) X)
            + (majMassMainTerm (sme := sme) X - main)| := by
      simpa using congrArg (fun t : ℝ => |t|) hSplit
    -- rewrite using `hAbs`, then apply `abs_add_le`
    simpa [hAbs] using
      (abs_add_le
        (majMass (sme := sme) X - majMassMainTerm (sme := sme) X)
        (majMassMainTerm (sme := sme) X - main))
  have :
      |majMass (sme := sme) X - main|
        ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 3 := by
    have h1 : |majMass (sme := sme) X - main| ≤ tailHalf + tailHalf :=
      le_trans hTri (add_le_add hSW hMT)
    -- `/6 + /6 = /3`
    have hTail : tailHalf + tailHalf = (P.eps * SS) * ((P.H : ℝ) + 1) / 3 := by
      -- `2*(.../6) = .../3`
      -- keep it robust against rewriting by using `ring`/`field_simp`
      have h6 : (6 : ℝ) ≠ 0 := by norm_num
      field_simp [tailHalf, h6]
      ring
    exact le_trans h1 (le_of_eq hTail)
  simpa [main] using this

theorem pinnedMajors_lower_raw
    [PinnedMajorsSWErrorEnvelopeBudget (sme := sme)]
    [PinnedMajorsMainTermEval (sme := sme)] :
  sme.X0 ≤ (P.X0 : ℝ) →
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass (sme := sme) X
      ≥ (1 - P.eps) * SS * ((P.H : ℝ) + 1)
        - (P.eps * SS) * ((P.H : ℝ) + 1) / 3 := by
  intro hsmeX0 X hX
  set main : ℝ := SS * ((P.H : ℝ) + 1)
  set tail : ℝ := (P.eps * SS) * ((P.H : ℝ) + 1) / 3
  have heval : |majMass (sme := sme) X - main| ≤ tail := by
    simpa [main, tail] using (pinnedMajors_eval_raw (sme := sme) hsmeX0 (X := X) hX)
  have hmain_lower : main - tail ≤ majMass (sme := sme) X := by
    have hle : -tail ≤ majMass (sme := sme) X - main := (abs_le.mp heval).1
    linarith
  -- `main` is nonnegative, hence `(1-eps)*main ≤ main`.
  have ss_nonneg : 0 ≤ SS :=
    Twin.fullTruncSingularSeries_nonneg_of_ge_three (S := P.S) P.S_ge_three
  have hH_nonneg : 0 ≤ ((P.H : ℝ) + 1) := by
    have : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
    linarith
  have main_nonneg : 0 ≤ main := by
    simpa [main] using mul_nonneg ss_nonneg hH_nonneg
  have hcoeff : (1 - P.eps) ≤ 1 := by linarith [P.eps_nonneg]
  have hscaled : (1 - P.eps) * main ≤ main := by
    simpa [one_mul] using (mul_le_mul_of_nonneg_right hcoeff main_nonneg)
  have hscaled' : (1 - P.eps) * main - tail ≤ main - tail := by
    linarith
  have hfinal : (1 - P.eps) * main - tail ≤ majMass (sme := sme) X :=
    le_trans hscaled' hmain_lower
  -- unfold `main`/`tail` back to the file-level expression
  simpa [main, tail, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc, add_comm,
    add_left_comm] using hfinal

theorem h_lower (hsmeX0 : sme.X0 ≤ (P.X0 : ℝ))
    [PinnedMajorsSWErrorEnvelopeBudget (sme := sme)]
    [PinnedMajorsMainTermEval (sme := sme)] :
    Twin.MajorArc.MajorArcLower P (majMass (sme := sme)) := by
  refine ⟨?_⟩
  intro X hX
  have h := pinnedMajors_lower_raw (sme := sme) hsmeX0 (X := X) hX
  -- rearrange `majMass ≥ main - cap` into `main ≤ majMass + cap`
  linarith

/-- Derived gate-on-window inequality from the two paper-facing major-arc obligations. -/
theorem gate_onWindow (hsmeX0 : sme.X0 ≤ (P.X0 : ℝ))
    [PinnedMajorsSWErrorEnvelopeBudget (sme := sme)]
    [PinnedMajorsMainTermEval (sme := sme)] :
    Twin.AnalyticCore.GateOnWindow P (emin (sme := sme)) eds :=
  Twin.MajorArc.gate_onWindow_of_majorArc (P := P) (emin := emin (sme := sme)) (eds := eds)
    (majMass := majMass (sme := sme)) (h_lower (sme := sme) hsmeX0) (h_transfer (sme := sme))

theorem pinnedMajors_lower (hsmeX0 : sme.X0 ≤ (P.X0 : ℝ))
    [PinnedMajorsSWErrorEnvelopeBudget (sme := sme)]
    [PinnedMajorsMainTermEval (sme := sme)] :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass (sme := sme) X
      ≥ (1 - P.eps) * SS * ((P.H : ℝ) + 1)
        - (P.eps * SS) * ((P.H : ℝ) + 1) / 3 :=
  pinnedMajors_lower_raw (sme := sme) hsmeX0

end

end Twin.ChecklistAxioms
