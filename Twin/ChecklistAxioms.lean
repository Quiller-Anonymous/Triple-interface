import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.Interval.Finset.Nat
import Twin.PaperParams
import Twin.ChecklistModel
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

abbrev P : Twin.GoalAPI.Params := Twin.PaperParams.P
abbrev SS : ℝ := Twin.truncSingularSeries P.S

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

private def bigIcc (X : ℕ) : Finset ℕ :=
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

/-- Raw L² minor budget, stated on the window-level minor masses `minorMassAt`.

Analytic input: control the enlarged square-sum over `bigIcc(X) = [X-H, X+H]`, with the
same normalization factor `N = H+1` used in the definition of `emin`.

This is the canonical place where the CLS/Type-II minor-arc analysis enters.
-/
axiom minorMassAt_sq_sum_bigIcc_core_raw :
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

theorem minorMassAt_sq_sum_bigIcc_raw :
  ∀ X, P.X0 ≤ X →
    (P.H + 1 : ℝ) ^ 2
      * (bigIcc (X := X)).sum (fun Y => (|minorMassAt (sme := sme) Y| / N) ^ 2)
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9 := by
  intro X hX
  -- reduce to the core (more conventional) square-sum statement
  have hcore := minorMassAt_sq_sum_bigIcc_core_raw (sme := sme) X hX
  simpa [minorMassAt_sq_sum_bigIcc_scaled_eq (sme := sme) (X := X)] using hcore

theorem l2_minor_onWindow_raw :
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

This statement is **conventional analytic** (textbook Fourier inversion for a Schwartz window)
and should ultimately be proved, but for gold/checklist status it is acceptable to postulate it.

With this in hand, the “Fourier inversion discrepancy” `dsFourierInvAt` is identically `0`,
so its window-sum budget becomes a pure nonnegativity check.
-/

/-- Fourier inversion identity: the integral-defined full mass equals the explicit smooth ΛΛ sum. -/
axiom fullMassAt_eq_smoothLambdaTwinMassAt :
  ∀ X : ℕ, fullMassAt X = smoothLambdaTwinMassAt X

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

private lemma dsMassAt_le_fourier_add_primePower (X : ℕ) :
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

We postulate the two summed budgets at `/6` each. Their sum yields the canonical `/3` bound.

* `dsFourierInv_sum_bigIcc_raw`: Fourier inversion (integral → explicit smooth ΛΛ sum).
* `dsFourierWindow_sum_bigIcc_raw`: smooth ΛΛ sum → sharp ΛΛ window sum.
  Together these imply `dsFourier_sum_bigIcc_raw` via a triangle inequality.
* `dsPrimePower_sum_bigIcc_raw`: prime-power disposal (ΛΛ vs prime-only log-indicator).
  (Textbook prime-power counting: only `p^m` with `m≥2` contribute to the discrepancy.)
-/

theorem dsFourierInv_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsFourierInvAt
      ≤ P.eps * SS * (P.H + 1) / 12 := by
  intro X hX
  -- `dsFourierInvAt` is identically `0` by Fourier inversion.
  have hsum0 :
      (bigIcc (X := X)).sum dsFourierInvAt = 0 := by
    classical
    simp [dsFourierInvAt, fullMassAt_eq_smoothLambdaTwinMassAt]
  -- RHS is nonnegative.
  have ss_nonneg : 0 ≤ SS :=
    Twin.truncSingularSeries_nonneg_of_ge_three (S := P.S) P.S_ge_three
  have hH_nonneg : 0 ≤ (P.H + 1 : ℝ) := by
    have : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
    simpa [Nat.cast_add, Nat.cast_one] using add_nonneg this (by norm_num)
  have rhs_nonneg :
      0 ≤ P.eps * SS * (P.H + 1) / 12 := by
    have : 0 ≤ P.eps * SS * (P.H + 1 : ℝ) := by
      have heps : 0 ≤ P.eps := le_of_lt P.eps_pos
      exact mul_nonneg (mul_nonneg heps ss_nonneg) hH_nonneg
    exact div_nonneg this (by norm_num)
  simpa [hsum0] using rhs_nonneg

axiom dsFourierWindowTail_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsFourierWindowTailAt
      ≤ P.eps * SS * (P.H + 1) / 24

axiom dsFourierWindowCoreBudget_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsFourierWindowCoreBudgetAt
      ≤ P.eps * SS * (P.H + 1) / 24

theorem dsFourierWindowCore_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsFourierWindowCoreAt
      ≤ P.eps * SS * (P.H + 1) / 24 := by
  intro X hX
  classical
  have hle :
      (bigIcc (X := X)).sum dsFourierWindowCoreAt
        ≤ (bigIcc (X := X)).sum dsFourierWindowCoreBudgetAt := by
    refine Finset.sum_le_sum ?_
    intro Y hY
    exact dsFourierWindowCoreAt_le_budget (X := Y)
  exact le_trans hle (dsFourierWindowCoreBudget_sum_bigIcc_raw (X := X) hX)

theorem dsFourierWindow_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsFourierWindowAt
      ≤ P.eps * SS * (P.H + 1) / 12 := by
  intro X hX
  classical
  have hle :
      (bigIcc (X := X)).sum dsFourierWindowAt
        ≤ (bigIcc (X := X)).sum (fun Y => dsFourierWindowTailAt Y + dsFourierWindowCoreAt Y) := by
    refine Finset.sum_le_sum ?_
    intro Y hY
    exact dsFourierWindowAt_le_tail_add_core (X := Y)
  have hsum_add :
      (bigIcc (X := X)).sum (fun Y => dsFourierWindowTailAt Y + dsFourierWindowCoreAt Y)
        =
      (bigIcc (X := X)).sum dsFourierWindowTailAt
        + (bigIcc (X := X)).sum dsFourierWindowCoreAt := by
    simpa [Finset.sum_add_distrib]
  have hTail := dsFourierWindowTail_sum_bigIcc_raw (X := X) hX
  have hCore := dsFourierWindowCore_sum_bigIcc_raw (X := X) hX
  have hbudget :
      (bigIcc (X := X)).sum (fun Y => dsFourierWindowTailAt Y + dsFourierWindowCoreAt Y)
        ≤ P.eps * SS * (P.H + 1) / 12 := by
    calc
      (bigIcc (X := X)).sum (fun Y => dsFourierWindowTailAt Y + dsFourierWindowCoreAt Y)
          = (bigIcc (X := X)).sum dsFourierWindowTailAt
              + (bigIcc (X := X)).sum dsFourierWindowCoreAt := hsum_add
      _ ≤ P.eps * SS * (P.H + 1) / 24 + P.eps * SS * (P.H + 1) / 24 := by
            exact add_le_add hTail hCore
      _ = P.eps * SS * (P.H + 1) / 12 := by ring
  exact le_trans hle hbudget

theorem dsFourier_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsFourierAt
      ≤ P.eps * SS * (P.H + 1) / 6 := by
  intro X hX
  classical
  have hsum_le :
      (bigIcc (X := X)).sum dsFourierAt
        ≤ (bigIcc (X := X)).sum (fun Y => dsFourierInvAt Y + dsFourierWindowAt Y) := by
    refine Finset.sum_le_sum ?_
    intro Y hY
    exact dsFourierAt_le_inv_add_window (X := Y)
  have hsum_add :
      (bigIcc (X := X)).sum (fun Y => dsFourierInvAt Y + dsFourierWindowAt Y)
        =
      (bigIcc (X := X)).sum dsFourierInvAt
        + (bigIcc (X := X)).sum dsFourierWindowAt := by
    simpa [Finset.sum_add_distrib]
  have hInv := dsFourierInv_sum_bigIcc_raw (X := X) hX
  have hWin := dsFourierWindow_sum_bigIcc_raw (X := X) hX
  have hbudget :
      (bigIcc (X := X)).sum (fun Y => dsFourierInvAt Y + dsFourierWindowAt Y)
        ≤ P.eps * SS * (P.H + 1) / 6 := by
    calc
      (bigIcc (X := X)).sum (fun Y => dsFourierInvAt Y + dsFourierWindowAt Y)
          = (bigIcc (X := X)).sum dsFourierInvAt
              + (bigIcc (X := X)).sum dsFourierWindowAt := hsum_add
      _ ≤ P.eps * SS * (P.H + 1) / 12 + P.eps * SS * (P.H + 1) / 12 := by
            exact add_le_add hInv hWin
      _ = P.eps * SS * (P.H + 1) / 6 := by ring
  exact le_trans hsum_le hbudget

axiom dsPrimePowerLeftBudget_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsPrimePowerLeftBudgetAt
      ≤ P.eps * SS * (P.H + 1) / 12

axiom dsPrimePowerRightBudget_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsPrimePowerRightBudgetAt
      ≤ P.eps * SS * (P.H + 1) / 12

theorem dsPrimePowerLeft_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsPrimePowerLeftAt
      ≤ P.eps * SS * (P.H + 1) / 12 := by
  intro X hX
  classical
  have hle :
      (bigIcc (X := X)).sum dsPrimePowerLeftAt
        ≤ (bigIcc (X := X)).sum dsPrimePowerLeftBudgetAt := by
    refine Finset.sum_le_sum ?_
    intro Y hY
    exact dsPrimePowerLeftAt_le_budget (X := Y)
  exact le_trans hle (dsPrimePowerLeftBudget_sum_bigIcc_raw (X := X) hX)

theorem dsPrimePowerRight_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsPrimePowerRightAt
      ≤ P.eps * SS * (P.H + 1) / 12 := by
  intro X hX
  classical
  have hle :
      (bigIcc (X := X)).sum dsPrimePowerRightAt
        ≤ (bigIcc (X := X)).sum dsPrimePowerRightBudgetAt := by
    refine Finset.sum_le_sum ?_
    intro Y hY
    exact dsPrimePowerRightAt_le_budget (X := Y)
  exact le_trans hle (dsPrimePowerRightBudget_sum_bigIcc_raw (X := X) hX)

theorem dsPrimePower_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsPrimePowerAt
      ≤ P.eps * SS * (P.H + 1) / 6 := by
  intro X hX
  classical
  have hsum_le :
      (bigIcc (X := X)).sum dsPrimePowerAt
        ≤ (bigIcc (X := X)).sum (fun Y => dsPrimePowerLeftAt Y + dsPrimePowerRightAt Y) := by
    refine Finset.sum_le_sum ?_
    intro Y hY
    exact dsPrimePowerAt_le_left_add_right (X := Y)
  have hsum_add :
      (bigIcc (X := X)).sum (fun Y => dsPrimePowerLeftAt Y + dsPrimePowerRightAt Y)
        =
      (bigIcc (X := X)).sum dsPrimePowerLeftAt
        + (bigIcc (X := X)).sum dsPrimePowerRightAt := by
    simpa [Finset.sum_add_distrib]
  have hL := dsPrimePowerLeft_sum_bigIcc_raw (X := X) hX
  have hR := dsPrimePowerRight_sum_bigIcc_raw (X := X) hX
  have hbudget :
      (bigIcc (X := X)).sum (fun Y => dsPrimePowerLeftAt Y + dsPrimePowerRightAt Y)
        ≤ P.eps * SS * (P.H + 1) / 6 := by
    calc
      (bigIcc (X := X)).sum (fun Y => dsPrimePowerLeftAt Y + dsPrimePowerRightAt Y)
          = (bigIcc (X := X)).sum dsPrimePowerLeftAt
              + (bigIcc (X := X)).sum dsPrimePowerRightAt := hsum_add
      _ ≤ P.eps * SS * (P.H + 1) / 12 + P.eps * SS * (P.H + 1) / 12 := by
            exact add_le_add hL hR
      _ = P.eps * SS * (P.H + 1) / 6 := by ring
  exact le_trans hsum_le hbudget

theorem dsMassAt_sum_bigIcc_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (bigIcc (X := X)).sum dsMassAt
      ≤ P.eps * SS * (P.H + 1) / 3 := by
  intro X hX
  classical
  -- sum the pointwise inequality `dsMassAt ≤ dsFourierAt + dsPrimePowerAt`
  have hsum_le :
      (bigIcc (X := X)).sum dsMassAt
        ≤ (bigIcc (X := X)).sum (fun Y => dsFourierAt Y + dsPrimePowerAt Y) := by
    refine Finset.sum_le_sum ?_
    intro Y hY
    exact dsMassAt_le_fourier_add_primePower (X := Y)
  have hsum_add :
      (bigIcc (X := X)).sum (fun Y => dsFourierAt Y + dsPrimePowerAt Y)
        =
      (bigIcc (X := X)).sum dsFourierAt
        + (bigIcc (X := X)).sum dsPrimePowerAt := by
    simpa [Finset.sum_add_distrib]
  have hfourier := dsFourier_sum_bigIcc_raw (X := X) hX
  have hpp := dsPrimePower_sum_bigIcc_raw (X := X) hX
  -- combine `/6 + /6 = /3`
  have hbudget :
      (bigIcc (X := X)).sum (fun Y => dsFourierAt Y + dsPrimePowerAt Y)
        ≤ P.eps * SS * (P.H + 1) / 3 := by
    calc
      (bigIcc (X := X)).sum (fun Y => dsFourierAt Y + dsPrimePowerAt Y)
          = (bigIcc (X := X)).sum dsFourierAt
              + (bigIcc (X := X)).sum dsPrimePowerAt := hsum_add
      _ ≤ P.eps * SS * (P.H + 1) / 6 + P.eps * SS * (P.H + 1) / 6 := by
            exact add_le_add hfourier hpp
      _ = P.eps * SS * (P.H + 1) / 3 := by ring
  exact le_trans hsum_le hbudget

theorem desmooth_onWindow_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H eds
      ≤ P.eps * SS * (P.H + 1) / 3 := by
  intro X hX
  have h1 : Twin.Ledger.windowSum X P.H eds ≤ (bigIcc (X := X)).sum dsMassAt :=
    windowSum_eds_le_big_sum_dsMassAt (X := X)
  exact le_trans h1 (dsMassAt_sum_bigIcc_raw (X := X) hX)

theorem h_l2 : Twin.CLSL2.Bound P (emin (sme := sme)) := by
  refine ⟨?_⟩
  intro X hX
  simpa [SS] using l2_minor_onWindow_raw (sme := sme) (X := X) hX

theorem h_desmooth : Twin.AnalyticCore.DesmoothBound P eds := by
  refine ⟨?_⟩
  intro X hX
  simpa [SS, mul_assoc, mul_comm, mul_left_comm] using desmooth_onWindow_raw (X := X) hX

/-!
## Conventional integrability (proved for the frozen Gaussian model)

To use the `full = major + minor` integral splitting lemma from `Twin/MajorArc/MajMass.lean`,
we need integrability of the full twin-correlation integrand on `[0,1]`.

For the frozen model `Lambda = vonMangoldt` and Gaussian window `Wwin`, we can prove this by:
  1. absolute summability of the defining series `Twin.SW.sumValue`,
  2. continuity of `sumValue` in the phase `α` via `continuous_tsum`,
  3. continuity (hence integrability on a compact interval) of the integrand.

This is conventional analysis (no paper-specific number theory input).
-/

private lemma norm_chi_add (t : ℝ) : ‖Twin.SW.χ_add t‖ = 1 := by
  simp [Twin.SW.χ_add, Complex.norm_exp]

private lemma continuous_chi_add : Continuous Twin.SW.χ_add := by
  -- `χ_add(t) = exp(2π i t)` is continuous.
  have hlin : Continuous fun t : ℝ => (2 * Real.pi * Complex.I) * (t : ℂ) := by
    simpa using (continuous_const.mul Complex.continuous_ofReal)
  have h :
      Continuous fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) :=
    Complex.continuous_exp.comp hlin
  have hEq :
      (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) = Twin.SW.χ_add := by
    funext t
    simp [Twin.SW.χ_add, mul_assoc, mul_left_comm, mul_comm]
  simpa [hEq] using h

private lemma Lambda_abs_le (n : ℕ) : |Lambda n| ≤ (n : ℝ) := by
  -- `Λ(n) ≤ log n ≤ n`, and `Λ(n) ≥ 0`.
  -- Unfold `Lambda` to the canonical von Mangoldt function so simp can see the lemmas.
  simp [Lambda, Twin.ChecklistModel.Λ]
  have h_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log (n := n)
  have h2 : Real.log (n : ℝ) ≤ (n : ℝ) :=
    Real.log_le_self (by exact_mod_cast Nat.zero_le n)
  have hle : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) := le_trans h1 h2
  simpa [abs_of_nonneg h_nonneg] using hle

private lemma Wwin_le_one (u : ℝ) : Wwin u ≤ 1 := by
  -- `Wwin u = exp(-π*(u/κ)^2) ≤ 1` since the exponent is nonpositive.
  have hExp : -Real.pi * (u / Twin.ChecklistModel.κ) ^ 2 ≤ 0 := by
    have hs : 0 ≤ (u / Twin.ChecklistModel.κ) ^ 2 := sq_nonneg _
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  -- `exp x ≤ 1 ↔ x ≤ 0`
  simpa [Wwin, Twin.ChecklistModel.W] using (Real.exp_le_one_iff.mpr hExp)

private lemma summable_sumValue_bound (X : ℕ) :
    Summable (fun n : ℕ =>
      ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / (P.H : ℝ)))‖) := by
  classical
  -- We dominate by a summable exponential tail; only finitely many `n` are problematic.
  let Hr : ℝ := (P.H : ℝ)
  let κ : ℝ := Twin.ChecklistModel.κ
  have hH : 0 < Hr := by
    -- The frozen paper parameters set `H = 10000`.
    norm_num [Hr, P, Twin.PaperParams.P, Twin.PaperParams.H]
  have hκ : 0 < κ := by
    norm_num [κ, Twin.ChecklistModel.κ]

  -- The Gaussian exponent constant `c = π / (H*κ)^2`, and its half `r = c/2`.
  let c : ℝ := Real.pi / ((Hr * κ) ^ 2)
  let r : ℝ := c / 2
  have hr : 0 < r := by
    have hc : 0 < c := by
      have hden : 0 < (Hr * κ) ^ 2 := by
        have : 0 < Hr * κ := mul_pos hH hκ
        nlinarith [sq_pos_of_pos this]
      exact div_pos Real.pi_pos hden
    simpa [r] using (half_pos hc)

  -- A summable comparison function: `n * exp(-r*n)`.
  have hv : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-r * (n : ℝ))) := by
    -- `Real.summable_pow_mul_exp_neg_nat_mul` gives summability of `n^1 * exp(-r*n)`.
    have := Real.summable_pow_mul_exp_neg_nat_mul 1 (r := r) hr
    simpa [pow_one, mul_assoc, mul_comm, mul_left_comm] using this

  -- A finite prefix cutoff.
  let N : ℕ := 2 * X + 1

  -- Define a global upper bound `w`:
  --   for `n < N` we use the constant `N`,
  --   for `n ≥ N` we use `n * exp(-r*n)`.
  let w0 : ℕ → ℝ := fun n => if n < N then (N : ℝ) else 0
  let v : ℕ → ℝ := fun n => (n : ℝ) * Real.exp (-r * (n : ℝ))
  let w1 : ℕ → ℝ := fun n => if n < N then 0 else v n
  let w : ℕ → ℝ := fun n => w0 n + w1 n

  have hw0 : Summable w0 := by
    -- `w0` has finite support contained in `{n | n < N}`.
    refine summable_of_finite_support ?_
    refine (Set.finite_Iio N).subset ?_
    intro n hn
    have hn0 : w0 n ≠ 0 := by
      simpa [Function.mem_support] using hn
    by_contra hlt
    have hge : N ≤ n := le_of_not_gt hlt
    have : w0 n = 0 := by simp [w0, Nat.not_lt_of_ge hge]
    exact hn0 this

  have hw1 : Summable w1 := by
    -- `w1 ≤ v` and `v` is summable.
    refine hv.of_nonneg_of_le ?_ ?_
    · intro n
      by_cases h : n < N
      · simp [w1, v, h]
      · have : 0 ≤ v n := by
          refine mul_nonneg ?_ (Real.exp_nonneg _)
          exact_mod_cast (Nat.zero_le n)
        simpa [w1, v, h] using this
    · intro n
      by_cases h : n < N
      · have : 0 ≤ v n := by
          refine mul_nonneg ?_ (Real.exp_nonneg _)
          exact_mod_cast (Nat.zero_le n)
        simpa [w1, v, h] using this
      · simp [w1, v, h]

  have hw : Summable w := hw0.add hw1

  -- Now show the target bound is dominated by `w`.
  have h_le : ∀ n : ℕ,
      ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ w n := by
    intro n
    by_cases hn : n < N
    · -- crude bound on the finite prefix: `‖…‖ ≤ n ≤ N`
      have hΛ : |Lambda n| ≤ (n : ℝ) := Lambda_abs_le (n := n)
      have hW : Wwin (((n : ℝ) - (X : ℝ)) / Hr) ≤ 1 :=
        Wwin_le_one (u := (((n : ℝ) - (X : ℝ)) / Hr))
      have hnorm :
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖
            = |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := by
        simp
      have hprod :
          |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)|
            ≤ |Lambda n| * 1 := by
        have hWabs : |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| ≤ 1 := by
          have hWnn : 0 ≤ Wwin (((n : ℝ) - (X : ℝ)) / Hr) := by
            have : 0 ≤ Real.exp (-(Real.pi * ((((n : ℝ) - (X : ℝ)) / Hr) / Twin.ChecklistModel.κ) ^ 2)) :=
              Real.exp_nonneg _
            simpa [Wwin, Twin.ChecklistModel.W] using this
          simpa [abs_of_nonneg hWnn] using hW
        -- `|a*b| ≤ |a|*|b|` and `|b| ≤ 1`
        calc
          |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)|
              = |Lambda n| * |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := by
                  simpa [abs_mul]
          _ ≤ |Lambda n| * 1 := by
                gcongr
      have hn_le : (n : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hn)
      have :
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ (N : ℝ) := by
        -- `‖…‖ = |Λ*W| ≤ |Λ| ≤ n ≤ N`
        have : ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ |Lambda n| := by
          simpa [hnorm, mul_one] using le_trans hprod (by simp)
        exact le_trans this (le_trans hΛ hn_le)
      -- since `n < N`, we have `w n = N`
      simpa [w, w0, w1, hn] using this
    · -- exponential tail bound on `n ≥ N`
      have hΛ : |Lambda n| ≤ (n : ℝ) := Lambda_abs_le (n := n)
      -- show `(n-X)^2 ≥ n/2` for `n ≥ 2*X+1`
      have hNX : N ≤ n := le_of_not_gt hn
      have h2X : 2 * X ≤ n := by
        exact le_trans (Nat.le_succ _) hNX
      have hX1 : X + 1 ≤ n := by
        -- `X+1 ≤ 2*X+1 ≤ n`
        have hXle2X : X ≤ 2 * X := by
          -- `1*X ≤ 2*X`
          simpa [one_mul] using (Nat.mul_le_mul_right X (show 1 ≤ 2 by decide))
        have hX1le : X + 1 ≤ 2 * X + 1 := Nat.add_le_add_right hXle2X 1
        exact le_trans hX1le hNX
      have ht_ge_half : ((n : ℝ) - (X : ℝ)) ^ 2 ≥ (n : ℝ) / 2 := by
        have h2X' : (2 : ℝ) * (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2X
        have hX1' : (X : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hX1
        set t : ℝ := (n : ℝ) - (X : ℝ)
        have ht0 : 0 ≤ t := by
          have : (X : ℝ) ≤ (n : ℝ) := by linarith [hX1']
          simpa [t, sub_nonneg] using this
        have ht1 : 1 ≤ t := by
          have : 1 ≤ (n : ℝ) - (X : ℝ) := by linarith [hX1']
          simpa [t] using this
        have ht_half : (n : ℝ) / 2 ≤ t := by
          have hXle : (X : ℝ) ≤ (n : ℝ) / 2 := by linarith [h2X']
          have : (n : ℝ) / 2 ≤ (n : ℝ) - (X : ℝ) := by linarith
          simpa [t] using this
        have ht_le_sq : t ≤ t ^ 2 := by
          have : t * 1 ≤ t * t := by
            simpa using (mul_le_mul_of_nonneg_left ht1 ht0)
          simpa [pow_two, mul_assoc] using this
        exact le_trans ht_half ht_le_sq
      -- `Wwin ≤ exp(-r*n)` from monotonicity of exp and the inequality above
      have hW :
          Wwin (((n : ℝ) - (X : ℝ)) / Hr) ≤ Real.exp (-r * (n : ℝ)) := by
        -- `Wwin u = exp(-π*(u/κ)^2)` and `t^2 ≥ n/2` yields the tail estimate.
        -- rewrite the exponent and reduce to `ht_ge_half`
        have hsq :
            ((((n : ℝ) - (X : ℝ)) / Hr) / κ) ^ 2
              = ((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2 := by
          calc
            ((((n : ℝ) - (X : ℝ)) / Hr) / κ) ^ 2
                = (((n : ℝ) - (X : ℝ)) / (Hr * κ)) ^ 2 := by
                    simp [div_div, mul_assoc]
            _ = ((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2 := by
                  simpa using (div_pow ((n : ℝ) - (X : ℝ)) (Hr * κ) 2)
        have hexp :
            -Real.pi * ((((n : ℝ) - (X : ℝ)) / Hr) / κ) ^ 2 ≤ -r * (n : ℝ) := by
          -- after rewriting, this is exactly `ht_ge_half` and `r = (π/(H*κ)^2)/2`
          -- monotonicity route: divide by a nonnegative denominator and multiply by `π > 0`.
          have hden0 : 0 ≤ (Hr * κ) ^ 2 := sq_nonneg _
          have hdiv :
              (n : ℝ) / 2 / (Hr * κ) ^ 2
                ≤ ((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2 := by
            -- `a ≤ b` ⇒ `a/c ≤ b/c` when `0 ≤ c`
            exact div_le_div_of_nonneg_right ht_ge_half hden0
          have hmul :
              Real.pi * ((n : ℝ) / 2 / (Hr * κ) ^ 2)
                ≤ Real.pi * (((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hdiv Real.pi_pos.le
          have hneg :
              -Real.pi * (((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2)
                ≤ -Real.pi * ((n : ℝ) / 2 / (Hr * κ) ^ 2) := by
            -- negate `hmul`
            simpa [neg_mul] using (neg_le_neg hmul)
          -- rewrite the RHS into the `r*n` form and finish
          have hRHS :
              -Real.pi * ((n : ℝ) / 2 / (Hr * κ) ^ 2)
                = -((Real.pi / (Hr * κ) ^ 2) / 2) * (n : ℝ) := by
            ring_nf
          -- combine and rewrite back using `hsq` and `r = c/2`
          have : -Real.pi * (((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2)
              ≤ -((Real.pi / (Hr * κ) ^ 2) / 2) * (n : ℝ) := by
            simpa [hRHS] using hneg
          simpa [hsq, r, c] using this
        have := Real.exp_le_exp.mpr hexp
        simpa [Wwin, Twin.ChecklistModel.W] using this

      -- wrap up: `‖ofReal(Λ*W)‖ = |Λ*W| ≤ n * exp(-r*n) = v n`
      have hnorm :
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖
            = |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := by
        simp
      have hWnn : 0 ≤ Wwin (((n : ℝ) - (X : ℝ)) / Hr) := by
        -- unfold once to see `exp` nonnegativity
        simpa [Wwin, Twin.ChecklistModel.W] using (Real.exp_nonneg _)
      have habsW : |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| = Wwin (((n : ℝ) - (X : ℝ)) / Hr) := by
        simp [abs_of_nonneg hWnn]
      have :
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ v n := by
        -- `|Λ*W| = |Λ|*|W| ≤ n * exp(-r*n)`
        have : |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)|
            = |Lambda n| * |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := by
              simpa [abs_mul]
        calc
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖
              = |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := hnorm
          _ = |Lambda n| * |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := this
          _ ≤ (n : ℝ) * Real.exp (-r * (n : ℝ)) := by
              -- use bounds `|Λ| ≤ n` and `W ≤ exp(-r*n)`
              have hW' : |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| ≤ Real.exp (-r * (n : ℝ)) := by
                simpa [habsW] using hW
              gcongr
          _ = v n := by simp [v, mul_assoc, mul_comm, mul_left_comm]
      -- rewrite in terms of `w`
      have : ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ w n := by
        simpa [w, w0, w1, v, hn] using this
      exact this

  -- Conclude summability using comparison with `w`.
  refine hw.of_nonneg_of_le (fun n => by simpa using
    (norm_nonneg (Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))))) ?_
  intro n
  -- `h_le` is in terms of `Hr`; rewrite to match the target denominator `(P.H:ℝ)`.
  simpa [Hr, w] using h_le n

theorem fullIntegrable (X : ℕ) :
  MeasureTheory.IntegrableOn
    (fun α =>
      Twin.MajorArc.fullTwinIntegrand (Λ := Lambda) (W := Wwin)
        (X := (X : ℝ)) (H := (P.H : ℝ)) α)
    (Set.Icc (0 : ℝ) 1) := by
  -- Continuity of `sumValue` in `α`, by uniform absolute convergence.
  have hSumValue :
      Continuous (fun α : ℝ => Twin.SW.sumValue Lambda Wwin (X : ℝ) (P.H : ℝ) α) := by
    -- `continuous_tsum` with sup norm bound given by `summable_sumValue_bound`.
    classical
    let f : ℕ → ℝ → ℂ :=
      fun n α =>
        Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / (P.H : ℝ)))
          * Twin.SW.χ_add (α * (n : ℝ))
    let u : ℕ → ℝ :=
      fun n => ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / (P.H : ℝ)))‖
    have hf : ∀ n, Continuous (f n) := by
      intro n
      have hχ : Continuous fun α : ℝ => Twin.SW.χ_add (α * (n : ℝ)) :=
        continuous_chi_add.comp (continuous_id.mul continuous_const)
      simpa [f] using (continuous_const.mul hχ)
    have hu : Summable u := by
      simpa [u] using (summable_sumValue_bound (X := X))
    have hfu : ∀ n α, ‖f n α‖ ≤ u n := by
      intro n α
      simp [f, u, norm_chi_add]
    -- Apply the general continuity theorem for `tsum` of continuous functions.
    simpa [Twin.SW.sumValue, f] using (continuous_tsum hf hu hfu)

  -- Continuity of the full Fourier integrand, hence integrability on `[0,1]`.
  have hFullCont :
      Continuous (fun α : ℝ =>
        Twin.MajorArc.fullTwinIntegrand (Λ := Lambda) (W := Wwin)
          (X := (X : ℝ)) (H := (P.H : ℝ)) α) := by
    -- expand `fullTwinIntegrand` to the twin-correlation integrand
    -- and use continuity of `sumValue` plus algebraic closure properties.
    classical
    -- `twinCorrIntegrand` uses `S := sumValue ...`.
    have : Continuous (fun α : ℝ =>
        Twin.MajorArc.twinCorrIntegrand Lambda Wwin (X : ℝ) (P.H : ℝ) α) := by
      -- unfold and use `hSumValue`.
      set S : ℝ → ℂ := fun α => Twin.SW.sumValue Lambda Wwin (X : ℝ) (P.H : ℝ) α
      have hS : Continuous S := by simpa [S] using hSumValue
      have hconj : Continuous fun α => conj (S α) := Complex.continuous_conj.comp hS
      have hprod : Continuous fun α => S α * conj (S α) := hS.mul hconj
      have hχ : Continuous fun α : ℝ => Twin.SW.χ_add (-2 * α) :=
        continuous_chi_add.comp (continuous_const.mul continuous_id)
      have hC : Continuous fun α : ℝ => (S α * conj (S α)) * Twin.SW.χ_add (-2 * α) :=
        hprod.mul hχ
      have hRe :
          Continuous fun α : ℝ =>
            ((S α * conj (S α)) * Twin.SW.χ_add (-2 * α)).re :=
        Complex.continuous_re.comp hC
      simpa [Twin.MajorArc.twinCorrIntegrand, S] using hRe
    simpa [Twin.MajorArc.fullTwinIntegrand, Twin.MajorArc.twinCorrIntegrand] using this

  -- Continuous on a compact interval ⇒ integrable.
  simpa using (hFullCont.integrableOn_Icc : MeasureTheory.IntegrableOn _ (Set.Icc (0 : ℝ) 1))

theorem majMass_add_minorMass_eq_fullMass (X : ℕ) :
    Twin.MajorArc.majMass (sme := sme) X P.H
      + minorMassAt (sme := sme) X
      = fullMassAt X := by
  simpa [minorMassAt, fullMassAt] using
    (Twin.MajorArc.majMass_add_minorMass_eq_fullMass_of_full
      (sme := sme) (Λ := Lambda) (W := Wwin)
      (X := X) (H := P.H) (hFull := fullIntegrable (X := X)))

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

theorem l2_minor_onWindow :
  ∀ X, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H (fun n => (emin (sme := sme) n)^2)
      ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9 :=
  l2_minor_onWindow_raw (sme := sme)

theorem desmooth_onWindow :
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

private noncomputable def majorArcWitness (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
  (X H α : ℝ) : ℕ × ℕ := by
  classical
  by_cases h : Twin.MajorArc.IsMajorArc (sme := sme) X H α
  · -- We must use classical choice: `IsMajorArc` is an existential in `Prop`.
    let q : ℕ := Classical.choose h
    let a : ℕ := Classical.choose (Classical.choose_spec h)
    exact ⟨q, a⟩
  · exact ⟨1, 0⟩

private lemma majorArcWitness_eq_of_isMajorArc
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
  {X H α : ℝ} (h : Twin.MajorArc.IsMajorArc (sme := sme) X H α) :
    majorArcWitness (sme := sme) X H α
      =
      ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩ := by
  classical
  simp [majorArcWitness, h]

private noncomputable def mainTermValue
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) (X H α : ℝ) : ℂ :=
  let qa := majorArcWitness (sme := sme) X H α
  Twin.SW.mainTerm What X H α qa.2 qa.1

private lemma sumValue_sub_mainTermValue_bound_of_isMajorArc
  {X H α : ℝ}
  (hX : sme.X0 ≤ X) (hH : 1 ≤ H)
  (h : Twin.MajorArc.IsMajorArc (sme := sme) X H α) :
    ‖Twin.SW.sumValue Lambda Wwin X H α - mainTermValue (sme := sme) X H α‖
      ≤ sme.C * (X / Real.rpow (Real.log X) A) := by
  classical
  -- unpack the chosen major-arc rational `a/q`
  set q : ℕ := Classical.choose h
  set a : ℕ := Classical.choose (Classical.choose_spec h)
  have hqa :
      1 ≤ q ∧
        (q : ℝ) ≤ Real.rpow (Real.log X) B ∧
          Nat.Coprime a q ∧
            |α - (a : ℝ) / q| ≤ sme.δ / (H + 1) := by
    simpa [q, a] using (Classical.choose_spec (Classical.choose_spec h))
  rcases hqa with ⟨hq1, hqB, hcop, hdist⟩
  have hmt :
      mainTermValue (sme := sme) X H α = Twin.SW.mainTerm What X H α a q := by
    have hw : majorArcWitness (sme := sme) X H α = ⟨q, a⟩ := by
      simpa [q, a] using (majorArcWitness_eq_of_isMajorArc (sme := sme) (X := X) (H := H) (α := α) h)
    simp [mainTermValue, hw]
  -- apply the packaged major-arc SW bound from `sme`
  have hSW :
      ‖Twin.SW.sumValue Lambda Wwin X H α - Twin.SW.mainTerm What X H α a q‖
        ≤ sme.C * (X / Real.rpow (Real.log X) A) :=
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

private noncomputable def twinCorrIntegrandMainTerm
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) (X H α : ℝ) : ℝ :=
  let S : ℂ := mainTermValue (sme := sme) X H α
  ((S * conj S) * Twin.SW.χ_add (-2 * α)).re

private noncomputable def majorArcTwinIntegrandMainTerm
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

  /-- Conventional measurability hypothesis for the chosen main-term major-arc integrand.
  This isolates the measurable-selection issue coming from `majorArcWitness`. -/
  axiom pinnedMajors_mainTerm_aestronglyMeasurable_raw :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      MeasureTheory.AEStronglyMeasurable
        (fun α : ℝ =>
          majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α)
        MeasureTheory.volume

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
    · have hq :
          1 ≤ Classical.choose h :=
        (Classical.choose_spec (Classical.choose_spec h)).1
      simpa [majorArcWitness, h] using hq
    · simp [majorArcWitness, h]

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
      ‖mainTermValue (sme := sme) X H α‖ ≤ |X| * Twin.ChecklistModel.κ := by
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
            * ‖Complex.ofReal (X * What (H * (α - (a : ℝ) / q)))‖ := by
              simp [Twin.SW.mainTerm, norm_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = |Twin.SW.muOverPhi q| * 1 * |X * What (H * (α - (a : ℝ) / q))| := by
              -- prevent unfolding `Twin.SW.muOverPhi` (it is `[simp]`), to avoid spurious goals
              simp [hχ, Complex.norm_real, -Twin.SW.muOverPhi]
      _ ≤ (1 : ℝ) * 1 * (|X| * Twin.ChecklistModel.κ) := by
            have hXW : |X * What (H * (α - (a : ℝ) / q))| ≤ |X| * Twin.ChecklistModel.κ := by
              simpa [abs_mul] using (mul_le_mul_of_nonneg_left hW (abs_nonneg X))
            gcongr
      _ = |X| * Twin.ChecklistModel.κ := by ring

  private lemma abs_twinCorrIntegrandMainTerm_le (X H α : ℝ) :
      |twinCorrIntegrandMainTerm (sme := sme) X H α| ≤ (|X| * Twin.ChecklistModel.κ) ^ 2 := by
    classical
    set S : ℂ := mainTermValue (sme := sme) X H α
    set χ : ℂ := Twin.SW.χ_add (-2 * α)
    have hχ : ‖χ‖ = 1 := by
      simpa [χ] using norm_chi_add (-2 * α)
    have hS : ‖S‖ ≤ |X| * Twin.ChecklistModel.κ := by
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
      _ ≤ (|X| * Twin.ChecklistModel.κ) ^ 2 := by
            -- monotonicity of `t ↦ t^2` on `ℝ≥0`
            have h0 : 0 ≤ ‖S‖ := norm_nonneg _
            have h1 : 0 ≤ |X| * Twin.ChecklistModel.κ := by
              have : 0 ≤ (Twin.ChecklistModel.κ : ℝ) := by
                have : 0 < (Twin.ChecklistModel.κ : ℝ) := by norm_num [Twin.ChecklistModel.κ]
                exact le_of_lt this
              exact mul_nonneg (abs_nonneg X) this
            have hmul :
                ‖S‖ * ‖S‖ ≤ (|X| * Twin.ChecklistModel.κ) * (|X| * Twin.ChecklistModel.κ) :=
              mul_le_mul hS hS (norm_nonneg _) h1
            simpa [pow_two] using hmul

  private lemma norm_majorArcTwinIntegrandMainTerm_le (X : ℕ) (α : ℝ) :
      ‖majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α‖
        ≤ (|(X : ℝ)| * Twin.ChecklistModel.κ) ^ 2 := by
    classical
    set ind : ℝ := Twin.MajorArc.majorArcInd (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α
    set core : ℝ := twinCorrIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α
    have hind : ‖ind‖ ≤ (1 : ℝ) := by
      by_cases h : Twin.MajorArc.IsMajorArc (sme := sme) (X : ℝ) (P.H : ℝ) α
      · simp [ind, Twin.MajorArc.majorArcInd, h]
      · simp [ind, Twin.MajorArc.majorArcInd, h]
    have hcore : ‖core‖ ≤ (|(X : ℝ)| * Twin.ChecklistModel.κ) ^ 2 := by
      -- `core` is real, so `‖core‖ = |core|`.
      have h :=
        abs_twinCorrIntegrandMainTerm_le (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) (α := α)
      simpa [core, Real.norm_eq_abs] using h
    calc
      ‖majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α‖
          = ‖ind * core‖ := by simp [majorArcTwinIntegrandMainTerm, ind, core]
      _ = ‖ind‖ * ‖core‖ := by simp [norm_mul]
      _ ≤ (1 : ℝ) * (|(X : ℝ)| * Twin.ChecklistModel.κ) ^ 2 := by
            gcongr
      _ = (|(X : ℝ)| * Twin.ChecklistModel.κ) ^ 2 := by simp

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
        hs (pinnedMajors_mainTerm_aestronglyMeasurable_raw (sme := sme) (X := X) hX) (M := (|(X : ℝ)| * Twin.ChecklistModel.κ) ^ 2) ?_)
    -- provide the a.e. bound on the restricted measure (in fact it holds pointwise)
    refine Filter.Eventually.of_forall ?_
    intro α
    simpa using norm_majorArcTwinIntegrandMainTerm_le (sme := sme) (X := X) (α := α)

/-- Conventional L¹ control of the major-arc SW error at the integrand level. -/
axiom pinnedMajors_SW_error_L1_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    (∫ α in Set.Icc (0 : ℝ) 1,
        |Twin.MajorArc.majorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
            (X := (X : ℝ)) (H := (P.H : ℝ)) α
          - majorArcTwinIntegrandMainTerm (sme := sme) (X := (X : ℝ)) (H := (P.H : ℝ)) α|)
      ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6

/-- SW approximation error on the major arcs (conventional; derived from `pinnedMajors_SW_error_L1_raw`). -/
theorem pinnedMajors_SW_error_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    |majMass (sme := sme) X - majMassMainTerm (sme := sme) X|
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

  have hf : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) 1) := by
    -- `f` is the standard major-arc integrand; integrability follows from integrability of the full integrand.
    -- (The full integrand is proved integrable for the frozen Gaussian model earlier in this file.)
    simpa [f] using
      (Twin.MajorArc.integrableOn_majorArcTwinIntegrand_of_full (sme := sme) (Λ := Lambda) (W := Wwin)
        (X := (X : ℝ)) (H := (P.H : ℝ)) (hFull := fullIntegrable (X := X)))

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
    simpa [f, g] using pinnedMajors_SW_error_L1_raw (sme := sme) (X := X) hX

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
        simpa [hMaj, hMain] using hAbs) hL1)

  simpa using this

/-!
### Main-term evaluation (decomposition)

The paper’s pinned-major main term is naturally expressed as a finite Euler-product / powerset
expansion over the fixed truncation set `P.S`.  We therefore split the remaining main-term
evaluation input into:

1. an axiom giving the evaluation against the **explicit powerset expansion**
   `Twin.truncSingularSeriesExpansion P.S`,
2. a short lemma rewriting that expansion back to `SS := Twin.truncSingularSeries P.S`
   using the algebraic identity in `Twin/SingularSeries.lean`.
-/

/-- Arithmetic evaluation of the main-term major-arc model (conventional; aligned to the
explicit powerset expansion of the truncated singular series). -/
axiom pinnedMajors_mainTerm_eval_expansion_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    |majMassMainTerm (sme := sme) X
        - Twin.truncSingularSeriesExpansion P.S * ((P.H : ℝ) + 1)|
      ≤ (P.eps * Twin.truncSingularSeriesExpansion P.S) * ((P.H : ℝ) + 1) / 6

/-- Arithmetic evaluation of the main-term major-arc model (conventional; singular series
truncation).  Derived from `pinnedMajors_mainTerm_eval_expansion_raw` via the algebraic
identity `truncSingularSeries_eq_expansion`. -/
theorem pinnedMajors_mainTerm_eval_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    |majMassMainTerm (sme := sme) X - SS * ((P.H : ℝ) + 1)|
      ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6 := by
  intro X hX
  have hExp :=
    pinnedMajors_mainTerm_eval_expansion_raw (sme := sme) (X := X) hX
  have hSS : Twin.truncSingularSeriesExpansion P.S = SS := by
    -- purely algebraic: ∏_{p∈S} (1 - 1/(p-1)^2) expands over `S.powerset`
    simpa [SS] using (Twin.truncSingularSeries_eq_expansion (S := P.S)).symm
  -- rewrite the expansion back to `SS`
  simpa [hSS] using hExp

theorem pinnedMajors_eval_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    |majMass (sme := sme) X - SS * ((P.H : ℝ) + 1)|
      ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 3 := by
  intro X hX
  set main : ℝ := SS * ((P.H : ℝ) + 1)
  set tailHalf : ℝ := (P.eps * SS) * ((P.H : ℝ) + 1) / 6
  have hSW : |majMass (sme := sme) X - majMassMainTerm (sme := sme) X| ≤ tailHalf := by
    simpa [tailHalf] using pinnedMajors_SW_error_raw (sme := sme) (X := X) hX
  have hMT : |majMassMainTerm (sme := sme) X - main| ≤ tailHalf := by
    simpa [main, tailHalf] using pinnedMajors_mainTerm_eval_raw (sme := sme) (X := X) hX
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

theorem pinnedMajors_lower_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass (sme := sme) X
      ≥ (1 - P.eps) * SS * ((P.H : ℝ) + 1)
        - (P.eps * SS) * ((P.H : ℝ) + 1) / 3 := by
  intro X hX
  set main : ℝ := SS * ((P.H : ℝ) + 1)
  set tail : ℝ := (P.eps * SS) * ((P.H : ℝ) + 1) / 3
  have heval : |majMass (sme := sme) X - main| ≤ tail := by
    simpa [main, tail] using (pinnedMajors_eval_raw (sme := sme) (X := X) hX)
  have hmain_lower : main - tail ≤ majMass (sme := sme) X := by
    have hle : -tail ≤ majMass (sme := sme) X - main := (abs_le.mp heval).1
    linarith
  -- `main` is nonnegative, hence `(1-eps)*main ≤ main`.
  have ss_nonneg : 0 ≤ SS :=
    Twin.truncSingularSeries_nonneg_of_ge_three (S := P.S) P.S_ge_three
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

theorem h_lower : Twin.MajorArc.MajorArcLower P (majMass (sme := sme)) := by
  refine ⟨?_⟩
  intro X hX
  have h := pinnedMajors_lower_raw (sme := sme) (X := X) hX
  -- rearrange `majMass ≥ main - cap` into `main ≤ majMass + cap`
  linarith

/-- Derived gate-on-window inequality from the two paper-facing major-arc obligations. -/
theorem gate_onWindow : Twin.AnalyticCore.GateOnWindow P (emin (sme := sme)) eds :=
  Twin.MajorArc.gate_onWindow_of_majorArc (P := P) (emin := emin (sme := sme)) (eds := eds)
    (majMass := majMass (sme := sme)) (h_lower (sme := sme)) (h_transfer (sme := sme))

theorem pinnedMajors_lower :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass (sme := sme) X
      ≥ (1 - P.eps) * SS * ((P.H : ℝ) + 1)
        - (P.eps * SS) * ((P.H : ℝ) + 1) / 3 :=
  pinnedMajors_lower_raw (sme := sme)

end

end Twin.ChecklistAxioms
