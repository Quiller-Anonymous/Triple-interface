import Goldbach.AO_OffDiag.SigmaTailReindexFun

/-!
An explicit (axiom-free) majorant bound for the Fun-track σ-tail reindex majorant.

This is *not* yet the pinned pipeline statement `|sigmaTail (Q X) N| ≤ K_tail / Q X`:
it is a mechanically checked inequality that makes clear what arithmetic/constant calibration
would be required to obtain a uniform `K_tail`.

Key point: the hard analytic estimate is already proved in
`Goldbach/AO_OffDiag/SigmaTailEuler_Analytic.lean` as
`Goldbach.AO_OffDiag.euler_tail_bound_tsum_ENNReal`.
-/

namespace Goldbach.Cert.SigmaTailExplicitBoundFun

open scoped BigOperators

open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.SigmaTailReindexFun

/-!
### The explicit ENNReal majorant

We name the explicit finite divisor-sum majorant so downstream code can state “calibration”
obligations without duplicating the expression.
-/

private noncomputable def a (r : ℕ) : ENNReal :=
  ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)

/--
Explicit ENNReal majorant for the reindexed tail majorant.

This is exactly the right-hand side used in `reindexMajorantENN_le_explicit` and
`sigmaTail_abs_le_explicit`.
-/
noncomputable def explicitMajorantENN (Q N : ℕ) : ENNReal :=
  ((Nat.divisors N).filter Squarefree).sum (fun d =>
    ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹ *
      (if h : 1 ≤ Q / d then
        ENNReal.ofReal ((90 : ℝ) / ((Q / d : ℕ) : ℝ))
      else
        ENNReal.ofReal (91 : ℝ)))

private lemma inner_sum_R0_le_91 (N : ℕ) :
    (∑' r : ℕ,
        if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
      ≤ ENNReal.ofReal (91 : ℝ) := by
  classical
  -- Split into the singleton contribution at `r = 1` and the tail `1 < r`.
  let f₁ : ℕ → ENNReal := fun r =>
    if r = 1 then
      if Squarefree r ∧ Nat.Coprime r N then a r else 0
    else 0
  let f₂ : ℕ → ENNReal := fun r =>
    if 1 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0
  have hsplit :
      (fun r : ℕ =>
          if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
        =
      fun r : ℕ => f₁ r + f₂ r := by
    funext r
    cases r with
    | zero =>
        simp [f₁, f₂, a]
    | succ r =>
        cases r with
        | zero =>
            -- r = 1
            simp [f₁, f₂, a]
        | succ r =>
            -- r ≥ 2
            have h1 : (1 : ℕ) < r.succ.succ := Nat.succ_lt_succ (Nat.succ_pos _)
            simp [f₁, f₂, a, h1]
  have htsum :
      (∑' r : ℕ, if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
        =
      (∑' r : ℕ, f₁ r) + (∑' r : ℕ, f₂ r) := by
    simpa [hsplit, ENNReal.tsum_add]
  have hf₁ :
      (∑' r : ℕ, f₁ r) ≤ ENNReal.ofReal (1 : ℝ) := by
    have : (∑' r : ℕ, f₁ r) = ENNReal.ofReal (1 : ℝ) := by
      have hsq1 : Squarefree (1 : ℕ) := by
        simpa using (squarefree_one : Squarefree (1 : ℕ))
      have hcop1 : Nat.Coprime (1 : ℕ) N := by
        simpa using (Nat.coprime_one_left N)
      have ha1 : a 1 = ENNReal.ofReal (1 : ℝ) := by
        simp [a, Nat.totient_one]
      simpa [f₁, hsq1, hcop1, ha1] using (tsum_ite_eq (1 : ℕ) (f₁ 1))
    simpa [this]
  have hf₂ :
      (∑' r : ℕ, f₂ r) ≤ ENNReal.ofReal ((90 : ℝ) / 1) := by
    have h :=
      Goldbach.AO_OffDiag.euler_tail_bound_tsum_ENNReal (R := 1) (N := N)
        (by decide : 1 ≤ (1 : ℕ))
    simpa [f₂, a, one_div] using h
  have hle :
      (∑' r : ℕ, if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
        ≤ ENNReal.ofReal (1 : ℝ) + ENNReal.ofReal ((90 : ℝ) / 1) := by
    rw [htsum]
    exact add_le_add hf₁ hf₂
  -- rewrite `ofReal 1 + ofReal 90` as `ofReal 91`
  have hrewrite : ENNReal.ofReal (1 : ℝ) + ENNReal.ofReal ((90 : ℝ) / 1) = ENNReal.ofReal (91 : ℝ) := by
    have h1 : (0 : ℝ) ≤ (1 : ℝ) := by positivity
    have h90 : (0 : ℝ) ≤ ((90 : ℝ) / 1) := by positivity
    calc
      ENNReal.ofReal (1 : ℝ) + ENNReal.ofReal ((90 : ℝ) / 1)
          = ENNReal.ofReal ((1 : ℝ) + (90 : ℝ) / 1) := by
              simpa using (ENNReal.ofReal_add h1 h90).symm
      _ = ENNReal.ofReal (91 : ℝ) := by
              norm_num
  exact le_trans hle (le_of_eq hrewrite)

private lemma inner_sum_le_piecewise (Q d N : ℕ) :
    (∑' r : ℕ,
        if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
      ≤
    (if h : 1 ≤ Q / d then
      ENNReal.ofReal ((90 : ℝ) / ((Q / d : ℕ) : ℝ))
    else
      ENNReal.ofReal (91 : ℝ)) := by
  classical
  by_cases hR : 1 ≤ Q / d
  ·
    have h :=
      Goldbach.AO_OffDiag.euler_tail_bound_tsum_ENNReal (R := Q / d) (N := N) hR
    -- match `a r` with the `1 / (φ(r))^2` form
    simpa [hR, a, one_div] using h
  · have hR0 : Q / d = 0 := by
      have hlt : Q / d < 1 := Nat.lt_of_not_ge hR
      have hle0 : Q / d ≤ 0 := (Nat.lt_succ_iff.mp hlt)
      exact Nat.le_zero.mp hle0
    -- `(Q/d) = 0` turns the cutoff condition into `0 < r`
    have h0 :
        (∑' r : ℕ,
            if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
          =
        (∑' r : ℕ,
            if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0) := by
      simp [hR0]
    have hle : (∑' r : ℕ,
            if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0) ≤ ENNReal.ofReal (91 : ℝ) :=
      inner_sum_R0_le_91 (N := N)
    -- discharge the goal
    simpa [hR, h0] using hle

/--
Explicit bound on the reindexed ENNReal majorant in terms of a finite divisor sum
and the Euler-tail constant `90` (with a safe `91` fallback when `Q/d = 0`).
-/
theorem reindexMajorantENN_le_explicit (Q N : ℕ) :
    reindexMajorantENN Q N
      ≤
    explicitMajorantENN Q N := by
  classical
  unfold reindexMajorantENN
  refine Finset.sum_le_sum ?_
  intro d hd
  have hinner := inner_sum_le_piecewise (Q := Q) (d := d) (N := N)
  -- Multiply the inner bound by the nonnegative prefactor `ofReal (φ(d)⁻¹)`.
  exact mul_le_mul_left' hinner _

/--
Explicit σ-tail bound obtained by combining the reindexing inequality with
`reindexMajorantENN_le_explicit`.

This is a diagnostic theorem: it exposes exactly what remains to be bounded/calibrated to obtain a
uniform `K_tail / Q`.
-/
theorem sigmaTail_abs_le_explicit (Q N : ℕ) (hN0 : N ≠ 0) :
    |sigmaTail Q N|
      ≤
    (explicitMajorantENN Q N).toReal := by
  have h1 : |sigmaTail Q N| ≤ (reindexMajorantENN Q N).toReal :=
    tail_reindex_bound (Q := Q) (N := N) hN0
  have h2 :
      reindexMajorantENN Q N
        ≤ explicitMajorantENN Q N :=
    reindexMajorantENN_le_explicit (Q := Q) (N := N)
  -- RHS is a finite sum of finite ENNReal terms, hence not `⊤`.
  have hRHS_ne_top :
      explicitMajorantENN Q N ≠ (⊤ : ENNReal) := by
    classical
    -- `explicitMajorantENN` is a finite sum of products of `ofReal` terms, so it is finite.
    have :
        (∑ d ∈ (Nat.divisors N).filter Squarefree,
            ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹ *
              (if h : 1 ≤ Q / d then
                ENNReal.ofReal ((90 : ℝ) / ((Q / d : ℕ) : ℝ))
              else
                ENNReal.ofReal (91 : ℝ))) ≠ (⊤ : ENNReal) := by
      -- membership-sum finiteness reduces to finiteness of each term
      refine (ENNReal.sum_ne_top).2 ?_
      intro d hd
      -- each summand is a product of finite `ofReal` values
      have hleft : ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹ ≠ (⊤ : ENNReal) := by simp
      by_cases h : 1 ≤ Q / d
      · have hright : ENNReal.ofReal ((90 : ℝ) / ((Q / d : ℕ) : ℝ)) ≠ (⊤ : ENNReal) := by simp
        simpa [h] using (ENNReal.mul_ne_top hleft hright)
      · have hright : ENNReal.ofReal (91 : ℝ) ≠ (⊤ : ENNReal) := by simp
        simpa [h] using (ENNReal.mul_ne_top hleft hright)
    simpa [explicitMajorantENN] using this
  have h2' : (reindexMajorantENN Q N).toReal
      ≤
    (explicitMajorantENN Q N).toReal := by
    exact ENNReal.toReal_mono hRHS_ne_top h2
  exact le_trans h1 h2'

end Goldbach.Cert.SigmaTailExplicitBoundFun
