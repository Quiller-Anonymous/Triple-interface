import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit
import Goldbach.Cert.MajorArcStep24IntegralExtraction
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.Int.Lemmas

/-!
Step 5 (ε₂-large TT*/Toeplitz): kernel-mass bounds from the explicit `AX + LX + RX` split.

This is the “glue” between:

* `Q0MajorTailTTStarToeplitzScaffold.lean`, which defines the kernel masses
  `kernelMassNZEven` / `kernelMassNZOdd` in terms of the hard-arc Fourier coefficient
  `majorArcWeightFourier`, and
* `Q0MajorTailTTStarStep5WeightSplit.lean`, which provides the explicit decomposition
  `majorArcWeightFourier = AX + LX + RX` for `t ≠ 0` and a uniform pointwise bound on `RX`.

At this stage we keep the `AX` and `LX` contributions symbolic; the certificate/generator is
expected to provide numeric bounds for their band-limited mean squares, while `RX` is discharged
deterministically via the uniform remainder bound in the split file.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit

noncomputable section

/-!
### Internal split parameter (AX+LX vs RX)

`δ_split = 50` is frozen upstream in `Q0MajorTailTTStarStep5ABC.lean` for the *Toeplitz* weighted
split (kernel nonzero modes vs the `t=0` spike).

The **Step-5 weight split** `Ŵ = (AX+LX) + RX` is a separate inequality step and should not be
forced to reuse the same parameter.  We introduce an independent (fixed) parameter here so the
generator and Lean can align on a single, stable inequality.
-/

noncomputable abbrev δ_weightSplit : ℝ := 1

lemma δ_weightSplit_pos : 0 < δ_weightSplit := by
  norm_num [δ_weightSplit]

private lemma sepQ0_one_of_X0_le {X : ℕ} (hX : X0 ≤ X) : SepQ0 X (1 : ℝ) := by
  -- `2*Q0 = 60000 < X0 ≤ X`.
  have hlt : 2 * AO_OffDiag.TailBlock.Q0 < X := by
    have : 2 * AO_OffDiag.TailBlock.Q0 < X0 := by
      -- `60000 < 1_000_000`
      decide
    exact lt_of_lt_of_le this hX
  exact sepQ0_one_of_two_mul_Q0_lt (X := X) hlt

private lemma two_le_of_X0_le {X : ℕ} (hX : X0 ≤ X) : 2 ≤ X := by
  exact le_trans (by decide : (2 : ℕ) ≤ X0) hX

private lemma norm_add3_sq_le_three_mul_sum_sq (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  -- `‖a+b+c‖ ≤ ‖a‖+‖b‖+‖c‖` then expand and use `2ab ≤ a^2+b^2`.
  have htri : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    -- `‖(a+b)+c‖ ≤ ‖a+b‖ + ‖c‖ ≤ (‖a‖+‖b‖)+‖c‖`.
    have h1 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := by
      simpa [add_assoc] using (norm_add_le (a + b) c)
    have h2 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
    linarith
  have hnonneg : 0 ≤ ‖a + b + c‖ := norm_nonneg _
  have hnonnegR : 0 ≤ (‖a‖ + ‖b‖ + ‖c‖ : ℝ) := by positivity
  have hsq : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := by
    have := mul_le_mul htri htri hnonneg hnonnegR
    simpa [pow_two] using this
  -- Expand `(x+y+z)^2` and use `2xy ≤ x^2+y^2`.
  set x : ℝ := ‖a‖
  set y : ℝ := ‖b‖
  set z : ℝ := ‖c‖
  have hx : 0 ≤ x := by simp [x]
  have hy : 0 ≤ y := by simp [y]
  have hz : 0 ≤ z := by simp [z]
  have hxy : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (two_mul_le_add_sq x y)
  have hxz : 2 * x * z ≤ x ^ 2 + z ^ 2 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (two_mul_le_add_sq x z)
  have hyz : 2 * y * z ≤ y ^ 2 + z ^ 2 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (two_mul_le_add_sq y z)
  have hsum :
      (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    -- expand and bound cross terms
    have : (x + y + z) ^ 2 =
        x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y + 2 * x * z + 2 * y * z := by
      ring
    rw [this]
    nlinarith [hxy, hxz, hyz]
  -- finish by substitution
  have hx' : x = ‖a‖ := by rfl
  have hy' : y = ‖b‖ := by rfl
  have hz' : z = ‖c‖ := by rfl
  -- `x^2 = ‖a‖^2`, etc.
  calc
    ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := hsq
    _ = (x + y + z) ^ 2 := by simp [x, y, z]
    _ ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := hsum
    _ = 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by simp [x, y, z]

private lemma two_mul_mul_le_add_mul_sq_div (a b δ : ℝ) (hδ : 0 < δ) :
    2 * a * b ≤ δ * a ^ 2 + (1 / δ) * b ^ 2 := by
  -- `0 ≤ (δ*a - b)^2` rearranged, then divide by `δ`.
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hsq : 0 ≤ (δ * a - b) ^ 2 := sq_nonneg _
  have hmul : 2 * δ * a * b ≤ δ ^ 2 * a ^ 2 + b ^ 2 := by
    -- Expand the square: `(δa - b)^2 = δ^2 a^2 - 2 δ a b + b^2 ≥ 0`.
    nlinarith [hsq]
  have hdiv := div_le_div_of_nonneg_right hmul (le_of_lt hδ)
  have hL : (2 * δ * a * b) / δ = 2 * a * b := by
    field_simp [hδne]
  have hR : (δ ^ 2 * a ^ 2 + b ^ 2) / δ = δ * a ^ 2 + (1 / δ) * b ^ 2 := by
    field_simp [hδne]
  -- Simplify: `(2*δ*a*b)/δ = 2*a*b`, `(δ^2*a^2 + b^2)/δ = δ*a^2 + (1/δ)*b^2`.
  simpa [hL, hR] using hdiv

private lemma norm_add_sq_le_scaled (u v : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ‖u + v‖ ^ 2 ≤ (1 + δ) * ‖u‖ ^ 2 + (1 + 1 / δ) * ‖v‖ ^ 2 := by
  -- `‖u+v‖ ≤ ‖u‖+‖v‖`, then expand and apply `2ab ≤ δ a^2 + (1/δ) b^2`.
  have htri : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    have hnonneg : 0 ≤ ‖u + v‖ := norm_nonneg _
    have hnonnegR : 0 ≤ (‖u‖ + ‖v‖ : ℝ) := by positivity
    have := mul_le_mul htri htri hnonneg hnonnegR
    simpa [pow_two] using this
  have hab :
      (‖u‖ + ‖v‖ : ℝ) ^ 2
        ≤ (1 + δ) * ‖u‖ ^ 2 + (1 + 1 / δ) * ‖v‖ ^ 2 := by
    have h2ab : 2 * ‖u‖ * ‖v‖ ≤ δ * ‖u‖ ^ 2 + (1 / δ) * ‖v‖ ^ 2 :=
      two_mul_mul_le_add_mul_sq_div (a := ‖u‖) (b := ‖v‖) δ hδ
    -- expand `(a+b)^2`
    have : (‖u‖ + ‖v‖ : ℝ) ^ 2 = ‖u‖ ^ 2 + 2 * ‖u‖ * ‖v‖ + ‖v‖ ^ 2 := by ring
    rw [this]
    nlinarith [h2ab]
  exact le_trans hsq hab

private lemma majorArcWeightFourier_sq_le_split
    {X : ℕ} (hX : X0 ≤ X) {t : ℤ} (ht0 : t ≠ 0) (htBand : t.natAbs ≤ X + H) :
    ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2
      ≤
    3 * (‖AX X (1 : ℝ) t‖ ^ 2 + ‖LX X t‖ ^ 2 + ‖RX X (1 : ℝ) t‖ ^ 2) := by
  have hsep : SepQ0 X (1 : ℝ) := sepQ0_one_of_X0_le (X := X) hX
  have h2 : 2 ≤ X := two_le_of_X0_le (X := X) hX
  have hsplit :
      Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t =
          AX X (1 : ℝ) t + LX X t + RX X (1 : ℝ) t :=
    majorArcWeightFourier_eq_AX_add_LX_add_RX (X := X) (Δ := (1 : ℝ)) (hsep := hsep)
      (hX := h2) (hΔ := rfl) (t := t) ht0
  -- rewrite then apply the 3-term inequality
  simpa [hsplit, add_assoc] using
    norm_add3_sq_le_three_mul_sum_sq (AX X (1 : ℝ) t) (LX X t) (RX X (1 : ℝ) t)

/-!
## Kernel-mass bounds (nonzero frequencies)

We bound `kernelMassNZEven`/`kernelMassNZOdd` by splitting the summand via the Step-5 split:
`Ŵ = AX + LX + RX`, and using the inequality `‖a+b+c‖² ≤ 3(‖a‖²+‖b‖²+‖c‖²)`.
-/

/-- Helper: sum of squared norms over a finset. -/
noncomputable def sumSqOn (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  ∑ t ∈ S, ‖f t‖ ^ 2

private lemma sumSqOn_le_of_pointwise
    {S : Finset ℤ} {f g : ℤ → ℂ} {C : ℝ}
    (hfg : ∀ t ∈ S, ‖f t‖ ^ 2 ≤ C * ‖g t‖ ^ 2) :
    sumSqOn S f ≤ C * sumSqOn S g := by
  classical
  unfold sumSqOn
  have :
      (∑ t ∈ S, ‖f t‖ ^ 2) ≤ ∑ t ∈ S, (C * ‖g t‖ ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    exact hfg t ht
  -- factor out `C`
  calc
    (∑ t ∈ S, ‖f t‖ ^ 2) ≤ ∑ t ∈ S, (C * ‖g t‖ ^ 2) := this
    _ = C * ∑ t ∈ S, ‖g t‖ ^ 2 := by
      simp [Finset.mul_sum]

private lemma sumSqOn_add3_le
    {S : Finset ℤ} (f₁ f₂ f₃ : ℤ → ℂ) :
    sumSqOn S (fun t => f₁ t + f₂ t + f₃ t)
      ≤
    3 * (sumSqOn S f₁ + sumSqOn S f₂ + sumSqOn S f₃) := by
  classical
  unfold sumSqOn
  -- pointwise inequality then sum
  have hpt :
      ∀ t ∈ S,
        ‖f₁ t + f₂ t + f₃ t‖ ^ 2
          ≤
        3 * (‖f₁ t‖ ^ 2 + ‖f₂ t‖ ^ 2 + ‖f₃ t‖ ^ 2) := by
    intro t ht
    simpa [add_assoc] using norm_add3_sq_le_three_mul_sum_sq (f₁ t) (f₂ t) (f₃ t)
  have hsum :
      (∑ t ∈ S, ‖f₁ t + f₂ t + f₃ t‖ ^ 2)
        ≤
      ∑ t ∈ S, 3 * (‖f₁ t‖ ^ 2 + ‖f₂ t‖ ^ 2 + ‖f₃ t‖ ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    exact hpt t ht
  -- distribute and factor constants
  calc
    (∑ t ∈ S, ‖f₁ t + f₂ t + f₃ t‖ ^ 2)
        ≤
      ∑ t ∈ S, 3 * (‖f₁ t‖ ^ 2 + ‖f₂ t‖ ^ 2 + ‖f₃ t‖ ^ 2) := hsum
    _ =
      3 * (∑ t ∈ S, (‖f₁ t‖ ^ 2 + ‖f₂ t‖ ^ 2 + ‖f₃ t‖ ^ 2)) := by
      simp [Finset.mul_sum]
    _ =
      3 * ((∑ t ∈ S, ‖f₁ t‖ ^ 2) + (∑ t ∈ S, ‖f₂ t‖ ^ 2) + (∑ t ∈ S, ‖f₃ t‖ ^ 2)) := by
      simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    _ = 3 * (sumSqOn S f₁ + sumSqOn S f₂ + sumSqOn S f₃) := by
      simp [sumSqOn, add_assoc, add_left_comm, add_comm]

/-- Split `kernelMassNZEven` using the `AX+LX+RX` decomposition (no numeric estimates yet). -/
theorem kernelMassNZEven_le_split_sums {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZEven X (1 : ℝ) (X + H)
      ≤
    3 * (sumSqOn (((tSupport (X + H)).erase 0).filter Even) (AX X (1 : ℝ))
        +
      sumSqOn (((tSupport (X + H)).erase 0).filter Even) (LX X)
        +
      sumSqOn (((tSupport (X + H)).erase 0).filter Even) (RX X (1 : ℝ))) := by
  classical
  -- use the pointwise split lemma on the `t≠0` band
  have hsep : SepQ0 X (1 : ℝ) := sepQ0_one_of_X0_le (X := X) hX
  have h2 : 2 ≤ X := two_le_of_X0_le (X := X) hX
  -- rewrite kernelMassNZEven as a sum over the same finset
  unfold kernelMassNZEven
  -- The filter set:
  set S : Finset ℤ := ((tSupport (X + H)).erase 0).filter Even
  have hsplit_on :
      ∀ t ∈ S,
        Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t =
          AX X (1 : ℝ) t + LX X t + RX X (1 : ℝ) t := by
    intro t htS
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp htS).1).1
    have htBand : t.natAbs ≤ X + H := by
      -- `t ∈ Icc (-(X+H)) (X+H)` by construction.
      have htMem : t ∈ tSupport (X + H) := by
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp htS).1).2
      -- Coarse: `|t| ≤ X+H`.
      rcases Finset.mem_Icc.mp htMem with ⟨hl, hu⟩
      have habs : |t| ≤ (X + H : ℤ) := by
        exact abs_le.2 ⟨hl, hu⟩
      have habs_eq : (t.natAbs : ℤ) = |t| := (Int.abs_eq_natAbs t).symm
      have hle : (t.natAbs : ℤ) ≤ (X + H : ℤ) :=
        habs_eq.le.trans habs
      exact_mod_cast hle
    exact majorArcWeightFourier_eq_AX_add_LX_add_RX (X := X) (Δ := (1 : ℝ)) (hsep := hsep)
      (hX := h2) (hΔ := rfl) (t := t) ht0
  -- apply the 3-term sum-square bound
  have :
      (∑ t ∈ S, ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2)
        ≤
      3 * ((∑ t ∈ S, ‖AX X (1 : ℝ) t‖ ^ 2) + (∑ t ∈ S, ‖LX X t‖ ^ 2) + (∑ t ∈ S, ‖RX X (1 : ℝ) t‖ ^ 2)) := by
    -- rewrite `majorArcWeightFourier` into `AX+LX+RX` inside the norm
    have hrewrite :
        (∑ t ∈ S, ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2)
          =
        (∑ t ∈ S, ‖AX X (1 : ℝ) t + LX X t + RX X (1 : ℝ) t‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro t htS
      have := hsplit_on t htS
      simp [this, add_assoc]
    -- now apply the generic lemma
    rw [hrewrite]
    -- `sumSqOn_add3_le` expects `sumSqOn`; convert.
    have :=
      sumSqOn_add3_le (S := S) (fun t => AX X (1 : ℝ) t) (fun t => LX X t) (fun t => RX X (1 : ℝ) t)
    -- unfold `sumSqOn` in that lemma to match the goal
    simpa [sumSqOn, add_assoc, add_left_comm, add_comm] using this
  -- finish: rewrite into `sumSqOn`
  have hsumSq :
      3 * ((∑ t ∈ S, ‖AX X (1 : ℝ) t‖ ^ 2) + (∑ t ∈ S, ‖LX X t‖ ^ 2) + (∑ t ∈ S, ‖RX X (1 : ℝ) t‖ ^ 2))
        =
      3 * (sumSqOn S (AX X (1 : ℝ)) + sumSqOn S (LX X) + sumSqOn S (RX X (1 : ℝ))) := by
    simp [sumSqOn, add_assoc, add_left_comm, add_comm]
  -- `kernelMassNZEven` is exactly the LHS sum
  simpa [kernelMassNZEven, S, sumSqOn, hsumSq, add_assoc, add_left_comm, add_comm] using this

/-- Split `kernelMassNZOdd` using the `AX+LX+RX` decomposition (no numeric estimates yet). -/
theorem kernelMassNZOdd_le_split_sums {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZOdd X (1 : ℝ) (X + H)
      ≤
    3 * (sumSqOn (((tSupport (X + H)).erase 0).filter (fun t => ¬ Even t)) (AX X (1 : ℝ))
        +
      sumSqOn (((tSupport (X + H)).erase 0).filter (fun t => ¬ Even t)) (LX X)
        +
      sumSqOn (((tSupport (X + H)).erase 0).filter (fun t => ¬ Even t)) (RX X (1 : ℝ))) := by
  classical
  have hsep : SepQ0 X (1 : ℝ) := sepQ0_one_of_X0_le (X := X) hX
  have h2 : 2 ≤ X := two_le_of_X0_le (X := X) hX
  set S : Finset ℤ := ((tSupport (X + H)).erase 0).filter (fun t => ¬ Even t)
  have hsplit_on :
      ∀ t ∈ S,
        Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t =
          AX X (1 : ℝ) t + LX X t + RX X (1 : ℝ) t := by
    intro t htS
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp htS).1).1
    exact majorArcWeightFourier_eq_AX_add_LX_add_RX (X := X) (Δ := (1 : ℝ)) (hsep := hsep)
      (hX := h2) (hΔ := rfl) (t := t) ht0
  have :
      (∑ t ∈ S, ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2)
        ≤
      3 * ((∑ t ∈ S, ‖AX X (1 : ℝ) t‖ ^ 2) + (∑ t ∈ S, ‖LX X t‖ ^ 2) + (∑ t ∈ S, ‖RX X (1 : ℝ) t‖ ^ 2)) := by
    have hrewrite :
        (∑ t ∈ S, ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2)
          =
        (∑ t ∈ S, ‖AX X (1 : ℝ) t + LX X t + RX X (1 : ℝ) t‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro t htS
      have := hsplit_on t htS
      simp [this, add_assoc]
    rw [hrewrite]
    have :=
      sumSqOn_add3_le (S := S) (fun t => AX X (1 : ℝ) t) (fun t => LX X t) (fun t => RX X (1 : ℝ) t)
    simpa [sumSqOn, add_assoc, add_left_comm, add_comm] using this
  have hsumSq :
      3 * ((∑ t ∈ S, ‖AX X (1 : ℝ) t‖ ^ 2) + (∑ t ∈ S, ‖LX X t‖ ^ 2) + (∑ t ∈ S, ‖RX X (1 : ℝ) t‖ ^ 2))
        =
      3 * (sumSqOn S (AX X (1 : ℝ)) + sumSqOn S (LX X) + sumSqOn S (RX X (1 : ℝ))) := by
    simp [sumSqOn, add_assoc, add_left_comm, add_comm]
  simpa [kernelMassNZOdd, S, sumSqOn, hsumSq, add_assoc, add_left_comm, add_comm] using this

/-!
## Easy remainder bound (RX)
-/

/-- Uniform remainder estimate: `RX` contributes at most `card(S) * ((3/2)/X)^2` on any sub-band. -/
theorem sumSqOn_RX_le (X : ℕ) (hX : X0 ≤ X) (S : Finset ℤ) (hS :
    S ⊆ (tSupport (X + H)).erase 0) :
    sumSqOn S (RX X (1 : ℝ)) ≤ (S.card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2 := by
  classical
  unfold sumSqOn
  -- pointwise bound by `(3/2)/X`
  have hpt :
      ∀ t ∈ S, ‖RX X (1 : ℝ) t‖ ^ 2 ≤ ((3 / 2 : ℝ) / (X : ℝ)) ^ 2 := by
    intro t htS
    have htBand : t.natAbs ≤ X + H := by
      have htMem : t ∈ tSupport (X + H) := by
        have : t ∈ (tSupport (X + H)).erase 0 := hS htS
        exact (Finset.mem_erase.mp this).2
      rcases Finset.mem_Icc.mp htMem with ⟨hl, hu⟩
      have habs : |t| ≤ (X + H : ℤ) := by
        exact abs_le.2 ⟨hl, hu⟩
      have habs_eq : (t.natAbs : ℤ) = |t| := (Int.abs_eq_natAbs t).symm
      have hle : (t.natAbs : ℤ) ≤ (X + H : ℤ) :=
        habs_eq.le.trans habs
      exact_mod_cast hle
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp (hS htS)).1
    have hRX : ‖RX X (1 : ℝ) t‖ ≤ (3 / 2 : ℝ) / (X : ℝ) :=
      norm_RX_le_const_div_X (X := X) (Δ := (1 : ℝ)) hX rfl ht0 htBand
    have hnonneg : 0 ≤ (3 / 2 : ℝ) / (X : ℝ) := by
      have : 0 < (X : ℝ) := by
        have : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
        exact_mod_cast this
      positivity
    -- square both sides using nonnegativity of norms
    have hmul :
        ‖RX X (1 : ℝ) t‖ * ‖RX X (1 : ℝ) t‖
          ≤
        ((3 / 2 : ℝ) / (X : ℝ)) * ((3 / 2 : ℝ) / (X : ℝ)) :=
      mul_le_mul hRX hRX (norm_nonneg _) hnonneg
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
  have :
      (∑ t ∈ S, ‖RX X (1 : ℝ) t‖ ^ 2)
        ≤
      ∑ t ∈ S, ((3 / 2 : ℝ) / (X : ℝ)) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro t htS
    exact hpt t htS
  -- sum of a constant
  calc
    (∑ t ∈ S, ‖RX X (1 : ℝ) t‖ ^ 2)
        ≤
      ∑ t ∈ S, ((3 / 2 : ℝ) / (X : ℝ)) ^ 2 := this
    _ = (S.card : ℝ) * (((3 / 2 : ℝ) / (X : ℝ)) ^ 2) := by
      simp [mul_comm, mul_left_comm, mul_assoc]

/-!
## Convenience corollaries: eliminate `RX` via the uniform bound
-/

noncomputable def evenBand (X : ℕ) : Finset ℤ :=
  (((tSupport (X + H)).erase 0).filter Even)

noncomputable def oddBand (X : ℕ) : Finset ℤ :=
  (((tSupport (X + H)).erase 0).filter fun t => ¬ Even t)

theorem kernelMassNZEven_le_AX_LX_plus_RX_bound {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZEven X (1 : ℝ) (X + H)
      ≤
    (1 + δ_weightSplit) * (sumSqOn (evenBand X) (fun t => AX X (1 : ℝ) t + LX X t))
      +
    (1 + 1 / δ_weightSplit) * (((evenBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2) := by
  classical
  have hsep : SepQ0 X (1 : ℝ) := sepQ0_one_of_X0_le (X := X) hX
  have h2 : 2 ≤ X := two_le_of_X0_le (X := X) hX
  set S : Finset ℤ := evenBand X
  have hδ : 0 < δ_weightSplit := δ_weightSplit_pos
  have hpt :
      ∀ t ∈ S,
        ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2
          ≤
        (1 + δ_weightSplit) * ‖AX X (1 : ℝ) t + LX X t‖ ^ 2
          +
        (1 + 1 / δ_weightSplit) * ‖RX X (1 : ℝ) t‖ ^ 2 := by
    intro t htS
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp htS).1).1
    have hsplit :
        Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t =
          AX X (1 : ℝ) t + LX X t + RX X (1 : ℝ) t :=
      majorArcWeightFourier_eq_AX_add_LX_add_RX (X := X) (Δ := (1 : ℝ)) (hsep := hsep)
        (hX := h2) (hΔ := rfl) (t := t) ht0
    have hmain :
        ‖(AX X (1 : ℝ) t + LX X t) + RX X (1 : ℝ) t‖ ^ 2
          ≤ (1 + δ_weightSplit) * ‖AX X (1 : ℝ) t + LX X t‖ ^ 2
            + (1 + 1 / δ_weightSplit) * ‖RX X (1 : ℝ) t‖ ^ 2 := by
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        using
          norm_add_sq_le_scaled (u := AX X (1 : ℝ) t + LX X t) (v := RX X (1 : ℝ) t)
            (δ := δ_weightSplit) hδ
    -- rewrite `Ŵ = AX+LX+RX`
    simpa [hsplit, add_assoc] using hmain
  have hsum :
      kernelMassNZEven X (1 : ℝ) (X + H)
        ≤
      (1 + δ_weightSplit) * sumSqOn S (fun t => AX X (1 : ℝ) t + LX X t)
        +
      (1 + 1 / δ_weightSplit) * sumSqOn S (RX X (1 : ℝ)) := by
    -- sum the pointwise inequality
    unfold kernelMassNZEven
    have :
        (∑ t ∈ S, ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2)
          ≤
        (∑ t ∈ S,
          ((1 + δ_weightSplit) * ‖AX X (1 : ℝ) t + LX X t‖ ^ 2
            + (1 + 1 / δ_weightSplit) * ‖RX X (1 : ℝ) t‖ ^ 2)) := by
      refine Finset.sum_le_sum ?_
      intro t ht
      exact hpt t ht
    -- split the RHS sum
    calc
      (∑ t ∈ S, ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2)
          ≤
        (∑ t ∈ S, (1 + δ_weightSplit) * ‖AX X (1 : ℝ) t + LX X t‖ ^ 2)
          +
        (∑ t ∈ S, (1 + 1 / δ_weightSplit) * ‖RX X (1 : ℝ) t‖ ^ 2) := by
            simpa [Finset.sum_add_distrib] using this
      _ =
        (1 + δ_weightSplit) * (∑ t ∈ S, ‖AX X (1 : ℝ) t + LX X t‖ ^ 2)
          +
        (1 + 1 / δ_weightSplit) * (∑ t ∈ S, ‖RX X (1 : ℝ) t‖ ^ 2) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 + δ_weightSplit) * sumSqOn S (fun t => AX X (1 : ℝ) t + LX X t)
          + (1 + 1 / δ_weightSplit) * sumSqOn S (RX X (1 : ℝ)) := by
            simp [sumSqOn]
  have hRX :
      sumSqOn S (RX X (1 : ℝ)) ≤ (S.card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2 := by
    refine sumSqOn_RX_le (X := X) hX (S := S) ?_
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  have hRX' :
      (1 + 1 / δ_weightSplit) * sumSqOn S (RX X (1 : ℝ))
        ≤
      (1 + 1 / δ_weightSplit) * ((S.card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2) := by
    have hδ' : 0 ≤ (1 + 1 / δ_weightSplit) := by
      have : 0 ≤ (1 / δ_weightSplit) := le_of_lt (one_div_pos.mpr δ_weightSplit_pos)
      nlinarith
    exact mul_le_mul_of_nonneg_left hRX hδ'
  -- combine
  have :
      (1 + δ_weightSplit) * sumSqOn S (fun t => AX X (1 : ℝ) t + LX X t)
        +
      (1 + 1 / δ_weightSplit) * sumSqOn S (RX X (1 : ℝ))
        ≤
      (1 + δ_weightSplit) * sumSqOn S (fun t => AX X (1 : ℝ) t + LX X t)
        +
      (1 + 1 / δ_weightSplit) * ((S.card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2) := by
    linarith [hRX']
  exact le_trans hsum this

theorem kernelMassNZOdd_le_AX_LX_plus_RX_bound {X : ℕ} (hX : X0 ≤ X) :
    kernelMassNZOdd X (1 : ℝ) (X + H)
      ≤
    (1 + δ_weightSplit) * (sumSqOn (oddBand X) (fun t => AX X (1 : ℝ) t + LX X t))
      +
    (1 + 1 / δ_weightSplit) * (((oddBand X).card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2) := by
  classical
  have hsep : SepQ0 X (1 : ℝ) := sepQ0_one_of_X0_le (X := X) hX
  have h2 : 2 ≤ X := two_le_of_X0_le (X := X) hX
  set S : Finset ℤ := oddBand X
  have hδ : 0 < δ_weightSplit := δ_weightSplit_pos
  have hpt :
      ∀ t ∈ S,
        ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2
          ≤
        (1 + δ_weightSplit) * ‖AX X (1 : ℝ) t + LX X t‖ ^ 2
          +
        (1 + 1 / δ_weightSplit) * ‖RX X (1 : ℝ) t‖ ^ 2 := by
    intro t htS
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp htS).1).1
    have hsplit :
        Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t =
          AX X (1 : ℝ) t + LX X t + RX X (1 : ℝ) t :=
      majorArcWeightFourier_eq_AX_add_LX_add_RX (X := X) (Δ := (1 : ℝ)) (hsep := hsep)
        (hX := h2) (hΔ := rfl) (t := t) ht0
    have hmain :
        ‖(AX X (1 : ℝ) t + LX X t) + RX X (1 : ℝ) t‖ ^ 2
          ≤ (1 + δ_weightSplit) * ‖AX X (1 : ℝ) t + LX X t‖ ^ 2
            + (1 + 1 / δ_weightSplit) * ‖RX X (1 : ℝ) t‖ ^ 2 := by
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        using
          norm_add_sq_le_scaled (u := AX X (1 : ℝ) t + LX X t) (v := RX X (1 : ℝ) t)
            (δ := δ_weightSplit) hδ
    simpa [hsplit, add_assoc] using hmain
  have hsum :
      kernelMassNZOdd X (1 : ℝ) (X + H)
        ≤
      (1 + δ_weightSplit) * sumSqOn S (fun t => AX X (1 : ℝ) t + LX X t)
        +
      (1 + 1 / δ_weightSplit) * sumSqOn S (RX X (1 : ℝ)) := by
    unfold kernelMassNZOdd
    have :
        (∑ t ∈ S, ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2)
          ≤
        (∑ t ∈ S,
          ((1 + δ_weightSplit) * ‖AX X (1 : ℝ) t + LX X t‖ ^ 2
            + (1 + 1 / δ_weightSplit) * ‖RX X (1 : ℝ) t‖ ^ 2)) := by
      refine Finset.sum_le_sum ?_
      intro t ht
      exact hpt t ht
    calc
      (∑ t ∈ S, ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X (1 : ℝ) t‖ ^ 2)
          ≤
        (∑ t ∈ S, (1 + δ_weightSplit) * ‖AX X (1 : ℝ) t + LX X t‖ ^ 2)
          +
        (∑ t ∈ S, (1 + 1 / δ_weightSplit) * ‖RX X (1 : ℝ) t‖ ^ 2) := by
            simpa [Finset.sum_add_distrib] using this
      _ =
        (1 + δ_weightSplit) * (∑ t ∈ S, ‖AX X (1 : ℝ) t + LX X t‖ ^ 2)
          +
        (1 + 1 / δ_weightSplit) * (∑ t ∈ S, ‖RX X (1 : ℝ) t‖ ^ 2) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 + δ_weightSplit) * sumSqOn S (fun t => AX X (1 : ℝ) t + LX X t)
          + (1 + 1 / δ_weightSplit) * sumSqOn S (RX X (1 : ℝ)) := by
            simp [sumSqOn]
  have hRX :
      sumSqOn S (RX X (1 : ℝ)) ≤ (S.card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2 := by
    refine sumSqOn_RX_le (X := X) hX (S := S) ?_
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  have hRX' :
      (1 + 1 / δ_weightSplit) * sumSqOn S (RX X (1 : ℝ))
        ≤
      (1 + 1 / δ_weightSplit) * ((S.card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2) := by
    have hδ' : 0 ≤ (1 + 1 / δ_weightSplit) := by
      have : 0 ≤ (1 / δ_weightSplit) := le_of_lt (one_div_pos.mpr δ_weightSplit_pos)
      nlinarith
    exact mul_le_mul_of_nonneg_left hRX hδ'
  have :
      (1 + δ_weightSplit) * sumSqOn S (fun t => AX X (1 : ℝ) t + LX X t)
        +
      (1 + 1 / δ_weightSplit) * sumSqOn S (RX X (1 : ℝ))
        ≤
      (1 + δ_weightSplit) * sumSqOn S (fun t => AX X (1 : ℝ) t + LX X t)
        +
      (1 + 1 / δ_weightSplit) * ((S.card : ℝ) * ((3 / 2 : ℝ) / (X : ℝ)) ^ 2) := by
    linarith [hRX']
  exact le_trans hsum this

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
