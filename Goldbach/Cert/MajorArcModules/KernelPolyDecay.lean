import Goldbach.Cert.MajorArcModules.BetaLocalization
import Goldbach.Cert.MajorArcStep13RealToCircle
import Goldbach.Cert.MajorArcStep22BetaKernelLocalization
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Deterministic decay bounds for the Fourier polynomial `kernelPolyC`.

This file provides a purely algebraic “second difference” identity for the finite Fourier
polynomial `kernelPolyC`, together with the resulting bound

`‖kernelPolyC (β)‖ ≤ (∑ ‖Δ² coeff‖) / ‖e β - 1‖²`.

It is designed as the missing (deterministic) input for bounding the large-β tail in the
turnkey `Q0` major-arc route.
-/

namespace Goldbach.Cert.MajorArcModules.KernelPolyDecay

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcStep13RealToCircle
open Goldbach.Cert.MajorArcStep22BetaKernelLocalization

noncomputable section

set_option maxRecDepth 2048

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

abbrev l : ℤ := (-(H : ℤ))
abbrev u : ℤ := (H : ℤ)
private abbrev SBG : Finset ℤ := Goldbach.BG_Identity.S_BG

private lemma SBG_eq_Icc : SBG = Finset.Icc l u := by
  rfl

private abbrev Kfull (k : ℤ) : ℝ := Goldbach.BG_Identity.K_full k

noncomputable def coeff (k : ℤ) : ℂ :=
  if k ∈ Finset.Icc l u then (Kfull k : ℂ) else 0

private lemma coeff_eq_of_mem {k : ℤ} (hk : k ∈ Finset.Icc l u) : coeff k = (Kfull k : ℂ) := by
  simp [coeff, hk]

private lemma coeff_eq_zero_of_notMem {k : ℤ} (hk : k ∉ Finset.Icc l u) : coeff k = 0 := by
  simp [coeff, hk]

private lemma kernelPolyC_coe_eq_sum_coeff_e (β : ℝ) :
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
      =
    ∑ k ∈ Finset.Icc l u, coeff k * e ((k : ℝ) * β) := by
  classical
  -- Expand `kernelPolyC` and rewrite `fourier k (β:UC)` as `e (k*β)`.
  rw [kernelPolyC_eq (x := (β : UC))]
  -- Replace the summation set `Goldbach.BG_Identity.S_BG` by `Icc l u`.
  have hSBG : (Goldbach.BG_Identity.S_BG : Finset ℤ) = Finset.Icc l u := by
    rfl
  rw [hSBG]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hfour : (fourier (T := (1 : ℝ)) k (β : UC) : ℂ) = e ((k : ℝ) * β) :=
    fourier_coe_eq_e (k := k) (x := β)
  have hcoeff : coeff k = (Kfull k : ℂ) := coeff_eq_of_mem (k := k) hk
  simp [hcoeff, hfour, mul_assoc]

/-!
### Backward differences
-/

noncomputable def Δ (a : ℤ → ℂ) (k : ℤ) : ℂ :=
  a (k - 1) - a k

noncomputable def Δ2 (a : ℤ → ℂ) (k : ℤ) : ℂ :=
  Δ a (k - 1) - Δ a k

private lemma Δ2_eq (a : ℤ → ℂ) (k : ℤ) :
    Δ2 a k = a (k - 2) - (2 : ℂ) * a (k - 1) + a k := by
  simp [Δ2, Δ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
    mul_comm, two_mul]

private lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp [e, mul_add, Complex.exp_add]

private lemma e_mul_shift (β : ℝ) (k : ℤ) :
    e β * e ((k : ℝ) * β) = e (((k + 1 : ℤ) : ℝ) * β) := by
  have hk : ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by
    norm_cast
  have hlin : (k : ℝ) * β + β = ((k : ℝ) + 1) * β := by
    ring
  calc
    e β * e ((k : ℝ) * β) = e ((k : ℝ) * β) * e β := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = e (((k : ℝ) * β) + β) := by
      simpa [e_add] using (e_add ((k : ℝ) * β) β).symm
    _ = e (((k : ℝ) + 1) * β) := by
      simpa [hlin]
    _ = e (((k + 1 : ℤ) : ℝ) * β) := by
      simpa [hk]

private lemma sum_Icc_shift_add_one {M : Type*} [AddCommMonoid M]
    (a b : ℤ) (f : ℤ → M) :
    (Finset.Icc a b).sum (fun k => f (k + 1)) = (Finset.Icc (a + 1) (b + 1)).sum f := by
  classical
  let emb : ℤ ↪ ℤ := addRightEmbedding (1 : ℤ)
  have hmap : (Finset.Icc a b).map emb = Finset.Icc (a + 1) (b + 1) := by
    simpa [emb] using (Finset.map_add_right_Icc (a := a) (b := b) (c := (1 : ℤ)))
  -- `sum_map` gives the reindexing for the mapped finset; rearrange to match the desired direction.
  have hsum :
      (Finset.Icc (a + 1) (b + 1)).sum f = (Finset.Icc a b).sum (fun k => f (k + 1)) := by
    calc
      (Finset.Icc (a + 1) (b + 1)).sum f = ((Finset.Icc a b).map emb).sum f := by
        simpa [hmap]
      _ = (Finset.Icc a b).sum (fun k => f (emb k)) := by
        simpa using (Finset.sum_map (s := Finset.Icc a b) (e := emb) (f := f))
      _ = (Finset.Icc a b).sum (fun k => f (k + 1)) := by
        rfl
  simpa using hsum.symm

/-!
### The second-difference identity for `kernelPolyC`
-/

private lemma e_sub_one_mul_sum_eq_sum_Δ
    (β : ℝ) (l u : ℤ) (a : ℤ → ℂ) (hlu1 : l ≤ u + 1)
    (ha_left : a (l - 1) = 0) (ha_right : a (u + 1) = 0) :
    (e β - 1) * (∑ k ∈ Finset.Icc l u, a k * e ((k : ℝ) * β))
      =
    ∑ k ∈ Finset.Icc l (u + 1), (Δ a k) * e ((k : ℝ) * β) := by
  classical
  -- Expand `(eβ-1)S` as `eβ*S - S`.
  set S : ℂ := ∑ k ∈ Finset.Icc l u, a k * e ((k : ℝ) * β)
  have hS : S = ∑ k ∈ Finset.Icc l u, a k * e ((k : ℝ) * β) := rfl

  -- Rewrite `eβ * S` by shifting the index `k ↦ k+1`.
  have hmul :
      e β * S = ∑ k ∈ Finset.Icc (l + 1) (u + 1), a (k - 1) * e ((k : ℝ) * β) := by
    -- Pull `eβ` inside, then use `e_mul_shift` and reindex.
    have hin :
        e β * S = ∑ k ∈ Finset.Icc l u, a k * e (((k + 1 : ℤ) : ℝ) * β) := by
      -- Push the scalar inside the sum, then rewrite `e β * e(kβ) = e((k+1)β)`.
      calc
        e β * S
            =
          ∑ k ∈ Finset.Icc l u, e β * (a k * e ((k : ℝ) * β)) := by
            simp [S, Finset.mul_sum]
        _ =
          ∑ k ∈ Finset.Icc l u, a k * e (((k + 1 : ℤ) : ℝ) * β) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            calc
              e β * (a k * e ((k : ℝ) * β))
                  = a k * (e β * e ((k : ℝ) * β)) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
              _ = a k * e (((k + 1 : ℤ) : ℝ) * β) := by
                      simpa [mul_assoc] using
                        congrArg (fun z : ℂ => a k * z) (e_mul_shift (β := β) (k := k))
    -- Reindex the shifted sum.
    have hreindex :
        (∑ k ∈ Finset.Icc l u, a k * e (((k + 1 : ℤ) : ℝ) * β))
          =
        ∑ k ∈ Finset.Icc (l + 1) (u + 1), a (k - 1) * e ((k : ℝ) * β) := by
      -- Use the general shift lemma with `f k := a (k-1) * e(kβ)`.
      simpa using
        (sum_Icc_shift_add_one (a := l) (b := u) (f := fun k : ℤ => a (k - 1) * e ((k : ℝ) * β)))
    exact hin.trans hreindex

  -- Extend the two sums to the common range `Icc l (u+1)` using `SuccPred` interval decomposition.
  have hIcc_right : insert (u + 1) (Finset.Icc l u) = Finset.Icc l (u + 1) :=
    Finset.insert_Icc_right_eq_Icc_add_one (a := l) (b := u) hlu1
  have hIcc_left : insert l (Finset.Icc (l + 1) (u + 1)) = Finset.Icc l (u + 1) :=
    Finset.insert_Icc_add_one_left_eq_Icc (a := l) (b := (u + 1)) hlu1

  have hl_not_mem : l ∉ Finset.Icc (l + 1) (u + 1) := by
    simp [Finset.mem_Icc]
  have hu1_not_mem : (u + 1) ∉ Finset.Icc l u := by
    simp [Finset.mem_Icc]

  have hmul' :
      e β * S = ∑ k ∈ Finset.Icc l (u + 1), a (k - 1) * e ((k : ℝ) * β) := by
    -- Insert `l` into the shifted-sum range; the inserted term is `a(l-1)=0`.
    rw [← hIcc_left]
    have ha_left' : a (l + -1) = 0 := by
      simpa [sub_eq_add_neg] using ha_left
    simp [hmul, hl_not_mem, ha_left', sub_eq_add_neg]

  have hS' :
      S = ∑ k ∈ Finset.Icc l (u + 1), a k * e ((k : ℝ) * β) := by
    -- Insert `u+1` into the original range; the inserted term is `a(u+1)=0`.
    rw [← hIcc_right]
    simp [S, hu1_not_mem, ha_right]

  calc
    (e β - 1) * (∑ k ∈ Finset.Icc l u, a k * e ((k : ℝ) * β))
        = (e β - 1) * S := by simp [hS]
    _ = e β * S - S := by ring
    _ =
        (∑ k ∈ Finset.Icc l (u + 1), a (k - 1) * e ((k : ℝ) * β))
          - (∑ k ∈ Finset.Icc l (u + 1), a k * e ((k : ℝ) * β)) := by
          have hmul'' :
              e β * (∑ k ∈ Finset.Icc l (u + 1), a k * e ((k : ℝ) * β))
                =
              ∑ k ∈ Finset.Icc l (u + 1), a (k - 1) * e ((k : ℝ) * β) := by
            simpa [hS'] using hmul'
          simpa [hmul'', hS']
    _ =
        ∑ k ∈ Finset.Icc l (u + 1),
          (a (k - 1) * e ((k : ℝ) * β) - a k * e ((k : ℝ) * β)) := by
          simpa using
            (Finset.sum_sub_distrib (s := Finset.Icc l (u + 1))
              (f := fun k : ℤ => a (k - 1) * e ((k : ℝ) * β))
              (g := fun k : ℤ => a k * e ((k : ℝ) * β))).symm
    _ =
        ∑ k ∈ Finset.Icc l (u + 1), (a (k - 1) - a k) * e ((k : ℝ) * β) := by
          simp [sub_mul]
    _ = ∑ k ∈ Finset.Icc l (u + 1), (Δ a k) * e ((k : ℝ) * β) := by
          simp [Δ]

private lemma Δ2_eq_ΔΔ (a : ℤ → ℂ) (k : ℤ) : Δ2 a k = Δ (Δ a) k := by
  rfl

private lemma e_sub_one_sq_mul_sum_eq_sum_Δ2
    (β : ℝ) (l u : ℤ) (a : ℤ → ℂ) (hlu1 : l ≤ u + 1)
    (ha_left : a (l - 1) = 0) (ha_right : a (u + 1) = 0)
    (hΔ_left : (Δ a) (l - 1) = 0) (hΔ_right : (Δ a) (u + 2) = 0) :
    (e β - 1) ^ 2 * (∑ k ∈ Finset.Icc l u, a k * e ((k : ℝ) * β))
      =
    ∑ k ∈ Finset.Icc l (u + 2), (Δ2 a k) * e ((k : ℝ) * β) := by
  classical
  have hlu2 : l ≤ u + 2 := by
    exact le_trans hlu1 (by omega)
  have h1 :=
    e_sub_one_mul_sum_eq_sum_Δ (β := β) (l := l) (u := u) (a := a) hlu1 ha_left ha_right
  have h2 :=
    e_sub_one_mul_sum_eq_sum_Δ (β := β) (l := l) (u := u + 1) (a := Δ a)
      (by simpa [add_assoc] using hlu2)
      hΔ_left (by simpa [add_assoc] using hΔ_right)
  -- Multiply the first identity by `(eβ-1)` and substitute the second.
  calc
    (e β - 1) ^ 2 * (∑ k ∈ Finset.Icc l u, a k * e ((k : ℝ) * β))
        = (e β - 1) * ((e β - 1) * (∑ k ∈ Finset.Icc l u, a k * e ((k : ℝ) * β))) := by
            simp [pow_two, mul_assoc]
    _ = (e β - 1) * (∑ k ∈ Finset.Icc l (u + 1), (Δ a k) * e ((k : ℝ) * β)) := by
            simpa [mul_assoc] using congrArg (fun z : ℂ => (e β - 1) * z) h1
    _ = ∑ k ∈ Finset.Icc l (u + 2), (Δ2 a k) * e ((k : ℝ) * β) := by
            simpa [Δ2_eq_ΔΔ, add_assoc] using h2

/--
Core deterministic decay bound for `kernelPolyC`, in terms of the ℓ¹ mass of the backward second
difference of its coefficient sequence (supported on `Icc(-H,H)`).

This lemma is intentionally “engine-free”: it does not compute `∑ ‖Δ²‖`. Downstream code can
either bound that sum analytically, or discharge it by a finite certificate.
-/
theorem norm_kernelPolyC_le_secondDiff
    (β : ℝ) (hβ : ‖e β - 1‖ ≠ 0) :
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
      ≤
    (∑ k ∈ Finset.Icc l (u + 2), ‖Δ2 coeff k‖) / ‖e β - 1‖ ^ 2 := by
  classical
  -- Rewrite `kernelPolyC` and apply the second-difference identity to `a := coeff`.
  have hk : Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
      = ∑ k ∈ Finset.Icc l u, coeff k * e ((k : ℝ) * β) := kernelPolyC_coe_eq_sum_coeff_e (β := β)
  have ha_left : coeff (l - 1) = 0 := by
    have hnot : (l - 1) ∉ Finset.Icc l u := by
      simp [Finset.mem_Icc]
    simpa [coeff] using (coeff_eq_zero_of_notMem (k := l - 1) hnot)
  have ha_right : coeff (u + 1) = 0 := by
    have hnot : (u + 1) ∉ Finset.Icc l u := by
      simp [Finset.mem_Icc]
    simpa [coeff] using (coeff_eq_zero_of_notMem (k := u + 1) hnot)
  have hΔ_left : (Δ coeff) (l - 1) = 0 := by
    -- both terms are outside the support
    have h0 : coeff (l - 2) = 0 := by
      have hnot : (l - 2) ∉ Finset.Icc l u := by
        simp [Finset.mem_Icc]
      simpa [coeff] using (coeff_eq_zero_of_notMem (k := l - 2) hnot)
    have h0' : coeff (l - 1 - 1) = 0 := by
      simpa [sub_eq_add_neg, add_assoc] using h0
    simp [Δ, ha_left, h0']
  have hΔ_right : (Δ coeff) (u + 2) = 0 := by
    have h0 : coeff (u + 1) = 0 := ha_right
    have h1 : coeff (u + 2) = 0 := by
      have hnot : (u + 2) ∉ Finset.Icc l u := by
        simp [Finset.mem_Icc]
      simpa [coeff] using (coeff_eq_zero_of_notMem (k := u + 2) hnot)
    have h0' : coeff (u + 2 - 1) = 0 := by
      simpa [sub_eq_add_neg, add_assoc] using h0
    simp [Δ, h0', h1]

  have hid :
      (e β - 1) ^ 2 * Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
        =
      ∑ k ∈ Finset.Icc l (u + 2), (Δ2 coeff k) * e ((k : ℝ) * β) := by
    -- substitute `hk` into the generic identity
    have hid' :=
      e_sub_one_sq_mul_sum_eq_sum_Δ2 (β := β) (l := l) (u := u) (a := coeff)
        (by
          dsimp [l, u]
          omega)
        ha_left ha_right hΔ_left hΔ_right
    simpa [hk] using hid'

  -- Take norms and divide by `‖eβ-1‖^2`.
  have hsum :
      ‖∑ k ∈ Finset.Icc l (u + 2), (Δ2 coeff k) * e ((k : ℝ) * β)‖
        ≤
      ∑ k ∈ Finset.Icc l (u + 2), ‖Δ2 coeff k‖ := by
    have h0 :=
      norm_sum_le (s := Finset.Icc l (u + 2))
        (f := fun k => (Δ2 coeff k) * e ((k : ℝ) * β))
    refine le_trans h0 ?_
    refine Finset.sum_le_sum ?_
    intro k hk'
    have hEq : ‖(Δ2 coeff k) * e ((k : ℝ) * β)‖ = ‖Δ2 coeff k‖ := by
      calc
        ‖(Δ2 coeff k) * e ((k : ℝ) * β)‖ = ‖Δ2 coeff k‖ * ‖e ((k : ℝ) * β)‖ := by
          simpa [norm_mul]
        _ = ‖Δ2 coeff k‖ := by simp [MajorArcExponential.norm_e]
    exact le_of_eq hEq

  have hmul :
      ‖e β - 1‖ ^ 2 * ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
        ≤
      ∑ k ∈ Finset.Icc l (u + 2), ‖Δ2 coeff k‖ := by
    have : ‖(e β - 1) ^ 2‖ * ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
          ≤ ∑ k ∈ Finset.Icc l (u + 2), ‖Δ2 coeff k‖ := by
      -- rewrite the LHS using `hid` then apply `hsum`
      have : ‖(e β - 1) ^ 2 * Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
            ≤ ∑ k ∈ Finset.Icc l (u + 2), ‖Δ2 coeff k‖ := by
        simpa [hid] using hsum
      simpa [norm_mul] using this
    -- `‖(eβ-1)^2‖ = ‖eβ-1‖^2`
    simpa [pow_two, norm_mul, mul_assoc, mul_left_comm, mul_comm] using this

  have hpos : 0 < ‖e β - 1‖ ^ 2 := by
    have : 0 < ‖e β - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hβ)
    exact pow_pos this 2

  exact (le_div_iff₀ hpos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)

/-!
### Packaged constants

These are convenient abbreviations for later “β-tail” bounds: the ℓ¹ mass of the backward second
difference of the coefficient sequence, and the corresponding uniform cap on `betaSmallSetᶜ`
inside `[-1/2, 1/2]`.
-/

/-- ℓ¹ mass of the backward second difference of the kernel coefficients on the extended band. -/
noncomputable def secondDiffMass : ℝ :=
  ∑ k ∈ Finset.Icc l (u + 2), ‖Δ2 coeff k‖

/-!
### Specialization (canonical parameters)

For the turnkey `Q0` route, `H = 10^4` and `Ucut = H + (H+99)/100 = 10100`.

For the truncated tent coefficient sequence

`coeff k := if k ∈ Icc(-H,H) then (K_full k : ℂ) else 0`,

the backward second difference `Δ2 coeff` vanishes everywhere except at the five points
`{-H, -H+1, 1, H+1, H+2}`. Consequently,

`secondDiffMass = ∑_{k} ‖Δ2 coeff k‖ = 400 / 10100^2 = 1/255025`.
-/

private lemma Ucut_eq : Goldbach.BG_Identity.Ucut = 10100 := by
  simp [Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]

private lemma Ucut_eq_real : (Goldbach.BG_Identity.Ucut : ℝ) = 10100 := by
  exact_mod_cast Ucut_eq

private lemma abs_secondDiff_eq_zero {k : ℤ} (hk : k ≠ 1) :
    (|k - 2| : ℤ) - 2 * (|k - 1| : ℤ) + |k| = 0 := by
  -- The absolute value is affine on `(-∞,0]` and `[2,∞)`, so its second difference vanishes.
  by_cases hk0 : k ≤ 0
  · have hk1 : k - 1 ≤ 0 := by omega
    have hk2 : k - 2 ≤ 0 := by omega
    simp [abs_of_nonpos hk0, abs_of_nonpos hk1, abs_of_nonpos hk2]
    ring
  · have hkge1 : 1 ≤ k := by omega
    have hkge2 : 2 ≤ k := by omega
    have hk1' : 0 ≤ k - 1 := by omega
    have hk2' : 0 ≤ k - 2 := by omega
    -- Exclude the kink at `k = 1`, so we are on the nonnegative affine branch.
    have hkne : k ≠ 1 := hk
    simp [abs_of_nonneg (show 0 ≤ k - 2 from hk2'), abs_of_nonneg (show 0 ≤ k - 1 from hk1'),
      abs_of_nonneg (show 0 ≤ k from le_trans (by omega) hkge2)]
    ring

private lemma Kfull_eq_affine_abs (j : ℤ) (hj : j ∈ Finset.Icc l u) :
    Goldbach.BG_Identity.K_full j
      =
    (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ - (|j| : ℝ) * ((Goldbach.BG_Identity.Ucut : ℝ)⁻¹) ^ 2 := by
  -- On `Icc(-H,H)` we are strictly inside the `max` cutoff, so `K_full` is the affine tent.
  have hUpos : (0 : ℝ) < (Goldbach.BG_Identity.Ucut : ℝ) := Goldbach.BG_Identity.Ucut_pos_real
  have hHU : (H : ℝ) ≤ (Goldbach.BG_Identity.Ucut : ℝ) := by
    -- `Ucut = H + ...`
    have : (H : ℕ) ≤ Goldbach.BG_Identity.Ucut := Nat.le_add_right _ _
    exact_mod_cast this
  have habs_le_H : (|j| : ℝ) ≤ (H : ℝ) := by
    -- `j ∈ [-H,H]` implies `|j| ≤ H`.
    rcases Finset.mem_Icc.mp hj with ⟨hjL, hjU⟩
    have : (|j| : ℤ) ≤ (H : ℤ) := by
      -- `abs_le` works in `ℤ`: `|j| ≤ H ↔ -H ≤ j ∧ j ≤ H`.
      have : -((H : ℤ)) ≤ j ∧ j ≤ (H : ℤ) := by
        simpa [l, u] using ⟨hjL, hjU⟩
      exact abs_le.2 this
    exact_mod_cast this
  have habs_le_U : (|j| : ℝ) ≤ (Goldbach.BG_Identity.Ucut : ℝ) := le_trans habs_le_H hHU
  have hnonneg : 0 ≤ (1 : ℝ) - (|j| : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) := by
    have hdiv : (|j| : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) ≤ 1 := by
      exact (Goldbach.BG_Identity.div_le_one_of_le (a := (|j| : ℝ)) (b := (Goldbach.BG_Identity.Ucut : ℝ)) hUpos habs_le_U)
    linarith
  -- Rewrite `K_full`, collapse the `max`, then expand the resulting affine expression.
  unfold Goldbach.BG_Identity.K_full Goldbach.BG_Identity.K_full_raw
  have hnatAbs : (Int.natAbs j : ℝ) = (|j| : ℝ) := by
    have hZ : (Int.natAbs j : ℤ) = |j| := by
      simpa using (Int.natCast_natAbs j)
    have hR : ((Int.natAbs j : ℤ) : ℝ) = (|j| : ℝ) := by
      exact_mod_cast hZ
    simpa using hR
  have hnonneg' :
      0 ≤ (1 : ℝ) - (Int.natAbs j : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) := by
    simpa [hnatAbs] using hnonneg
  have hmax' :
      max (1 - (Int.natAbs j : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) 0
        =
      (1 - (Int.natAbs j : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    exact max_eq_left hnonneg'
  -- At this point `K_full j = (1 - natAbs/U)/U`; rewrite to the stated `U⁻¹ - |j|*U⁻²` form.
  rw [hmax']
  simp [hnatAbs, div_eq_mul_inv, pow_two, sub_eq_add_neg, mul_add, mul_assoc, mul_left_comm, mul_comm,
    add_assoc, add_left_comm, add_comm]

private lemma Δ2_coeff_eq_zero_of_mem_Icc_l_add_two_u_of_ne_one
    {k : ℤ} (hk : k ∈ Finset.Icc (l + 2) u) (hk1 : k ≠ 1) :
    Δ2 coeff k = 0 := by
  classical
  have hk0 : k ∈ Finset.Icc l u := by
    rcases Finset.mem_Icc.mp hk with ⟨hkL, hkU⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hkU⟩
  have hk1' : k - 1 ∈ Finset.Icc l u := by
    rcases Finset.mem_Icc.mp hk with ⟨hkL, hkU⟩
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hk2' : k - 2 ∈ Finset.Icc l u := by
    rcases Finset.mem_Icc.mp hk with ⟨hkL, hkU⟩
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hΔ :
      Δ2 coeff k =
        (Goldbach.BG_Identity.K_full (k - 2) : ℂ)
          - (2 : ℂ) * (Goldbach.BG_Identity.K_full (k - 1) : ℂ)
          + (Goldbach.BG_Identity.K_full k : ℂ) := by
    simp [Δ2_eq, coeff, hk0, hk1', hk2', Kfull]
  -- Convert to a real identity using the affine-abs form of `K_full`.
  have hK0 := Kfull_eq_affine_abs (j := k) hk0
  have hK1 := Kfull_eq_affine_abs (j := k - 1) hk1'
  have hK2 := Kfull_eq_affine_abs (j := k - 2) hk2'
  have habs :
      ((|k - 2| : ℤ) - 2 * (|k - 1| : ℤ) + |k| : ℤ) = 0 :=
    abs_secondDiff_eq_zero (k := k) hk1
  have habsR :
      (|k - 2| : ℝ) - (2 : ℝ) * (|k - 1| : ℝ) + (|k| : ℝ) = 0 := by
    exact_mod_cast habs
  have hreal :
      (Goldbach.BG_Identity.K_full (k - 2))
        - (2 : ℝ) * (Goldbach.BG_Identity.K_full (k - 1))
        + (Goldbach.BG_Identity.K_full k) = 0 := by
    have habsRneg :
        (-(|(k : ℝ) - 2|) + (2 : ℝ) * |(k : ℝ) - 1| - |(k : ℝ)|) = 0 := by
      linarith [habsR]
    have hform :
        (Goldbach.BG_Identity.K_full (k - 2))
            - (2 : ℝ) * (Goldbach.BG_Identity.K_full (k - 1))
            + (Goldbach.BG_Identity.K_full k)
          =
        ((Goldbach.BG_Identity.Ucut : ℝ)⁻¹ ^ 2) *
          (-(|(k : ℝ) - 2|) + (2 : ℝ) * |(k : ℝ) - 1| - |(k : ℝ)|) := by
      -- Rewrite each `K_full` in affine form and expand.
      simp [hK0, hK1, hK2, mul_add, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
        add_comm]
      ring_nf
    -- Apply the reshaped identity and use `habsRneg`.
    rw [hform]
    simp [habsRneg]
  have hC :
      (Goldbach.BG_Identity.K_full (k - 2) : ℂ)
        - (2 : ℂ) * (Goldbach.BG_Identity.K_full (k - 1) : ℂ)
        + (Goldbach.BG_Identity.K_full k : ℂ) = 0 := by
    exact_mod_cast hreal
  simpa [hΔ] using hC

theorem secondDiffMass_eq_one_div_255025 : secondDiffMass = (1 : ℝ) / 255025 := by
  classical
  -- Split the sum into the five special points and the zero remainder.
  let special : Finset ℤ :=
    insert (u + 2) (insert (u + 1) (insert (1 : ℤ) (insert (l + 1) ({l} : Finset ℤ))))
  have hspecial_mem : ∀ k ∈ special, k ∈ Finset.Icc l (u + 2) := by
    intro k hk
    -- all five points are visibly in the interval.
    have : k = u + 2 ∨ k = u + 1 ∨ k = (1 : ℤ) ∨ k = l + 1 ∨ k = l := by
      simpa [special] using hk
    rcases this with rfl | rfl | rfl | rfl | rfl <;>
      -- `omega` is robust on these linear integer inequalities.
      (refine Finset.mem_Icc.mpr ?_ <;> dsimp [l, u] <;> omega)
  have hfilter :
      (Finset.Icc l (u + 2)).filter (fun k => k ∈ special) = special := by
    ext k
    constructor
    · intro hk
      exact (Finset.mem_filter.mp hk).2
    · intro hk
      have hkI : k ∈ Finset.Icc l (u + 2) := hspecial_mem k hk
      exact Finset.mem_filter.mpr ⟨hkI, hk⟩
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not (s := Finset.Icc l (u + 2)) (p := fun k => k ∈ special)
      (f := fun k : ℤ => ‖Δ2 coeff k‖))
  -- The complement sum is zero because `Δ2 coeff k = 0` there.
  have hrest :
      (Finset.filter (fun k : ℤ => k ∉ special) (Finset.Icc l (u + 2))).sum (fun k : ℤ => ‖Δ2 coeff k‖) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hkI : k ∈ Finset.Icc l (u + 2) := (Finset.mem_filter.mp hk).1
    have hknot : k ∉ special := (Finset.mem_filter.mp hk).2
    have hk_le_u : k ≤ u := by
      rcases Finset.mem_Icc.mp hkI with ⟨_, hkU⟩
      by_contra hku
      have : k = u + 1 ∨ k = u + 2 := by omega
      rcases this with rfl | rfl <;> exact hknot (by simp [special])
    have hk_ge_l2 : l + 2 ≤ k := by
      rcases Finset.mem_Icc.mp hkI with ⟨hkl, _⟩
      by_contra hklt
      have : k = l ∨ k = l + 1 := by omega
      rcases this with rfl | rfl <;> exact hknot (by simp [special])
    have hk_ne_one : k ≠ 1 := by
      intro hk1
      exact hknot (by simpa [hk1] using (by simp [special] : (1 : ℤ) ∈ special))
    have hk_inner : k ∈ Finset.Icc (l + 2) u := Finset.mem_Icc.mpr ⟨hk_ge_l2, hk_le_u⟩
    have hzero : Δ2 coeff k = 0 :=
      Δ2_coeff_eq_zero_of_mem_Icc_l_add_two_u_of_ne_one (k := k) hk_inner hk_ne_one
    simpa [hzero]
  -- Evaluate the sum over `special` by explicit computation (all terms are rational).
  -- First rewrite the `secondDiffMass` sum using `hsplit` and `hfilter`.
  have hmain :
      secondDiffMass
        =
      special.sum (fun k : ℤ => ‖Δ2 coeff k‖) := by
    -- `secondDiffMass` is the full sum; the complement contributes `0`.
    unfold secondDiffMass
    -- `hsplit` is `sum(filter p) + sum(filter ¬p) = sum`.
    -- Rewrite the RHS (the full sum) using this split, then eliminate the `¬p` part using `hrest`.
    calc
      (∑ k ∈ Finset.Icc l (u + 2), ‖Δ2 coeff k‖)
          =
        (∑ k ∈ Finset.Icc l (u + 2) with k ∈ special, ‖Δ2 coeff k‖) +
        (∑ k ∈ Finset.Icc l (u + 2) with k ∉ special, ‖Δ2 coeff k‖) := by
            simpa [Finset.filter_filter] using hsplit.symm
      _ =
        (∑ k ∈ special, ‖Δ2 coeff k‖) + 0 := by
            simp [hfilter, hrest]
      _ = ∑ k ∈ special, ‖Δ2 coeff k‖ := by simp

  -- Expand `special.sum` and evaluate the five nonzero terms.
  have hs :
      (∑ k ∈ special, ‖Δ2 coeff k‖)
        =
      ‖Δ2 coeff l‖ +
        (‖Δ2 coeff 1‖ +
          (‖Δ2 coeff (u + 1)‖ + (‖Δ2 coeff (l + 1)‖ + ‖Δ2 coeff (u + 2)‖))) := by
    classical
    have hl1 : l + 1 ∉ ({l} : Finset ℤ) := by
      simp [Finset.mem_singleton]
    have h1 : (1 : ℤ) ∉ insert (l + 1) ({l} : Finset ℤ) := by
      simp [Finset.mem_singleton]
      dsimp [l]
      simp [Goldbach.BankParams.H] at *
    have hu1 :
        u + 1 ∉ insert (1 : ℤ) (insert (l + 1) ({l} : Finset ℤ)) := by
      simp [Finset.mem_singleton]
      dsimp [l, u]
      simp [Goldbach.BankParams.H] at *
    have hu2 :
        u + 2 ∉ insert (u + 1) (insert (1 : ℤ) (insert (l + 1) ({l} : Finset ℤ))) := by
      simp [Finset.mem_singleton]
      dsimp [l, u]
      simp [Goldbach.BankParams.H] at *
    -- Expand the finite sum using `sum_insert` repeatedly.
    simp [special, Finset.sum_insert, hl1, h1, hu1, hu2, add_assoc, add_left_comm, add_comm]

  -- Compute each of the five norms explicitly.
  have hUcut_nat : H ≤ Goldbach.BG_Identity.Ucut := Nat.le_add_right _ _
  have hUcut_nat' : H - 1 ≤ Goldbach.BG_Identity.Ucut := by
    exact le_trans (Nat.sub_le _ _) hUcut_nat

  have hK_H : Goldbach.BG_Identity.K_full (H : ℤ) = (1 : ℝ) / 1020100 := by
    have h := Goldbach.BG_Identity.K_full_ofNat_le (m := H) hUcut_nat
    -- Evaluate with `H = 10^4`, `Ucut = 10100`.
    have h' : Goldbach.BG_Identity.K_full (H : ℤ) = (1 - (10000 : ℝ) / 10100) / 10100 := by
      simpa [Goldbach.BankParams.H, Ucut_eq_real] using h
    -- Normalize the rational expression.
    calc
      Goldbach.BG_Identity.K_full (H : ℤ) = (1 - (10000 : ℝ) / 10100) / 10100 := h'
      _ = (1 : ℝ) / 1020100 := by norm_num

  have hK_Hm1 : Goldbach.BG_Identity.K_full ((H : ℤ) - 1) = (101 : ℝ) / 102010000 := by
    have h := Goldbach.BG_Identity.K_full_ofNat_le (m := H - 1) hUcut_nat'
    have h' : Goldbach.BG_Identity.K_full ((H : ℤ) - 1) = (1 - (9999 : ℝ) / 10100) / 10100 := by
      simpa [Goldbach.BankParams.H, Ucut_eq_real] using h
    calc
      Goldbach.BG_Identity.K_full ((H : ℤ) - 1) = (1 - (9999 : ℝ) / 10100) / 10100 := h'
      _ = (101 : ℝ) / 102010000 := by norm_num

  have hK_1 : Goldbach.BG_Identity.K_full (1 : ℤ) = (10099 : ℝ) / 102010000 := by
    have h := Goldbach.BG_Identity.K_full_ofNat_le (m := 1) (by
      have : 1 ≤ H := by simp [Goldbach.BankParams.H]
      exact le_trans this hUcut_nat)
    have h' : Goldbach.BG_Identity.K_full (1 : ℤ) = (1 - (1 : ℝ) / 10100) / 10100 := by
      simpa [Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H] using h
    calc
      Goldbach.BG_Identity.K_full (1 : ℤ) = (1 - (1 : ℝ) / 10100) / 10100 := h'
      _ = (10099 : ℝ) / 102010000 := by norm_num

  have hK_0 : Goldbach.BG_Identity.K_full (0 : ℤ) = (1 : ℝ) / 10100 := by
    have h := Goldbach.BG_Identity.K_full_ofNat_le (m := 0) (Nat.zero_le _)
    have h' : Goldbach.BG_Identity.K_full (0 : ℤ) = (1 : ℝ) / 10100 := by
      simpa [Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H] using h
    simpa [div_eq_mul_inv] using h'

  have hnorm_l : ‖Δ2 coeff l‖ = (1 : ℝ) / 1020100 := by
    -- `Δ2 coeff l = coeff l` since `l-1,l-2` are outside.
    have : Δ2 coeff l = (Goldbach.BG_Identity.K_full l : ℂ) := by
      have hl2 : l - 2 ∉ Finset.Icc l u := by simp [Finset.mem_Icc]
      have hl1 : l - 1 ∉ Finset.Icc l u := by simp [Finset.mem_Icc]
      have hl0 : l ∈ Finset.Icc l u := by simp [Finset.mem_Icc]
      simp [Δ2_eq, coeff, hl2, hl1, hl0, Kfull]
    -- rewrite `K_full l = K_full H` by evenness, then use `hK_H`.
    have hlK : Goldbach.BG_Identity.K_full l = Goldbach.BG_Identity.K_full (H : ℤ) := by
      simpa [l] using (Goldbach.BG_Identity.K_full_neg (k := (H : ℤ))).symm
    have hnonneg : 0 ≤ Goldbach.BG_Identity.K_full l := by
      simpa [hlK] using (Goldbach.BG_Identity.K_full_nonneg (k := (H : ℤ)))
    simpa [this, hlK, hK_H, Real.norm_eq_abs, abs_of_nonneg hnonneg]

  have hnorm_l1 : ‖Δ2 coeff (l + 1)‖ = (99 : ℝ) / 102010000 := by
    have hlm1 : l - 1 ∉ Finset.Icc l u := by simp [Finset.mem_Icc]
    have hl0 : l ∈ Finset.Icc l u := by simp [Finset.mem_Icc]
    have hl1 : l + 1 ∈ Finset.Icc l u := by
      refine Finset.mem_Icc.mpr ?_
      constructor
      · simpa using (le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide))
      · -- `l + 1 ≤ u` is a concrete inequality on the canonical window.
        dsimp [l, u]
        simp [Goldbach.BankParams.H]
    have hΔ : Δ2 coeff (l + 1) =
        -(2 : ℂ) * (Goldbach.BG_Identity.K_full l : ℂ) + (Goldbach.BG_Identity.K_full (l + 1) : ℂ) := by
      -- `l+1-2 = l-1` is outside; `l+1-1 = l`.
      have hsub2 : l + 1 - 2 = l - 1 := by omega
      have hsub1 : l + 1 - 1 = l := by omega
      simp [Δ2_eq, coeff, hsub2, hsub1, hlm1, hl0, hl1, Kfull, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm, mul_assoc]
    have hlK : Goldbach.BG_Identity.K_full l = Goldbach.BG_Identity.K_full (H : ℤ) := by
      simpa [l] using (Goldbach.BG_Identity.K_full_neg (k := (H : ℤ))).symm
    have hl1K : Goldbach.BG_Identity.K_full (l + 1) = Goldbach.BG_Identity.K_full ((H : ℤ) - 1) := by
      -- `l+1 = -(H-1)` and `K_full` is even.
      have : l + 1 = -((H : ℤ) - 1) := by dsimp [l]; omega
      simpa [this] using (Goldbach.BG_Identity.K_full_neg (k := (H : ℤ) - 1)).symm
    -- Evaluate the complex norm of the real number `(-99)/10100^2`.
    have hreal :
        (Goldbach.BG_Identity.K_full (l + 1)) - 2 * (Goldbach.BG_Identity.K_full l) =
          (-(99 : ℝ)) / 102010000 := by
      simp [hlK, hl1K, hK_H, hK_Hm1]
      norm_num
    have hval : Δ2 coeff (l + 1) = ((-(99 : ℝ)) / 102010000 : ℂ) := by
      have hrealC :
          (Goldbach.BG_Identity.K_full (l + 1) : ℂ) - (2 : ℂ) * (Goldbach.BG_Identity.K_full l : ℂ) =
            ((-(99 : ℝ)) / 102010000 : ℂ) := by
        exact_mod_cast hreal
      calc
        Δ2 coeff (l + 1)
            = -(2 : ℂ) * (Goldbach.BG_Identity.K_full l : ℂ) + (Goldbach.BG_Identity.K_full (l + 1) : ℂ) := hΔ
        _ = (Goldbach.BG_Identity.K_full (l + 1) : ℂ) - (2 : ℂ) * (Goldbach.BG_Identity.K_full l : ℂ) := by
              ring
        _ = ((-(99 : ℝ)) / 102010000 : ℂ) := hrealC
    -- Now take norms.
    have hpos : (0 : ℝ) < (102010000 : ℝ) := by norm_num
    calc
      ‖Δ2 coeff (l + 1)‖ = ‖((-(99 : ℝ)) / 102010000 : ℂ)‖ := by simp [hval]
      _ = ‖(-(99 : ℝ) / 102010000)‖ := by
            simpa using (Complex.norm_real (-(99 : ℝ) / 102010000))
      _ = |(-(99 : ℝ) / 102010000)| := by
            simpa using (Real.norm_eq_abs (-(99 : ℝ) / 102010000))
      _ = (99 : ℝ) / 102010000 := by
            have hpos99 : (0 : ℝ) < (99 : ℝ) := by norm_num
            have habs : |(-(99 : ℝ) / 102010000)| = (99 : ℝ) / 102010000 := by
              simp [abs_div, abs_neg, abs_of_pos hpos99, abs_of_pos hpos]
            exact habs

  have hnorm_one : ‖Δ2 coeff (1 : ℤ)‖ = (1 : ℝ) / 51005000 := by
    have hmem1 : (1 : ℤ) ∈ Finset.Icc l u := by
      dsimp [l, u]
      simp [Goldbach.BankParams.H]
    have hmem0 : (0 : ℤ) ∈ Finset.Icc l u := by
      dsimp [l, u]
      simp [Goldbach.BankParams.H]
    have hmemm1 : (-1 : ℤ) ∈ Finset.Icc l u := by
      dsimp [l, u]
      simp [Goldbach.BankParams.H]
    have hΔ :
        Δ2 coeff (1 : ℤ)
          =
        (Goldbach.BG_Identity.K_full (-1 : ℤ) : ℂ)
          - (2 : ℂ) * (Goldbach.BG_Identity.K_full (0 : ℤ) : ℂ)
          + (Goldbach.BG_Identity.K_full (1 : ℤ) : ℂ) := by
      simp [Δ2_eq, coeff, hmem1, hmem0, hmemm1, Kfull]
    -- Use evenness `K_full(-1)=K_full(1)` and evaluate.
    have hKneg : Goldbach.BG_Identity.K_full (-1 : ℤ) = Goldbach.BG_Identity.K_full (1 : ℤ) :=
      Goldbach.BG_Identity.K_full_neg (1 : ℤ)
    have hreal :
        Goldbach.BG_Identity.K_full (1 : ℤ) - 2 * Goldbach.BG_Identity.K_full (0 : ℤ) +
            Goldbach.BG_Identity.K_full (1 : ℤ)
          = (-(2 : ℝ)) / 102010000 := by
      simp [hK_1, hK_0]
      norm_num
    have hrealC :
        (Goldbach.BG_Identity.K_full (1 : ℤ) : ℂ) - (2 : ℂ) * (Goldbach.BG_Identity.K_full (0 : ℤ) : ℂ) +
            (Goldbach.BG_Identity.K_full (1 : ℤ) : ℂ)
          = ((-(2 : ℝ)) / 102010000 : ℂ) := by
      exact_mod_cast hreal
    have hval : Δ2 coeff (1 : ℤ) = ((-(2 : ℝ)) / 102010000 : ℂ) := by
      calc
        Δ2 coeff (1 : ℤ)
            =
            (Goldbach.BG_Identity.K_full (-1 : ℤ) : ℂ)
              - (2 : ℂ) * (Goldbach.BG_Identity.K_full (0 : ℤ) : ℂ)
              + (Goldbach.BG_Identity.K_full (1 : ℤ) : ℂ) := hΔ
        _ =
            (Goldbach.BG_Identity.K_full (1 : ℤ) : ℂ)
              - (2 : ℂ) * (Goldbach.BG_Identity.K_full (0 : ℤ) : ℂ)
              + (Goldbach.BG_Identity.K_full (1 : ℤ) : ℂ) := by
                simpa [hKneg]
        _ = ((-(2 : ℝ)) / 102010000 : ℂ) := hrealC
    have hpos : (0 : ℝ) < (102010000 : ℝ) := by norm_num
    calc
      ‖Δ2 coeff (1 : ℤ)‖ = ‖((-(2 : ℝ)) / 102010000 : ℂ)‖ := by simp [hval]
      _ = ‖(-(2 : ℝ) / 102010000)‖ := by
            simpa using (Complex.norm_real (-(2 : ℝ) / 102010000))
      _ = |(-(2 : ℝ) / 102010000)| := by
            simpa using (Real.norm_eq_abs (-(2 : ℝ) / 102010000))
      _ = (1 : ℝ) / 51005000 := by
            have hpos2 : (0 : ℝ) < (2 : ℝ) := by norm_num
            have habs : |(-(2 : ℝ) / 102010000)| = (2 : ℝ) / 102010000 := by
              simp [abs_div, abs_neg, abs_of_pos hpos2, abs_of_pos hpos]
            have hnum : (2 : ℝ) / 102010000 = (1 : ℝ) / 51005000 := by norm_num
            have hcalc : |(-(2 : ℝ) / 102010000)| = (1 : ℝ) / 51005000 := by
              calc
                |(-(2 : ℝ) / 102010000)| = (2 : ℝ) / 102010000 := habs
                _ = (1 : ℝ) / 51005000 := hnum
            exact hcalc

  have hnorm_u1 : ‖Δ2 coeff (u + 1)‖ = (99 : ℝ) / 102010000 := by
    have hmemu : u ∈ Finset.Icc l u := by simp [Finset.mem_Icc]
    have hmemum1 : u - 1 ∈ Finset.Icc l u := by
      dsimp [l, u]
      simp [Goldbach.BankParams.H]
    have hnot : u + 1 ∉ Finset.Icc l u := by
      simp [Finset.mem_Icc]
    have hΔ :
        Δ2 coeff (u + 1)
          =
        (Goldbach.BG_Identity.K_full (u - 1) : ℂ) - (2 : ℂ) * (Goldbach.BG_Identity.K_full u : ℂ) := by
      have hsub2 : u + 1 - 2 = u - 1 := by omega
      have hsub1 : u + 1 - 1 = u := by omega
      have hcoeff_um1 : coeff (u - 1) = (Kfull (u - 1) : ℂ) := coeff_eq_of_mem (k := u - 1) hmemum1
      have hcoeff_u : coeff u = (Kfull u : ℂ) := coeff_eq_of_mem (k := u) hmemu
      have hcoeff_u1 : coeff (u + 1) = 0 := coeff_eq_zero_of_notMem (k := u + 1) hnot
      calc
        Δ2 coeff (u + 1) = coeff (u - 1) - (2 : ℂ) * coeff u + coeff (u + 1) := by
          simpa [Δ2_eq, hsub2, hsub1]
        _ = (Kfull (u - 1) : ℂ) - (2 : ℂ) * (Kfull u : ℂ) := by
          simp [hcoeff_um1, hcoeff_u, hcoeff_u1, Kfull]
    have hreal :
        Goldbach.BG_Identity.K_full (u - 1) - 2 * Goldbach.BG_Identity.K_full u = (-(99 : ℝ)) / 102010000 := by
      simp [u, hK_H, hK_Hm1]
      norm_num
    have hval :
        Δ2 coeff (u + 1) = ((-(99 : ℝ)) / 102010000 : ℂ) := by
      calc
        Δ2 coeff (u + 1)
            = (Goldbach.BG_Identity.K_full (u - 1) : ℂ) - (2 : ℂ) * (Goldbach.BG_Identity.K_full u : ℂ) := hΔ
        _ = ((-(99 : ℝ)) / 102010000 : ℂ) := by
              exact_mod_cast hreal
    -- Take norms.
    simpa [hval, Real.norm_eq_abs]

  have hnorm_u2 : ‖Δ2 coeff (u + 2)‖ = (1 : ℝ) / 1020100 := by
    have hmemu : u ∈ Finset.Icc l u := by simp [Finset.mem_Icc]
    have hnot1 : u + 1 ∉ Finset.Icc l u := by simp [Finset.mem_Icc]
    have hnot2 : u + 2 ∉ Finset.Icc l u := by simp [Finset.mem_Icc]
    have hΔ : Δ2 coeff (u + 2) = (Goldbach.BG_Identity.K_full u : ℂ) := by
      have : u + 2 - 2 = u := by omega
      have : u + 2 - 1 = u + 1 := by omega
      simp [Δ2_eq, coeff, this, hmemu, hnot1, hnot2, Kfull]
    have hnonneg : 0 ≤ Goldbach.BG_Identity.K_full u := by
      simpa using (Goldbach.BG_Identity.K_full_nonneg (k := u))
    simpa [hΔ, hK_H, u, Real.norm_eq_abs, abs_of_nonneg hnonneg]

  -- Finish by summing the five explicit contributions.
  have hsum :
      ∑ k ∈ special, ‖Δ2 coeff k‖ = (1 : ℝ) / 255025 := by
    -- expand the sum and substitute the computed values
    simp [hs, hnorm_l, hnorm_l1, hnorm_one, hnorm_u1, hnorm_u2]
    norm_num
  -- Combine with the earlier reduction `secondDiffMass = special.sum ...`.
  simpa [hmain] using hsum

/-!
### A stable lower bound for `‖e β - 1‖` on `[-1/2,1/2]`

This is a tiny Real-analysis wrapper (Jordan's inequality) that is convenient when turning the
identity above into a uniform tail cap on `betaSmallSetᶜ`.
-/

theorem norm_e_sub_one_ge_four_abs (β : ℝ) (hβ : |β| ≤ ((2 : ℝ)⁻¹)) :
    (4 : ℝ) * |β| ≤ ‖e β - 1‖ := by
  -- `‖e β - 1‖ = ‖2 * sin (πβ)‖`.
  have hnorm :
      ‖e β - 1‖ = ‖2 * Real.sin (Real.pi * β)‖ := by
    -- Use `‖exp(I*x) - 1‖ = ‖2*sin(x/2)‖` with `x = 2πβ`.
    have harg : (2 * Real.pi * β) / 2 = Real.pi * β := by ring
    simpa [e, harg] using (Complex.norm_exp_I_mul_ofReal_sub_one (x := (2 * Real.pi * β)))
  -- Jordan inequality: `|sin(πβ)| ≥ 2|β|` on `|β| ≤ 1/2`.
  have hsin :
      (2 : ℝ) * |β| ≤ |Real.sin (Real.pi * β)| := by
    have hpi : |Real.pi * β| ≤ Real.pi / 2 := by
      -- `|πβ| ≤ π/2` when `|β| ≤ 1/2`.
      have : |Real.pi * β| = Real.pi * |β| := by
        simp [abs_mul, abs_of_pos Real.pi_pos]
      rw [this]
      have : Real.pi * |β| ≤ Real.pi * ((2 : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hβ (le_of_lt Real.pi_pos)
      simpa [mul_assoc, one_div] using this
    -- `2/π * |πβ| ≤ |sin(πβ)|`.
    have hJordan := Real.mul_abs_le_abs_sin (x := Real.pi * β) hpi
    have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have habs : |Real.pi * β| = Real.pi * |β| := by
      simp [abs_mul, abs_of_pos Real.pi_pos]
    -- Rewrite `2/π * (π|β|)` as `2*|β|`.
    have hleft1 :
        (2 / Real.pi : ℝ) * (Real.pi * |β|) = (2 : ℝ) * |β| := by
      have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      calc
        (2 / Real.pi : ℝ) * (Real.pi * |β|)
            = ((2 : ℝ) * Real.pi⁻¹) * (Real.pi * |β|) := by
                simp [div_eq_mul_inv]
        _ = (2 : ℝ) * (Real.pi⁻¹ * (Real.pi * |β|)) := by
                simp [mul_assoc]
        _ = (2 : ℝ) * ((Real.pi⁻¹ * Real.pi) * |β|) := by
                simp [mul_assoc]
        _ = (2 : ℝ) * |β| := by
                simp [hpi0, mul_assoc]
    -- Convert `hJordan` using `hleft`.
    have hJordan' : (2 : ℝ) * |β| ≤ |Real.sin (Real.pi * β)| := by
      -- First rewrite `|πβ|` to `π|β|`, then use `hleft`.
      have hJordan1 :
          (2 / Real.pi : ℝ) * (Real.pi * |β|) ≤ |Real.sin (Real.pi * β)| := by
        simpa [habs, abs_of_pos Real.pi_pos, mul_assoc, mul_left_comm, mul_comm] using hJordan
      simpa [hleft1] using hJordan1
    exact hJordan'
  -- Combine: `‖2*sin(πβ)‖ = 2*|sin(πβ)| ≥ 4*|β|`.
  have :
      (4 : ℝ) * |β| ≤ ‖2 * Real.sin (Real.pi * β)‖ := by
    have : (4 : ℝ) * |β| = (2 : ℝ) * ((2 : ℝ) * |β|) := by ring
    rw [this]
    have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
    have hmul := mul_le_mul_of_nonneg_left hsin hnonneg
    -- `‖2*sin‖ = 2*|sin|`.
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg, mul_assoc] using hmul
  simpa [hnorm] using this

end

end Goldbach.Cert.MajorArcModules.KernelPolyDecay
