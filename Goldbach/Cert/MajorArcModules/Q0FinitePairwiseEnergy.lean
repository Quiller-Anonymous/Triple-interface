import Goldbach.Windows

/-!
Generic finite-set pairwise-energy identities used by the arithmetic boundary layer.
-/

namespace Goldbach.Cert.MajorArcModules.Q0FinitePairwiseEnergy

open scoped BigOperators
open Complex
open Finset

noncomputable section

theorem sum_mul_star_re
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℂ) (a : ℂ) :
    Finset.sum s (fun x => ((f x * star a).re))
      =
    ((Finset.sum s f) * star a).re := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro x s hx ih
    simp [hx, add_mul, Complex.add_re]
    calc
      ∑ y ∈ s, ((f y).re * a.re + (f y).im * a.im)
          =
        (∑ y ∈ s, (f y).re * a.re) + ∑ y ∈ s, (f y).im * a.im := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ y ∈ s, (f y).re) * a.re + (∑ y ∈ s, (f y).im) * a.im := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]

theorem sum_star_mul_re
    {α : Type*} [DecidableEq α] (s : Finset α) (a : ℂ) (f : α → ℂ) :
    Finset.sum s (fun x => ((a * star (f x)).re))
      =
    (a * star (Finset.sum s f)).re := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro x s hx ih
    simp [hx, mul_add, Complex.add_re]
    calc
      ∑ y ∈ s, (a.re * (f y).re + a.im * (f y).im)
          =
        (∑ y ∈ s, a.re * (f y).re) + ∑ y ∈ s, a.im * (f y).im := by
            rw [Finset.sum_add_distrib]
      _ =
        a.re * (∑ y ∈ s, (f y).re) + a.im * (∑ y ∈ s, (f y).im) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]

/--
Exact pairwise `‖·‖²` identity on a finite set.

This is the complex-valued analogue of the scalar variance identity
`∑∑ (f(a)-f(b))² = 2|s|∑ f(a)² - 2(∑ f(a))²`.
-/
theorem sum_pairwise_norm_sq_eq
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℂ) :
    Finset.sum s (fun a => Finset.sum s (fun b => ‖f a - f b‖ ^ 2))
      =
    2 * (((s.card : ℝ) * (Finset.sum s (fun a => ‖f a‖ ^ 2))) - ‖(Finset.sum s f)‖ ^ 2) := by
  have hstep :
      Finset.sum s (fun a => Finset.sum s (fun b => ‖f a - f b‖ ^ 2))
        =
      Finset.sum s (fun a => Finset.sum s
        (fun b => ‖f a‖ ^ 2 + ‖f b‖ ^ 2 - 2 * ((f a * star (f b)).re))) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    refine Finset.sum_congr rfl ?_
    intro b hb
    simp [Complex.sq_norm, Complex.normSq_sub]
  have hconst_left :
      Finset.sum s (fun a => Finset.sum s (fun _ => ‖f a‖ ^ 2))
        =
      ((s.card : ℝ) * (Finset.sum s (fun a => ‖f a‖ ^ 2))) := by
    calc
      Finset.sum s (fun a => Finset.sum s (fun _ => ‖f a‖ ^ 2))
          = Finset.sum s (fun a => ((s.card : ℝ) * ‖f a‖ ^ 2)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((s.card : ℝ) * (Finset.sum s (fun a => ‖f a‖ ^ 2))) := by
              rw [Finset.mul_sum]
  have hconst_right :
      Finset.sum s (fun a => Finset.sum s (fun b => ‖f b‖ ^ 2))
        =
      ((s.card : ℝ) * (Finset.sum s (fun b => ‖f b‖ ^ 2))) := by
    calc
      Finset.sum s (fun a => Finset.sum s (fun b => ‖f b‖ ^ 2))
          = Finset.sum s (fun b => Finset.sum s (fun a => ‖f b‖ ^ 2)) := by
              rw [Finset.sum_comm]
      _ = ((s.card : ℝ) * (Finset.sum s (fun b => ‖f b‖ ^ 2))) := by
            calc
              Finset.sum s (fun b => Finset.sum s (fun _ => ‖f b‖ ^ 2))
                  = Finset.sum s (fun b => ((s.card : ℝ) * ‖f b‖ ^ 2)) := by
                      refine Finset.sum_congr rfl ?_
                      intro b hb
                      rw [Finset.sum_const, nsmul_eq_mul]
              _ = ((s.card : ℝ) * (Finset.sum s (fun b => ‖f b‖ ^ 2))) := by
                      rw [Finset.mul_sum]
  have hcross_sum :
      Finset.sum s (fun a => Finset.sum s (fun b => ((f a * star (f b)).re)))
        =
      ‖(Finset.sum s f)‖ ^ 2 := by
    calc
      Finset.sum s (fun a => Finset.sum s (fun b => ((f a * star (f b)).re)))
          = Finset.sum s (fun a => ((f a * star (Finset.sum s f)).re)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              rw [sum_star_mul_re]
      _ = (((Finset.sum s f) * star (Finset.sum s f)).re) := by
            rw [sum_mul_star_re]
      _ = ‖(Finset.sum s f)‖ ^ 2 := by
            have hmulconj :
                (((Finset.sum s f) * star (Finset.sum s f)).re)
                  =
                Complex.normSq (Finset.sum s f) := by
              exact congrArg Complex.re (Complex.mul_conj (Finset.sum s f))
            rw [hmulconj, Complex.normSq_eq_norm_sq]
  have hcross :
      Finset.sum s (fun a => Finset.sum s (fun b => 2 * ((f a * star (f b)).re)))
        =
      2 * ‖(Finset.sum s f)‖ ^ 2 := by
    calc
      Finset.sum s (fun a => Finset.sum s (fun b => 2 * ((f a * star (f b)).re)))
          = Finset.sum s (fun a => 2 * Finset.sum s (fun b => ((f a * star (f b)).re))) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              rw [Finset.mul_sum]
      _ = 2 * Finset.sum s (fun a => Finset.sum s (fun b => ((f a * star (f b)).re))) := by
            rw [Finset.mul_sum]
      _ = 2 * ‖(Finset.sum s f)‖ ^ 2 := by rw [hcross_sum]
  have hsum_add :
      Finset.sum s (fun a => Finset.sum s (fun b => ‖f a‖ ^ 2 + ‖f b‖ ^ 2))
        =
      (Finset.sum s (fun a => Finset.sum s (fun _ => ‖f a‖ ^ 2)))
        + (Finset.sum s (fun a => Finset.sum s (fun b => ‖f b‖ ^ 2))) := by
    calc
      Finset.sum s (fun a => Finset.sum s (fun b => ‖f a‖ ^ 2 + ‖f b‖ ^ 2))
          =
        Finset.sum s
          (fun a => Finset.sum s (fun b => ‖f a‖ ^ 2) + Finset.sum s (fun b => ‖f b‖ ^ 2)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [Finset.sum_add_distrib]
      _ =
        (Finset.sum s (fun a => Finset.sum s (fun _ => ‖f a‖ ^ 2)))
          + (Finset.sum s (fun a => Finset.sum s (fun b => ‖f b‖ ^ 2))) := by
            rw [Finset.sum_add_distrib]
  calc
    Finset.sum s (fun a => Finset.sum s (fun b => ‖f a - f b‖ ^ 2))
        =
      Finset.sum s (fun a => Finset.sum s
        (fun b => ‖f a‖ ^ 2 + ‖f b‖ ^ 2 - 2 * ((f a * star (f b)).re))) := hstep
    _ =
      Finset.sum s (fun a =>
        (Finset.sum s (fun b => ‖f a‖ ^ 2 + ‖f b‖ ^ 2))
          - Finset.sum s (fun b => 2 * ((f a * star (f b)).re))) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Finset.sum_sub_distrib]
    _ =
      (Finset.sum s (fun a => Finset.sum s (fun b => ‖f a‖ ^ 2 + ‖f b‖ ^ 2)))
        - (Finset.sum s (fun a => Finset.sum s (fun b => 2 * ((f a * star (f b)).re)))) := by
          rw [Finset.sum_sub_distrib]
    _ =
      (Finset.sum s (fun a => Finset.sum s (fun _ => ‖f a‖ ^ 2)))
        + (Finset.sum s (fun a => Finset.sum s (fun b => ‖f b‖ ^ 2)))
        - (Finset.sum s (fun a => Finset.sum s (fun b => 2 * ((f a * star (f b)).re)))) := by
          rw [hsum_add]
    _ =
      ((s.card : ℝ) * (Finset.sum s (fun a => ‖f a‖ ^ 2)))
        + ((s.card : ℝ) * (Finset.sum s (fun b => ‖f b‖ ^ 2)))
        - (2 * ‖(Finset.sum s f)‖ ^ 2) := by
          rw [hconst_left, hconst_right, hcross]
    _ = 2 * (((s.card : ℝ) * (Finset.sum s (fun a => ‖f a‖ ^ 2))) - ‖(Finset.sum s f)‖ ^ 2) := by
          ring

/--
Zero-sum corollary of the pairwise `‖·‖²` identity.
-/
theorem sum_pairwise_norm_sq_eq_two_card_mul_sum_norm_sq_of_sum_eq_zero
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℂ)
    (hzero : Finset.sum s f = 0) :
    Finset.sum s (fun a => Finset.sum s (fun b => ‖f a - f b‖ ^ 2))
      =
    2 * ((s.card : ℝ) * (Finset.sum s (fun a => ‖f a‖ ^ 2)) ) := by
  rw [sum_pairwise_norm_sq_eq]
  simp [hzero]

end
