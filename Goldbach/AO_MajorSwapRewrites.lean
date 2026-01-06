import Goldbach.BG_Identity
import Goldbach.BG_Bank

/-!
Rewrites for the major-arc / “inner swap” step (no analytic number theory).

This file expresses the banked inner correlation `conv_ref X N` as an explicit finite sum over
the Goldbach split variable `n`, using only finite-sum algebra (swap of sums + `sum_ite`).

These rewrites are intended to be the starting point for any serious derivation of the major-arc
swap bound from orthodox inputs (e.g. Siegel–Walfisz).
-/

namespace Goldbach.AO_MajorSwapRewrites

open scoped BigOperators

open Goldbach

private lemma sum_ite_eq_if_mem
    {α β : Type} [DecidableEq α] [AddCommMonoid β]
    (s : Finset α) (a : α) (f : α → β) :
    (Finset.sum s (fun x => (if a = x then f x else 0)))
      = if a ∈ s then f a else 0 := by
  classical
  by_cases ha : a ∈ s
  · -- split off the `x=a` term using `sum_erase_add`
    have hsplit :
        Finset.sum s (fun x => (if a = x then f x else 0))
          =
          Finset.sum (s.erase a) (fun x => (if a = x then f x else 0))
            + (if a = a then f a else 0) := by
      -- `sum_erase_add` gives `sum (erase a) + term = sum`; we rewrite it in the desired direction.
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := s) (a := a) (f := fun x => (if a = x then f x else 0)) ha).symm
    have hzero :
        Finset.sum (s.erase a) (fun x => (if a = x then f x else 0)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxa : x ≠ a := Finset.ne_of_mem_erase hx
      have hax : a ≠ x := by simpa [eq_comm] using hxa
      simp [hax]
    -- finish
    simp [hsplit, hzero, ha]
  · -- if `a ∉ s`, every summand is `0`
    have : Finset.sum s (fun x => (if a = x then f x else 0)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hax : a ≠ x := by
        exact fun h => ha (h ▸ hx)
      simp [hax]
    simp [this, ha]

/--
`conv_ref` rewritten as a single sum over `n` (the Goldbach split variable),
with the inner-band cutoff expressed via `S_BG`.
-/
lemma conv_ref_eq_sum_n (X N : ℕ) :
    Goldbach.BG_Identity.conv_ref X N
      =
      ((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2))
        * ∑ n ∈ Finset.Icc 2 (N - 2),
            ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
              * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
              *
              (if (↑n - (↑N - ↑n) : ℤ) ∈ Goldbach.BG_Identity.S_BG
               then Goldbach.BG_Identity.K_full (↑n - (↑N - ↑n) : ℤ)
               else 0) := by
  classical
  -- start from the inner-band rewrite of `conv_ref`
  have href :
      Goldbach.BG_Identity.conv_ref X N =
        Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
          Goldbach.BG_Bank.P_BG X N k * Goldbach.BG_Identity.K_full k) :=
    Goldbach.BG_Identity.conv_ref_eq_sum_S_BG (X := X) (N := N)

  -- expand `P_BG`, swap sums, and collapse the `k`-sum via `sum_ite`
  -- (we keep the `if`-membership form to avoid brittle arithmetic normalization).
  unfold Goldbach.BG_Bank.P_BG at href
  -- pull out the constant prefactor
  have :
      Goldbach.BG_Identity.conv_ref X N
        =
        ((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2))
          * Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
              (∑ n ∈ Finset.Icc 2 (N - 2),
                (if ((↑n : ℤ) - ((↑N : ℤ) - (↑n : ℤ)) = k)
                 then ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
                   * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
                 else 0)) * Goldbach.BG_Identity.K_full k) := by
    -- `href` already has the right structure; just rearrange multiplications
    -- `href` has the prefactor inside the sum; factor it out.
    -- (Do this with a `mul_sum` rewrite rather than brittle `simp` on big expressions.)
    simpa [href, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

  -- swap the `k` and `n` sums (finite Fubini)
  rw [this]
  -- bring the `n` sum out front
  have hswap :
      (Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
            (∑ n ∈ Finset.Icc 2 (N - 2),
              (if ((↑n : ℤ) - ((↑N : ℤ) - (↑n : ℤ)) = k)
               then ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
                 * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
               else 0)) * Goldbach.BG_Identity.K_full k))
        =
        ∑ n ∈ Finset.Icc 2 (N - 2),
          ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
            * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
            *
            (Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
              (if ((↑n : ℤ) - ((↑N : ℤ) - (↑n : ℤ)) = k) then Goldbach.BG_Identity.K_full k else 0))) := by
    -- rewrite as iterated sums and apply `Finset.sum_comm`
    -- (use binder form to keep rewriting stable in this toolchain snapshot).
    calc
      (Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
            (∑ n ∈ Finset.Icc 2 (N - 2),
              (if ((↑n : ℤ) - ((↑N : ℤ) - (↑n : ℤ)) = k)
               then ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
                 * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
               else 0)) * Goldbach.BG_Identity.K_full k))
          =
          Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
            ∑ n ∈ Finset.Icc 2 (N - 2),
              ((if ((↑n : ℤ) - ((↑N : ℤ) - (↑n : ℤ)) = k)
                then ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
                  * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
                else 0) * Goldbach.BG_Identity.K_full k)) := by
              simp [Finset.sum_mul]
      _ =
          ∑ n ∈ Finset.Icc 2 (N - 2),
            Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
              ((if ((↑n : ℤ) - ((↑N : ℤ) - (↑n : ℤ)) = k)
                then ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
                  * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
                else 0) * Goldbach.BG_Identity.K_full k)) := by
              simpa using (Finset.sum_comm (s := Goldbach.BG_Identity.S_BG)
                (t := Finset.Icc 2 (N - 2))
                (f := fun k n =>
                  (if ((↑n : ℤ) - ((↑N : ℤ) - (↑n : ℤ)) = k)
                   then ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
                     * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
                   else 0) * Goldbach.BG_Identity.K_full k))
      _ =
          ∑ n ∈ Finset.Icc 2 (N - 2),
            ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
              * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
              *
              (Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
                (if ((↑n : ℤ) - ((↑N : ℤ) - (↑n : ℤ)) = k)
                 then Goldbach.BG_Identity.K_full k else 0))) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              -- pull the `n`-dependent factor outside the `k`-sum
              simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, mul_add]

  -- collapse the inner `k`-sum by `sum_ite`
  rw [hswap]
  refine congrArg (fun t => ((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) * t) ?_
  refine Finset.sum_congr rfl ?_
  intro n hn
  set k0 : ℤ := (↑n - (↑N - ↑n) : ℤ)
  have hk :
      (Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
            (if ((↑n : ℤ) - ((↑N : ℤ) - (↑n : ℤ)) = k) then Goldbach.BG_Identity.K_full k else 0)))
        = if k0 ∈ Goldbach.BG_Identity.S_BG then Goldbach.BG_Identity.K_full k0 else 0 := by
    -- rewrite the equality test to the `k0 = k` form
    simpa [k0] using
      (sum_ite_eq_if_mem
        (s := Goldbach.BG_Identity.S_BG)
        (a := k0)
        (f := fun k => Goldbach.BG_Identity.K_full k))
  -- finish the pointwise rewrite
  simp [k0, hk, mul_assoc, mul_left_comm, mul_comm]

/--
`conv_ref - conv_ref_const` rewritten as the explicit `n`-sum minus the singular-series model.

This is the algebraic “front door” for a future proof from orthodox major-arc/Siegel–Walfisz input.
-/
lemma conv_ref_sub_conv_ref_const_eq_sum_n (X N : ℕ) :
    Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N
      =
      ((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2))
        * ∑ n ∈ Finset.Icc 2 (N - 2),
            ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
              * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
              *
              (if (↑n - (↑N - ↑n) : ℤ) ∈ Goldbach.BG_Identity.S_BG
               then Goldbach.BG_Identity.K_full (↑n - (↑N - ↑n) : ℤ)
               else 0)
        - (Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X) := by
  classical
  -- rewrite `conv_ref` and `conv_ref_const` and simplify
  simpa [conv_ref_eq_sum_n, Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass]

end Goldbach.AO_MajorSwapRewrites
