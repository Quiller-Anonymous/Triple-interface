import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Parity
import Goldbach.BG_Identity
import Goldbach.AO_OffDiag.TailBlock

/-!
Scratchpad: the “textbook” Fejér major-arc main term in the repo’s *discrete* normalization.

This file only records algebraic facts about the kernel mass and the truncated singular series
object already defined in `Goldbach.AO_OffDiag.TailBlock`.

It does **not** attempt to prove the major-arc approximation itself (Siegel–Walfisz, etc.).
-/

namespace Goldbach.Cert
namespace MajorArcFejerModelScratch

open scoped BigOperators

open Goldbach
open Goldbach.BankParams

noncomputable section

/-!
## Kernel masses on the canonical window

The kernel is `K_full_raw Ucut` (a normalized discrete tent / Fejér kernel), but the *banked*
correlation only samples the offsets `k = 2n - N`. For even `N`, these offsets are even integers,
so the correct scalar in the main term is the **even-offset** mass:
`∑_{|k|≤H, k even} K_full k`.
-/

abbrev Ucut : ℕ := Goldbach.BG_Identity.Ucut

@[simp] lemma H_eq : H = 10000 := by
  norm_num [Goldbach.BankParams.H]

@[simp] lemma Ucut_eq : Ucut = 10100 := by
  -- `Ucut = H + ⌈H/100⌉` with `H = 10000`.
  norm_num [Ucut, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]

abbrev m : ℕ := 5000

@[simp] lemma two_m_eq_H : 2 * m = H := by
  -- `H = 10000`.
  norm_num [m, Goldbach.BankParams.H]

lemma two_m_le_Ucut : 2 * m ≤ Ucut := by
  -- `H ≤ Ucut` holds by definition, and `2*m = H`.
  have hHU : H ≤ Ucut := by
    simp [Ucut, Goldbach.BG_Identity.Ucut]
  simpa [two_m_eq_H] using hHU

/-!
### A small real-summation helper

We keep a minimal version of “Gauss summation” for casting `(∑ i, i)` into `ℝ`.
-/

private lemma sum_range_id_real (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => (i : ℝ)) = ((n : ℝ) * (n - 1 : ℕ) : ℝ) / 2 := by
  -- Start from the nat identity `(∑ i<n, i) * 2 = n * (n-1)`.
  have hNat : (Finset.sum (Finset.range n) (fun i => i) : ℕ) * 2 = n * (n - 1) :=
    Finset.sum_range_id_mul_two n
  have hCast :
      (((Finset.sum (Finset.range n) (fun i => i) : ℕ) * 2 : ℕ) : ℝ)
        = ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast hNat
  have hReal2 :
      (Finset.sum (Finset.range n) (fun i => (i : ℝ))) * 2 = ((n * (n - 1) : ℕ) : ℝ) := by
    -- Push casts through `sum` and `mul`.
    simpa [Nat.cast_sum, Nat.cast_mul] using hCast
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  -- Solve for the sum by dividing by 2.
  have : Finset.sum (Finset.range n) (fun i => (i : ℝ))
      = ((n * (n - 1) : ℕ) : ℝ) / 2 := by
    nlinarith [hReal2]
  simpa [Nat.cast_mul] using this

private lemma sum_range_succ_real (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => (Nat.succ i : ℝ)) = ((n : ℝ) * (n + 1 : ℕ) : ℝ) / 2 := by
  -- ∑ (i+1) = ∑ i + ∑ 1.
  have hStep :
      Finset.sum (Finset.range n) (fun i => (Nat.succ i : ℝ))
        =
      Finset.sum (Finset.range n) (fun i => (i : ℝ)) + (n : ℝ) := by
    calc
      Finset.sum (Finset.range n) (fun i => (Nat.succ i : ℝ))
          = Finset.sum (Finset.range n) (fun i => (i : ℝ) + 1) := by
              simp [Nat.succ_eq_add_one, Nat.cast_add]
      _ = Finset.sum (Finset.range n) (fun i => (i : ℝ))
            + Finset.sum (Finset.range n) (fun _i => (1 : ℝ)) := by
            simpa [Finset.sum_add_distrib]
      _ = Finset.sum (Finset.range n) (fun i => (i : ℝ)) + (n : ℝ) := by
            simp
  have hId : Finset.sum (Finset.range n) (fun i => (i : ℝ)) = ((n : ℝ) * (n - 1 : ℕ) : ℝ) / 2 :=
    sum_range_id_real n
  -- Now simplify the arithmetic identity by cases on `n` to eliminate the `n-1` truncation.
  cases n with
  | zero =>
      simp
  | succ n =>
      -- `n+1` case: (n+1)n/2 + (n+1) = (n+1)(n+2)/2.
      have hId' :
          Finset.sum (Finset.range (Nat.succ n)) (fun i => (i : ℝ))
            = ((Nat.succ n : ℝ) * (n : ℕ) : ℝ) / 2 := by
        simpa using (sum_range_id_real (Nat.succ n))
      have hStep' :
          Finset.sum (Finset.range (Nat.succ n)) (fun i => (Nat.succ i : ℝ))
            = ((Nat.succ n : ℝ) * (n : ℕ) : ℝ) / 2 + (Nat.succ n : ℝ) := by
        calc
          Finset.sum (Finset.range (Nat.succ n)) (fun i => (Nat.succ i : ℝ))
              = Finset.sum (Finset.range (Nat.succ n)) (fun i => (i : ℝ)) + (Nat.succ n : ℝ) := by
                  simpa using hStep
          _ = ((Nat.succ n : ℝ) * (n : ℕ) : ℝ) / 2 + (Nat.succ n : ℝ) := by
                  simpa [hId']
      -- Prove the target by multiplying by 2 (to avoid `n-1` truncation entirely).
      refine (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2 ?_
      -- rewrite the LHS using `hStep'` and clear `/2`.
      have hMul :
          (Finset.sum (Finset.range (Nat.succ n)) (fun i => (Nat.succ i : ℝ))) * 2
            = ((Nat.succ n : ℝ) * (n : ℕ) : ℝ) + 2 * (Nat.succ n : ℝ) := by
        -- Multiply `hStep'` by 2 and simplify.
        have := congrArg (fun t : ℝ => t * 2) hStep'
        -- `(a/2)*2 = a` and `(b)*2 = 2*b`
        simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using this
      -- Finish: `((n+1)*n) + 2*(n+1) = (n+1)*(n+2)`.
      -- Put `n+2` in the exact Nat-cast form `Nat.succ (Nat.succ n)`.
      have : ((Nat.succ n : ℝ) * (Nat.succ (Nat.succ n) : ℕ) : ℝ)
              = ((Nat.succ n : ℝ) * (n : ℕ) : ℝ) + 2 * (Nat.succ n : ℝ) := by
        -- `↑(n+2) = ↑n + 2`.
        -- First reduce to a polynomial identity, then close by `ring`.
        simp [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
        ring
      -- Combine.
      have hProd :
          ((Nat.succ n : ℝ) * (n : ℕ) : ℝ) + 2 * (Nat.succ n : ℝ)
            = ((Nat.succ n : ℝ) * (Nat.succ (Nat.succ n) : ℕ) : ℝ) := by
        simpa using this.symm
      -- Chain the equalities (avoid `simp`-based rewriting loops).
      calc
        (Finset.sum (Finset.range (Nat.succ n)) (fun i => (Nat.succ i : ℝ))) * 2
            = ((Nat.succ n : ℝ) * (n : ℕ) : ℝ) + 2 * (Nat.succ n : ℝ) := hMul
        _ = ((Nat.succ n : ℝ) * (Nat.succ (Nat.succ n) : ℕ) : ℝ) := hProd

/-!
### Even-offset mass for the truncated Fejér kernel

We record it in the form needed by the “textbook main term”:
`mass_even(H,Ucut) = ∑_{|k|≤H, k even} K_full k`.

We define it in the equivalent closed form `K(0) + 2 * ∑_{j=1..m} K(2j)` since `K_full` is even.
-/

noncomputable def mass_even : ℝ :=
  Goldbach.BG_Identity.K_full (0 : ℤ)
    + 2 * Finset.sum (Finset.range m) (fun i =>
        Goldbach.BG_Identity.K_full (Int.ofNat (2 * Nat.succ i)))

lemma mass_even_closed_form :
    mass_even
      =
      ((1 + 2 * m : ℝ) / (Ucut : ℝ))
        - ((2 * m * (m + 1) : ℝ) / (Ucut : ℝ) ^ 2) := by
  classical
  -- Expand the definition and rewrite each `K_full` term using `K_full_ofNat_le`.
  unfold mass_even

  have hK0 : Goldbach.BG_Identity.K_full (0 : ℤ) = (1 : ℝ) / (Ucut : ℝ) := by
    -- `K_full 0 = ((1 - 0/U)/U) = 1/U`.
    have := Goldbach.BG_Identity.K_full_ofNat_le (m := 0) (hm := Nat.zero_le Ucut)
    simpa using this

  have hU0 : (Ucut : ℝ) ≠ 0 := Goldbach.BG_Identity.Ucut_ne_zero_real

  have hKpos :
      ∀ i ∈ Finset.range m,
        Goldbach.BG_Identity.K_full (Int.ofNat (2 * Nat.succ i))
          = ((1 : ℝ) - ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ) := by
    intro i hi
    have hi_lt : i < m := Finset.mem_range.1 hi
    have hi_succ : Nat.succ i ≤ m := Nat.succ_le_of_lt hi_lt
    have h2le : 2 * Nat.succ i ≤ 2 * m := Nat.mul_le_mul_left 2 hi_succ
    have h2leU : 2 * Nat.succ i ≤ Ucut := by
      have : 2 * m ≤ Ucut := two_m_le_Ucut
      exact le_trans h2le this
    simpa using (Goldbach.BG_Identity.K_full_ofNat_le (m := 2 * Nat.succ i) (hm := h2leU))

  -- Turn the `range` sum into a closed form (pure algebra).
  have hSum :
      Finset.sum (Finset.range m) (fun i =>
          Goldbach.BG_Identity.K_full (Int.ofNat (2 * Nat.succ i)))
        = (m : ℝ) / (Ucut : ℝ) - ((m : ℝ) * (m + 1 : ℕ) : ℝ) / (Ucut : ℝ) ^ 2 := by
    -- Rewrite the kernel values and expand the sum linearly.
    have hRewrite :
        Finset.sum (Finset.range m) (fun i =>
            Goldbach.BG_Identity.K_full (Int.ofNat (2 * Nat.succ i)))
          =
        Finset.sum (Finset.range m) (fun i =>
            ((1 : ℝ) - ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa using (hKpos i hi)

    -- Pointwise identity: `((1 - a/U)/U) = 1/U - a/U^2`.
    have hPoint :
        ∀ i, ((1 : ℝ) - ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ)
          = (1 : ℝ) / (Ucut : ℝ) - ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2 := by
      intro i
      field_simp [hU0]

    -- Sum the pointwise identity.
    have hExpand :
        Finset.sum (Finset.range m) (fun i =>
            ((1 : ℝ) - ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ))
          =
        Finset.sum (Finset.range m) (fun _i => (1 : ℝ) / (Ucut : ℝ))
          -
        Finset.sum (Finset.range m) (fun i => ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2) := by
      -- Rewrite the LHS pointwise, then apply `Finset.sum_sub_distrib` with no `simp` loops.
      have hL :
          Finset.sum (Finset.range m) (fun i =>
              ((1 : ℝ) - ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ))
            =
          Finset.sum (Finset.range m) (fun i =>
              (1 : ℝ) / (Ucut : ℝ) - ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simpa using (hPoint i)
      -- Now split the sum of a difference.
      -- (binder notation `∑ i ∈ s, ...` is used elsewhere in the repo and parses reliably here)
      -- but we keep it binder-free.
      have hSplit :
          Finset.sum (Finset.range m) (fun i =>
              (1 : ℝ) / (Ucut : ℝ) - ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2)
            =
          Finset.sum (Finset.range m) (fun _i => (1 : ℝ) / (Ucut : ℝ))
            -
          Finset.sum (Finset.range m) (fun i => ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2) := by
        simpa using (Finset.sum_sub_distrib (s := Finset.range m)
          (f := fun _i => (1 : ℝ) / (Ucut : ℝ))
          (g := fun i => ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2))
      exact hL.trans hSplit

    have hConst :
        Finset.sum (Finset.range m) (fun _i => (1 : ℝ) / (Ucut : ℝ)) = (m : ℝ) / (Ucut : ℝ) := by
      simp [div_eq_mul_inv, mul_assoc]

    have hDen :
        Finset.sum (Finset.range m) (fun i => ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2)
          =
        ((m : ℝ) * (m + 1 : ℕ) : ℝ) / (Ucut : ℝ) ^ 2 := by
      -- First: sum of `(2*(i+1))` over `i < m` is `m*(m+1)`.
      have hSucc : Finset.sum (Finset.range m) (fun i => (Nat.succ i : ℝ)) = ((m : ℝ) * (m + 1 : ℕ) : ℝ) / 2 := by
        simpa using (sum_range_succ_real m)
      have hTwo :
          Finset.sum (Finset.range m) (fun i => ((2 * Nat.succ i : ℕ) : ℝ))
            = (2 : ℝ) * (((m : ℝ) * (m + 1 : ℕ) : ℝ) / 2) := by
        calc
          Finset.sum (Finset.range m) (fun i => ((2 * Nat.succ i : ℕ) : ℝ))
              =
            Finset.sum (Finset.range m) (fun i => (2 : ℝ) * ((Nat.succ i : ℕ) : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
          _ = (2 : ℝ) * Finset.sum (Finset.range m) (fun i => ((Nat.succ i : ℕ) : ℝ)) := by
              simpa [Finset.mul_sum, mul_assoc]
          _ = (2 : ℝ) * (((m : ℝ) * (m + 1 : ℕ) : ℝ) / 2) := by
              rw [hSucc]

      -- Now divide by `U^2` termwise (as multiplication by a constant).
      calc
        Finset.sum (Finset.range m) (fun i => ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2)
            =
          (1 / (Ucut : ℝ) ^ 2) * Finset.sum (Finset.range m) (fun i => ((2 * Nat.succ i : ℕ) : ℝ)) := by
          -- convert division to multiplication and factor out the constant
          have hSwap :
              Finset.sum (Finset.range m) (fun i => ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2)
                =
              Finset.sum (Finset.range m) (fun i => (1 / (Ucut : ℝ) ^ 2) * ((2 * Nat.succ i : ℕ) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          -- now use `mul_sum`
          rw [hSwap]
          exact
            (Finset.mul_sum (s := Finset.range m)
              (f := fun i => ((2 * Nat.succ i : ℕ) : ℝ))
              (a := (1 / (Ucut : ℝ) ^ 2))).symm
        _ = (1 / (Ucut : ℝ) ^ 2) * ((2 : ℝ) * (((m : ℝ) * (m + 1 : ℕ) : ℝ) / 2)) := by
          rw [hTwo]
        _ = ((m : ℝ) * (m + 1 : ℕ) : ℝ) / (Ucut : ℝ) ^ 2 := by
          ring_nf

    -- Combine.
    calc
      Finset.sum (Finset.range m) (fun i =>
          Goldbach.BG_Identity.K_full (Int.ofNat (2 * Nat.succ i)))
          =
        Finset.sum (Finset.range m) (fun i =>
            ((1 : ℝ) - ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ)) := by
          rw [hRewrite]
      _ =
        Finset.sum (Finset.range m) (fun _i => (1 : ℝ) / (Ucut : ℝ))
          -
        Finset.sum (Finset.range m) (fun i => ((2 * Nat.succ i : ℕ) : ℝ) / (Ucut : ℝ) ^ 2) := by
          rw [hExpand]
      _ = (m : ℝ) / (Ucut : ℝ) - ((m : ℝ) * (m + 1 : ℕ) : ℝ) / (Ucut : ℝ) ^ 2 := by
          rw [hConst, hDen]

  -- Final algebra: `K_full 0 + 2 * hSum`.
  -- Put the pieces together.
  calc
    Goldbach.BG_Identity.K_full (0 : ℤ)
        + 2 * Finset.sum (Finset.range m) (fun i =>
            Goldbach.BG_Identity.K_full (Int.ofNat (2 * Nat.succ i)))
        =
      (1 : ℝ) / (Ucut : ℝ) + 2 * ((m : ℝ) / (Ucut : ℝ) - (((m : ℝ) * (m + 1 : ℕ) : ℝ) / (Ucut : ℝ) ^ 2)) := by
      -- avoid `simp` rewriting the argument `Int.ofNat (2 * i.succ)` into other arithmetically equal forms
      rw [hK0, hSum]
    _ =
      ((1 + 2 * m : ℝ) / (Ucut : ℝ)) - ((2 * m * (m + 1) : ℝ) / (Ucut : ℝ) ^ 2) := by
      field_simp [hU0]
      ring

lemma mass_even_eval :
    mass_even = ((10001 : ℝ) / (10100 : ℝ)) - ((5001 : ℝ) / (10201 : ℝ)) := by
  -- Start from the closed form and then simplify the second fraction.
  have h := mass_even_closed_form
  have h' :
      mass_even
        =
        (10001 : ℝ) / (10100 : ℝ) - (2 * (5000 : ℝ) * (5000 + 1 : ℝ)) / (10100 : ℝ) ^ 2 := by
    -- `simp` reduces to `(1 + 2*5000)/10100`; `norm_num` finishes the numeral arithmetic.
    have h0 : mass_even = (1 + 2 * (5000 : ℝ)) / (10100 : ℝ) - (2 * (5000 : ℝ) * (5000 + 1 : ℝ)) / (10100 : ℝ) ^ 2 := by
      simpa [m, Ucut, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H] using h
    -- normalize `1 + 2*5000` to `10001`
    have : (1 + 2 * (5000 : ℝ)) / (10100 : ℝ) = (10001 : ℝ) / (10100 : ℝ) := by norm_num
    simpa [this] using h0
  -- `2*5000*(5001) / 10100^2 = 5001/10201`.
  have hden : (2 * (5000 : ℝ) * (5000 + 1 : ℝ)) / (10100 : ℝ) ^ 2 = (5001 : ℝ) / (10201 : ℝ) := by
    norm_num
  simpa [hden] using h'

/-!
## The truncated singular series and the “Fejér main term” model

The truncated series `σ≤Q0` is already defined in the sigma-tail module, with `Q0 = 30000`.
We record the “textbook” main term on the major arcs in the repo’s discrete normalization:

`prefactor(N) * mass_even * σ≤Q0(N)`.
-/

noncomputable abbrev sigma_trunc_Q0 (N : ℕ) : ℝ :=
  Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N

noncomputable def prefactor (N : ℕ) : ℝ :=
  ((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2))

noncomputable def RΛ_model_fejer (_X N : ℕ) : ℝ :=
  prefactor N * mass_even * sigma_trunc_Q0 N

end

end MajorArcFejerModelScratch
end Goldbach.Cert
