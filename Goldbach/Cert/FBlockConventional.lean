import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.SigmaTailEuler_Analytic

/-!
Conventional facts about the arithmetic block factor `F_block`.

This file is part of the “Tenor last shot” attempt to understand whether the paper-level
“uniform truncation” σ-tail statements can be reconciled with the Lean pipeline.

The key conventional identity is:

`F_block(N) = (N : ℝ) / φ(N)`.

This is textbook (Euler product for `φ`) and is a reasonable Mathlib-candidate lemma.
Once in hand, any conventional bound on `N/φ(N)` (e.g. Rosser–Schoenfeld type bounds in terms of
`log log N`) can be imported as an independent conventional input, and then specialized to
project windows by purely numeric calibration.
-/

namespace Goldbach.Cert.FBlockConventional

open Real

open Goldbach.AO_OffDiag

/--
`F_block` matches the classical totient ratio `N/φ(N)`.

Proof strategy: both quantities equal the same sum over squarefree divisors.
-/
theorem F_block_eq_nat_div_totient (N : ℕ) (hN : N ≠ 0) :
    Goldbach.AO_OffDiag.TailBlockFun.F_block N =
      (N : ℝ) / (Nat.totient N : ℝ) := by
  classical

  -- `F_block` as a squarefree-divisor sum (already proved in the fixed-cutoff file).
  have hF :
      Goldbach.AO_OffDiag.TailBlockFun.F_block N =
        ∑ d ∈ N.divisors with Squarefree d, (Nat.totient d : ℝ)⁻¹ := by
    -- `TailBlockFun.F_block` and `TailBlock.F_block` are definitional copies.
    -- Normalize `1 / φ(d)` to `φ(d)⁻¹` to match the totient-ratio expansion.
    simpa [Goldbach.AO_OffDiag.TailBlockFun.F_block, Goldbach.AO_OffDiag.TailBlock.F_block, one_div] using
      (Goldbach.AO_OffDiag.TailBlock.F_block_eq_sum_squarefree_divisors (N := N) hN)

  -- `N/φ(N)` as the same squarefree-divisor sum (proved in `SigmaTailEuler_Analytic`).
  have htot :
      (N : ℝ) / (Nat.totient N : ℝ) =
        ∑ d ∈ N.divisors with Squarefree d, (Nat.totient d : ℝ)⁻¹ := by
    -- Start from the `muSq` divisor expansion, then rewrite `muSq` as a squarefree filter.
    have h0 := Goldbach.AO_OffDiag.totient_divisor_expansion (n := N) hN
    -- Rewrite the RHS into a filter sum.
    have hsq :
        (Nat.divisors N).sum (fun d =>
            Goldbach.AO_OffDiag.muSq d * (Nat.totient d : ℝ)⁻¹)
          =
        ∑ d ∈ N.divisors with Squarefree d, (Nat.totient d : ℝ)⁻¹ := by
      -- `muSq d` is `1` on squarefree `d`, else `0`.
      -- First rewrite `muSq d * f d` as an `if Squarefree d then f d else 0`.
      have :
          (Nat.divisors N).sum (fun d =>
              Goldbach.AO_OffDiag.muSq d * (Nat.totient d : ℝ)⁻¹)
            =
          (Nat.divisors N).sum (fun d =>
              if Squarefree d then (Nat.totient d : ℝ)⁻¹ else 0) := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        by_cases hsq : Squarefree d <;> simp [Goldbach.AO_OffDiag.muSq, hsq]
      -- Then apply `Finset.sum_filter`.
      calc
        (Nat.divisors N).sum (fun d =>
              Goldbach.AO_OffDiag.muSq d * (Nat.totient d : ℝ)⁻¹)
            =
          (Nat.divisors N).sum (fun d =>
              if Squarefree d then (Nat.totient d : ℝ)⁻¹ else 0) := this
        _ =
          ∑ d ∈ N.divisors with Squarefree d, (Nat.totient d : ℝ)⁻¹ := by
          simpa using
            (Finset.sum_filter (s := N.divisors) (p := Squarefree)
              (f := fun d => (Nat.totient d : ℝ)⁻¹)).symm
    -- Conclude.
    simpa [hsq] using h0

  -- Combine.
  exact (hF.trans htot.symm)

/--
Conventional interface: a bound on the totient ratio `N/φ(N)`.

This is intended to be instantiated by a literature theorem (e.g. Rosser–Schoenfeld) with explicit
constants, and then specialized to project windows via monotonicity + numeric bounds on `log`.
-/
def TotientRatioBound (B : ℕ → ℝ) : Prop :=
  ∀ ⦃N : ℕ⦄, N ≠ 0 → (N : ℝ) / (Nat.totient N : ℝ) ≤ B N

theorem F_block_le_of_totientRatioBound
    {B : ℕ → ℝ} (hB : TotientRatioBound B) {N : ℕ} (hN : N ≠ 0) :
    Goldbach.AO_OffDiag.TailBlockFun.F_block N ≤ B N := by
  have hEq := F_block_eq_nat_div_totient (N := N) hN
  simpa [hEq] using hB (N := N) hN

end Goldbach.Cert.FBlockConventional
