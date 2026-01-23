import Goldbach.Cert.MajorArcModules.BetaInterval
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebraResource
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
Finite-support bookkeeping for the TT*/Parseval route.

The β-Fourier expansion in `Q0MajorTailTTStarAlgebra` shows that `β ↦ innerMajorQ0 X N Δ β` is a
finite Fourier polynomial in β, with frequencies coming from differences `m-n` where
`n,m ∈ s N = Icc 2 (N-2)`.

This module packages the resulting *finite k-support* fact, so that the TT* target

`∑' k : ℤ, ‖fourierCoeffOn hab (fun β => innerMajorQ0 ...) k‖^2`

can be rewritten as a `Finset.sum`. This is the key seam for a generator/checker certificate.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.Cert.MajorArcModules.IntegralPipeline

open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral

noncomputable section

/-- A conservative finite frequency range for β-Fourier coefficients of `innerMajorQ0`. -/
noncomputable def kSupport (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

private lemma sub_mem_kSupport_of_mem_s {N n m : ℕ} (hn : n ∈ s N) (hm : m ∈ s N) :
    ((m : ℤ) - (n : ℤ)) ∈ kSupport N := by
  classical
  -- From `n,m ∈ Icc 2 (N-2)` we have `n,m ≤ N`.
  have hn_le : n ≤ N := by
    have hn_le' : n ≤ N - 2 := (Finset.mem_Icc.mp hn).2
    exact le_trans hn_le' (Nat.sub_le N 2)
  have hm_le : m ≤ N := by
    have hm_le' : m ≤ N - 2 := (Finset.mem_Icc.mp hm).2
    exact le_trans hm_le' (Nat.sub_le N 2)
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (Nat.zero_le m)
  have hn_leZ : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn_le
  have hm_leZ : (m : ℤ) ≤ (N : ℤ) := by exact_mod_cast hm_le

  have hlower : (-(N : ℤ)) ≤ (m : ℤ) - (n : ℤ) := by
    -- `0 - N ≤ m - n` since `0 ≤ m` and `n ≤ N`.
    have := sub_le_sub hm0 hn_leZ
    simpa using this
  have hupper : (m : ℤ) - (n : ℤ) ≤ (N : ℤ) := by
    -- `m - n ≤ N - 0` since `m ≤ N` and `0 ≤ n`.
    have := sub_le_sub hm_leZ hn0
    simpa using this
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

theorem fourierCoeffOn_innerMajorQ0_eq_zero_of_not_mem_kSupport
    (X N : ℕ) (Δ : ℝ) (k : ℤ) (hk : k ∉ kSupport N) :
    fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k = 0 := by
  classical
  -- Use the explicit finite (n,m) formula for the β-Fourier coefficient.
  rw [fourierCoeffOn_innerMajorQ0_eq_sum_nm (X := X) (N := N) (Δ := Δ) (k := k)]
  -- Show every summand vanishes because `k` cannot equal `m-n` outside `kSupport N`.
  refine Finset.sum_eq_zero ?_
  intro n hn
  refine Finset.sum_eq_zero ?_
  intro m hm
  have hmn : ((m : ℤ) - (n : ℤ)) ∈ kSupport N := sub_mem_kSupport_of_mem_s (N := N) hn hm
  have hkne : k ≠ (m : ℤ) - (n : ℤ) := by
    intro hkEq
    apply hk
    simpa [hkEq] using hmn
  simp [hkne]

theorem tsum_sq_fourierCoeffOn_innerMajorQ0_eq_sum_kSupport
    (X N : ℕ) (Δ : ℝ) :
    (∑' k : ℤ, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
      =
    ∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2 := by
  classical
  -- Reduce the `tsum` using finite support in `k`.
  refine (tsum_eq_sum (s := kSupport N) ?_)
  intro k hk
  have h0 :
      fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k = 0 :=
    fourierCoeffOn_innerMajorQ0_eq_zero_of_not_mem_kSupport (X := X) (N := N) (Δ := Δ) (k := k)
      hk
  simp [h0]

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
