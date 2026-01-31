import Goldbach.Cert.MajorArcModules.Q0MajorSmallTrimBridge
import Goldbach.Cert.MajorArcStep13RealToCircle

/-!
Deterministic bridge for ε₂-small assembly:

`Step21OnArcSmallBetaBMOR` is phrased using the real additive character `gExp`.
The turnkey `Q0` pipeline is phrased using circle characters `fourier` (and `expSum`).

This file records the coercion lemmas needed to compare the Step-21 “trimmed” sums with the
project exponential sums (and uses the existing trim-correction bound).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge

open scoped BigOperators

open Complex AddCircle

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep13RealToCircle
open Goldbach.Cert.MajorArcModules.Q0MajorSmallTrimBridge

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/-!
### `gExp` vs `fourier` on embedded reals
-/

lemma gExp_eq_fourier_coe (x : ℝ) (n : ℕ) :
    gExp x n = (fourier (T := (1 : ℝ)) (n : ℤ) (x : UC) : ℂ) := by
  -- `fourier_coe_eq_e` gives `fourier(n) (x:UC) = e((n:ℝ)*x)`.
  have hfour : (fourier (T := (1 : ℝ)) (n : ℤ) (x : UC) : ℂ) = e ((n : ℝ) * x) :=
    fourier_coe_eq_e (k := (n : ℤ)) (x := x)
  -- `gExp x n = e(x*(n:ℝ))`, and multiplication commutes.
  simp [MajorArcStep2ExpSums.gExp, hfour, mul_comm, mul_left_comm, mul_assoc]

/-!
### Step-21 “trimmed” sums as specializations of `expSumTrim`
-/

lemma expSumTrim_coe_eq_sum_Lambda_gExp (X N : ℕ) (x : ℝ) :
    expSumTrim X N (x : UC)
      =
    ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), aTerm X n * gExp x n := by
  classical
  unfold expSumTrim
  refine Finset.sum_congr rfl ?_
  intro n hn
  -- Replace `fourier` by `gExp` on a real argument.
  have : (fourier (T := (1 : ℝ)) (n : ℤ) (x : UC) : ℂ) = gExp x n := by
    simpa [gExp_eq_fourier_coe (x := x) (n := n)] using (rfl : gExp x n = gExp x n)
  simp [this, mul_assoc]

lemma sum_gExp_eq_sum_fourier_coe (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp x n)
      =
    ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), (fourier (T := (1 : ℝ)) (n : ℤ) (x : UC) : ℂ) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro n hn
  simpa [gExp_eq_fourier_coe (x := x) (n := n)]

/-!
### Upgrade: `expSum` vs `expSumTrim` (re-export)
-/

theorem norm_expSum_sub_expSumTrim_le (X N : ℕ) (γ : UC) (hN : 6 ≤ N) :
    ‖expSum X N γ - expSumTrim X N γ‖ ≤ 2 * Real.log (N : ℝ) :=
  Q0MajorSmallTrimBridge.norm_expSum_sub_expSumTrim_le (X := X) (N := N) (γ := γ) hN

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge
