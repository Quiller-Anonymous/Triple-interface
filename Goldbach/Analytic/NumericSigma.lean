import Mathlib.Tactic
import Goldbach.SingularSeries
import Goldbach.SingularSeriesExtras
import Goldbach.Analytic.MajorBoundFromSigma
import Goldbach.Windows

namespace Goldbach
namespace Analytic

open Singular

/-- A conservative numeric lower bound for the Euler-product constant. -/
noncomputable def C2_numeric : C2Const := ⟨(1 : ℝ) / 10, by norm_num⟩

/-- Working window parameters. -/
def X0 : ℕ := 1_000_000
def H  : ℕ := 10_000

/-- A concrete lower bound used for σ on the working window. -/
noncomputable def σmin_working : ℝ := (2 : ℝ) * C2_numeric.C2

/-- Members of the even window are even. Adjust the lemma if your `Windows` API differs. -/
lemma even_of_window {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Windows.EvenIn X H) : Even N := by
  -- We recorded membership using `Windows.IsEven`; convert back.
  have hIsEven : Windows.IsEven N := by
    -- `EvenIn` is a filter by `IsEven`, so membership implies the predicate holds.
    have hmem := (Finset.mem_filter.mp hN).2
    exact hmem
  exact Windows.even_of_isEven hIsEven

/-- `N ≥ 2` for members of the window (since X0 ≥ 4). -/
lemma two_le_of_window {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Windows.EvenIn X H) : 2 ≤ N := by
  -- `EvenIn` is a subset of `IccShift X H = {X, X+1, ..., X+H}`; take the minimum.
  have hmem_Icc : N ∈ Windows.IccShift X H := (Finset.mem_filter.mp hN).1
  rcases Finset.mem_image.mp hmem_Icc with ⟨k, hk_range, hk_eq⟩
  -- N = X + k, with k ≤ H.
  have hk_nonneg : 0 ≤ k := Nat.zero_le _
  have hX2 : 2 ≤ X := by
    have : 2 ≤ X0 := by decide
    exact le_trans this hX
  have hX_le : X ≤ X + k := Nat.le_add_right _ _
  have h2 : 2 ≤ X + k := le_trans hX2 hX_le
  simpa [hk_eq] using h2

/-- Concrete σ-lower bound on the working window: σ(N) ≥ 2 * C2. -/
def SigmaLowerOn_working : SigmaLowerOn X0 H C2_numeric σmin_working :=
by
  refine ⟨?σpos, ?bound⟩
  · -- σmin_pos
    dsimp [σmin_working]
    have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact mul_pos h2 C2_numeric.pos
  · -- bound
    intro X N hX hN
    -- extract evenness from `N ∈ Windows.EvenIn X H`
    have hIsEven : Windows.IsEven N := (Finset.mem_filter.mp (by simpa [Windows.EvenIn] using hN)).2
    have he : Even N := Windows.even_of_isEven hIsEven

    -- expand sigma for even N
    have hs :
        Singular.sigma C2_numeric N
          = (2 : ℝ) * C2_numeric.C2 * Finset.prod (oddPrimeSupport N) (fun p => oddFactor p) :=
      Singular.sigma_even_expand (C := C2_numeric) he

    -- use the “product ≥ 1” lemma from SingularSeriesExtras
    have hprod : (1 : ℝ) ≤ Finset.prod (oddPrimeSupport N) (fun p => oddFactor p) :=
      Singular.prod_oddFactor_ge_one (n := N)

    have hCnonneg : 0 ≤ (2 : ℝ) * C2_numeric.C2 := by
      nlinarith [le_of_lt C2_numeric.pos]

    -- multiply 1 ≤ prod by (2*C2) ≥ 0
    have hmul :
        (2 : ℝ) * C2_numeric.C2
          ≤ (2 : ℝ) * C2_numeric.C2 * Finset.prod (oddPrimeSupport N) (fun p => oddFactor p) := by
      have := mul_le_mul_of_nonneg_left hprod hCnonneg
      simpa [one_mul, mul_assoc] using this

    -- rewrite and finish
    -- goal: sigma ≥ σmin_working = 2*C2
    have : σmin_working ≤ Singular.sigma C2_numeric N := by
      simpa [σmin_working, hs] using hmul
    exact this

end Analytic
end Goldbach
