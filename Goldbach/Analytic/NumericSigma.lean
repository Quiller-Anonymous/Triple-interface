import Mathlib.Tactic
import Goldbach.SingularSeries
import Goldbach.SingularSeriesExtras
import Goldbach.Analytic.MajorBoundFromSigma
import Goldbach.Windows

namespace Goldbach
namespace Analytic

open Singular

/-- A conservative numeric lower bound for the Euler-product constant. -/
def C2_numeric : C2Const := ⟨(1 : ℝ) / 10, by norm_num⟩

/-- Working window parameters. -/
def X0 : ℕ := 1_000_000
def H  : ℕ := 10_000

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
def SigmaLowerOn_working : SigmaLowerOn X0 H C2_numeric :=
{ σmin     := (2 : ℝ) * C2_numeric.C2,
  σmin_pos := by
    have : 0 < C2_numeric.C2 := C2_numeric.pos
    nlinarith,
  bound    := by
    intro X N hX hN
    have he : Even N := even_of_window hX hN
    simpa using Singular.sigma_floor_even (C:=C2_numeric) he }

end Analytic
end Goldbach
