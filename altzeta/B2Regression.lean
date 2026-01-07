import AltZeta.B2Comparator

/-!
AltZeta/B2Regression.lean
=========================

Regression/sanity checks for the B2 interface layer.

This file intentionally uses a trivial kernel `K = 0` to produce a completely
elementary (but nontrivial) instantiation of the B2 hypothesis bundles:

* `Ψ_K(x) = 0` and `Ψ_K^N(x) = 0` for all `x`;
* hence `|Ψ_K(x) - x| = |x|` on any window;
* a toy baseline `Eζ(x) = 2|x|` strictly dominates `E_AZ(x) = |x|` on valid windows.

These checks give us a compilation guard for the B2 API without depending on any
analytic claims.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

def K0 : LogKernel := fun _ => 0

@[simp] lemma psiKernelTerm_K0 (x : ℝ) (n : ℕ) : psiKernelTerm K0 x n = 0 := by
  simp [psiKernelTerm, K0]

@[simp] lemma PsiK_K0 (x : ℝ) : PsiK K0 x = 0 := by
  simp [PsiK]

@[simp] lemma PsiKTrunc_K0 (x : ℝ) (N : ℕ) : PsiKTrunc K0 x N = 0 := by
  simp [PsiKTrunc]

def truncControlK0 (W : Window) (N : ℕ) : TruncControl W K0 N :=
{ ETrunc := fun x => |x|
, ETrunc_nonneg := fun _ _ => abs_nonneg _
, bound_trunc := by
    intro x hx
    simpa using (le_rfl : |0 - x| ≤ |x|)
}

def tailControlK0 (W : Window) (N : ℕ) : TailControl W K0 N :=
{ ETail := fun _ => 0
, ETail_nonneg := fun _ _ => le_rfl
, summable_abs := by
    intro x hx
    -- everything is identically zero
    simpa using (summable_zero : Summable (fun n : ℕ => (0 : ℝ)))
, bound_tail := by
    intro x hx
    simp
}

def baseline2 (W : Window) : ZetaBaseline W :=
{ EZeta := fun x => 2 * |x|
, EZeta_nonneg := by
    intro x hx
    nlinarith [abs_nonneg x]
}

lemma b2_bound_K0_on_window (W : Window) (N : ℕ) :
    ∀ x, ValidX W x → |PsiK K0 x - x| ≤ EFull (truncControlK0 W N) (tailControlK0 W N) x := by
  simpa using bound_full_on_window (W := W) (K := K0) (N := N)
    (truncControlK0 W N) (tailControlK0 W N)

lemma b2_beats_baseline_K0 (W : Window) (N : ℕ) (x : ℝ) (hx : ValidX W x) :
    BeatsBaselineAt (truncControlK0 W N) (tailControlK0 W N) (baseline2 W) x := by
  have hxpos : 0 < x := hx.2.2
  -- Here `EFull = |x|` and `EZeta = 2|x|`, so strict inequality follows from `|x| > 0`.
  have habspos : 0 < |x| := abs_pos.mpr (ne_of_gt hxpos)
  have h12 : (1 : ℝ) < 2 := by norm_num
  have hlt : |x| < 2 * |x| := by
    -- `|x|*1 < |x|*2`
    have := mul_lt_mul_of_pos_left h12 habspos
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  simpa [BeatsBaselineAt, EFull, truncControlK0, tailControlK0, baseline2] using hlt

end B2
end AltZeta
