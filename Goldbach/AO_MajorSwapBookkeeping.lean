import Goldbach.BG_Identity

/-!
Bookkeeping for the major-arc “inner swap” step (no analytic number theory).

This file isolates the purely algebraic part of the story:

  (pointwise gap on the inner payload)  ⇒  (kernel-averaged convolution gap)

so that the eventual analytic work only needs to supply the pointwise gap (or a direct bound on the
kernel sum), and the rest of the pipeline can reuse a stable lemma.
-/

namespace Goldbach.AO_MajorSwapBookkeeping

open scoped BigOperators

open Goldbach

/--
If the inner-band payload is uniformly close to the constant reference payload, then the inner
convolution operator `conv_ref` is close to its constant model `conv_ref_const`.

This is pure bookkeeping:
- rewrite `conv_ref - conv_ref_const` as a finite sum against `K_full`, and
- apply the ℓ∞·ℓ¹ estimate `BG_Identity.swap_bound_linf_l1`.
-/
lemma conv_ref_gap_le_of_payload_gap
    {X N : ℕ} {M : ℝ}
    (hM : ∀ {k : ℤ}, k ∈ BG_Identity.S_BG →
      |BG_Bank.P_BG X N k - BG_Identity.Pref X N k| ≤ M) :
    |BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N|
      ≤ M * ((2 * (BankParams.H : ℝ) + 1) / (BG_Identity.Ucut : ℝ)) := by
  classical
  have hsum :
      BG_Identity.conv_ref X N - BG_Identity.conv_ref_const X N =
        Finset.sum BG_Identity.S_BG (fun k =>
          BG_Identity.K_full k * (BG_Bank.P_BG X N k - BG_Identity.Pref X N k)) :=
    BG_Identity.conv_ref_sub_conv_ref_const_eq_sum (X := X) (N := N)
  have hswap :
      |Finset.sum BG_Identity.S_BG (fun k =>
          BG_Identity.K_full k * (BG_Bank.P_BG X N k - BG_Identity.Pref X N k))|
        ≤ M * ((2 * (BankParams.H : ℝ) + 1) / (BG_Identity.Ucut : ℝ)) := by
    simpa using
      (BG_Identity.swap_bound_linf_l1
        (P := fun k => BG_Bank.P_BG X N k)
        (Q := fun k => BG_Identity.Pref X N k)
        (M := M)
        (hM := by intro k hk; exact hM (k := k) hk))
  simpa [hsum] using hswap

end Goldbach.AO_MajorSwapBookkeeping
