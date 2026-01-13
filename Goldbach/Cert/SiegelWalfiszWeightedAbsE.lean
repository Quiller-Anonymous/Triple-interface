import Goldbach.Cert.SiegelWalfiszWeighted

/-!
Weighted AP bounds from a **uniform bound** on the SW deviation `E`.

`Goldbach.Cert.SiegelWalfiszWeighted` provides a convenient lemma
`abs_weightedSum_Ico_sub_mainTerm_le_of_PsiBound` that packages the whole argument from a
`PsiBound A` hypothesis.

For “effective / explicit constant” work, one often wants to bypass the log-power interface and
instead plug in a uniform bound of the form `|E x| ≤ M` on the relevant interval. This file
provides exactly that interface, reusing the same summation-by-parts identity.
-/

namespace Goldbach.Cert
namespace SiegelWalfiszWeighted

open scoped BigOperators

open Goldbach.Cert.SiegelWalfisz

noncomputable section

variable (q a : ℕ)

/--
If `|E x|` is uniformly bounded by `M` for `x ∈ [L-1, U]`, then the weighted AP sum on `Ico L (U+1)`
differs from the main term by at most `M` times the discrete variation of `g`.

This is the same inequality as `abs_weightedSum_Ico_sub_mainTerm_le_of_PsiBound`, but with the
`PsiBound` hypothesis replaced by an explicit uniform bound on `E`.
-/
theorem abs_weightedSum_Ico_sub_mainTerm_le_of_absE_uniform
    (g : ℕ → ℝ) {L U : ℕ}
    (hLU : L ≤ U) (hL : 0 < L)
    (hgL : g (L - 1) = 0)
    (M : ℝ)
    (hE_uniform : ∀ {x : ℕ}, x ∈ Finset.Icc (L - 1) U → |E (q := q) (a := a) x| ≤ M) :
    |(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
        - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n)|
      ≤
      M * (|g U| + (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|)) := by
  classical
  have hId :=
    weightedSum_Ico_eq_mainTerm_add_error_of_pos (q := q) (a := a) (g := g) (L := L) (U := U)
      hLU hL
  -- Rearrange the identity to isolate `S - mainTerm`.
  have hsub :
      (∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
          - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n)
        =
        (E (q := q) (a := a) U) * g U
          - (E (q := q) (a := a) (L - 1)) * g (L - 1)
          - (∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
    linarith [hId]
  -- Use `g(L-1)=0`.
  have hsub' :
      (∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
          - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n)
        =
        (E (q := q) (a := a) U) * g U
          - (∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
    simpa [hgL] using hsub

  calc
    |(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
        - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n)|
        =
        |(E (q := q) (a := a) U) * g U
          - (∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n))| := by
          simpa [one_div] using congrArg abs hsub'
    _ ≤ |(E (q := q) (a := a) U) * g U|
          + |(∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n))| := by
          simpa [sub_eq_add_neg] using
            (abs_add_le ((E (q := q) (a := a) U) * g U)
              (-(∑ n ∈ Finset.Ico (L - 1) U,
                (E (q := q) (a := a) n) * (g (n + 1) - g n))))
    _ ≤ M * |g U| + M * (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|) := by
          -- First term: cap `|E U|` by `M`.
          have hEU :
              |(E (q := q) (a := a) U) * g U| ≤ M * |g U| := by
            have hmem : U ∈ Finset.Icc (L - 1) U := by
              refine Finset.mem_Icc.mpr ?_
              constructor
              · exact le_trans (Nat.sub_le L 1) hLU
              · exact le_rfl
            have hE := hE_uniform (x := U) hmem
            simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm] using
              (mul_le_mul_of_nonneg_right hE (abs_nonneg (g U)))
          -- Second term: `|∑| ≤ ∑| |` and cap each `|E n|` by `M`.
          have hsum :
              |(∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n))|
                ≤
                M * (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|) := by
            have htri :
                |(∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n))|
                  ≤
                  ∑ n ∈ Finset.Ico (L - 1) U,
                    |(E (q := q) (a := a) n) * (g (n + 1) - g n)| :=
              Finset.abs_sum_le_sum_abs _ _
            have hpt :
                (∑ n ∈ Finset.Ico (L - 1) U, |(E (q := q) (a := a) n) * (g (n + 1) - g n)|)
                  ≤
                ∑ n ∈ Finset.Ico (L - 1) U, M * |g (n + 1) - g n| := by
              refine Finset.sum_le_sum ?_
              intro n hn
              have hnIcc : n ∈ Finset.Icc (L - 1) U := by
                refine Finset.mem_Icc.mpr ?_
                constructor
                · exact (Finset.mem_Ico.mp hn).1
                · exact le_of_lt (Finset.mem_Ico.mp hn).2
              have hEn := hE_uniform (x := n) hnIcc
              have habs :
                  |(E (q := q) (a := a) n) * (g (n + 1) - g n)|
                    =
                  |E (q := q) (a := a) n| * |g (n + 1) - g n| := by
                simp [abs_mul]
              -- `|E n|*|Δg| ≤ M*|Δg|`
              simpa [habs, mul_assoc, mul_left_comm, mul_comm] using
                (mul_le_mul_of_nonneg_right hEn (abs_nonneg (g (n + 1) - g n)))
            have hfactor :
                (∑ n ∈ Finset.Ico (L - 1) U, M * |g (n + 1) - g n|)
                  =
                M * (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|) := by
              simp [Finset.mul_sum]
            exact le_trans (le_trans htri hpt) (le_of_eq hfactor)
          exact add_le_add hEU hsum
    _ = M * (|g U| + (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|)) := by
          ring

end

end SiegelWalfiszWeighted
end Goldbach.Cert
