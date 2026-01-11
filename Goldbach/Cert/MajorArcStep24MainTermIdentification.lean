import Goldbach.Cert.MajorArcStep24RamanujanBridge
import Goldbach.AO_OffDiag.TailBlock
import Mathlib.Data.Complex.BigOperators

/-!
Major arcs (Step 24, bookkeeping): identify the σ-side truncation with the Ramanujan phase sum.

This file contains purely algebraic rewrites needed when matching the major-arc main term to the
σ-side model:

* `TailBlock.sigma_trunc_Q0 N` is defined in terms of the closed-form integer-valued Ramanujan sum
  `TailBlock.ramanujanZ q N` (cast to `ℝ`).
* The major-arc main term naturally produces the reduced-residue phase sum
  `∑ r ∈ Rcop q, e (-(N*r)/q)`.

Step 24a (`MajorArcStep24RamanujanBridge`) identifies these in the squarefree case; here we add
the “µ² kills non-squarefree” wrapper and cast/sum plumbing so the truncation can be rewritten in
the same shape as the analytic main term.
-/

namespace Goldbach.Cert
namespace MajorArcStep24MainTermIdentification

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep23RamanujanSum

open Goldbach.AO_OffDiag

noncomputable section

lemma phaseSum_neg_eq_star_ramanujanSumC (q N : ℕ) :
    (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) = star (ramanujanSumC q N) := by
  simpa using
    (Goldbach.Cert.MajorArcStep24RamanujanBridge.star_ramanujanSumC (q := q) (N := N)).symm

lemma moebius_sq_cast_eq_muSq (q : ℕ) :
    ((μ q : ℂ) ^ 2) = ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ) := by
  by_cases hq : Squarefree q
  · -- squarefree: `μ(q)^2 = 1`
    have hm : (μ q : ℤ) ^ 2 = (1 : ℤ) :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
    have hmC : ((μ q : ℂ) ^ 2) = (1 : ℂ) := by
      simpa using congrArg (fun z : ℤ => (z : ℂ)) hm
    simpa [AO_OffDiag.TailBlock.muSq, hq] using hmC
  · -- not squarefree: `μ(q)=0`
    have hm : (μ q : ℤ) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
    have hmC : (μ q : ℂ) = 0 := by
      simpa using congrArg (fun z : ℤ => (z : ℂ)) hm
    simp [AO_OffDiag.TailBlock.muSq, hq, hmC]

lemma muSq_cast_eq_moebius_sq (q : ℕ) :
    ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ) = ((μ q : ℂ) ^ 2) :=
  (moebius_sq_cast_eq_muSq (q := q)).symm

private lemma muSq_mul_phaseSum_neg_eq_muSq_mul_ramanujanZ
    {q N : ℕ} (hq1 : 1 ≤ q) :
    ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))
      =
    ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * (AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) := by
  classical
  by_cases hq : Squarefree q
  · have hbridge :
        (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))
          =
        (AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) :=
      Goldbach.Cert.MajorArcStep24RamanujanBridge.ramanujanSumC_neg_eq_ramanujanZ_of_squarefree
        (q := q) (N := N) hq1 hq
    simp [AO_OffDiag.TailBlock.muSq, hq, hbridge]
  · simp [AO_OffDiag.TailBlock.muSq, hq]

/--
Cast the σ-side truncation `sigma_trunc_Q0` into `ℂ` and rewrite the Ramanujan closed form as the
reduced-residue phase sum with a minus sign.

This is the “shape alignment” lemma used in Step 24 main-term identification.
-/
theorem sigma_trunc_Q0_eq_sum_muSq_phaseSum_neg (N : ℕ) :
    ((AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ)
      =
    (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
      ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))) := by
  classical
  -- Push the `ℝ → ℂ` cast inside the finite sum.
  have hcast :
      ((AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ)
        =
      (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
        (((AO_OffDiag.TailBlock.muSq q)
            * (1 / ((Nat.totient q : ℝ) ^ 2))
            * (AO_OffDiag.TailBlock.ramanujanR q N) : ℝ) : ℂ)) := by
    -- `Complex.ofReal_sum` is the cleanest way to avoid coercion churn.
    have h :=
      (Complex.ofReal_sum (s := Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0)
        (fun q =>
          (AO_OffDiag.TailBlock.muSq q)
            * (1 / ((Nat.totient q : ℝ) ^ 2))
            * (AO_OffDiag.TailBlock.ramanujanR q N)))
    simpa [AO_OffDiag.TailBlock.sigma_trunc_Q0] using h

  -- Rewrite each summand using `ramanujanR = (ramanujanZ : ℤ)` and the `muSq`-killed bridge.
  rw [hcast]
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  -- Convert `ramanujanR` and reorder factors, then apply the `muSq`-killed bridge.
  set cR : ℝ := (1 / ((Nat.totient q : ℝ) ^ 2)) with hcR

  have hbridge :
      ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
          * (AO_OffDiag.TailBlock.ramanujanZ q N : ℂ)
        =
      ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
          * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) := by
    simpa [mul_assoc] using
      (muSq_mul_phaseSum_neg_eq_muSq_mul_ramanujanZ (q := q) (N := N) hq1).symm

  -- Multiply the `muSq`-killed bridge by the totient factor.
  have hbridge' :
      ((cR : ℂ) * (((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ) * (AO_OffDiag.TailBlock.ramanujanZ q N : ℂ)))
        =
      ((cR : ℂ) * (((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))))) :=
    congrArg (fun z : ℂ => (cR : ℂ) * z) hbridge

  -- Now match the exact summand shape from the statement.
  calc
    (((AO_OffDiag.TailBlock.muSq q)
        * (1 / ((Nat.totient q : ℝ) ^ 2))
        * (AO_OffDiag.TailBlock.ramanujanR q N) : ℝ) : ℂ)
        =
      ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * (cR : ℂ)
        * (AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) := by
          -- Push casts through products and rewrite `ramanujanR`.
          simp [hcR, AO_OffDiag.TailBlock.ramanujanR, mul_assoc]
    _ =
      ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * (cR : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) := by
          -- Use `hbridge'` and re-associate/commute.
          -- (Avoid `simp` on equalities of products; just rearrange by commutativity.)
          have := hbridge'
          -- rewrite both sides of `hbridge'` into the `muSq * cR * ...` form
          -- and then read off the desired equality.
          -- `simp` is safe here since it only normalizes products (no cancellation).
          simpa [mul_assoc, mul_left_comm, mul_comm] using this

/--
Variant of `sigma_trunc_Q0_eq_sum_muSq_phaseSum_neg` rewriting the reduced-residue phase sum
as `star (ramanujanSumC q N)`.
-/
theorem sigma_trunc_Q0_eq_sum_muSq_star_ramanujanSumC (N : ℕ) :
    ((AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ)
      =
    (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
      ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * star (ramanujanSumC q N)) := by
  classical
  rw [sigma_trunc_Q0_eq_sum_muSq_phaseSum_neg (N := N)]
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hstar :
      star (ramanujanSumC q N) = ∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)) :=
    Goldbach.Cert.MajorArcStep24RamanujanBridge.star_ramanujanSumC (q := q) (N := N)
  set C : ℂ :=
    ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ) * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
  change C * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) = C * star (ramanujanSumC q N)
  exact congrArg (fun z : ℂ => C * z) (by simpa using hstar.symm)

/--
Variant of `sigma_trunc_Q0_eq_sum_muSq_phaseSum_neg` rewriting the squarefree cutoff as `μ(q)^2`.

This matches the `(μ/φ)^2` structure that appears when multiplying two major-arc main terms.
-/
theorem sigma_trunc_Q0_eq_sum_moebius_sq_phaseSum_neg (N : ℕ) :
    ((AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ)
      =
    (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
      ((μ q : ℂ) ^ 2)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))) := by
  classical
  -- Start from the `muSq` version and rewrite termwise using `moebius_sq_cast_eq_muSq`.
  rw [sigma_trunc_Q0_eq_sum_muSq_phaseSum_neg (N := N)]
  refine Finset.sum_congr rfl ?_
  intro q hq
  -- Replace `muSq` by `μ^2` and re-associate.
  have hμ : ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ) = ((μ q : ℂ) ^ 2) :=
    muSq_cast_eq_moebius_sq (q := q)
  -- Keep the right two factors fixed and rewrite the left factor.
  -- (Avoid `simp` rewriting products into disjunctions; explicit re-association is stable here.)
  calc
    ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))
        =
      ((μ q : ℂ) ^ 2)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) := by
          simpa [hμ, mul_assoc, mul_left_comm, mul_comm]

/--
Variant of `sigma_trunc_Q0_eq_sum_moebius_sq_phaseSum_neg` rewriting the reduced-residue phase sum
as `star (ramanujanSumC q N)`.

This is often the most convenient “σ-side” form when the major-arc main term naturally produces
`∑_{(a,q)=1} e(aN/q)` up to conjugation/sign.
-/
theorem sigma_trunc_Q0_eq_sum_moebius_sq_star_ramanujanSumC (N : ℕ) :
    ((AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ)
      =
    (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
      ((μ q : ℂ) ^ 2)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * star (ramanujanSumC q N)) := by
  classical
  rw [sigma_trunc_Q0_eq_sum_moebius_sq_phaseSum_neg (N := N)]
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hstar :
      star (ramanujanSumC q N) = ∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)) :=
    Goldbach.Cert.MajorArcStep24RamanujanBridge.star_ramanujanSumC (q := q) (N := N)
  set C : ℂ :=
    ((μ q : ℂ) ^ 2) * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
  change C * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) = C * star (ramanujanSumC q N)
  exact congrArg (fun z : ℂ => C * z) (by simpa using hstar.symm)

/--
The “expected” σ-side main term on the major arcs at height `Q0`, written in the `(μ/φ)^2` form
with a conjugated Ramanujan sum.

This is the exact finite expression that should appear after:
1) inserting the exponential-sum major-arc main terms into the quadratic integrand, and
2) summing over reduced residues `a (mod q)` with the phase `e(-aN/q)`.
-/
noncomputable def sigma_mainTerm_Q0C (N : ℕ) : ℂ :=
  (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
    ((μ q : ℂ) ^ 2)
      * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
      * star (ramanujanSumC q N))

/-!
### Convenience rewrites for the packaged main term

The definition `sigma_mainTerm_Q0C` uses the conjugated Ramanujan sum form.  When connecting to an
“analytic main term” extracted from a major-arc decomposition, it is often more convenient to use
the explicit reduced-residue phase sum `∑_{(r,q)=1} e(-(N*r)/q)`.
-/

theorem sigma_mainTerm_Q0C_eq_sum_muSq_star_ramanujanSumC (N : ℕ) :
    sigma_mainTerm_Q0C N
      =
    (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
      ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * star (ramanujanSumC q N)) := by
  classical
  unfold sigma_mainTerm_Q0C
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hμ : ((μ q : ℂ) ^ 2) = ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ) :=
    moebius_sq_cast_eq_muSq (q := q)
  simpa [hμ, mul_assoc, mul_left_comm, mul_comm]

theorem sigma_mainTerm_Q0C_eq_sum_muSq_phaseSum_neg (N : ℕ) :
    sigma_mainTerm_Q0C N
      =
    (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
      ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))) := by
  classical
  rw [sigma_mainTerm_Q0C_eq_sum_muSq_star_ramanujanSumC (N := N)]
  refine Finset.sum_congr rfl ?_
  intro q hq
  set C : ℂ :=
    ((AO_OffDiag.TailBlock.muSq q : ℝ) : ℂ)
      * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
  have hphase :
      star (ramanujanSumC q N) = ∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)) := by
    simpa using (phaseSum_neg_eq_star_ramanujanSumC (q := q) (N := N)).symm
  have hmul :
      C * star (ramanujanSumC q N) = C * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) := by
    exact congrArg (fun z : ℂ => C * z) hphase
  simpa [C, mul_assoc] using hmul

theorem sigma_mainTerm_Q0C_eq_sum_moebius_sq_phaseSum_neg (N : ℕ) :
    sigma_mainTerm_Q0C N
      =
    (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
      ((μ q : ℂ) ^ 2)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
        * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))) := by
  classical
  -- Termwise rewrite `star (ramanujanSumC q N)` as the explicit reduced-residue phase sum.
  unfold sigma_mainTerm_Q0C
  refine Finset.sum_congr rfl ?_
  intro q hq
  set C : ℂ := ((μ q : ℂ) ^ 2) * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
  have hphase :
      star (ramanujanSumC q N) = ∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)) := by
    simpa using (phaseSum_neg_eq_star_ramanujanSumC (q := q) (N := N)).symm
  have hmul :
      C * star (ramanujanSumC q N) = C * (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q))) := by
    exact congrArg (fun z : ℂ => C * z) hphase
  simpa [C, mul_assoc] using hmul

theorem sigma_mainTerm_Q0C_eq_sigma_trunc_Q0_via_muSq (N : ℕ) :
    sigma_mainTerm_Q0C N = ((AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ) := by
  rw [sigma_mainTerm_Q0C_eq_sum_muSq_phaseSum_neg (N := N)]
  simpa using (sigma_trunc_Q0_eq_sum_muSq_phaseSum_neg (N := N)).symm

theorem sigma_mainTerm_Q0C_eq_sigma_trunc_Q0 (N : ℕ) :
    sigma_mainTerm_Q0C N = ((AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ) := by
  simpa [sigma_mainTerm_Q0C] using
    (sigma_trunc_Q0_eq_sum_moebius_sq_star_ramanujanSumC (N := N)).symm

end

end MajorArcStep24MainTermIdentification
end Goldbach.Cert
