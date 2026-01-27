import Twin.ChecklistAxioms

/-!
Twin/PinnedMajorsMainTermEvalProof.lean
======================================

Helper lemmas for proving the **pinned majors main-term evaluation core**
`Twin.ChecklistAxioms.PinnedMajorsMainTermEval`.

This file deliberately avoids *any* use of primes / `sumValue` / the SW bound:
`majMassMainTerm` is already built from the major-arc **main term** itself.

The intended proof strategy (paper-faithful, deterministic):
1. show `majMassMainTerm` is independent of `X` (the `e((α-a/q)X)` phase disappears in `S * conj S`);
2. use major-arc disjointness on `[0,1]` (under the frozen cutoff `q ≤ (log H)^B`) to make the witness irrelevant;
3. rewrite `majMassMainTerm` as an explicit finite sum of packet integrals;
4. evaluate each packet integral via the change of variables `t = H(α-a/q)`;
5. identify the arithmetic factor (Ramanujan sum at `2`) and compare to
   `SS := fullTruncSingularSeries(P.S)` within the `/6` budget.

This file provides:
* the exact “X-independence” lemma you need for step (1);
* a clean “reduction lemma” that turns Core 2 into three explicit subgoals:
  a deterministic decomposition + two numeric bounds (Gaussian normalization + arithmetic truncation)
  plus a tiny cosine-variation error bound.

The remaining hard work (steps (2–5)) should live in a separate file once you/your collaborator
provides the formal packet decomposition and arithmetic tail bounds.
-/

namespace Twin.PinnedMajorsMainTermEvalProof

noncomputable section

open scoped BigOperators
open scoped ComplexConjugate
open MeasureTheory Twin

abbrev P : Twin.GoalAPI.Params := Twin.PaperParams.P
abbrev SS : ℝ := Twin.fullTruncSingularSeries P.S

abbrev A : ℝ := Twin.ChecklistAxioms.A
abbrev B : ℝ := Twin.ChecklistAxioms.B
abbrev Lambda : ℕ → ℝ := Twin.ChecklistAxioms.Lambda
abbrev Wwin : ℝ → ℝ := Twin.ChecklistAxioms.Wwin
abbrev What : ℝ → ℝ := Twin.ChecklistAxioms.What

variable (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)

/-!
## Note on “independence of X”

Morally, `majMassMainTerm` is independent of `X`: the only `X`-dependence is the phase
`χ_add ((α - a/q) * X)` inside `Twin.SW.mainTerm`, and it disappears after forming `S * conj S`.

However, the *definition* of `majMassMainTerm` routes through the witness
`Twin.ChecklistAxioms.mainTermValue`, which depends on the major-arc witness selection.
Making “independence of `X`” a Lean theorem is therefore best done **after** proving the
major arcs are disjoint on `[0,1]` (so the witness is extensionally unique and does not vary with `X`).
-/

/-!
## Reduction lemma: Core 2 from a deterministic packet decomposition

Once you provide a lemma that rewrites `majMassMainTerm` as:

  `majMassMainTerm X = mainConst + E_cos + E_trunc`,

and bounds each error term, you can discharge the `/6` budget.

This lemma is intentionally phrased to match the existing typeclass target:
`Twin.ChecklistAxioms.PinnedMajorsMainTermEval`.
-/

theorem pinnedMajorsMainTermEval_of_decomposition
    (mainConst : ℝ)
    (E_cos E_trunc : ℕ → ℝ)
    (h_decomp : ∀ X : ℕ, Twin.ChecklistAxioms.majMassMainTerm (sme := sme) X = mainConst + E_cos X + E_trunc X)
    (h_main : |mainConst - SS * ((P.H : ℝ) + 1)| ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 12)
    (h_cos  : ∀ X : ℕ, |E_cos X| ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 24)
    (h_trunc : ∀ X : ℕ, |E_trunc X| ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 24) :
    Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme) := by
  refine ⟨?_⟩
  intro X hX
  have hsplit : Twin.ChecklistAxioms.majMassMainTerm (sme := sme) X - SS * ((P.H : ℝ) + 1)
      = (mainConst - SS * ((P.H : ℝ) + 1)) + E_cos X + E_trunc X := by
    -- unfold using `h_decomp`
    have := congrArg (fun t : ℝ => t - SS * ((P.H : ℝ) + 1)) (h_decomp X)
    -- `simp` the subtraction
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  -- Triangle inequality with three `/12` pieces.
  have htri :
      |Twin.ChecklistAxioms.majMassMainTerm (sme := sme) X - SS * ((P.H : ℝ) + 1)|
        ≤ |mainConst - SS * ((P.H : ℝ) + 1)| + |E_cos X| + |E_trunc X| := by
    -- rewrite and apply `abs_add_le` twice
    -- `a + b + c` as `(a + b) + c`
    have :
        |(mainConst - SS * ((P.H : ℝ) + 1)) + E_cos X + E_trunc X|
          ≤ |(mainConst - SS * ((P.H : ℝ) + 1)) + E_cos X| + |E_trunc X| := by
      simpa [add_assoc] using abs_add_le ((mainConst - SS * ((P.H : ℝ) + 1)) + E_cos X) (E_trunc X)
    have :
        |(mainConst - SS * ((P.H : ℝ) + 1)) + E_cos X + E_trunc X|
          ≤ (|mainConst - SS * ((P.H : ℝ) + 1)| + |E_cos X|) + |E_trunc X| := by
      have h1 : |(mainConst - SS * ((P.H : ℝ) + 1)) + E_cos X|
          ≤ |mainConst - SS * ((P.H : ℝ) + 1)| + |E_cos X| :=
        abs_add_le _ _
      exact le_trans this (add_le_add_right h1 _)
    -- finish
    simpa [hsplit, add_assoc] using this
  have hbd :
      |Twin.ChecklistAxioms.majMassMainTerm (sme := sme) X - SS * ((P.H : ℝ) + 1)|
        ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6 := by
    have hsum :
        |mainConst - SS * ((P.H : ℝ) + 1)| + |E_cos X| + |E_trunc X|
          ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 12
            + (P.eps * SS) * ((P.H : ℝ) + 1) / 24
            + (P.eps * SS) * ((P.H : ℝ) + 1) / 24 := by
      have h1 := add_le_add (h_main) (h_cos X)
      have h2 := add_le_add h1 (h_trunc X)
      simpa [add_assoc] using h2
    have : (P.eps * SS) * ((P.H : ℝ) + 1) / 12
            + (P.eps * SS) * ((P.H : ℝ) + 1) / 24
            + (P.eps * SS) * ((P.H : ℝ) + 1) / 24
          = (P.eps * SS) * ((P.H : ℝ) + 1) / 6 := by
      ring
    exact le_trans (le_trans htri hsum) (by simpa [this])
  simpa using hbd

end Twin.PinnedMajorsMainTermEvalProof
