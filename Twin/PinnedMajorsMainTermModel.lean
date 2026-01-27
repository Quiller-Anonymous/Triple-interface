import Twin.ChecklistAxioms

/-!
`PinnedMajorsMainTermEval` via a deterministic model (Core 2)
============================================================

This file provides a *decomposed* route to the core pinned-major main-term evaluation:

* `Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme)`

The intent is:
1. express `majMassMainTerm` as an explicit model quantity built only from the SW main term
   (no primes, no `sumValue`, no minor arcs),
2. reduce the core inequality to two numeric/elementary analytic bounds:
   - an arithmetic factor is close to `SS := fullTruncSingularSeries P.S`,
   - a Gaussian packet integral is close to the normalization `(H+1)/H`.

In the current repository state we package (1)+(2) as a single “conventional” hypothesis
`PinnedMajorsMainTermModel`.  The downstream pipeline then uses a short, fully formal
algebraic wrapper to produce `PinnedMajorsMainTermEval`.

Paper-facing guidance for proving the model:
* major arcs are frozen at `q ≤ (log H)^B` and width `δ/(H+1)`,
* the model is a finite sum of packet integrals after disjointness,
* the packet integral is an explicit Gaussian integral (with a tiny `cos(4π t/H)` phase),
* the arithmetic factor is a truncated Ramanujan/μ/φ sum at shift `2`.
-/

namespace Twin.ChecklistAxioms

noncomputable section

open Twin
open scoped BigOperators
open MeasureTheory

variable (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)

/-!
### Explicit model quantities

These are *definitions only*; they are meant to pin down the exact objects a mathematician
should estimate when proving Core 2 against the current Lean definitions.
-/

noncomputable def QNat (_sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) : ℕ :=
  Nat.floor (Real.rpow (Real.log (P.H : ℝ)) B)

noncomputable def ramanujanSumAtTwo (_sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) (q : ℕ) : ℂ :=
  (Finset.range q).sum fun a =>
    if Nat.Coprime a q then Twin.SW.χ_add (-2 * (a : ℝ) / (q : ℝ)) else 0

noncomputable def arithFactor (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) : ℝ :=
  (Finset.Icc 1 (QNat sme)).sum fun q =>
    (Twin.SW.muOverPhi q) ^ 2 * (ramanujanSumAtTwo sme q).re

noncomputable def tMax (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) : ℝ :=
  (P.H : ℝ) * sme.δ / ((P.H : ℝ) + 1)

noncomputable def packetIntegralCos (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) : ℝ :=
  ∫ t in Set.Icc (-(tMax sme)) (tMax sme),
    |What t| ^ 2 * Real.cos (4 * Real.pi * (t / (P.H : ℝ)))

/-!
### Conventional model hypothesis

`PinnedMajorsMainTermModel` is intended to be *textbook-level* analytic number theory + harmonic
analysis on explicit Gaussians, specialized to the frozen model and the concrete paper parameters.

Once this is proved, the core typeclass `PinnedMajorsMainTermEval` becomes a lemma.
-/

class PinnedMajorsMainTermModel : Prop where
  /-- Deterministic evaluation: `majMassMainTerm` equals the explicit model mass
  `H * packetIntegralCos * arithFactor`.

  Paper guide: disjoint major arcs on `[0,1]`, rewrite the witness-based selection into a finite
  `∑_{q≤Q} ∑_{(a,q)=1}` of packet integrals, change variables `t = H(α-a/q)`, and sum over
  numerators (Ramanujan sum at `2`). -/
  majMassMainTerm_eq :
    ∀ X : ℕ,
      majMassMainTerm (sme := sme) X
        = (P.H : ℝ) * packetIntegralCos sme * arithFactor sme

  /-- Arithmetic factor matches `SS := fullTruncSingularSeries P.S` up to a small absolute error.

  Paper guide: Euler-product evaluation of the `μ/φ` Ramanujan factor at shift `2` and a tail bound
  for the truncation `q ≤ ⌊(log H)^B⌋`. -/
  arithFactor_close :
    |arithFactor sme - SS|
      ≤ (P.eps * SS) / 24

  /-- Gaussian packet integral normalization: `H * packetIntegralCos ≈ H+1`.

  Paper guide: monotonicity of the Gaussian and the fact that the packet half-width is
  `tMax = H*δ/(H+1)` with `δ = 1/200` (so the truncated integral is very close to the full mass). -/
  packetIntegralCos_close :
    |(P.H : ℝ) * packetIntegralCos sme - ((P.H : ℝ) + 1)|
      ≤ P.eps * ((P.H : ℝ) + 1) / 24

/-!
### From the model hypothesis to the core typeclass
-/

theorem pinnedMajorsMainTermEval_of_model
    [PinnedMajorsMainTermModel (sme := sme)] :
    PinnedMajorsMainTermEval (sme := sme) := by
  classical
  refine ⟨?_⟩
  intro X _hX
  -- abbreviate constants
  set H : ℝ := (P.H : ℝ)
  set N : ℝ := H + 1
  have hN : 0 ≤ N := by
    have hH' : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
    have hH : 0 ≤ H := by simpa [H] using hH'
    simpa [N] using add_nonneg hH (by norm_num : (0 : ℝ) ≤ 1)
  have hSS : 0 ≤ SS :=
    Twin.fullTruncSingularSeries_nonneg_of_ge_three (S := P.S) P.S_ge_three
  have hSSabs : |SS| = SS := abs_of_nonneg hSS
  have heps0 : 0 ≤ P.eps := le_of_lt P.eps_pos

  -- unpack the model equations/bounds
  have hEq :=
    PinnedMajorsMainTermModel.majMassMainTerm_eq (sme := sme) X
  have hAr :=
    PinnedMajorsMainTermModel.arithFactor_close (sme := sme)
  have hJ :=
    PinnedMajorsMainTermModel.packetIntegralCos_close (sme := sme)

  -- triangle inequality through `SS * (H * packetIntegralCos)`
  set HJ : ℝ := H * packetIntegralCos sme
  have hSplit :
      HJ * arithFactor sme - SS * N
        =
      HJ * (arithFactor sme - SS) + SS * (HJ - N) := by
    -- `HJ*ar - SS*N = HJ*(ar-SS) + SS*(HJ-N)`
    -- (add and subtract `HJ*SS`)
    ring

  have hTri :
      |HJ * arithFactor sme - SS * N|
        ≤ |HJ| * |arithFactor sme - SS| + |SS| * |HJ - N| := by
    calc
      |HJ * arithFactor sme - SS * N|
          = |HJ * (arithFactor sme - SS) + SS * (HJ - N)| := by
              simpa [hSplit]
      _ ≤ |HJ * (arithFactor sme - SS)| + |SS * (HJ - N)| := by
              simpa using
                (abs_add_le (HJ * (arithFactor sme - SS)) (SS * (HJ - N)))
      _ = |HJ| * |arithFactor sme - SS| + |SS| * |HJ - N| := by
              simp [abs_mul, mul_assoc, mul_left_comm, mul_comm]

  -- bound `|HJ|` by `N + |HJ - N|`
  have hHJ_le : |HJ| ≤ N + |HJ - N| := by
    -- `HJ = N + (HJ - N)`
    have : HJ = N + (HJ - N) := by ring
    have habs : |HJ| = |N + (HJ - N)| :=
      congrArg (fun t : ℝ => |t|) this
    calc
      |HJ| = |N + (HJ - N)| := habs
      _ ≤ |N| + |HJ - N| := by simpa using abs_add_le N (HJ - N)
      _ = N + |HJ - N| := by simp [abs_of_nonneg hN]

  -- apply the two model error budgets
  have hAr' : |arithFactor sme - SS| ≤ (P.eps * SS) / 24 := by
    simpa [sub_eq_add_neg] using hAr
  have hJ' : |HJ - N| ≤ P.eps * N / 24 := by
    -- `HJ = H * packetIntegralCos`, `N = H+1`
    simpa [HJ, H, N, mul_assoc, mul_comm, mul_left_comm] using hJ

  -- combine everything into the `/6` allowance with slack
  have hBound :
      |HJ * arithFactor sme - SS * N|
        ≤ (P.eps * SS) * N / 6 := by
    -- from `hTri`, `hHJ_le`, and the two budgets
    have h1 :
        |HJ * arithFactor sme - SS * N|
          ≤ (N + |HJ - N|) * ((P.eps * SS) / 24) + SS * (P.eps * N / 24) := by
      have h2 : |HJ| * |arithFactor sme - SS| ≤ (N + |HJ - N|) * ((P.eps * SS) / 24) := by
        have h0 : 0 ≤ |arithFactor sme - SS| := abs_nonneg _
        have hN' : 0 ≤ N + |HJ - N| := add_nonneg hN (abs_nonneg _)
        calc
          |HJ| * |arithFactor sme - SS|
              ≤ (N + |HJ - N|) * |arithFactor sme - SS| := by
                  exact mul_le_mul_of_nonneg_right hHJ_le h0
          _ ≤ (N + |HJ - N|) * ((P.eps * SS) / 24) := by
                  exact mul_le_mul_of_nonneg_left hAr' hN'
      have h3 : |SS| * |HJ - N| ≤ SS * (P.eps * N / 24) := by
        have : |SS| * |HJ - N| = SS * |HJ - N| := by simpa [hSSabs]
        -- use `|HJ-N|` budget and `SS ≥ 0`
        calc
          |SS| * |HJ - N|
              = SS * |HJ - N| := this
          _ ≤ SS * (P.eps * N / 24) := by
              exact mul_le_mul_of_nonneg_left hJ' hSS
      exact le_trans hTri (by linarith [h2, h3])
    -- expand and compare to `/6`
    have h4 :
        (N + |HJ - N|) * ((P.eps * SS) / 24) + SS * (P.eps * N / 24)
          ≤ (P.eps * SS) * N / 6 := by
      -- Use `|HJ-N| ≤ eps*N/24` and `SS ≥ 0`, `N ≥ 0`.
      have hHJ' : N + |HJ - N| ≤ N + (P.eps * N / 24) := by
        exact add_le_add_left hJ' N
      have h5 :
          (N + |HJ - N|) * ((P.eps * SS) / 24)
            ≤ (N + (P.eps * N / 24)) * ((P.eps * SS) / 24) := by
        have hnonneg : 0 ≤ (P.eps * SS) / 24 := by
          have : 0 ≤ P.eps * SS := mul_nonneg heps0 hSS
          nlinarith
        exact mul_le_mul_of_nonneg_right hHJ' hnonneg
      -- Now it's pure algebra with plenty of slack: we only use `eps ≤ 1`.
      have heps1 : P.eps ≤ 1 := by
        have : P.eps < 1 := lt_of_lt_of_le P.eps_lt_half (by norm_num : (1 : ℝ) / 2 ≤ 1)
        exact le_of_lt this
      -- bound `N + eps*N/24 ≤ (25/24)*N`
      have hN_eps : N + (P.eps * N / 24) ≤ (25 / 24 : ℝ) * N := by
        have hterm : P.eps * N / 24 ≤ N / 24 := by
          -- multiply `eps ≤ 1` by the nonnegative constant `N/24`
          have hN24 : 0 ≤ N / 24 := by nlinarith [hN]
          have : P.eps * (N / 24) ≤ 1 * (N / 24) := by
            exact mul_le_mul_of_nonneg_right heps1 hN24
          simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using this
        -- `N + (eps*N/24) ≤ N + (N/24) = (25/24)*N`
        nlinarith [hterm]
      have hmain :
          (N + (P.eps * N / 24)) * ((P.eps * SS) / 24) + SS * (P.eps * N / 24)
            ≤ (P.eps * SS) * N / 6 := by
        set E : ℝ := P.eps * SS
        have hE_nonneg : 0 ≤ E := mul_nonneg heps0 hSS
        have hE24 : 0 ≤ E / 24 := by nlinarith [hE_nonneg]
        have hfirst :
            (N + (P.eps * N / 24)) * (E / 24) ≤ ((25 / 24 : ℝ) * N) * (E / 24) := by
          exact mul_le_mul_of_nonneg_right hN_eps hE24
        have hsum :
            ((25 / 24 : ℝ) * N) * (E / 24) + SS * (P.eps * N / 24)
              = (49 / 576 : ℝ) * (E * N) := by
          -- `SS * (eps*N/24) = (eps*SS) * N / 24 = E*N/24`
          simp [E, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
          ring
        have hcoef : (49 / 576 : ℝ) ≤ (1 / 6 : ℝ) := by norm_num
        have hEN : 0 ≤ E * N := mul_nonneg hE_nonneg hN
        have hmainE :
            (N + (P.eps * N / 24)) * (E / 24) + SS * (P.eps * N / 24) ≤ E * N / 6 := by
          calc
            (N + (P.eps * N / 24)) * (E / 24) + SS * (P.eps * N / 24)
                ≤ ((25 / 24 : ℝ) * N) * (E / 24) + SS * (P.eps * N / 24) := by
                    exact add_le_add_right hfirst _
            _ = (49 / 576 : ℝ) * (E * N) := by simpa using hsum
            _ ≤ (1 / 6 : ℝ) * (E * N) := by
                    exact mul_le_mul_of_nonneg_right hcoef hEN
            _ = E * N / 6 := by simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
        -- rewrite back from `E`
        simpa [E, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmainE
      -- apply `h5` then `hmain`
      have h6 :
          (N + |HJ - N|) * ((P.eps * SS) / 24) + SS * (P.eps * N / 24)
            ≤ (N + (P.eps * N / 24)) * ((P.eps * SS) / 24) + SS * (P.eps * N / 24) := by
        exact add_le_add_right h5 _
      exact le_trans h6 (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmain)
    exact le_trans h1 h4

  -- reassemble the target and use the repo's `/6` normalization
  -- `SS * ((P.H:ℝ)+1)` is `SS * N`
  -- start by rewriting `majMassMainTerm` via the model identity
  -- (this is where the `X`-dependence is removed)
  have :
      |majMassMainTerm (sme := sme) X - SS * N|
        ≤ (P.eps * SS) * N / 6 := by
    -- rewrite `majMassMainTerm` using the model identity
    simpa [H, N, HJ, hEq, mul_assoc, mul_comm, mul_left_comm] using hBound
  simpa [H, N, mul_assoc, mul_comm, mul_left_comm] using this

-- Make the core evaluation available automatically once the model package is available.
instance instPinnedMajorsMainTermEval_of_model
    (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
    [PinnedMajorsMainTermModel (sme := sme)] :
    PinnedMajorsMainTermEval (sme := sme) :=
  pinnedMajorsMainTermEval_of_model (sme := sme)

end

end Twin.ChecklistAxioms
