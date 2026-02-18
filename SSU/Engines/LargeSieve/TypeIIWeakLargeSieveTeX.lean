import SSU.Engines.LargeSieve.MontgomeryVaughanTypeII
import SSU.Engines.LargeSieve.TypeIIStep34CombineTeX

/-!
Weak (geometry-only) TeX Step 3/4/5 instances for the Type–II large-sieve interfaces.

This file is **plumbing**:
it turns the deterministic Cauchy–Schwarz + cardinality surrogates
(`Step3MontgomeryVaughan.of_box_geometry`, `Step4MontgomeryVaughan.of_box_geometry`)
into actual `Step3LargeSieveOuterU` / `Step4LargeSieveOuterV` objects, and then combines them
into `Step34LargeSieveTeX`.

It is not TeX-strength: the resulting constants are much larger than the displayed ones in
`05b_SSU.tex`.  The point is to keep the SSU heart wiring runnable end-to-end while the real MV
large sieve specializations are under construction.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

/-!
## Step 3: geometry-only → `Step3LargeSieveOuterU`
-/

/-- Build a weak `Step3LargeSieveOuterU` instance from the geometry-only Step 3 surrogate. -/
def step3LargeSieveOuterU_of_box_geometry
    (td : TubeData)
    (hDq : 1 ≤ td.D / (td.q : ℝ)) (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) :
    Step3LargeSieveOuterU td :=
by
  classical
  -- Geometry-only MV surrogate (Cauchy–Schwarz + `card(zSet)` bounds).
  let hMV : Step3MontgomeryVaughan td :=
    Step3MontgomeryVaughan.of_box_geometry (td := td) (hDq := hDq) (hD := hD) (hU := hU) (hX := hX)
  -- Convert MV-shape to the Step 3 “fiber” interface.
  let hFiber : Step3FiberLargeSieve td :=
    step3FiberLargeSieve_of_montgomeryVaughan (td := td) (hMV := hMV) (by simpa using hD)
      (by
        -- `0 ≤ U` follows from `1 ≤ U`.
        have : (0 : ℝ) ≤ td.U := le_trans (by linarith) hU
        simpa using this)
      (by simpa using hX)
  -- Deterministic Cauchy–Schwarz outer-`u` reduction.
  exact step3OuterU_of_fiberLargeSieve (td := td) hFiber

/-!
## Step 4: geometry-only → `Step4LargeSieveOuterV`
-/

/-- Build a weak `Step4LargeSieveOuterV` instance from the geometry-only Step 4 surrogate. -/
def step4LargeSieveOuterV_of_box_geometry
    (td : TubeData)
    (hU : 0 ≤ td.U) (hX : 0 ≤ td.X) (hD1 : 1 ≤ td.D) (hXH1 : 1 ≤ td.X * td.H) :
    Step4LargeSieveOuterV td :=
by
  classical
  let hMV : Step4MontgomeryVaughan td :=
    Step4MontgomeryVaughan.of_box_geometry (td := td) (hU := hU) (hX := hX) (hD1 := hD1) (hXH1 := hXH1)
  let hFiber : Step4FiberLargeSieve td :=
    step4FiberLargeSieve_of_montgomeryVaughan (td := td) (hMV := hMV)
      (by
        -- `0 ≤ D` follows from `1 ≤ D`.
        have : (0 : ℝ) ≤ td.D := le_trans (by linarith) hD1
        simpa using this)
      hU
      hX
  exact step4OuterV_of_fiberLargeSieve (td := td) hFiber

/-!
## Step 5: combine weak Step 3/4 into a weak `Step34LargeSieveTeX`
-/

/-- Combine the weak Step 3/4 instances into a weak `Step34LargeSieveTeX`. -/
def step34LargeSieveTeX_of_box_geometry
    (td : TubeData)
    (hDq : 1 ≤ td.D / (td.q : ℝ)) (hD : 0 ≤ td.D) (hU1 : 1 ≤ td.U) (hX : 0 ≤ td.X)
    (hU0 : 0 ≤ td.U) (hD1 : 1 ≤ td.D) (hXH1 : 1 ≤ td.X * td.H) :
    Step34LargeSieveTeX td :=
by
  -- Build weak Step 3 and Step 4 objects, then combine by the existing TeX combiner.
  let h3 : Step3LargeSieveOuterU td :=
    step3LargeSieveOuterU_of_box_geometry (td := td) (hDq := hDq) (hD := hD) (hU := hU1) (hX := hX)
  let h4 : Step4LargeSieveOuterV td :=
    step4LargeSieveOuterV_of_box_geometry (td := td) (hU := hU0) (hX := hX) (hD1 := hD1) (hXH1 := hXH1)
  -- The combiner expects strict positivity of `D,U` and nonnegativity of `X`.
  have hDpos : 0 < td.D := lt_of_lt_of_le (by linarith) hD1
  have hUpos : 0 < td.U := lt_of_lt_of_le (by linarith) hU1
  have hX0 : 0 ≤ td.X := hX
  exact step34LargeSieveTeX_of_step3_step4 (td := td) h3 h4 hDpos hUpos hX0

end

end LargeSieve
end TypeII
end Engines
end SSU
