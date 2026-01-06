import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.VonMangoldt

/-!
Orthodox “Siegel–Walfisz” axioms (textbook-facing).

This file is intentionally *project-agnostic*: it does not mention `P_BG`, `Pref`, kernels, or any
Goldbach-specific bank notation. The intent is that any project-specific “major arc swap” bound
should be derived as a corollary from these axioms plus routine bookkeeping.

We record a standard Prime-Number-Theorem-in-arithmetic-progressions (Siegel–Walfisz) statement for
the Chebyshev `ψ`-function with von Mangoldt weights:

  ψ(x; q, a) = x / φ(q) + O_A(x / (log x)^A)

uniformly for `q ≤ (log x)^A` and `(a,q)=1`.

This is the conventional analytic input typically used to justify major-arc evaluations.
-/

namespace Goldbach.Cert.SiegelWalfisz

noncomputable section

private def ΛVM (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ)

/-- Chebyshev `ψ(x; q, a)` with von Mangoldt weight, as a finite sum over `n ≤ x`. -/
noncomputable def psi (x q a : ℕ) : ℝ :=
  Finset.sum (Finset.range (x + 1)) (fun n =>
    if Nat.ModEq q n a then ΛVM n else 0)

/--
Siegel–Walfisz (PNT in arithmetic progressions), in a standard “uniform error” form.

This is meant to be a *textbook* analytic axiom; project-specific major-arc consequences should be
proved from it.
-/
axiom siegelWalfisz_psi :
  ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ ⦃x q a : ℕ⦄,
      3 ≤ x →
      1 ≤ q →
      Nat.Coprime a q →
      (q : ℝ) ≤ (Real.log (x : ℝ)) ^ A →
      |psi x q a - (x : ℝ) / (Nat.totient q : ℝ)|
        ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ A

/--
Packaged Siegel–Walfisz `ψ`-bound at a fixed exponent `A`.

This is a small “interface” object: later files can assume `PsiBound A` (or build it from
`siegelWalfisz_psi`) without repeatedly unpacking an existential.
-/
structure PsiBound (A : ℕ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ⦃x q a : ℕ⦄,
      3 ≤ x →
      1 ≤ q →
      Nat.Coprime a q →
      (q : ℝ) ≤ (Real.log (x : ℝ)) ^ A →
      |psi x q a - (x : ℝ) / (Nat.totient q : ℝ)|
        ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ A

/-- Build the fixed-`A` interface from the textbook axiom. -/
noncomputable def psiBound (A : ℕ) : PsiBound A := by
  classical
  -- `siegelWalfisz_psi A` lives in `Prop`, so we use classical choice to extract the witness.
  let ex : ∃ C : ℝ, 0 ≤ C ∧
      ∀ ⦃x q a : ℕ⦄,
        3 ≤ x →
        1 ≤ q →
        Nat.Coprime a q →
        (q : ℝ) ≤ (Real.log (x : ℝ)) ^ A →
        |psi x q a - (x : ℝ) / (Nat.totient q : ℝ)|
          ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ A := siegelWalfisz_psi A
  refine ⟨Classical.choose ex, ?_, ?_⟩
  · exact (Classical.choose_spec ex).1
  · exact (Classical.choose_spec ex).2

end

end Goldbach.Cert.SiegelWalfisz
