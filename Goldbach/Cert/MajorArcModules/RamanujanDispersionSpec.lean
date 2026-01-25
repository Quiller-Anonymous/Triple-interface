import Goldbach.Cert.MajorArcStep23RamanujanSum
import Mathlib.Analysis.Fourier.AddCircle

/-!
Project-neutral “Ramanujan dispersion” / orthogonality interfaces.

This file is intentionally *conventional* (textbook analytic number theory), and does not pin any
of the Goldbach project constants (`Q0`, `X0`, `H`, …).  It is meant as a home for axioms/interfaces
that can later be proved in Lean and then specialized inside Step 5 (ε₂-large TT*/Toeplitz).

The immediate use is to record the standard orthogonality of Ramanujan sums over a full period.
 -/

namespace Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec

open scoped BigOperators

open Goldbach.Cert.MajorArcStep23RamanujanSum

noncomputable section

/--
Ramanujan sum over reduced residues with an **integer** frequency.

This matches the reduced-residue convention used throughout the major-arc code (`Rcop q ⊆ {0,…,q-1}`),
and is the natural object that appears when taking Fourier coefficients in an `ℤ`-frequency variable.
-/
noncomputable def ramanujanSumZ (q : ℕ) (t : ℤ) : ℂ :=
  ∑ a ∈ Rcop q, Goldbach.Cert.MajorArcExponential.e ((a : ℝ) * (t : ℝ) / (q : ℝ))

lemma ramanujanSumZ_eq_sum (q : ℕ) (t : ℤ) :
    ramanujanSumZ q t =
      ∑ a ∈ Rcop q, Goldbach.Cert.MajorArcExponential.e ((a : ℝ) * (t : ℝ) / (q : ℝ)) := by
  rfl

/--
Conventional orthogonality of Ramanujan sums over one full period.

This is a textbook identity (finite Fourier orthogonality) and is the “dispersion mechanism”
that suppresses `q ≠ q'` cross terms *after averaging*, before taking absolute values.

We keep it as an interface here so that Step 5 can import it as a conventional-math ingredient
without pinning project parameters.
-/
structure RamanujanOrthogonality : Prop where
  /--
  For `q,q' ≥ 1` and `L = lcm q q'`, the reduced-residue character sums are orthogonal on
  `n ∈ {0,1,…,L-1}`.

  The `q=q'` case specializes to `∑_{n=0}^{q-1} c_q(n)^2 = q * φ(q)`.
  -/
  ortho :
    ∀ {q q' : ℕ}, 1 ≤ q → 1 ≤ q' →
      let L : ℕ := Nat.lcm q q'
      (Finset.sum (Finset.range L) (fun n =>
          (ramanujanSumC q n) * star (ramanujanSumC q' n)))
        =
      if q = q' then (q * Nat.totient q : ℂ) else 0

/--
Conventional pointwise bound for Ramanujan sums by the gcd.

This is a standard textbook inequality:
`|c_q(N)| ≤ gcd(q,N)`.

We state it for the project’s `ramanujanSumC` so it can be reused in both the σ-side and the
Step-5 TT*/Toeplitz analysis.
-/
structure RamanujanGcdBound : Prop where
  bound :
    ∀ (q N : ℕ), ‖ramanujanSumC q N‖ ≤ (Nat.gcd q N : ℝ)

/--
Project-neutral “band-limited dispersion” inequality for Ramanujan sums.

This is the schematic analytic instrument used in Step 5 (ε₂-large TT*/Toeplitz) to suppress
`q ≠ q'` cross terms *after squaring/averaging in the frequency variable*, without taking absolute
values inside the `q`-sum.

We state it on an arbitrary finite band `S : Finset ℤ` and a generic weight function
`b : ℕ → ℤ → ℂ` (the intended specialization is the Ramanujan–sinc factor for hard major arcs).
-/
structure RamanujanBandDispersion (Cdisp : ℝ) : Prop where
  disp :
    ∀ {S : Finset ℤ} {Q : ℕ} (b : ℕ → ℤ → ℂ),
      (∑ t ∈ S,
          ‖∑ q ∈ Finset.Icc 1 Q, (ramanujanSumZ q t) * (b q t)‖ ^ 2)
        ≤
      Cdisp *
        (∑ q ∈ Finset.Icc 1 Q, ∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2))

end

end Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec
