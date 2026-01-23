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

end

end Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec
