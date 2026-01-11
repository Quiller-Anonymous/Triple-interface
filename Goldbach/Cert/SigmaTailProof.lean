import Goldbach.Cert.SigmaTailAxiomsFun
import Goldbach.Cert.SigmaTailExplicitBoundFun

/-!
σ-tail checkpoint (honest).

The repo contains a *specification layer* for a Tenor-shaped σ-tail statement
(`Goldbach/Cert/SigmaTailAxiomsFun.lean`), but the canonical FunX Goldbach pipeline does **not**
depend on any σ-tail axiom: it uses the explicit-majorant route plus a conservative real bound.

What we have proved so far is different (but still useful):

* An axiom-free **explicit majorant** for `|sigmaTail Q N|`, derived from reindexing plus an
  auxiliary Euler-tail estimate. This bound is expressed as an explicit finite sum over (squarefree)
  divisors of `N`, and is therefore computable/inspectable for concrete `Q,N`.

This file is intentionally small: it exposes the proved explicit bound with a stable name and
documents the remaining gap (deriving a *uniform* `K_tail / Q` bound requires additional structure
and cannot be obtained by blindly majorizing by absolute values).
-/

namespace Goldbach.Cert.SigmaTailProof

open Goldbach.AO_OffDiag.SigmaTailReindexFun

/--
Explicit, axiom-free upper bound on `|sigmaTail Q N|` (finite divisor sum).

This is a diagnostic statement: it does not yet imply a uniform constant independent of `N`.
-/
theorem sigmaTail_abs_le_explicit_majorant (Q N : ℕ) (hN0 : N ≠ 0) :
    |sigmaTail Q N|
      ≤
    (((Nat.divisors N).filter Squarefree).sum (fun d =>
        ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹ *
          (if h : 1 ≤ Q / d then
            ENNReal.ofReal ((90 : ℝ) / ((Q / d : ℕ) : ℝ))
          else
            ENNReal.ofReal (91 : ℝ)))).toReal :=
  Goldbach.Cert.SigmaTailExplicitBoundFun.sigmaTail_abs_le_explicit (Q := Q) (N := N) hN0

end Goldbach.Cert.SigmaTailProof
