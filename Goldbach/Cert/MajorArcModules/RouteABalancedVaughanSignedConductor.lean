import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanTypeIInterface

/-!
# Signed-conductor interface for the balanced Vaughan Type-I term

The maximal Bombieri--Vinogradov norm recorded in
`RouteABalancedVaughanTypeIInterface` is a sufficient analytic input, but it takes absolute values
before using the outer Mobius coefficient. A conductor-grouped argument should instead preserve
the signed sum over moduli.

This file records that narrower route without asserting the missing character estimates. It proves
the exact signed partial-summation identity and shows that a bound on this expression populates the
existing coprime-progression interface. The remaining conductor decomposition and explicit
analytic estimates stay visible as hypotheses rather than project axioms.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor

open ArithmeticFunction
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanTypeIInterface

noncomputable section

/--
The exact Mobius-signed partial-summation expression. Unlike a sum of per-modulus absolute values,
this retains the cancellation that a primitive-conductor regrouping is meant to exploit.
-/
noncomputable def balancedVaughanTypeISignedCoprimePartialSummationError
    (L N u : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) (N - L) *
          balancedVaughanTypeILogWeight N d (N - L)
        - Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) (L - 1) *
          balancedVaughanTypeILogWeight N d (L - 1)
        - ∑ n ∈ Finset.Ico (L - 1) (N - L),
            Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) n *
              (balancedVaughanTypeILogWeight N d (n + 1)
                - balancedVaughanTypeILogWeight N d n))

/--
The signed partial-summation expression is exactly the named coprime progression error. This is the
formal point at which the stronger modulus-by-modulus triangle inequality can be avoided.
-/
theorem balancedVaughanTypeISignedCoprimePartialSummationError_eq
    {L N u : ℕ} (hLU : L ≤ N - L) (hL : 0 < L) :
    balancedVaughanTypeISignedCoprimePartialSummationError L N u
      = balancedVaughanTypeICoprimeProgressionError L N u := by
  unfold balancedVaughanTypeISignedCoprimePartialSummationError
    balancedVaughanTypeICoprimeProgressionError
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [balancedVaughanTypeICoprimeModulusError_eq_partialSummation hLU hL]

/--
The finite Mobius/totient sum whose cancellation is retained after grouping induced characters by
primitive conductor.
-/
noncomputable def signedMoebiusTotientPartialSum (m X : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 X).filter (Nat.Coprime m),
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (Nat.totient k : ℝ)

/--
The elementary arithmetic lemma proposed for the conductor route. It is deliberately a `Prop`, not
an axiom or an asserted theorem: proving it is the first independent gate for that route.
-/
def SignedMoebiusTotientSixBound : Prop :=
  ∀ m X : ℕ, 0 < m →
    |signedMoebiusTotientPartialSum m X|
      ≤ 6 * (m : ℝ) / (Nat.totient m : ℝ)

/--
Discrete version of the proposed primitive-conductor weight. The cutoff `d ≤ N - t` makes every
active logarithm have nonnegative argument ratio when `d` is positive. No claim relating this
weight to Dirichlet characters is made here.
-/
noncomputable def balancedVaughanTypeIConductorWeight
    (N u r t : ℕ) : ℝ :=
  ∑ d ∈ ((Finset.Icc 1 u).filter (Nat.Coprime N)).filter
      (fun d => r ∣ d ∧ d ≤ N - t),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
      (Nat.totient d : ℝ) * Real.log ((N - t) / d)

/--
Narrow analytic input for the actual signed coprime aggregate. This is weaker than an unrestricted
maximal Bombieri--Vinogradov norm and is the intended target of a conductor-grouped proof.
`window_nonempty` keeps the exact discrete partial-summation formula applicable.
-/
structure EffectiveSignedConductorTypeIInput
    (L Xmin : ℕ) (u : ℕ → ℕ) (bound : ℕ → ℝ) : Prop where
  support_lower : 2 ≤ L
  window_nonempty : ∀ {N : ℕ}, Xmin ≤ N → L ≤ N - L
  signed_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |balancedVaughanTypeISignedCoprimePartialSummationError L N (u N)| ≤ bound N

/--
A completed signed-conductor estimate supplies the pre-existing coprime progression obligation.
All downstream Type-I and fixed-center recombination theorems can therefore be reused unchanged.
-/
theorem coprimeProgressionErrorBound_of_signedConductorInput
    {L Xmin : ℕ} {u : ℕ → ℕ} {bound : ℕ → ℝ}
    (hSigned : EffectiveSignedConductorTypeIInput L Xmin u bound) :
    BalancedVaughanTypeICoprimeProgressionErrorBound L Xmin u bound := by
  refine ⟨hSigned.support_lower, ?_⟩
  intro N hN hEven
  rw [← balancedVaughanTypeISignedCoprimePartialSummationError_eq
    (hSigned.window_nonempty hN) (lt_of_lt_of_le Nat.zero_lt_two hSigned.support_lower)]
  exact hSigned.signed_bound hN hEven

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
