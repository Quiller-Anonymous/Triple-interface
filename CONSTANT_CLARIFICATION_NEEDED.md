# σ-Tail constant clarification (updated)

## The Issue

When analyzing the σ-tail bound:
```
|sigmaTail (Q X) N| ≤ K_tail_canon / (Q X)
```

With `K_tail_canon = 1.02`, it’s easy to get confused by the appearance of the number `90`
in the current proofs. This note clarifies what `90` means and what the *real* blocker is.

## What the `90` actually is

The lemma `Goldbach/AO_OffDiag/SigmaTailEuler_Analytic.lean` proves an **upper bound**:

- `∑_{r>R} 1/φ(r)² ≤ 90/R`.

This is not an exact evaluation, and it is not a lower bound. It is just a (currently crude)
global constant that makes the inequality easy to close.

So statements like “the `d = 1` term contributes exactly `90/Q`” are incorrect: `90/Q` is only an
upper bound produced by this lemma.

## Possible Resolutions

### The real blocker: uniformity in `N`

What we currently have (proved, axiom-free) is an explicit **finite-sum majorant** for
`|sigmaTail Q N|`:

- `Goldbach/Cert/SigmaTailExplicitBoundFun.lean` proves an explicit bound in terms of a divisor sum
  over squarefree divisors `d ∣ N`.

This is valuable, but it does **not** yet imply the project’s uniform axiom
`|sigmaTail (Q X) N| ≤ 1.02 / (Q X)` because:

- the explicit majorant depends on the arithmetic of `N`, and
- bounding that majorant uniformly for all `N` by a single small constant is not something the
  current proof path establishes.

In other words: the gap is not “a missing normalization factor”; the gap is that we have an
absolute-value majorant, while the intended axiom is a uniform-in-`N` truncation statement for the
**signed** tail.

## Action Items

1. Decide whether the intended σ-tail statement is truly uniform in `N` (as the current axiom is).
2. If yes: switch proof strategy toward an Euler-product truncation bound for the signed σ-tail
   (not an absolute-value majorant).
3. If no: weaken/reformulate the axiom to match what the current majorant machinery can support.

## Current Status

`Goldbach/Cert/SigmaTailProof.lean` is now a short checkpoint file exposing the proved explicit
majorant with a stable name (no sorries/axioms).

## Recommendation

Treat the σ-tail constant as **not yet justified** under the current proof path, and proceed by:

- keeping the axiom (for now) as a conventional analytic assumption, and
- using the explicit majorant as a diagnostic tool while developing a genuinely uniform bound for
  the signed tail.
