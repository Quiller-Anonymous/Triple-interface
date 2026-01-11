# σ-Tail constant clarification (updated)

## The Issue

When analyzing σ-tail bounds, it’s easy to misread where the numeric constants are coming from.
In particular, the number `90` shows up in the repo and can look like a “main term” constant if you
read it out of context.

Historically, there was also discussion of a tiny pinned uniform constant for the σ-tail. That
route has been abandoned: the canonical FunX pipeline uses a conservative proved bound instead.

## What the `90` actually is

The lemma `Goldbach/AO_OffDiag/SigmaTailEuler_Analytic.lean` proves a **purely auxiliary** upper
bound:

- `∑_{r>R} 1/φ(r)² ≤ 90/R`.

This is not an evaluation, and it is not a lower bound. It is a global constant that makes the
inequality easy to close.

So statements like “the `d = 1` term contributes exactly `90/Q`” are incorrect: `90/R` is only an
upper bound produced by that lemma.

## How this `90` is used in the current pipeline

In the canonical FunX σ-tail route, the `90/R` bound is pushed through reindexing/majorization and
then converted into a crude real bound of the form

```
|sigmaTail Q N| ≤ (180 / Q) * N^2
```

under mild side conditions (notably `N ≤ Q` and `N ≠ 0`).

This is implemented in `Goldbach/Cert/SigmaTailRealBoundFun.lean`, and then used in the canonical
off-diagonal hypothesis wiring in `Goldbach/AO_OffDiag/TenorHypFunX_Canon.lean` with a growing
truncation schedule `Q(X) = max Q0 (X^3)` and a proved numeric budget lemma.

## Takeaway

- `90/R` is an auxiliary Euler-tail bound constant, not a “σ constant”.
- The canonical pipeline does not rely on any tiny pinned σ-tail constant; it uses a conservative
  proved bound.
