# σ-Tail status report (honest checkpoint)

## Executive Summary

**Status: complete for the canonical FunX pipeline**.

The canonical FunX track no longer postulates any σ-tail axiom: it derives a conservative bound
from the proved explicit majorant and uses a growing truncation schedule `Q(X)` to make the windowed
numeric budget close.

The explicit majorant remains valuable infrastructure (it is the proof-theoretic “source” of the
crude bound used by the pipeline).

## Legacy Goal (retired)

Originally, the project aimed to eliminate a *fixed-cutoff* σ-tail axiom of the shape:
```lean
∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → 1 ≤ Q X →
  |sigmaTail (Q X) N| ≤ (K_tail / (Q X : ℝ)) * F_block N
```

In particular, the idea of a tiny pinned uniform constant on all windows has been abandoned: it is
not used by the canonical theorem, and the repo’s current σ-tail proof route is explicitly
“conservative but honest”.

## What Was Accomplished

### 1. Complete Analytic Infrastructure (PROVED)

**File: `Goldbach/AO_OffDiag/SigmaTailEuler_Analytic.lean`**
- ✅ `totient_divisor_expansion`: Divisor identity for n/φ(n) (lines 106-199)
- ✅ `inv_totient_sq_le_double_divisor_sum`: Expansion of 1/φ(n)² (lines 300-450)
- ✅ `Cstar_le_45`: Euler product constant bound (line 1587)
- ✅ `euler_tail_bound_tsum_ENNReal`: Tail bound ∑_{r>R} 1/φ(r)² ≤ 90/R (lines 1870-2004)

**Mathematical Content:**
- Full Euler product factorization
- Convergence analysis with exp(3) < 45 bound
- Explicit 90/R tail estimates

**Axioms Used:** NONE (all proved from first principles)

### 2. Reindexing Machinery (PROVED)

**File: `Goldbach/AO_OffDiag/SigmaTailReindexFun.lean`**
- ✅ Transform sigmaTail into divisor-based majorant (lines 100-380)
- ✅ Injection proof for gcd-quotient pairs (line 185)
- ✅ Finiteness proofs via Euler bound (lines 380-482)

**Mathematical Content:**
- Reindex tail ∑_{q>Q} by pairs (d,r) where d|N, r coprime to N
- Each term bounded via (1/φ(d)) * (1/φ(r)²)
- Connect to Euler tail via Q/d threshold

**Axioms Used:** NONE

### 3. Explicit Bound Formula (PROVED)

**File: `Goldbach/Cert/SigmaTailExplicitBoundFun.lean`**
- ✅ `reindexMajorantENN_le_explicit`: explicit divisor-sum upper bound for `reindexMajorantENN`
- ✅ `sigmaTail_abs_le_explicit`: combines reindexing + explicit majorant to bound `|sigmaTail|`

**Mathematical Content:**
- Case split on `Q/d = 0` vs `Q/d ≥ 1`
- Uses the *proved upper bound* `≤ 90/R` for the auxiliary totient-squared tail

**Axioms Used:** NONE

### 4. Reduction Framework (PROVED)

**File: `Goldbach/Cert/SigmaTailReductionFun.lean`**
- ✅ `sigmaTailBoundOnWindow_of_reindexMajorant`: Formal reduction (lines 26-50)
- ✅ Reduces axiom to: `reindexMajorantENN.toReal ≤ K_tail / Q`

**Axioms Used:** NONE

## What Remains

### Optional tightening only (not a pipeline blocker)

The current σ-tail route is intentionally coarse: it bounds `|sigmaTail|` by a nonnegative explicit
majorant, then turns that into a crude real bound `≤ (180/Q) * N^2` (valid under mild side
conditions), and finally uses a growing `Q(X)` to make the windowed budget close.

What remains (if desired) is *tightening*: replacing the crude `N^2` factor by a more conventional
`F_block(N)` factor (and/or improving constants). This is not currently required to run the
canonical Goldbach pipeline; the major-arc calibration axiom is the blocker for “gold”.

### Why This Is Plausible

This is the wrong axis of plausibility.

The constant `90` is an *upper bound constant* in the auxiliary lemma
`euler_tail_bound_tsum_ENNReal`; it does **not** mean `sigmaTail` is “about `90/Q`”, and it does
not produce a lower bound. So there is no contradiction from “d=1 gives 90/Q”.

What this *does* show is: the explicit-majorant route is too coarse to recover any “tiny pinned
uniform constant”. If one ever wants a sharp uniform statement, it would require substantially more
cancellation than an absolute majorant.

### CRITICAL INSIGHT

The important integrity point is not “tiny constant vs coarse constant”. It is:

- Our current proved bound is an explicit absolute majorant depending on `N`.
- The project axiom is a uniform bound independent of `N`.

For the canonical pipeline, we avoid this gap entirely by using a growing `Q(X)` and a conservative
bound.

## Verification Strategy

### Next likely steps

1. Decide whether the intended bound is genuinely uniform in `N` (as currently axiomatized).
2. If yes: switch proof strategy toward an Euler-product truncation argument for the *signed* tail.
3. If no: weaken the axiom statement to the strongest provable form consistent with the current
   absolute-majorant machinery (this will likely introduce an `N`-dependent factor).

## Next Steps

1. Treat `Goldbach/Cert/SigmaTailExplicitBoundFun.lean` as the current “proved output”.
2. Treat `Goldbach/Cert/SigmaTailRealBoundFun.lean` + `Goldbach/Cert/OffDiagBudgetAxiomsFun.lean`
   as the canonical “pipeline closure” layer (crude bound + growing `Q(X)` + proved budget).
3. Only if needed: pursue tightening to `F_block(N)/Q(X)` with better constants.

## Files Created/Modified

**New/updated:**
- `Goldbach/Cert/SigmaTailExplicitBoundFun.lean`: now compiles and provides the explicit majorant.
- `Goldbach/Cert/SigmaTailProof.lean`: now a small checkpoint file (no sorries/axioms).

**To Review:**
- `Goldbach/AO_OffDiag/SigmaTailEuler_Analytic.lean:1870`: euler-tail bound constant
- `Goldbach/Cert/SigmaTailRealBoundFun.lean`: crude real bound constants (`180`)

## Mathematical Dependencies

```
Classical axioms
    ↓
Euler product (Cstar ≤ 45)
    ↓
Tail bounds (90/R)
    ↓
Reindexing (divisor sums)
    ↓
Explicit formula
    ↓
Crude real bound (`≤ (180/Q) * N^2`)
    ↓
Growing truncation schedule `Q(X)`
    ↓
Windowed budget closes (proved)
```

## Conclusion

The σ-tail work is **not** at “gold” by the strict conventional-math standard yet.

What is proved is an explicit, axiom-free **absolute majorant** for `|sigmaTail Q N|` that depends
on the arithmetic of `N` (via a divisor sum), plus a conservative pipeline-usable real bound derived
from it.

**Status for Gold:** σ-tail is not currently the “gold blocker” for the canonical theorem; major-arc
calibration is.
