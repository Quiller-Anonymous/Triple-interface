# σ-Tail status report (honest checkpoint)

## Executive Summary

**Status: partial**.

We now have a fully proved, axiom-free **explicit majorant** for `|sigmaTail Q N|` (a finite divisor
sum bound). This is valuable as a diagnostic and as infrastructure, but it does **not** yet imply
the current project axiom `|sigmaTail (Q X) N| ≤ 1.02 / (Q X)` uniformly in `N`.

## Original Goal

Eliminate the axiom:
```lean
axiom sigmaTail_bound_on_window (X0 H : ℕ) (Q : ℕ → ℕ) :
  SigmaTailBoundOnWindow X0 H Q K_tail_canon
```
where `K_tail_canon = 1.02` and the bound states:
```lean
∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → 1 ≤ Q X →
  |sigmaTail (Q X) N| ≤ K_tail_canon / (Q X : ℝ)
```

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

### The real remaining issue: uniformity vs absolute majorants

The explicit bound currently proved is obtained by majorizing `|sigmaTail|` by a sum of
nonnegative terms (triangle inequality + reindexing). That bound depends on the arithmetic of `N`
via a divisor sum. As a result, it does **not** directly yield a uniform constant independent of
`N` (such as `1.02`).

### Why This Is Plausible

This is the wrong axis of plausibility.

The constant `90` is an *upper bound constant* in the auxiliary lemma
`euler_tail_bound_tsum_ENNReal`; it does **not** mean `sigmaTail` is “about `90/Q`”, and it does
not produce a lower bound. So there is no contradiction from “d=1 gives 90/Q”.

What this *does* show is: the present proof path is too coarse to recover a small uniform constant.
To prove a bound like `1.02/Q` uniformly in `N`, one likely needs a different argument that uses
Euler-product style factorization/cancellation of the **signed** tail, not an absolute majorant.

### CRITICAL INSIGHT

The important integrity point is not “1.02 vs 91”. It is:

- Our current proved bound is an explicit absolute majorant depending on `N`.
- The project axiom is a uniform bound independent of `N`.

Bridging that gap requires new mathematics (or weakening/reformulating the axiom).

## Verification Strategy

### Next likely steps

1. Decide whether the intended bound is genuinely uniform in `N` (as currently axiomatized).
2. If yes: switch proof strategy toward an Euler-product truncation argument for the *signed* tail.
3. If no: weaken the axiom statement to the strongest provable form consistent with the current
   absolute-majorant machinery (this will likely introduce an `N`-dependent factor).

## Next Steps

1. Treat `Goldbach/Cert/SigmaTailExplicitBoundFun.lean` as the current “proved output”.
2. Update the project plan/ledger to reflect that the remaining σ-tail axiom is not yet reduced
   to a finite numeric check.
3. Start a new proof attempt aimed at a uniform-in-`N` truncation statement (Euler-product route).

## Files Created/Modified

**New/updated:**
- `Goldbach/Cert/SigmaTailExplicitBoundFun.lean`: now compiles and provides the explicit majorant.
- `Goldbach/Cert/SigmaTailProof.lean`: now a small checkpoint file (no sorries/axioms).

**To Review:**
- `Goldbach/Cert/SigmaTailAxiomsFun.lean:20`: K_tail_canon definition
- `Goldbach/AO_OffDiag/SigmaTailEuler_Analytic.lean:1870`: euler_tail_bound value

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
[UNIFORMITY GAP]  ← YOU ARE HERE
    ↓
σ-tail axiom eliminated (pending)
```

## Conclusion

The σ-tail work is **not** at “gold” by the strict conventional-math standard yet.

What is proved is an explicit, axiom-free **absolute majorant** for `|sigmaTail Q N|` that depends
on the arithmetic of `N` (via a divisor sum). What is still missing is a **uniform-in-`N`** bound of
the form `|sigmaTail (Q X) N| ≤ K / (Q X)` with a small pinned `K` (currently `1.02`).

**Status for Gold:** σ-tail remains “fool’s gold” until either:
- a genuine uniform bound is proved (likely using more cancellation than an absolute majorant), or
- the project axiom is reformulated to match the strongest provable statement.
