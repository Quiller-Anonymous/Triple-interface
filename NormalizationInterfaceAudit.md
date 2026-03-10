# Normalization Interface Audit

Goal: record where the current FunX normalization mismatch is introduced, so the next refactor
targets the correct interface instead of adding more wrapper variants.

## Executive summary

The current blocker is **not** in the new scale wrappers. It is already present in the lower AO/BG
assembly:

1. the major lower term is suppressed by `weight_mass(X) = wScale(X)^2`,
2. the AO envelope remains an **absolute** cap,
3. the bank bridge/tail side can now be kept **weighted** in the live code,
4. so the closure-facing lower term is of the shape
   `sigma * weight_mass(X) - absolute_error`,
   which is too small on the canonical window.

This means the next honest refactor must replace the closure surface or the normalized main term
interface itself. More `c0(X)` / `S(X)` / `ε(X)` wrappers do not solve the core issue.

## Trace of the current normalization

### 1. Weight suppression enters in the bank payload

In `Goldbach/BG_Bank.lean`:

- `wScale X = 1 / (log X * (2H + 1))`
- `wX X n` is either `wScale X` or `0`

So the bank-side payload is already carrying a factor of `wScale(X)` on each input.

### 2. The reference major term becomes `sigma * weight_mass(X)`

In `Goldbach/AO_WeightMass.lean`:

- `weight_mass X := (BG_Bank.wScale X)^2`

In `Goldbach/BG_Identity.lean`:

- `conv_ref_const_eq_sigma_mass` proves
  `conv_ref_const X N = sigma N * weight_mass X`

This is the key normalization change. The staged constant-reference object is no longer `sigma N`;
it is `sigma N * weight_mass X`.

### 3. AO lower packaging subtracts an absolute envelope from that suppressed term

In `Goldbach/AO_Major.lean`:

- `cAO K X := σmin * weight_mass X - δAO K`

In `Goldbach/AO_AssembleEnvelope.lean`:

- `δAO K` is the sum of four absolute channel caps `δ_kernel + δ_mellin + δ_smooth + δ_off`

So the first hard mismatch is already visible here:

- positive part: `σmin * weight_mass(X)`
- negative part: absolute `δAO`

That is the first place the new `weight_mass(X)` regime and the old absolute-envelope regime are
combined.

### 4. The FunX route preserves the absolute-gap formulation

In `Goldbach/AO_InstantiateTenorFunX.lean`:

- `McanoN_lb_cAO` gives `Mcanon Hoff X N ≥ cAO(caps Hoff) X`

In `Goldbach/ParallelTenorFunXCore.lean`:

- `bank_cert_bound_funX` proves
  `|R_bank X N - Mcanon Hoff X N| ≤ ε`

where the right-hand side is an **absolute** sum of:

- `δbridge_canon`
- `payload_cap * C_tail_closed`
- `δAO_gap_bound`

So the second mismatch point is:

- lower bound enters as `cAO(X)`
- gap enters as an absolute `ε`

### 4a. The bank payload cap used to flatten away the window scale

In `Goldbach/BG_Bank.lean`, the proof of `payload_bound_window` bounds the window weights by

- `|wX X n| ≤ 1`
- `|wX X (N-n)| ≤ 1`

instead of preserving the actual factor `wScale(X)^2 = weight_mass(X)`.

That relative structure is now also available in the live code:

- `BG_Bank.payload_bound_window_wScale_sq`
- `BG_Identity.errTI_bound_closed_wScale_sq`
- `AO_KernelTail.E_kernel_bound_relative`
- `BG_CalibBridgeStub.bridge_bound_window_weighted`
- `ParallelTenorFunXCore.bank_gap_le_mixed`

So the bank side is no longer the main source of absoluteness. The remaining absolute obstruction is
concentrated in the AO/Mellin packaging.

### 5. The bridge itself is not the culprit

In `Goldbach/BG_Calib.lean` and `Goldbach/BG_CalibBridgeStub.lean`:

- the current `WeightsBridgeHyp` is only a tiny log-normalization mismatch between `log X` and
  `log N`
- the proof now also exports the weighted form
  `bridge_bound_window_weighted`

This part is small and absolute, but it is not the main structural issue. Even if it vanished, the
core obstruction from `cAO(X)` versus absolute error would remain.

## What the obstruction theorem now says

In `Goldbach/ParallelFunXCanonScaleObstacle.lean`:

- `c0_lt_eps_on_window`
- `not_eps_lt_c0_on_window`
- `not_div_route_possible_on_window`

formally show that:

- the current honest closure margin is below the canonical slack on the whole window,
- and even the third additive route `ε(X) = ε_raw / S(X)` collapses back to the same impossible
  comparison `ε_raw < cAO(X)`.

## Conclusion

The first genuinely wrong interface is **not** the final `BudgetHyp` class. The first genuinely
wrong interface is the one that packages the major lower term as

- `σmin * weight_mass(X) - absolute_error`

while the bank gap remains absolute.

So the next refactor should begin **before** the current closure layer.

## Recommended replacement surface

The immediate replacement should avoid the forced factorization `c0(X) * S(X)`.

That new bridge surface now exists in:

- `Goldbach/ClosureBridgeDirect.lean`
- `Goldbach/AnalyticGlobalDirect.lean`
- `Goldbach/CompleteTenorFunX_Direct.lean`

Its shape is:

- direct lower term `L(X)`
- direct additive gap `Δ(X)`
- closure asks only for `0 < L(X) - Δ(X)` and
  `R_bank X N ≥ L(X) - Δ(X)`

This is better because it matches the actual theorem shape we want to reason about, instead of
forcing the lower term into a product form before we know that such a factorization is honest.

## What still has to change

`ClosureBridgeDirect` is only a better *surface*. It does not fix the normalization by itself.

To get a real canonical budget instance, we still need at least one deeper change:

1. a relative AO envelope whose error scales with the same normalization as the main term, or
2. a deweighted comparison object whose main term is not crushed by `weight_mass(X)`, or
3. a new bank theorem stated against a different normalization target than the current `R_bank`.

## AO cap classification

Current status of the four AO channels:

1. `kernel`
   - mixed
   - `AO_KernelTail.E_kernel` is identified with `errTI N N`
   - its bound comes from `payload_cap * C_tail_closed`
   - the relative theorem
     `AO_KernelTail.E_kernel_bound_relative`
     is now available
   - after the recent audit, the kernel term is no longer the main unresolved source of
     absoluteness

2. `mellin`
   - no longer absolute by definition
   - `AO_MellinTrunc.E_mellin` is now the named gap `M_infT_sm X N - M_infInf_sm X N`
   - the current local approximants are still placeholders, so the exported bound remains the
     absolute canonical budget `δ_mellin_canon`
   - this is better bookkeeping, but not yet a normalization-aware Mellin theorem

3. `smooth`
   - zero placeholder
   - not a normalization issue yet

4. `off`
   - naturally relative
   - `AO_OffDiagFunX.E_off = sigma_tail * weight_mass(X)`
   - this relative shape is now preserved explicitly in
     `AO_OffDiagFunX.E_off_bound_relative`
     and
     `AO_OffDiag.TenorHypFunX.E_off_bound_relative`
   - it only becomes absolute when the code applies `|weight_mass(X)| ≤ 1`

So the off-diagonal channel is the clearest evidence that the current assembly is flattening a
relative estimate into an absolute cap too early.

## Current mixed theorem surface

The strongest honest FunX-side bound now available in the repo is:

- `ParallelTenorFunXCore.bank_gap_le_mixed`
- `ParallelTenorFunXCore.bank_gap_le_semimixed`
- `CompleteTenorFunX_Direct.goldbach_from_tenorFunX_direct_mixed`
- `CompleteTenorFunX_Direct.analyticHypDirect_funX_semimixed`
- `CompleteTenorFunX_Direct.goldbach_from_tenorFunX_direct_mixed_autoHoff`

It shows that the canonical bank gap is bounded by:

- weighted bridge term
- weighted tail term
- `δ_major`
- absolute Mellin floor
- weighted kernel term
- weighted off-diagonal term

The important new fact is that the wrapper stack no longer forces the Mellin term to be literally
the canonical constant. There is now an additive semimixed route in:

- `AO_InstantiateTenorFunX.errAO_bound_semimixed`
- `ParallelTenorFunXCore.conv_ref_Mcanon_gap_le_semimixed`
- `ParallelTenorFunXCore.bank_gap_le_semimixed`
- `CompleteTenorFunX_Direct.analyticHypDirect_funX_semimixed`

This means the remaining theorem-design question is now very focused:

1. keep a genuinely mixed direct closure theorem, with an absolute Mellin floor plus weighted
   remainder, or
2. refactor the Mellin channel so the top-level direct lower term can also be stated in a more
   normalization-aware way.

The first option is now implemented as a theorem surface: the mixed direct route asks for a
window-uniform `Δ(X)` dominating the mixed gap expression, and then feeds that directly into the
closure witness machinery without forcing any product normalization.

## Concrete next refactor steps

1. Introduce a direct analytic hypothesis layer on top of `ClosureBridgeDirect`.
   This is now done in `Goldbach/AnalyticGlobalDirect.lean` and consumed by
   `Goldbach/CompleteTenorFunX_Direct.lean`.

2. Rebuild the canonical budget layer on that direct route only.
   Do not add more product-style `c0 * S` wrappers.

3. Audit the AO caps one level deeper.
   This is now substantially done:
   - `δ_mellin` is still absolute by construction,
   - `δ_smooth` is zero placeholder,
   - `δ_off` has an honest relative precursor and that relative form is already exported,
   - `δ_kernel` also has an exported relative form.

4. Replace the canonical Mellin specialization.
   The wrapper work is now done. The next real theorem task is to prove an honest window envelope
   `|(channels Hoff).E_mellin X N| ≤ δm(X)` and feed it into the semimixed route.

5. Decide whether the next honest object after that is:
   - a mixed direct closure theorem that isolates the Mellin floor, or
   - a refactored Mellin/deweighted major object.

Until that decision is made, more wrapper-level normalization work is low-yield.
