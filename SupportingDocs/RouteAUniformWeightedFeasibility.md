# Route A: uniform truncation and weighted zero-mode feasibility

This work removes the unweighted normalized shape targets from the proposed Route A proof path. It preserves the raw target `ZeroModeEnvelopeShapeTarget` and the existing generated certificate. A centered truncation estimate is a separate arithmetic theorem; it does not by itself transfer to the weighted true zero mode.

## The normalization issue

Write `B_X(N) = zeroModeSigmaBaseline X N`, `c_X = routeVisibleWindowNormFloor X`, and `F_X(N) = normalizedZeroModeShapeObservable X N`. At points where the baseline and floor are nonzero, the existing definitions give

\[
T_X(N)-\kappa c_X B_X(N)=c_XB_X(N)(F_X(N)-\kappa).
\]

Consequently the correct energy transfer retains the baseline:

\[
\sum_N |T_X(N)-\kappa c_X B_X(N)|^2
=c_X^2\sum_N |B_X(N)|^2|F_X(N)-\kappa|^2.
\]

The new weighted-energy modules state this identity and discharge the nonvanishing hypotheses on the canonical window. The earlier unweighted average/variance targets remain declared for compatibility, but their comments no longer describe them as a viable uniform route.

The prime-diagonal diagnosis concerns the quotient `F`, not the raw zero mode. Subject to the stated diagonal lower estimate, at `X=N=2p` the quotient grows at least as a positive constant times `log(p)^2 log(2p)^2 log(2p+H)^2`. Its nonnegative window average therefore cannot remain within a bounded distance of a fixed scalar. This impossibility argument has not been formalized here. It does not contradict a raw upper bound after multiplication by the baseline and floor.

## A uniform finite-truncation argument

Let `g(N) = sigma_trunc_Q0 N`, with `Q0=30000`. For odd squarefree `r`, put `t_r = 1 + 1_{2r≤Q0}`. The exact even-input identity is

\[
g(2n)=\sum_{r\le Q_0,\ r\text{ odd squarefree}}
 \frac{t_r}{\varphi(r)^2}c_r(n)
=\sum_{d\le Q_0}B_d\,1_{d\mid n}.
\]

The divisor/CRT identities give full-period mean `2` and variance

\[
v=\sum_{1<r\le Q_0,\ r\text{ odd squarefree}}
 \frac{t_r^2}{\varphi(r)^3}=0.601923083014\ldots.
\]

The formal proof works directly with densities: `Σ B_d/d=2` and `Σ B_d B_e/lcm(d,e)=4+v`. No enormous common period is enumerated. Every consecutive interval of `m` half-arguments has divisibility count error at most one.

All `B_d` are nonnegative. For a contributing `r=d*k`, totient multiplicativity bounds the magnitude of its contribution by the positive `r=d` term times `1/φ(k)^2`. A single exact finite scalar bounds the total possible negative contribution by `7/8` of that positive term. This supplies coefficient positivity for every divisor at the fixed cutoff; it is not a numerical check of one window.

The economical discrepancy bound keeps the diagonal cancellations at `d=3,5`. With `a=2-B_1` and `S=Σ_{d>1} B_d=g(0)-B_1`, it is

\[
L\le(a+S)^2-2(B_3^2+B_5^2).
\]

Exact rational checks establish `v<0.601924`, `2≤g(0)<11.642`, `1.3203<B_1,B_3<1.321`, and `0.4401<B_5<0.441`. Thus every relevant window, containing at most 5001 even integers, has centered normalized energy bounded by

\[
\frac{5001v+L}{1.32^2}
\le \frac{2443264817}{1361250}
=1794.868552\ldots<1795.
\]

The denominator uses the actual canonical constant, not the conservative numerical surrogate: an Euler-product identification connects the series-defined `C2` to the odd-prime product, whose finite product through 10000 and elementary tail bound yield `C2>0.66`.

The sharper coefficient estimate `Σ|C_e|<100` is independently checked by exact rational Python arithmetic. It gives a stronger budget below 1785, but is not part of the Lean proof proposed here. The two-cancellation estimate suffices for the requested 1795 target and avoids a larger finite computation.

## What the raw feasibility study says

The checked direct raw proof uses the existing coefficient cap, geometric-mass upper bound, Fourier-weight bound, and logarithmic normalization comparison. It also proves the elementary estimate `|sigma C N/(2*C.C2)|≤2 log N` for `N≥X0`. The resulting conservative dimensionless residual budget is about `3.400438`, below `C3=4` with `C2=0`. The theorem `zeroModeEnvelopeShapeTarget_four` holds for every `|κ|≤1`, including the frozen candidate. Its zero-scalar instance gives the checked theorem `zeroModeEnergyBound_four : canonicalExpansion.ZeroModeEnergyBound 4`.

The floating-point study checks the same weighted expression at `X=1000000`, the prime-diagonal example `X=1000018=2*500009`, and larger windows. At the first two windows, error energy divided by `c_X²` is approximately `8.88e-19`, corresponding to `C3≈8e-6`. These samples are diagnostics, not a uniform proof.

This upper bound can hold even when the frozen formula is a poor relative approximation: in these samples the baseline contribution is tiny relative to the raw zero mode. Proving the raw upper-error target therefore does not establish the heuristic provenance or relative accuracy of that formula.

The downstream distinction matters. The direct minor-energy path already has the source-level proofs `nonzeroModeEnergyBound_80`, `zeroModeEnergyBound_72000000`, and `q0Minor_energyBound16`; it does not need the new truncation theorem. The improved Type-I constant therefore does not newly close that existing surface. This statement is a review of those declarations, not a complete axiom audit of the final Goldbach theorem.

The frozen-formula/PSB path instead needs a positive actual mean after errors. Its present coarse mean-channel estimates, combined with the proposed raw target, give a residual coefficient `C2r>45900`; this is an upper-budget problem, not a lower bound on the actual residual or an impossibility proof. At `X0`, the explicit candidate main lower profile is approximately `5.58e-28`, whereas even the `C3=4` zero-mode Cauchy allowance is approximately `3.08e-10`. The new raw bound does not establish the `hμpos` hypothesis required by `routeADenseGoodGridTarget_of_mean_and_variance`. Boundary/bulk, variance, and sampling obligations also remain on that path. A useful positive-mean comparison is therefore a separate feasibility question before further Route A formalization.

## Reproduction and trust

The scripts `scripts/experiments/route_a_uniform_truncation_budget.py` and `route_a_uniform_truncation_exact_l1.py` use Python standard-library rational arithmetic; displayed decimals are explanatory approximations. The latter is the optional sharper calculation. `route_a_raw_envelope_feasibility.py` uses the repository's existing numerical harness and the Python standard library. Its four sample records are saved in `RouteA_RawEnvelopeSamples.jsonl`.

The Lean finite scalar comparisons use `native_decide`. Their axiom reports therefore include `Lean.ofReduceBool` and `Lean.trustCompiler`, in addition to the standard logical axioms. The generic discrepancy, CRT, cancellation, and normalization arguments are theorem proofs rather than external numerical assumptions. No new `sorry` or custom axiom was added.

`Q0MinorSigmaTruncUniform.centeredNormalizedSigmaTruncWindowEnergyTarget_1795` has compiled under Lean 4.26.0-rc2 with the repository's pinned mathlib. Its complete axiom report is `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`. It has no `sorryAx` or project-specific analytic axiom. The declaration has exactly the existing `CenteredNormalizedSigmaTruncWindowEnergyTarget 1795` type.

The truncation observable and energy declarations were moved into small modules while preserving their fully qualified names and definitions. Existing modules import those declarations, allowing the new arithmetic theorem to be checked independently of historical geometric and generated-certificate machinery. All six extracted declarations were compared byte for byte with their original definitions, and the envelope's executable tokens are unchanged.

All new proof modules and the 264-module project dependency closure have compiled. The weighted identity on the canonical window, the uniform raw envelope bounds, and `zeroModeEnergyBound_four` use only `propext`, `Classical.choice`, and `Quot.sound`. The modified true-sigma and true-tail compatibility modules also compiled. The historical normalized-average monolith and generated certificate chain were not rebuilt. No generated `X0` certificate is used by the new uniform proof, no generated certificate files or workflows were changed, and no larger certificate was commissioned.

The focused proof checks can be reproduced with the pinned project toolchain:

```sh
lake build +Goldbach.Cert.MajorArcModules.Q0MinorSigmaTruncUniform:olean
lake build +Goldbach.Cert.MajorArcModules.Q0MinorZeroModeWeightedEnergyOnWindow:olean
lake build +Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelopeRawBound:olean
lake env lean scripts/experiments/route_a_uniform_weighted_audit.lean
```
