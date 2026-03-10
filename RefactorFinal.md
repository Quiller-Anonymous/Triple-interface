## Final-Normalization Refactor Plan

Goal: complete the transition from the old scalar-`c0` FunX witness route to the honest
scale-sensitive normalization regime, without breaking the older compatibility routes until the
new path is stable.

### Design choice

Use an additive migration first.

- Keep the existing scalar witness path untouched while the new route is built.
- Extend the current `Fun` layer minimally:
  - keep `H : ℕ → ℕ`,
  - keep `S` and `ε` scalar,
  - make `c0` scale-dependent as `c0 : ℕ → ℝ`.
- Use a scale-sensitive projected main term `M : ℕ → ℕ → ℝ`.

This matches the current AO/FunX reality:

- `AO_Major.cAO ... X` is already `X`-dependent,
- `AO_Mcanon.Mcanon X N` is already `X`-dependent,
- the current stale FunX route only breaks because it still expects a scalar closure constant.

### Refactor phases

1. Add a new bridge predicate and witness layer rather than mutating the old one.
   New files:
   - `Goldbach/ClosureBridgeScale.lean`
   - `Goldbach/AnalyticPointwiseScale.lean`
   - `Goldbach/FinalScale.lean`

2. In `ClosureBridgeScale`, define scale-sensitive pointwise closure with:
   - `H : ℕ → ℕ`
   - `c0 : ℕ → ℝ`
   - scalar `S, ε`

   Target shape:
   - `ClosurePointwiseScale X H S c0 ε`
   - `GlobalClosurePointwiseScale X0 H S c0 ε`

3. Prove the scale-sensitive bridge lemmas:
   - pointwise closure implies representation on the corresponding window,
   - global closure plus finite base implies Goldbach for all large even integers.

4. Add a scale-sensitive analytic hypothesis layer.
   New file:
   - `Goldbach/AnalyticGlobalScale.lean`

   It should mirror `AnalyticGlobal.lean`, but with:
   - `TenorHypScale`
   - `AnalyticHypScale`
   - `ofTenor`

5. Keep the major-term interface honest.
   The major inequality should be stated with:
   - `M : ℕ → ℕ → ℝ`
   - `∀ X N, ... -> M X N ≥ c0 X * S`

   Do not force the main term back to `ℕ → ℝ`.

6. Add a scale-sensitive witness packaging layer.
   New files:
   - `Goldbach/Analytic/WitnessScale.lean`
   - optionally `Goldbach/Analytic/WitnessesScale.lean`

7. Rebuild the FunX conditional theorem on the new layer.
   New file:
   - `Goldbach/CompleteTenorFunX_Scale.lean`

   Core ingredients:
   - `ParallelTenorFunXCore.bank_cert_bound_funX`
   - `AO_InstantiateTenorFunX.McanoN_lb_cAO`
   - `c0 X := AO_Major.cAO (AO_InstantiateTenorFunX.caps Hoff) X`

8. Replace the stale scalar positivity requirement with an honest on-window assumption:
   - `∀ X ≥ X0, ε < c0 X`

9. Add the canonical budget wrapper on the new route.
   New files:
   - `Goldbach/CompleteTenorFunX_CanonBudget_Scale.lean`
   - `Goldbach/Cert/ParallelFunXCanonBudgetCert_Scale.lean`

10. Switch downstream entrypoints only after the new route builds:
   - `Goldbach/GoldFunX.lean`
   - `Goldbach/GoldFunX_OptionB_TextbookMajorArc.lean`
   - `Goldbach/GoldFunX_OptionB_Cert.lean`
   - corresponding audit files

11. Keep the old scalar route as compatibility until the new route is stable.

### Milestones

- M1: `ClosureBridgeScale` builds.
- M2: `AnalyticPointwiseScale` and `FinalScale` build.
- M3: `AnalyticGlobalScale` builds.
- M4: `CompleteTenorFunX_Scale` builds.
- M5: canonical budget cert wiring builds.
- M6: `GoldFunX` and both Option-B entrypoints are moved to the new route.

### Risks

- Reintroducing the old bug by collapsing `M X N` back to `M N`.
- Generalizing too aggressively and creating unnecessary churn.
- Discovering later that `S` must also vary with `X`.

If that happens, extend only the new route; do not disturb the legacy compatibility path.

### Current blocker

The additive `c0 : ℕ → ℝ` migration compiles, but the canonical budget target is not actually
instantiable under the current honest bank normalization.

What is now proved in Lean:

- `Goldbach/ParallelFunXCanonScaleObstacle.lean` shows
  `ParallelFunXCanonScale.c0 X < CanonParams.ε`
  on the whole canonical window `X ≥ X0`.
- In particular, the wanted hypothesis
  `∀ X ≥ X0, CanonParams.ε < ParallelFunXCanonScale.c0 X`
  is false for the current definition
  `c0(X) = σmin * weight_mass(X) - δAO`.

Reason:

- `weight_mass(X) = wScale(X)^2`,
- `wScale(X) ≤ 1 / 20001` on the canonical window,
- so the positive main-term contribution is crushed by an extra `20001^-2`,
- while `δAO` stays as an absolute cap.

Practical consequence:

- the next step is not to keep searching for a `BudgetHyp` proof,
- the next step is to redesign the closure normalization so that the major lower term and the bank
  error live on compatible scales.

Update after the Mellin refactor audit:

- the wrapper stack now has a stable semimixed seam:
  `AO_InstantiateTenorFunX.errAO_bound_semimixed`,
  `ParallelTenorFunXCore.bank_gap_le_semimixed`,
  `CompleteTenorFunX_Direct.analyticHypDirect_funX_semimixed`.
- `AO_MellinTrunc.E_mellin` is now a remainder-style object
  `M_infT_sm X N - M_infInf_sm X N`, rather than a definitionally inlined budget constant.
- so the active blocker is no longer "how do we thread a non-canonical Mellin term through the
  closure route?"
- it is now "what honest Mellin envelope `δm(X)` should replace the canonical constant
  `δ_mellin_canon`?"

### Next decision point

The most likely repair is a second normalization pass in the new route only:

- either allow `S` to vary with `X`,
- or redefine the closure-facing major constant so it no longer subtracts an absolute AO cap from a
  `weight_mass(X)`-suppressed quantity,
- or both.

Do not try to resurrect the old scalar `eps_lt_c0` proof. The obstacle theorem shows that route is
mathematically blocked, not merely missing wiring.

### Variable-`S(X)` attempt

This attempt now exists and builds:

- `Goldbach/ClosureBridgeScaleNorm.lean`
- `Goldbach/AnalyticGlobalScaleNorm.lean`
- `Goldbach/AnalyticPointwiseScaleNorm.lean`
- `Goldbach/FinalScaleNorm.lean`
- `Goldbach/CompleteTenorFunX_ScaleNorm.lean`

What it proves:

- the entire closure / witness / final route works if the user supplies a variable normalization
  scale `S(X)`,
- a compatible major lower comparison
  `c0(X) * S(X) ≤ AO_Major.cAO(...) X`,
- and a compatible scaled bank-gap comparison
  `ε_raw ≤ ε * S(X)`.

Important outcome:

- the new top wrapper makes the remaining issue explicit:
  if the old absolute bank error `ε_raw` is kept fixed, then varying `S(X)` alone only helps when
  `S(X)` is large enough to absorb that absolute slack.
- So the likely honest endpoint is not just `S(X)`: the slack normalization also has to move, or
  the closure-facing major lower term has to be repackaged.

### Variable-`ε(X)` attempt

This third additive route now also exists and builds:

- `Goldbach/ClosureBridgeScaleNormEps.lean`
- `Goldbach/AnalyticGlobalScaleNormEps.lean`
- `Goldbach/AnalyticPointwiseScaleNormEps.lean`
- `Goldbach/FinalScaleNormEps.lean`
- `Goldbach/CompleteTenorFunX_ScaleNormEps.lean`

What it adds:

- the closure / witness / final route now allows the slack itself to vary with `X`,
- the current FunX theorem fits this interface with the natural specialization
  `ε(X) = ε_raw / S(X)`,
- so the bank comparison no longer needs a separately supplied scaled-slack hypothesis in that
  specialization.

What it does **not** fix:

- the local positivity condition becomes
  `ε_raw / S(X) < c0(X)`,
  equivalently
  `ε_raw < c0(X) * S(X)`,
- and together with the required major lower comparison
  `c0(X) * S(X) ≤ cAO(X)`,
  this still forces
  `ε_raw < cAO(X)`.

This collapse is now formalized in
`Goldbach/ParallelFunXCanonScaleObstacle.lean`:

- `not_div_route_possible_on_window`

So the third route is useful diagnostically and architecturally, but it still does not discharge the
canonical budget target. The remaining issue is deeper than the slack parameterization: the closure
surface is still forcing the main lower term and the bank error into incompatible normalized shapes.
