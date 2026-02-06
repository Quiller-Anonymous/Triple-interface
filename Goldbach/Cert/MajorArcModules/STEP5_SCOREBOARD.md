# Step 5 scoreboard (Q0 route): frozen interfaces + budgets

This file is the “freeze point” for the successive-approximation workflow:

1. Keep definitions/interfaces fixed.
2. Get coarse bounds that pass the current budgets.
3. Tighten only the bottleneck terms (by computation/certificates) without refactoring Lean.

## Frozen parameters (do not change unless forced)

- Window parameters: `X0 = 1_000_000`, `H = 10_000` (from `Goldbach/BankParams`).
- Q0 truncation: `Q0 = 30_000` (from `Goldbach/AO_OffDiag/TailBlock`).
- Major-arc width: `Δ_canon = 1` (from `Goldbach/Cert/MajorArcModules/TurnkeyRouteQ0.lean`).
- β split: `betaSmallRadius = 1 / (4 * π)` and `betaSmallSet = [-betaSmallRadius, betaSmallRadius]`
  (from `Goldbach/Cert/MajorArcModules/BetaLocalization.lean`).

## Budgeting constants (generated ℚ artifacts)

- Global budgets (`Goldbach/Cert/MajorArcModules/Q0CertData.lean`):
  - `ε₁ = 4`, `ε₂ = 4`.
- ε₂-large budgeting (`Goldbach/Cert/MajorArcModules/Q0MajorTailCertData.lean`):
  - TT* advertised constant `M2 = 50_000`, tail budget `εl = 2`.
- Current ε₂ split convention in `Goldbach/Cert/MajorArcModules/Q0TwoBoundsSpec.lean`:
  - ε₂-small is pinned as `εs = 2`,
  - ε₂-large uses the certified `εl = 2`,
  - so `εs + εl = 4 = ε₂`.

## Step-5 interfaces (Lean “seams”)

All downstream “turnkey Q0 major arc” code depends only on these interfaces + the ℚ budget checks.

- ε₁ (minor / Q0-complement): `Q0MinorEnergyBound Δ_canon 16`
  - Spec: `Goldbach/Cert/MajorArcModules/Q0MinorBound.lean`
  - Tool-axiom seam (polished gold): `Goldbach/Cert/MajorArcModules/Q0MinorEnergyBoundAxiom.lean`
  - Provider module (stage (3) prep): `Goldbach/Cert/MajorArcModules/Q0MinorEnergyBoundProvider.lean`
- ε₂-small (small β major evaluation): `Q0MajorSmallBound Δ_canon εs`
  - Spec: `Goldbach/Cert/MajorArcModules/Q0MajorRoute.lean`
  - Certificate seam (new): `Q0MajorSmallUpperBound Δ_canon U_s` +
    cert check `U_s ≤ εs` (`Goldbach/Cert/MajorArcModules/Q0MajorSmallUpperBoundFromCert.lean`).
  - Current status: proved deterministically (axiom-free) in
    `Goldbach/Cert/MajorArcModules/Q0MajorSmallUpperBoundDeterministic.lean`.
- ε₂-large (large β tail, option-3): `Q0InnerMajorFullTTStarKSupportBound Δ_canon M2`
  - Spec/scaffold: `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarCertScaffold.lean`
  - This is the TT*/Parseval payload that ultimately drives `Q0MajorLargeBound Δ_canon εl`.
  - Current status: Toeplitz top bound is proved deterministically (axiom-free) in
    `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarUpperBoundFromToeplitz.lean`.

The remaining analytic assumptions are centralized in:

- Project-neutral spec sheet: `Goldbach/Cert/MajorArcModules/Q0TwoBoundsConventionalAxioms.lean`
- Current pinned assumptions (fool’s gold): `Goldbach/Cert/MajorArcModules/Q0TwoBoundsPinnedAxioms.lean`

Note (Stage 2 target): the remaining ε₂-large Step-5 goal is generator-facing:
`Q0MajorTailTTStarUpperBoundFromToeplitz.toeplitzExprTopTight_upper_le_U_target`,
where `toeplitzExprTopTight_upper` is the explicit expression from
`Q0MajorTailTTStarStep5ToeplitzUpperBound.lean`.

Build notes:
- Gold-grade staging bundle (no pinned axioms): `lake build Goldbach.Cert.MajorArcModules.All`
- Fool’s-gold turnkey bundle (imports pinned assumptions via `Q0TwoBoundsSpec.lean`):
  `lake build Goldbach.Cert.MajorArcModules.AllFoolsGold`

## Deterministic facts already in Lean (reused during tightening)

- β-splitting bookkeeping: `Goldbach/Cert/MajorArcModules/Q0MajorBoundSplit.lean`.
- TT* “successive approximation” scaffolding (blockwise Cauchy–Schwarz + dyadic q-block indexing):
  `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarBlocks.lean`.
- Kernel tail cap on `betaSmallSetᶜ`:
  - `kernelTailCap = (π^2)/255025` and the derived bound used in budgeting
    (see `Goldbach/Cert/MajorArcModules/KernelTailCapBounds.lean`).
- TT*/Parseval packaging and reduction to a finite `kSupport` sum:
  - `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStar.lean`,
  - `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarFiniteSupport.lean`,
  - `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarCertScaffold.lean`.
- Non-analytic TT* algebra bridge (β-Fourier expansion of `innerMajorQ0`):
  - `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarAlgebra.lean`.

## What “coarse but passes” means here

- Preserve structure until after averaging/squaring:
  - For ε₂-large, do **not** bound Ramanujan sums by absolute values before the TT* expansion.
- Be crude only *after* the cancellation step:
  - Once cross-terms are eliminated/suppressed, use safe bounds (`|sin| ≤ 1`, divisor-sum bounds, etc.).

## Optimization methodology (successive approximation)

This is the “no snipe hunt” workflow we follow once interfaces/parameters are frozen.

**Goal form.** Replace each remaining analytic axiom by:

1. a deterministic Lean reduction to an explicit finite expression `Expr(...)`, and
2. a generated ℚ artifact that bounds `Expr(...)` by a number `U`, plus a final check
   `U ≤ budget` (e.g. `U ≤ M2^2`).

**Key policy.** Be crude only after the cancellation/averaging step:

- Do **not** take `|c_q(t)|` (or `sup_k`) too early if doing so reintroduces the `+Q0^2` barrier.
- Do take crude bounds (`|sin|≤1`, divisor-sum estimates, `Λ(n)≤log N`) once TT*/dispersion has
  produced a positive expression in which cross-terms are already eliminated/suppressed.

Companion spec sheet (what must be preserved vs what can be made coarse):

- `Goldbach/Cert/MajorArcModules/STEP5_U_SPEC.md`

### ε₂-large (TT*/Toeplitz) tightening ladder

We treat the certified TT* budget `M2 = 50_000` as frozen and tighten only the *numerical* upper
bound `U` produced for the finite `kSupport` sum.

- **Knob A (Ramanujan handling):**
  - A0: `|c_q(t)| ≤ q` (fast, pessimistic).
  - A1: `|c_q(t)| ≤ gcd(q,t)` and sum by divisors (moderate work, large gain).
  - A2: exact `c_q(t)=μ(q/d)φ(d)` with `d=gcd(q,t)` (more work).
- **Knob B (sinc handling):**
  - B0: `|sin| ≤ 1`.
  - B1: `|sin y| ≤ min(1,|y|)` and range-split in `t`.
  - B2: use explicit Fourier decay for the smooth weight (where available).
- **Knob C (dispersion structure):**
  - C0: diagonal-only / post-TT* crude bounds.
  - C1: explicit `q=q'` vs `q≠q'` suppression *after* TT* expansion (AO dispersion / alias suppression).

Stop at the first rung where the computed `U` satisfies `U ≤ M2^2`; record the rung and margin.

### ε₂-small tightening (major evaluation on small-β)

ε₂-small is not “wiring only” at the pinned budget `εs=2` unless a dispersion/orthogonality step
is available before absolute values (same genre as ε₂-large).

For experiments:

- Introduce one explicit “engine knob” constant `C_disp` (project-neutral TT*/dispersion input).
- Reduce the ε₂-small bound to a finite expression in `C_disp` + `q≤Q0` sums.
- Sweep `C_disp` to see what range makes `εs ≤ 2` plausible before investing in a full proof.

### Recording rule

Every experiment entry should include:

- which knobs were used (A*, B*, C* or `C_disp` value),
- the resulting `U`/`εs` value and the budget margin,
- the command used and runtime (rough).

## Experiment scripts (feasibility only; not proofs)

- Linearized hard-arc kernel + TT* scale estimate:
  - `scripts/experiments/exp_q0_wlin_ttstar_feasibility.py`
  - Run: `python3 scripts/experiments/exp_q0_wlin_ttstar_feasibility.py`
  - Optional (slow) check against true hard-arc kernel samples:
    `python3 scripts/experiments/exp_q0_wlin_ttstar_feasibility.py --sample-w-hat --samples 200`
  - Parity-stress (recommended): sample only even `t`:
    `python3 scripts/experiments/exp_q0_wlin_ttstar_feasibility.py --sample-w-hat --samples 500 --sample-parity even`

- Linearized `F_k` probe (Toeplitz coefficients) via `W_lin`:
  - `scripts/experiments/exp_q0_fk_ttstar_linearized.py`
  - Run (basic): `python3 scripts/experiments/exp_q0_fk_ttstar_linearized.py`
  - Run (structured `k` clusters): `python3 scripts/experiments/exp_q0_fk_ttstar_linearized.py --k-list '29000:31000:200,59000:61000:200,89000:91000:200,0,2,4,10,20,50,100,200,500,1000,2000,5000,10000,20000'`

- Linearized TT* scale estimate by sampling `F_k` (extrapolation, not a proof):
  - `scripts/experiments/exp_q0_fk_ttstar_linearized_stats.py`
  - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized_stats.py --samples 300 --seed 7 --include-structured`

- True `W_hat(t)` cancellation statistics (random t sampling):
  - `scripts/experiments/exp_q0_w_hat_cancel_ratio_stats.py`
  - Run: `python3 scripts/experiments/exp_q0_w_hat_cancel_ratio_stats.py --samples 200 --seed 1 --parity any`

### Recent experiment outputs (informal)

- Deterministic TT* scaffolds (no q-dispersion; uses only divisor-sum bounds):
  - Run: `python3 scripts/experiments/exp_q0_u_expr_l2_scaffold.py`
    - `Σ_{q≤Q0} Bq2(q) ≈ 7.020816e-04`
    - `U_l2_scaffold ≈ 4.211217e+15` (fails `M2^2=2.5e9`)
  - Run: `python3 scripts/experiments/exp_q0_u_expr_l2_scaffold_cq2.py`
    - (tightens by using exact `|c_q(t)|^2 = μ(q/d)^2 φ(d)^2` instead of `gcd(q,t)^2 ≤ q*gcd(q,t)`)
    - `Σ_{q≤Q0} Bq2(q) ≈ 9.037101e-05`
    - `U_diag (no q factor) ≈ 1.806874e+10` (still 7.23× too big)
    - `U_qcs (global C–S in q) ≈ 5.420623e+14` (hopelessly too big)
    - implied: without a genuine q-dispersion step, a proved TT* bound with `M2=50_000` is not reachable from these scaffolds.
  - Run: `python3 scripts/experiments/exp_q0_u_diag_best.py`
    - computes `S2_exact = ∑_{n≤N0} Λ(n)^2` exactly (prime powers) and uses an “as exact as practical” diagonal-only kernel bound
    - `S2_exact ≈ 1.294681e+07` (vs crude `≤ 1.414e+07`)
    - `Σ_{q≤Q0} Bq2 ≈ 8.191310e-05`
    - `U_diag_best ≈ 1.373027e+10` (still 5.49× above `M2^2`)
    - takeaway: even a fairly sharp *diagonal-only* bound is not enough; a TT*/dispersion step that controls `q≠q'` cross-terms is required to reach `M2=50_000`.

- Repro suite run (fast; pinned commands):
  - Run: `bash scripts/experiments/run_step5_suite.sh`
  - `exp_q0_w_hat_moments.py` (200 samples, seed=1):
    - even `t`: `max |W_hat| ≈ 1.62e-05` at `t=1,996,400`, `mean(W_hat^2) ≈ 1.29e-11`
    - odd `t`: `max |W_hat| ≈ 3.59e-06` at `t=1,181,411`, `mean(W_hat^2) ≈ 1.78e-12`

- Higher-sample `W_hat` moments (still heuristic; slow exact evaluation):
  - Run: `python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 2000 --seed 1 --parity any`
    - `mean |W_hat|^2 ≈ 7.41e-12`
    - extrapolated `∑_{t≤2e6} |W_hat(t)|^2 ≈ 1.48e-05`
  - Run: `python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 2000 --seed 1 --parity even`
    - `mean |W_hat|^2 ≈ 1.23e-11`
    - extrapolated `∑_{t≤2e6} |W_hat(t)|^2 ≈ 2.46e-05`
  - Run: `python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 2000 --seed 1 --parity odd`
    - `mean |W_hat|^2 ≈ 2.10e-12`
    - extrapolated `∑_{t≤2e6} |W_hat(t)|^2 ≈ 4.20e-06`
  - takeaway: the “right” proved inequality to target is an **L2-in-t / large-sieve style** bound
    on `∑ |W_hat(t)|^2`; numerically, this looks close to the `M2=50k` threshold when combined with
    the crude `S2^2` bound.

- Exact fast computation for the *linearized* Ramanujan-cancellation main term
  `W_lin(t) = (2/X) * ∑_{q≤Q0} c_q(t)/q` (derivable from the small-angle regime `sin y ≈ y`):
  - Script: `scripts/experiments/exp_q0_w_hat_linear_main_l2.py`
  - Run: `python3 scripts/experiments/exp_q0_w_hat_linear_main_l2.py`
    - `Tmax=2,000,000`: `∑_{t≤Tmax} |W_lin(t)|^2 ≈ 2.675420e-05` (even ≈ `2.349488e-05`, odd ≈ `3.259312e-06`)

- Generator-aligned Step5 “Toeplitz top” bound (current Lean resource lemma):
  - Script: `scripts/gen_q0_major_tail_ttstar_cert.py`
  - Run: `python3 scripts/gen_q0_major_tail_ttstar_cert.py`
  - Parameters: `X0=1_000_000`, `H=10_000`, `Q0=30_000`, `q_small=12`, `delta_split=50`, `delta_weight_split=1`
  - Output: `U_raw = 12_864_746_585` (fails `M2^2 = 2_500_000_000` by `≈ 5.15×`; the Lean artifact is currently capped at `M2^2` to keep builds green)

- Deterministic band-sums for the “passes-budget” hybrid kernel
  `W_mix(t) = W_small(t) + W_large_lin(t)` on the TT*/Toeplitz bandwidth `t≤N0=X0+H`:
  - Script: `scripts/experiments/exp_q0_w_mix_band_sums.py`
  - Run: `python3 scripts/experiments/exp_q0_w_mix_band_sums.py --q-small q_small`
  - Output (X=1e6, Q0=30000, N0=1,010,000; BW_mix := 2*∑_{t even≤N0} |W_mix(t)|^2):
    - `q_small=1`:  `BW_mix ≈ 1.442470836124e-05`, `U_nonzero ≈ 2.417868017e+09`
    - `q_small=4`:  `BW_mix ≈ 1.322821890668e-05`, `U_nonzero ≈ 2.217312587e+09`
    - `q_small=12`: `BW_mix ≈ 1.284703238013e-05`, `U_nonzero ≈ 2.153418144e+09`
    - `q_small=32`: `BW_mix ≈ 1.279120048746e-05`, `U_nonzero ≈ 2.144059608e+09`
  - Interpretation:
    - `q_small` is not a sensitive knob (changes `U_nonzero` by < 12% between 1 and 32).
    - We freeze `q_small=12` as the current “good default” (fast and already safely under budget).
  - Scaling sanity check (evidence that the worst case is at `X=X0`):
    - Run: `python3 scripts/experiments/exp_q0_w_mix_band_sums.py --X 2000000 --H 10000 --q-small 12`
    - Output: `BW_mix ≈ 7.943848360838e-06` at `X=2e6` (vs `1.284703238013e-05` at `X=1e6`).

- `t=0` spike sanity bound (crude but safe):
  - For hard arcs, `Ŵ_X(0) = (2/X) * ∑_{q≤Q0} φ(q)/q`.
  - At `X0=1e6`, `∑_{q≤30000} φ(q)/q ≈ 18237.9658`, so `Ŵ_{X0}(0) ≈ 0.036476` and `Ŵ_{X0}(0)^2 ≈ 0.0013305`.
  - A fully crude bound on the `t=0` contribution to `∑_k |F_k|^2` is `(N0-3)*(log N0)^4 * Ŵ_{X0}(0)^2 ≈ 4.91e7`.
  - Combined with `U_nonzero(q_small=12) ≈ 2.153e9`, this keeps the total within `M2^2 = 2.5e9` with comfortable slack.

- Deterministic Taylor-remainder bound for the `q≥13` small-angle linearization:
  - Using `|sin y - y| ≤ |y|^3/6` (valid for `|y|≤1`) and `|c_q(t)|≤q`, we get
    `|W_err(t)| ≤ (π^2/9) * t^2 / X^3` for the `q≥13` remainder term on the band `t≤N0`.
  - This implies `BW_err := 2*∑_{t even≤N0} |W_err(t)|^2 ≲ 2.528e-07`, hence
    `U_err ≤ S2_exact^2 * BW_err ≲ 4.24e7` (tiny compared to the `2.5e9` budget).

- Combined “coarse but passes” numerical picture at the frozen `M2=50_000`:
  - Use `q_small=12` (default), `U_nonzero ≈ 2.153e9`.
  - Add the crude `t=0` bound `U_t0 ≈ 4.91e7`.
  - Add the crude Taylor remainder bound `U_err ≈ 4.24e7`.
  - Total heuristic upper envelope: `U_total ≈ 2.245e9 < 2.5e9 = M2^2` (≈ 10% slack).
    - `max |W_lin| ≈ 5.852776e-05` at `t=1,884,960` (same “worst t” found by the hard-arc scans)
  - Run: `python3 scripts/experiments/exp_q0_w_hat_linear_main_l2.py --Tmax 1010000`
    - `Tmax=1,010,000`: `∑_{t≤Tmax} |W_lin(t)|^2 ≈ 1.183394e-05` (even ≈ `1.032591e-05`, odd ≈ `1.508024e-06`)
  - takeaway: in the TT*/Toeplitz *bandwidth* (`|t| ≲ 2N0`), the “linearized” Ramanujan sum model already
    matches the observed hard-arc `W_hat` scale extremely well, and is computable in `O(Tmax log Q0)`.

- “Small-q exact + large-q linear” hybrid kernel (still heuristic, but now *structurally* aligned):
  - Define for `t≥1`:
    - `W_small(t) := (1/(π t)) * ∑_{1≤q≤12} c_q(t) * sin(2π t/(qX))`
    - `W_large_lin(t) := (2/X) * ∑_{13≤q≤Q0} c_q(t)/q`
    - `W_mix(t) := W_small(t) + W_large_lin(t)`
  - Computed directly (Python, `t≤N0=1,010,000`, using the divisor-convolution for the large-q term):
    - `∑_{t even ≤ N0} |W_mix(t)|^2 ≈ 6.423516e-06`
    - implied worst-case progression bound for `k=0` (parity even): `BW_mix := 2 * ∑_{t even≤N0} |W_mix(t)|^2 ≈ 1.284703e-05`
    - plugging into the “HS-style” TT bound `U ≈ S2_exact^2 * BW_mix` (with `S2_exact ≈ 1.294681e+07`) gives
      `U ≈ 2.153418e+09` which is **below** `M2^2 = 2.5e+09` (ratio ≈ `0.861`).
  - takeaway: this is the first “coarse but passes” *numerical* scaffold that uses cancellation in the q-sum
    and lands under the `M2=50,000` budget; the remaining job is to turn the `q≥13` linearization into a
    rigorous inequality (bound the `sin(y)-y` remainder with explicit constants).
  - `exp_q0_fk_ttstar_w_hat_mc.py` (MC, `k_samples=20`, `n_samples=100`, seed=1):
    - `F_0 ≈ 15.63` (`|F_0|^2 ≈ 244.30`)
    - `max |F_k| ≈ 9.56` on sampled `k>0`
    - extrapolated `M2_est ≈ 3,235.3`

- Structured/stress “worst t” confirmation (exact hard-arc `W_hat`):
  - Run: `python3 scripts/experiments/exp_q0_w_hat_top_s.py --Tmax 2000000 --topK 500`
    - `max |W_hat| ≈ 4.84997e-05` at `t=1,884,960` (still the maximizer on the top-`|S(t)|` scan)
  - Run: `python3 scripts/experiments/exp_q0_w_hat_structured_t.py --Tmax 2000000 --topK 2000 --primorial-p 19 --primorial-min-prime 11 --include-hc --preselect-by-S --evalE 400`
    - `max |W_hat| ≈ 4.84997e-05` at `t=1,884,960` (same maximizer; evaluated 400 preselected candidates)
  - Run: `python3 scripts/experiments/exp_q0_w_hat_gcd_stress.py --Tmax 2000000 --topK 300 --primorials 11,13,17,19 --lcms 10,12,14,16,18,20`
    - `max |W_hat| ≈ 4.84997e-05` at `t=1,884,960` (runtime ≈ 245s; still no larger maximizer)

- q-block cancellation diagnostics (exact hard-arc `W_hat`):
  - Run: `python3 scripts/experiments/exp_q0_w_hat_q_decomposition.py --t 1884960 --t 1996400 --t 1181411 --show-top-blocks 12`
    - `t=1,884,960`: `|W_hat|≈4.85e-05`, cancellation ratio `≈0.141` (trivial abs bound `≈3.44e-04`)
    - `t=1,996,400`: `|W_hat|≈1.62e-05`, cancellation ratio `≈0.0746` (trivial abs bound `≈2.17e-04`)
    - `t=1,181,411` (odd): `|W_hat|≈3.59e-06`, cancellation ratio `≈0.0469` (trivial abs bound `≈7.65e-05`)

- Kernel ℓ² mass along the *actual* TT*/Toeplitz progression `t=|2n+k-N|` (hybrid kernel, not a proof):
  - Script: `scripts/experiments/exp_q0_w_hat_progression_l2.py`
  - Run (N = `X0+H`, hybrid `Qsplit=500`):  
    `python3 scripts/experiments/exp_q0_w_hat_progression_l2.py --Qsplit 500 --k-samples 60 --n-samples 2000 --seed 3 --include-structured --N 1010000 --Tmax 1200000`
    - `max Σ_n |W(t)|^2` (over sampled `k`) ≈ `1.400028e-05`
    - typical `Σ_n |W(t)|^2` ≈ `6e-06`
  - Run (N = `X0`, same settings but smaller):  
    `python3 scripts/experiments/exp_q0_w_hat_progression_l2.py --Qsplit 500 --k-samples 30 --n-samples 1500 --seed 4 --include-structured --N 1000000 --Tmax 1200000`
    - `max Σ_n |W(t)|^2` (over sampled `k`) ≈ `1.303371e-05`
  - takeaway: the progression ℓ² scale is in the `≈1e-5` range that is consistent with `M2=50,000`.

- “t=0 spike” adversarial probe (isolates the constant-mode contribution scale):
  - Run: `python3 scripts/experiments/exp_q0_ttstar_t0_spike.py --k-samples 5000 --seed 1 --include-structured --top 15`
    - `W0 hard ≈ 3.6476e-02`, `W0 smooth ≈ 5.4714e-02` (≈1.5×)
    - max sampled `|F_k[t=0]|_hard ≈ 6.29`, `|F_k[t=0]|_smooth ≈ 9.44`

- TT* scale estimates (heuristic; not proofs):
  - N-endpoint sensitivity (same random seed; `k_samples=40`, `n_samples=200`, `Qsplit=2000`):
    - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --N 1000000 --k-samples 40 --n-samples 200 --seed 7 --include-structured --Qsplit 2000 --estimate-f0`
      - `M2_est ≈ 3,472.4`
    - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --N 1005000 --k-samples 40 --n-samples 200 --seed 7 --include-structured --Qsplit 2000 --estimate-f0`
      - `M2_est ≈ 4,049.5`
    - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --N 1010000 --k-samples 40 --n-samples 200 --seed 7 --include-structured --Qsplit 2000 --estimate-f0`
      - `M2_est ≈ 3,546.8`
    - takeaway: the heuristic TT* scale is fairly stable across `N∈{X, X+H/2, X+H}` at these sample sizes.

  - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized_stats.py --samples 500 --seed 7 --include-structured`
    - `W_lin` model: extrapolated `M2_est ≈ 4,313.5` (max sampled `|F_k| ≈ 16.49` at `k=48,846`)
  - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --k-samples 80 --n-samples 300 --seed 3 --include-structured --Qsplit 2000 --estimate-f0 --quantiles 0.5,0.9,0.99 --top 12`
    - hybrid `W_hat` MC: extrapolated `M2_est ≈ 3,001.6` (max sampled `|F_k| ≈ 9.59`)
  - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_small_t_split.py --k-samples 60 --n-samples 300 --seed 4 --include-structured --Qsplit 2000 --T-list 0,10,100,1000 --quantiles 0.5,0.9,0.99`
    - `M2_full_est ≈ 2,368.8`; small-`|t|` energy shares are `≪ 1` up to `T=1000` in this sample

- Run (defaults; linearized full scan to `t≤2,000,000`, `N=1,010,000`):
  - `M2_est (all t mean) ≈ 47,588.8`
  - `M2_est (max parity) ≈ 63,068.2`
- Sampled true hard-arc `W_hat` (200 samples, all `t≤2,000,000`):
  - `mean(W_hat^2) ≈ 4.42e-12`, `max |W_hat| ≈ 1.14e-05`
- Sampled true hard-arc `W_hat` (500 samples, even `t≤2,000,000`):
  - `mean(W_hat^2) ≈ 1.08e-11`, `max |W_hat| ≈ 1.43e-05`
- Sampled true hard-arc `W_hat` (1000 samples, all `t≤2,000,000`, seed=1):
  - `mean(W_hat^2) ≈ 7.11e-12`, `max |W_hat| ≈ 2.68e-05`
- Sampled true hard-arc `W_hat` (1000 samples, even `t≤2,000,000`, seed=2):
  - `mean(W_hat^2) ≈ 1.16e-11`, `max |W_hat| ≈ 2.15e-05`
- Structured stress (top-30 `t` by `|S(t)|` from the linearized model; exact `W_hat(t)` computed):
  - `max |W_hat| ≈ 4.85e-05` at `t=1,884,960` (ratio `|W_hat|/|W_lin| ≈ 0.83` on this set)
- Structured stress (top-200 `t` by `|S(t)|`; exact `W_hat(t)` computed):
  - Run: `python3 scripts/experiments/exp_q0_w_hat_top_s.py --topK 200`
  - `max |W_hat| ≈ 4.85e-05` at `t=1,884,960` (same maximizer; ratios in this list are typically `≈ 0.74–0.87`)
- Structured stress (primorial-multiple family; 865 candidates; exact `W_hat(t)` computed):
  - `max |W_hat| ≈ 4.85e-05` at `t=1,884,960` (same maximizer as the top-`|S(t)|` scan)
- Structured stress (primorial-multiples + highly-composite-ish family; 1,153 candidates; exact `W_hat(t)` computed):
  - `max |W_hat| ≈ 4.85e-05` at `t=1,884,960` (no larger maximizer found)
- q-decomposition of `W_hat(t)` (dyadic q-blocks, keeping Ramanujan signs):
  - At `t=1,884,960`: `|W_hat| ≈ 4.85e-05` while the trivial abs bound gives `≈ 3.44e-04` (≈7.1×),
    cancellation ratio `|Σ term_q|/Σ|term_q| ≈ 0.141`.
  - Dominant positive blocks are small/medium q (`(32,64]`, `(64,128]`, `(128,256]`); dominant negative
    blocks are large q (`(4096,8192]`, `(8192,16384]`, `(16384,30000]`).
  - Odd-parity stress: at `t=1,576,575` (max-`|S(t)|` among odd `t` in the linearized scan),
    `|W_hat| ≈ 1.71e-05` and cancellation ratio `≈ 0.0667` (trivial abs bound `≈ 2.56e-04`, ≈15×).
- gcd-structure stress (multiples of `primorial≤11,13,17` and `lcm≤10,12,14,16,18`; 1,586 candidates):
  - `max |W_hat|` still occurs at `t=1,884,960` with `|W_hat| ≈ 4.85e-05`.
  - Sampled cancellation ratios for top candidates stay in the same range (e.g. `t=1,834,560` gives `≈ 0.137`).

- Random t cancellation statistics for true `W_hat(t)`:
  - Run: `python3 scripts/experiments/exp_q0_w_hat_cancel_ratio_stats.py --samples 200 --seed 1 --parity any`
    - `max |W_hat| ≈ 1.28e-05`, mean `|W_hat| ≈ 1.88e-06`
    - mean cancellation ratio `|Σ term| / Σ|term| ≈ 0.0429` (median `≈ 0.0314`, min `≈ 5.19e-05`)
  - Even-parity stress:
    - Run: `python3 scripts/experiments/exp_q0_w_hat_cancel_ratio_stats.py --samples 200 --seed 2 --parity even`
    - `max |W_hat| ≈ 1.95e-05`, mean cancellation ratio `≈ 0.0553` (median `≈ 0.0453`)
  - Higher-sample even-parity probe:
    - Run: `python3 scripts/experiments/exp_q0_w_hat_cancel_ratio_stats.py --samples 1000 --seed 3 --parity even`
    - `max |W_hat| ≈ 2.87e-05` (random; still below the structured worst `≈ 4.85e-05`), top samples have cancellation ratios in the `≈ 0.08–0.12` range.
  - Higher-sample odd-parity probe:
    - Run: `python3 scripts/experiments/exp_q0_w_hat_cancel_ratio_stats.py --samples 1000 --seed 4 --parity odd`
    - `max |W_hat| ≈ 6.76e-06`, mean cancellation ratio `≈ 0.0332` (median `≈ 0.0236`).

- Direct comparison: true `W_hat(t)` vs linearized `W_lin(t) = (2/X)·Σ_{q≤Q0} c_q(t)/q` (not a proof):
  - Run: `python3 scripts/experiments/exp_q0_w_hat_vs_w_lin.py --samples 200 --seed 1 --parity any --include '1884960,1834560,1576575'`
    - `max |W_hat| ≈ 4.85e-05`, `max |W_lin| ≈ 5.85e-05`.
    - At the structured maximizers:
      - `t=1,884,960`: `|W_hat|/|W_lin| ≈ 0.83`
      - `t=1,834,560`: `|W_hat|/|W_lin| ≈ 0.81`
      - `t=1,576,575`: `|W_hat|/|W_lin| ≈ 0.81`
    - Caution: `W_lin` is *not* a pointwise majorant; there are many sampled `t` where `|W_lin(t)|` is
      extremely small (near cancellation in `Σ c_q(t)/q`) while `|W_hat(t)|` is still around `≈ 1e-06`,
      so the ratio `|W_hat|/|W_lin|` can be huge even though both are small in absolute terms.
  - Run: `python3 scripts/experiments/exp_q0_w_hat_vs_w_lin.py --samples 400 --seed 3 --parity even --include '1884960,1834560'`
    - Confirms the same pattern on even `t`: the “large `|W_hat|` cases” track `W_lin` with ratios
      roughly `≈ 0.6–0.9`, but `W_lin` can be near-zero on other `t`.

- Linearized `F_k` probe via `W_lin` (selected `k`, not a proof):
  - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized.py --k-list '0,2,4,10,20,50,100,200,500,1000,2000,5000,10000,20000,50000,100000,0:200000:10000'`
    - `N=1,010,000`: `max |F_k| ≈ 25.47` at `k=0`; typical `|F_k|` in the tested list is `≈ 1–7`; `∑|F_k|^2 ≈ 9.73e2` (over the 32 tested `k`).
    - `N=1,000,000`: `max |F_k| ≈ 25.17` at `k=0`; typical `|F_k|` in the tested list is `≈ 1–7`; `∑|F_k|^2 ≈ 9.59e2` (same `k` list).
    - Clustered resonance scan near multiples of `30,000`:
    - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized.py --k-list '0,2,4,10,20,50,100,200,500,1000,2000,5000,10000,20000,29000:31000:200,59000:61000:200,89000:91000:200'`
    - `N=1,010,000`: spikes up to `|F_29400| ≈ 8.39`, `|F_30600| ≈ 6.58`, `|F_60600| ≈ 6.92`, `|F_90600| ≈ 6.80` (still far below any catastrophic regime).

- Hybrid-`W_hat` TT* Monte Carlo (fast sanity, not a proof):
  - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --k-samples 20 --n-samples 100 --seed 1 --Qsplit 2000 --estimate-f0`
  - `N=1,010,000`: `F_0 ≈ 1.563e+01`, `mean |F_k|^2 ≈ 5.18`, extrapolated `M2_est ≈ 3.24e+03` (well below `50,000`).

- `W_hat` moment probe (quick sanity, not a proof):
  - Run: `python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 200 --seed 1 --parity even`
  - `max |W_hat| ≈ 1.62e-05`, `mean |W_hat|^2 ≈ 1.29e-11` on even `t` sampled uniformly from `[1,2X]`.
  - Random/structured mix (`100` values of `k`, including clusters at `30k·m` and 50 random `k∈[0,10^6]`):
    - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized.py --k-list "$(python3 - <<'PY'\nimport random\nrandom.seed(7)\nks=set()\nwhile len(ks)<50:\n    ks.add(random.randrange(0,1_000_000+1))\nfor base in [30000,60000,90000,120000,150000,180000]:\n    for off in [0,200,400,600,800,1000]:\n        ks.add(base+off)\nks.update([0,2,4,10,20,50,100,200,500,1000,2000,5000,10000,20000])\nprint(','.join(str(k) for k in sorted(ks)))\nPY\n)"` (bash)
    - `N=1,010,000`: `max |F_k| ≈ 25.47` at `k=0`, `∑|F_k|^2 ≈ 1.79e3` over the tested `k`, with many sampled `k` giving `|F_k| ≪ 1` (often `≲ 1e-4`).
  - Random-only mix (`200` random `k∈[1,10^6]`):
    - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized.py --k-list "$(python3 - <<'PY'\nimport random\nrandom.seed(11)\nks=set()\nwhile len(ks)<200:\n    ks.add(random.randrange(1,1_000_000+1))\nprint(','.join(str(k) for k in sorted(ks)))\nPY\n)"` (bash)
    - `N=1,010,000`: `∑|F_k|^2 ≈ 2.14e3` over the 200 tested `k` (mean `|F_k|^2 ≈ 10.7`), `max |F_k| ≈ 17.23` at `k=66,234`.

  - Extrapolated TT* scale from sampled `k>0`:
    - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized_stats.py --samples 300 --seed 7 --include-structured`
      - sampled mean `|F_k|^2 ≈ 9.50`, extrapolated `M2_est ≈ 4,380` (uses symmetry + `|F_0|`).
    - Same sample seed across the window endpoints:
      - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized_stats.py --N 1000000 --samples 300 --seed 7 --include-structured`
        - sampled mean `|F_k|^2 ≈ 8.65`, extrapolated `M2_est ≈ 4,160`.
      - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized_stats.py --N 1005000 --samples 300 --seed 7 --include-structured`
        - sampled mean `|F_k|^2 ≈ 10.5`, extrapolated `M2_est ≈ 4,598`.
    - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_linearized_stats.py --samples 600 --seed 8 --include-structured`
      - sampled mean `|F_k|^2 ≈ 10.33`, extrapolated `M2_est ≈ 4,569`.
    - Interpretation: on the `W_lin` model, the “natural” scale is `M2 ~ 4–5k`, making the frozen
      budget `M2=50k` plausibly conservative by an order of magnitude.

- Monte-Carlo `F_k` probe using a fast hybrid approximation to the true hard-arc kernel `W_hat(t)` (not a proof):
  - Script: `scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py`
  - Kernel used:
    - Exact sine sum for `q ≤ Qsplit` plus linearized tail for `q > Qsplit` via the precomputed
      divisor/Mertens identity for `Σ_{q≤Q} c_q(t)/q`.
  - Run (default `N=X+H=1,010,000`):
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 30 --n-samples 2000 --seed 11 --include-structured --estimate-f0`
    - Results:
      - sampled mean `|F_k|^2 ≈ 1.04` over `k>0`, extrapolated `M2_est ≈ 1,450`.
  - Run (window start `N=1,000,000`):
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --N 1000000 --Qsplit 500 --k-samples 30 --n-samples 2000 --seed 11 --include-structured --estimate-f0`
    - Results:
      - sampled mean `|F_k|^2 ≈ 0.986` over `k>0`, extrapolated `M2_est ≈ 1,404`.
  - Interpretation: this is very strong feasibility evidence that `M2=50k` is conservative; it also suggests
    the `W_lin` model is (as expected) pessimistic for TT*/Toeplitz because it has less oscillatory cancellation.

- q-block “dispersion locus” probe for true `W_hat(t)` (dyadic q-block covariance on sampled `t`, not a proof):
  - Script: `scripts/experiments/exp_q0_w_hat_qblock_corr.py`
  - Run: `python3 scripts/experiments/exp_q0_w_hat_qblock_corr.py --samples 200 --seed 5 --parity even --include '1884960,1834560,1576575'`
    - `blocks=16` (dyadic up to `Q0=30000`), processed `203` `t` values in `≈1.14s`.
    - `sum diag E[raw_j^2] ≈ 5.55e+02`, `max off-diagonal |E[raw_j raw_j’]| ≈ 5.37e+01` (between adjacent blocks).
    - Largest mean `|raw_j|` blocks are mid-q (`(32,64]`, `(64,128]`, `(128,256]`) and the top-q blocks (`(8192,16384]`, `(16384,30000]`),
      matching the earlier dyadic decomposition seen at `t=1,884,960`.
  - Weighted variant (closer to the TT*/Toeplitz kernel scale; uses `w_j(t)=raw_j(t)/(π t)` so that `Σ_j w_j(t)=W_hat(t)`):
    - Run (even `t`): `python3 scripts/experiments/exp_q0_w_hat_qblock_corr.py --samples 200 --seed 5 --parity even --include '1884960,1834560,1576575' --report-top 8 --weighted`
      - `sum diag E[w_j^2] ≈ 3.09e-11`, `max off abs ≈ 1.97e-12` (adjacent blocks).
      - Largest correlations among top pairs are `|corr| ≈ 0.58–0.63` between adjacent/mid-vs-top blocks.
      - Top mean `|w_j|` blocks: `(64,128]`, `(128,256]`, and the top-q blocks `(8192,16384]`, `(16384,30000]`.
    - Run (odd `t`): `python3 scripts/experiments/exp_q0_w_hat_qblock_corr.py --samples 200 --seed 6 --parity odd --include '1884960,1576575' --report-top 8 --weighted`
      - `sum diag E[w_j^2] ≈ 2.41e-11`, `max off abs ≈ 1.10e-12` (between `(1024,2048]` and `(2048,4096]`).
      - Largest correlations among top pairs are `|corr| ≈ 0.48–0.63` (still localized to nearby blocks).

- Stability check: `Qsplit` sweep for the hybrid-`W_hat` Monte-Carlo `F_k` probe (not a proof):
  - Same run parameters: `X=1,000,000`, `Q0=30,000`, `N=1,010,000`, `k-samples=30`, `n-samples=2000`, `seed=11`, `--include-structured`, `--estimate-f0`.
  - Runs:
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 200 --k-samples 30 --n-samples 2000 --seed 11 --include-structured --estimate-f0`
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 30 --n-samples 2000 --seed 11 --include-structured --estimate-f0`
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 1000 --k-samples 30 --n-samples 2000 --seed 11 --include-structured --estimate-f0`
  - Result: identical (to printed precision) `mean |F_k|^2 ≈ 1.041` and `M2_est ≈ 1450` across `Qsplit ∈ {200,500,1000}`.
    This suggests the hybrid kernel split is not driving the observed scale.

- Kernel-moment probe (true `W_hat` moments over sampled `t`, not a proof):
  - Script: `scripts/experiments/exp_q0_w_hat_moments.py`
  - Even `t`:
    - Run: `python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 400 --seed 6 --parity even --include '1884960,1834560,1576575'`
    - `mean |W_hat|^2 ≈ 2.19e-11`, `Sum_{t<=Tmax} |W_hat(t)|^2 ≈ 4.37e-05` (heuristic extrapolation, `Tmax=2,000,000`).
    - Higher-sample rerun (reduced MC noise):
      - Run: `python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 1200 --seed 6 --parity even --include '1884960,1834560,1576575'`
      - `mean |W_hat|^2 ≈ 1.42e-11`, `Sum_{t<=Tmax} |W_hat(t)|^2 ≈ 2.83e-05`.
  - Odd `t`:
    - Run: `python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 400 --seed 7 --parity odd --include '1884960,1576575'`
    - `mean |W_hat|^2 ≈ 8.54e-12`, `Sum_{t<=Tmax} |W_hat(t)|^2 ≈ 1.71e-05`.
  - Mixed parity:
    - Run: `python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 400 --seed 8 --parity any --include '1884960,1834560,1576575'`
    - `mean |W_hat|^2 ≈ 1.74e-11`, `Sum_{t<=Tmax} |W_hat(t)|^2 ≈ 3.47e-05`.

- Hybrid-`W_hat` Monte Carlo `F_k` probe: larger k/n sampling at the mid-window point `N=1,005,000` (not a proof):
  - Runs (`X=1e6`, `Q0=30000`, `Qsplit=500`, `k-samples=50`, `n-samples=5000`, `--include-structured`, `--estimate-f0`):
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --N 1005000 --Qsplit 500 --k-samples 50 --n-samples 5000 --seed 12 --include-structured --estimate-f0`
      - `mean |F_k|^2 ≈ 4.30`, `M2_est ≈ 2,941`.
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --N 1005000 --Qsplit 500 --k-samples 50 --n-samples 5000 --seed 13 --include-structured --estimate-f0`
      - `mean |F_k|^2 ≈ 3.87`, `M2_est ≈ 2,790`.
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --N 1005000 --Qsplit 500 --k-samples 50 --n-samples 5000 --seed 14 --include-structured --estimate-f0`
      - `mean |F_k|^2 ≈ 2.80`, `M2_est ≈ 2,370`.
  - Interpretation: still orders of magnitude below the frozen budget `M2=50k`; distribution appears heavy-tailed (median `|F_k|^2` stays `≈ 0.75–1.0` while means vary with the sampled tail).

- Hybrid-`W_hat` Monte Carlo `F_k` probe: larger k-sample at the window endpoint `N=1,010,000` (not a proof):
  - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 200 --n-samples 5000 --seed 15 --include-structured --estimate-f0`
    - computed `236` `k>0` values, `kernel cache size ≈ 9,310` `t` values.
    - `mean |F_k|^2 ≈ 2.15`, `median |F_k|^2 ≈ 4.6e-02`, `max |F_k| ≈ 10.18`.
    - extrapolated `M2_est ≈ 2,083` (still far below `50,000`).
  - Repeat seed:
    - Run: `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 200 --n-samples 5000 --seed 16 --include-structured --estimate-f0`
      - `mean |F_k|^2 ≈ 2.92`, `median |F_k|^2 ≈ 4.7e-02`, `max |F_k| ≈ 11.72`.
      - extrapolated `M2_est ≈ 2,428`.

- Hybrid-`W_hat` Monte Carlo `F_k` probe: tail quantiles for `|F_k|^2` (not a proof):
  - Runs (`N=1,010,000`, `Qsplit=500`, `k-samples=1000`, `n-samples=2000`, `--include-structured`, `--estimate-f0`):
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 1000 --n-samples 2000 --seed 21 --include-structured --estimate-f0 --top 12`
      - `mean |F_k|^2 ≈ 2.64`, `median ≈ 2.07e-03`.
      - quantiles: `q90 ≈ 3.84`, `q99 ≈ 5.91e+01`, `q99.9 ≈ 1.33e+02`.
      - extrapolated `M2_est ≈ 2,311`.
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 1000 --n-samples 2000 --seed 22 --include-structured --estimate-f0 --top 8`
      - `mean |F_k|^2 ≈ 2.94`, `median ≈ 1.89e-04`.
      - quantiles: `q90 ≈ 4.22`, `q99 ≈ 7.38e+01`, `q99.9 ≈ 1.23e+02`.
      - extrapolated `M2_est ≈ 2,439`.
  - Interpretation: the distribution is extremely heavy-tailed (median ≪ mean), but even the observed `q99.9`
    values are compatible with `M2=50k` being very conservative.

- Hybrid-`W_hat` Monte Carlo `F_k` probe: reduced MC noise (`n-samples=5000`) for the tail quantiles (not a proof):
  - Runs (`N=1,010,000`, `Qsplit=500`, `k-samples=1000`, `n-samples=5000`, `--include-structured`, `--estimate-f0`, no top list):
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 1000 --n-samples 5000 --seed 21 --include-structured --estimate-f0 --top 0`
      - `mean |F_k|^2 ≈ 2.32`, `median ≈ 1.37e-03`.
      - quantiles: `q90 ≈ 3.23`, `q99 ≈ 4.66e+01`, `q99.9 ≈ 9.31e+01`.
      - extrapolated `M2_est ≈ 2,166`.
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 1000 --n-samples 5000 --seed 22 --include-structured --estimate-f0 --top 0`
      - `mean |F_k|^2 ≈ 2.91`, `median ≈ 5.27e-04`.
      - quantiles: `q90 ≈ 4.43`, `q99 ≈ 7.13e+01`, `q99.9 ≈ 1.30e+02`.
      - extrapolated `M2_est ≈ 2,426`.
  - Interpretation: quantiles are consistent with the lower-noise expectation (q99.9 stabilizes around `~1e2`),
    and `M2_est` remains safely ≪ `50,000`.

- Hybrid-kernel validation: error of `W_hat_hybrid(t;Qsplit)` vs true `W_hat(t)` (not a proof):
  - Script: `scripts/experiments/exp_q0_w_hat_hybrid_error.py`
  - Runs (even `t`, `samples=150`, `seed=21`, include the structured `t` values):
    - `python3 scripts/experiments/exp_q0_w_hat_hybrid_error.py --Qsplit 200 --samples 150 --seed 21 --parity even --include '1884960,1834560,1576575'`
      - `max abs err ≈ 3.86e-09`, `mean abs err ≈ 1.86e-10`, `max rel err ≈ 1.54e-02`.
    - `python3 scripts/experiments/exp_q0_w_hat_hybrid_error.py --Qsplit 500 --samples 150 --seed 21 --parity even --include '1884960,1834560,1576575'`
      - `max abs err ≈ 5.00e-10`, `mean abs err ≈ 2.37e-11`, `max rel err ≈ 4.59e-03`.
    - `python3 scripts/experiments/exp_q0_w_hat_hybrid_error.py --Qsplit 1000 --samples 150 --seed 21 --parity even --include '1884960,1834560,1576575'`
      - `max abs err ≈ 7.15e-11`, `mean abs err ≈ 3.83e-12`, `max rel err ≈ 2.28e-04`.
  - Interpretation: hybridization error is far below the natural `W_hat` scale (`~1e-05` to `5e-05`) for the tested `t`,
    so the `F_k` hybrid-`W_hat` Monte Carlo looks like a reliable feasibility proxy (not a proof).

- Hybrid-`W_hat` Monte Carlo `F_k` probe: adversarial structured `k` list (not a proof):
  - Data: `scripts/experiments/data/adversarial_k_set1.txt` (1,159 admissible `k>0` values after filtering).
  - Runs (`N=1,010,000`, `Qsplit=500`, `n-samples=5000`, `--estimate-f0`, `--k-file`):
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --n-samples 5000 --seed 30 --estimate-f0 --top 20 --quantiles 0.5,0.9,0.99,0.999,0.9999 --k-file scripts/experiments/data/adversarial_k_set1.txt`
      - `mean |F_k|^2 ≈ 9.21`, `median ≈ 1.83`, `max |F_k| ≈ 11.14`.
      - extrapolated `M2_est ≈ 4,314` (still ≪ `50,000`).
    - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --n-samples 5000 --seed 31 --estimate-f0 --top 10 --quantiles 0.5,0.9,0.99,0.999 --k-file scripts/experiments/data/adversarial_k_set1.txt`
      - `mean |F_k|^2 ≈ 9.45`, `median ≈ 2.09`, `max |F_k| ≈ 11.23`.
      - extrapolated `M2_est ≈ 4,370` (still ≪ `50,000`).
  - Interpretation: even a highly gcd-structured `k` family (far from “random k”) lands at `M2_est ~ 4.3k`,
    supporting `M2=50k` as very conservative for experiments.

- Small-|t| split experiment (to guide a certifiable split `U = U_small(T) + U_tail(T)`) (not a proof):
  - Script: `scripts/experiments/exp_q0_fk_ttstar_small_t_split.py`
  - Meaning of `t`: `t = |2n + k - N|`. For each sampled `k`, we estimate `F_k(full)` by MC and compute `F_k(|t|≤T)`
    exactly by enumerating the (at most two) `n` solutions for each `t`.
  - Note: default is `W(0)=0` (balanced / constant mode removed), matching the `W_hat(t)` convention in the MC scripts.
  - Runs (`N=1,010,000`, `Qsplit=500`, `n-samples=5000`, cutoffs `T ∈ {0,10,100,1000,10000}`):
    - Mixed k set (200 random + `--include-structured`, 563 admissible `k`):
      - `python3 scripts/experiments/exp_q0_fk_ttstar_small_t_split.py --Qsplit 500 --n-samples 5000 --seed 41 --k-samples 200 --include-structured --T-list 0,10,100,1000,10000`
      - Full: `mean |F_k(full)|^2 ≈ 1.28`, `M2_full_est ≈ 1,608`.
      - Energy shares `Σ|F(|t|≤T)|^2 / Σ|F(full)|^2`:
        - `T=0`: `≈ 1.23e-15`
        - `T=100`: `≈ 1.72e-12`
        - `T=1000`: `≈ 2.56e-10`
        - `T=10000`: `≈ 1.48e-05` (`M2_small_est ≈ 6.2`)
    - Adversarial k file (1,359 admissible `k` after filtering):
      - `python3 scripts/experiments/exp_q0_fk_ttstar_small_t_split.py --Qsplit 500 --n-samples 5000 --seed 42 --k-file scripts/experiments/data/adversarial_k_set1.txt --T-list 0,10,100,1000,10000`
      - Full: `mean |F_k(full)|^2 ≈ 8.59`, `M2_full_est ≈ 4,166`.
      - Energy shares `Σ|F(|t|≤T)|^2 / Σ|F(full)|^2`:
        - `T=0`: `≈ 2.01e-15`
        - `T=100`: `≈ 4.47e-13`
        - `T=1000`: `≈ 7.59e-11`
        - `T=10000`: `≈ 6.24e-06` (`M2_small_est ≈ 10.4`)
  - Interpretation: at least for these probes, essentially none of the TT* energy is coming from very small `|t|`
    (even `|t|≤1000`), and even `|t|≤10000` contributes only ~`1e-5` of sampled energy. This supports a future
    certificate split where the “small-|t|” part is handled by finite enumeration and the tail by a coarse bound.

- t=0 (“constant mode”) spike sanity check (not a proof):
  - Script: `scripts/experiments/exp_q0_ttstar_t0_spike.py`
  - Interpretation: for unbalanced hard arcs, the only `t=0` contribution to a given `F_k` comes from the single
    term `n=(N-k)/2` (when it exists), with size `W(0)·Λ(n)Λ(n+k)`. For the *balanced* weight used in the TT* plan,
    the `t=0` mode is removed; this experiment just quantifies the unbalanced spike scale.
  - Run (`N=1,010,000`, scan all `n` to maximize `Λ(n)Λ(N-n)`; also sample random/structured `k`):
    - `python3 scripts/experiments/exp_q0_ttstar_t0_spike.py --N 1010000 --seed 51 --k-samples 5000 --include-structured --top 20`
    - Constant modes:
      - `W0 hard ≈ 3.6476e-02` (hard arcs measure)
      - `W0 smooth ≈ 5.4714e-02` (wTextbook total mass; `=1.5×hard`)
    - Max spike (from the scan): `Λ(n)Λ(N-n) ≈ 172.4577`, giving
      - `max |F_k[t=0]|_hard ≈ 6.29`
      - `max |F_k[t=0]|_smooth ≈ 9.44`
    - In 5000 random+structured `k` samples, `t=0` was nonzero only 33 times; among those nonzero cases
      the values cluster near the max (as expected, since both endpoints must be prime powers).
  - Adversarial `k` file note:
    - `python3 scripts/experiments/exp_q0_ttstar_t0_spike.py --N 1010000 --seed 52 --k-samples 0 --k-file scripts/experiments/data/adversarial_k_set1.txt --top 20`
    - Found zero nonzero `t=0` contributions within that file (just means none of those `k` happened to hit prime-power endpoints).

- Progression ℓ² diagnostics for the hard-arc Toeplitz kernel `W_hat(t)` (not a proof):
  - Script: `scripts/experiments/exp_q0_w_hat_progression_l2.py`
  - Meaning of progression: for fixed `(N,k)`, sample `n` uniformly in `[2, N-2-k]` and set `t=|2n+k-N|`;
    compute moments of `W_hat_hybrid(t)` along this *exact* `t` distribution.
  - Run A (mixed k set, `N=1,010,000`, `Qsplit=500`, `k-samples=200`, `--include-structured`, `n-samples=10,000`):
    - `python3 scripts/experiments/exp_q0_w_hat_progression_l2.py --Qsplit 500 --seed 61 --k-samples 200 --include-structured --n-samples 10000 --quantiles 0.5,0.9,0.99,0.999`
    - Per-k estimated sums (mean over the 563 admissible k values):
      - `Σ_n |W(t)|^2` mean `≈ 5.47e-06` (max `≈ 1.29e-05`)
      - `Σ_n |W(t)|`   mean `≈ 1.19` (max `≈ 2.58`)
    - Per-k mean moments:
      - `E_n |W(t)|^2` mean `≈ 1.02e-11` (max `≈ 1.35e-11`)
      - `E_n |W(t)|`   mean `≈ 2.30e-06` (max `≈ 2.76e-06`)
      - sampled `max_n |W(t)|` up to `≈ 3.57e-05` (consistent with the structured `max |W_hat| ≈ 4.85e-05` seen elsewhere).
  - Run B (adversarial k file, `N=1,010,000`, `Qsplit=500`, `k-file=adversarial_k_set1.txt`, `n-samples=5,000`):
    - `python3 scripts/experiments/exp_q0_w_hat_progression_l2.py --Qsplit 500 --seed 62 --k-samples 0 --k-file scripts/experiments/data/adversarial_k_set1.txt --n-samples 5000 --quantiles 0.5,0.9,0.99,0.999`
    - Per-k estimated sums (mean over the 1,159 k values):
      - `Σ_n |W(t)|^2` mean `≈ 6.33e-06` (max `≈ 1.35e-05`)
      - `Σ_n |W(t)|`   mean `≈ 1.30` (max `≈ 2.62`)
    - Per-k mean moments:
      - `E_n |W(t)|^2` mean `≈ 1.19e-11` (max `≈ 1.39e-11`)
      - `E_n |W(t)|`   mean `≈ 2.54e-06` (max `≈ 2.78e-06`)
      - sampled `max_n |W(t)|` up to `≈ 3.75e-05`.
  - Interpretation: along the actual `t=|2n+k-N|` progression, `Σ_n |W(t)|^2` is on the order of `1e-5` per k,
    and appears only weakly dependent on k (aside from parity/range effects). This is a useful scale check for
    any future Toeplitz/TT* inequality that bounds a k-sum using kernel ℓ²-type norms.

- N-sweep robustness (not a proof):
  - Goal: check that ε₂-large experiments (kernel, TT* proxy) behave similarly for `N ∈ {X, X+H/2, X+H}`.
  - Hybrid-`W_hat` Monte Carlo `F_k` probe (`Qsplit=500`, `k-samples=100`, `n-samples=5000`, `--include-structured`, `--estimate-f0`):
    - `N=1,000,000`:
      - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 100 --n-samples 5000 --seed 70 --estimate-f0 --include-structured --N 1000000`
      - `mean |F_k|^2 ≈ 3.06`, `M2_est ≈ 2,473`.
    - `N=1,005,000`:
      - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 100 --n-samples 5000 --seed 71 --estimate-f0 --include-structured --N 1005000`
      - `mean |F_k|^2 ≈ 4.02`, `M2_est ≈ 2,842`.
    - `N=1,010,000`:
      - `python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py --Qsplit 500 --k-samples 100 --n-samples 5000 --seed 72 --estimate-f0 --include-structured --N 1010000`
      - `mean |F_k|^2 ≈ 2.77`, `M2_est ≈ 2,364`.
  - Small-|t| split (`T ∈ {0,100,1000,10000}`, `k-samples=150`, `--include-structured`, `n-samples=5000`):
    - `N=1,000,000`:
      - `python3 scripts/experiments/exp_q0_fk_ttstar_small_t_split.py --Qsplit 500 --n-samples 5000 --seed 81 --k-samples 150 --include-structured --T-list 0,100,1000,10000 --N 1000000`
      - Full: `mean |F_k(full)|^2 ≈ 1.03`, `M2_full_est ≈ 1,433`.
      - Energy shares `Σ|F(|t|≤T)|^2 / Σ|F(full)|^2`: `T=1000 ≈ 3.71e-10`, `T=10000 ≈ 1.85e-05`.
    - `N=1,005,000`:
      - `python3 scripts/experiments/exp_q0_fk_ttstar_small_t_split.py --Qsplit 500 --n-samples 5000 --seed 82 --k-samples 150 --include-structured --T-list 0,100,1000,10000 --N 1005000`
      - Full: `mean |F_k(full)|^2 ≈ 2.53`, `M2_full_est ≈ 2,256`.
      - Energy shares: `T=1000 ≈ 1.56e-10`, `T=10000 ≈ 7.46e-06`.
    - `N=1,010,000`:
      - `python3 scripts/experiments/exp_q0_fk_ttstar_small_t_split.py --Qsplit 500 --n-samples 5000 --seed 83 --k-samples 150 --include-structured --T-list 0,100,1000,10000 --N 1010000`
      - Full: `mean |F_k(full)|^2 ≈ 1.45`, `M2_full_est ≈ 1,709`.
      - Energy shares: `T=1000 ≈ 2.33e-10`, `T=10000 ≈ 1.33e-05`.
  - Progression ℓ² diagnostics (`k-samples=100`, `--include-structured`, `n-samples=3000`, `Qsplit=500`):
    - `N=1,000,000`:
      - `python3 scripts/experiments/exp_q0_w_hat_progression_l2.py --Qsplit 500 --seed 91 --k-samples 100 --include-structured --n-samples 3000 --quantiles 0.5,0.9,0.99 --N 1000000`
      - `Σ_n |W(t)|^2` mean `≈ 5.54e-06` (max `≈ 1.33e-05`).
    - `N=1,005,000`:
      - `python3 scripts/experiments/exp_q0_w_hat_progression_l2.py --Qsplit 500 --seed 92 --k-samples 100 --include-structured --n-samples 3000 --quantiles 0.5,0.9,0.99 --N 1005000`
      - `Σ_n |W(t)|^2` mean `≈ 5.59e-06` (max `≈ 1.37e-05`).
    - `N=1,010,000`:
      - `python3 scripts/experiments/exp_q0_w_hat_progression_l2.py --Qsplit 500 --seed 93 --k-samples 100 --include-structured --n-samples 3000 --quantiles 0.5,0.9,0.99 --N 1010000`
      - `Σ_n |W(t)|^2` mean `≈ 5.69e-06` (max `≈ 1.51e-05`).
  - Interpretation: across the window endpoints and midpoint, the proxy TT* scale and kernel progression ℓ² scale
    are stable to within modest constant factors; no “endpoint blow-up” observed.

## Next experiments (once ε₂-small is reduced to finite sums)

- ε₂-small: compute/upper-bound the finite sums over `q ≤ Q0` that come from:
  - Step21OnArcSmallBetaBMOR error terms, integrated over arc length and β-small range;
  - Step24 main-term identification vs `corrModel`.
- ε₂-large: compute/upper-bound the finite `kSupport` TT* sum bound `U` in
  `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarCertData.lean`
  (now generated; see below).
- ε₁: either keep the ledger engine as a **paper-quality analytic tool axiom** (polished-gold),
  or replace it by a separate certificate once the SSU/dispersion constants are available.

## Generated TT* certificate `U` (current “passes budget” run; not a proof)

- Generator: `python3 scripts/gen_q0_major_tail_ttstar_cert.py`
- Output file: `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarCertData.lean`
- Parameters: `X0=1_000_000`, `H=10_000`, `Q0=30_000`, `q_small=12`, `N0=X0+H=1_010_000`
- Result:
  - `M2 = 50_000`, `M2^2 = 2_500_000_000`
  - `U = 2_244_888_192` (so `U < M2^2` with ~10% slack)
- Decomposition used by the generator (floating evaluation; see `scripts/gen_q0_major_tail_ttstar_cert.py`):
  - `BW_mix = 1.2847032380129186e-05`
  - `S2_exact = ∑_{n≤N0} Λ(n)^2 = 12946814.27313341`
  - `U_nonzero = (S2_exact^2) * BW_mix = 2_153_419_565.2834706`
  - `U_t0` (crude `t=0` spike envelope) `= 49_096_591.294955686`
  - `U_err` (Taylor remainder for `q≥13` linearization) `= 42_372_034.9961869`
  - Total `U = ceil(U_nonzero + U_t0 + U_err) = 2_244_888_192`
