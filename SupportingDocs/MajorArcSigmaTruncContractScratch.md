# Major-Arc Contract Scratch: `sigma_trunc_Q0` model

This note records a “contract-only” major-arc statement to ask an external mathematician for, and to
use as a target for later formalization. It is written to match the repo’s *actual* objects, and
it highlights the current interface mismatch.

## Current mismatch (important)

- The current FunX major-arc interface model is
  `Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N = Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X`
  (`Goldbach/Cert/MajorArcAxiomsFunX.lean:48`).
- In the repo, `Goldbach.AO_SigmaModel.sigma` is currently **`N`-dependent** and built from
  the Step-24 truncation `sigma_trunc_Q0` (see `Goldbach/AO_SigmaModel.lean`).
- `weight_mass` is identically `1`
  (`Goldbach/AO_WeightMass.lean:14`).
- Meanwhile, the Step-24 σ-side main term already present in the repo is the **truncated** singular
  series `Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N` with `Q0 = 30000`
  (`Goldbach/AO_OffDiag/TailBlock.lean:34`, `Goldbach/AO_OffDiag/TailBlock.lean:53`), which is
  **not** constant in `N` (and is the explicit arithmetic object the major-arc plumbing produces).

So: the remaining mismatch is not “constant vs `N`-dependent”; it is about **normalization**:
`RΛ_smooth` includes an explicit `(log N)^{-2}` factor, while the σ-model may or may not.

## Contract (repo objects only; no internal numeric splits)

Let the canonical window parameters be `X0 = 10^6` and `H = 10^4` (from `Goldbach/BankParams`), and
let `EvenIn X H` be the even window predicate (from `Goldbach/Windows`).

Let `Q0 = 30000` (from `Goldbach.AO_OffDiag.TailBlock.Q0`).

Define:

- `RΛ_smooth(X,N)` to be **exactly**
  `Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N` (`Goldbach/Cert/MajorArcAxiomsFunX.lean:38`).
  This uses:
  - the prime-only weight `Goldbach.BG_Bank.Λ n` (log on primes, 0 otherwise)
    (`Goldbach/BG_Bank.lean:13`),
  - the flat bank weight `Goldbach.BG_Bank.wX X n = 1` (`Goldbach/BG_Bank.lean:14`),
  - the tent kernel factor `Goldbach.BG_Identity.K_full` supported on the inner band `S_BG`,
  - the prefactor `((1/800) * (1/(log N)^2))`.

- `σ≤Q0(N)` to be **exactly**
  `Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N` (`Goldbach/AO_OffDiag/TailBlock.lean:53`).

### First: a necessary scaling sanity check

Because `RΛ_smooth` includes the global normalization factor `(1/800) * (1/(log N)^2)`, it is a
*very small* quantity. In fact, on any window where `log N > 0` one has the crude bound

> `0 ≤ RΛ_smooth(X,N) ≤ 1/800`

since:

- `0 ≤ BG_Bank.Λ n ≤ log N` for `n ∈ [2,N-2]` (prime-only log weight),
- `0 ≤ K_full k` and `∑_{k ∈ S_BG} K_full k ≤ 1`,
- and `RΛ_smooth` is a nonnegative weighted average of terms bounded by `log N * log N`.

Therefore, a contract of the form `RΛ_smooth(X,N) ≈ sigma_trunc_Q0(N)` (unscaled) cannot be
correct: `sigma_trunc_Q0(N)` is typically order `1`, while `RΛ_smooth(X,N)` is always ≤ `1/800`.

The Step-24 object `sigma_trunc_Q0(N)` can only appear as a main term **after** inserting the
normalization factor from `RΛ_smooth`.

### Second: a necessary parity sanity check (even `N`)

On the canonical window, `N ∈ EvenIn X H`, so `N` is even. In the `RΛ_smooth` sum, the kernel index
is

`k = (n : ℤ) - ((N : ℤ) - (n : ℤ)) = 2n - N`,

so **`k` is always even**. Concretely:

- `RΛ_smooth` only ever samples `K_full k` on *even* offsets `k`,
- but the current kernel mass bookkeeping `mass_BG := ∑_{k∈S_BG} K_full k` sums *all* offsets.

Numerically for `H = 10^4` and `Ucut = 10100`:

- `mass_BG ≈ 0.9999029507`,
- `mass_even := ∑_{k∈S_BG, k even} K_full k ≈ 0.4999519655`.

So any “main term scalar” coming from the kernel on the *even* window is naturally proportional to
`mass_even`, not `mass_BG`.

### Proposed (scaled) target statement

Define the *scaled truncation model*

> `model_trunc_scaled(X,N) := ((1/800) * (1/(log N)^2)) * mass_even * sigma_trunc_Q0(N)`.

This matches the fact (proved in the repo) that `(RΛ_smooth : ℂ)` is exactly the normalization
factor times the unnormalized correlation sum (`MajorArcStep11RLSmoothIntegralScaled`).

Target statement (“textbook-shaped”, but fully concrete):

> There exist explicit `A_canon : ℕ` and `C_canon : ℝ` with `0 ≤ C_canon` such that
>
> for all `X ≥ X0` and all `N ∈ EvenIn X H`,
> \[
>   \big| RΛ\_smooth(X,N) - model\_trunc\_scaled(X,N) \big|
>     \le \frac{C\_{canon}}{(\log X)^{A\_{canon}}}.
> \]
>
> (Here `log` is the real logarithm, and the RHS depends only on `X`.)

Remark: if you prefer to avoid carrying `mass_even`, you can equivalently renormalize the kernel on
even offsets (replace `K_full(k)` by `2 * K_full(k)` for even `k`, and `0` for odd `k`) so that the
even-offset mass is `1`. The contract then uses the same `model_trunc_scaled` without an explicit
`mass_even` factor.

This contract intentionally does **not** claim that `C_canon` is small; it only asks for an
*explicit* constant.

## Calibration slack (why this is worth trying)

The pipeline’s pinned cap is
`Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon`
(`Goldbach/Cert/MajorArcAxiomsFunX.lean:62`), which evaluates numerically to about `0.0035645`
given `H = 10^4` and `Ucut = 10100`.

At the cutoff `X0 = 10^6`, `log(X0)^4 ≈ 36430.72`, so if you take `A_canon = 4` then the cutoff
inequality
\[
  \frac{C\_{canon}}{(\log X0)^4} \le δ\_{major,canon}
\]
already holds for any `C_canon ≤ 129.86…`. In particular, `C_canon = 100` passes the cutoff.

## Why the *current* constant σ-model is implausible (design warning)

If the σ-model used by `RΛ_model` is taken to be order `1` (e.g. an unscaled singular series),
then `RΛ_smooth(X,N)` (which has a built-in `(1/800) * (log N)^{-2}` normalization) cannot be
close to `RΛ_model` in absolute terms. Any viable contract must align these scalings explicitly.

## Implementation options (for later experimentation)

To *use* the contract in the current pipeline, the model term has to become `N`-dependent.
Two minimally-invasive options:

- Option A (most direct): redefine `Goldbach.AO_SigmaModel.sigma` to be the **scaled** truncation
  model `((1/800) * (1/(log N)^2)) * mass_even * sigma_trunc_Q0(N)` (or a refined version), so
  `MajorArcAxiomsFunX.RΛ_model` becomes the correct-scale `N`-dependent quantity without changing
  any signatures.

- Option B: keep `AO_SigmaModel.sigma` as-is but change `MajorArcAxiomsFunX.RΛ_model` (and the
  `BG_Identity.Pref/conv_ref_const` plumbing) to use `sigma_trunc_Q0`.

Either way, the existing Step-24 σ-side machinery (`TailBlock` and the main-term identification
files) becomes structurally relevant to the major-arc model.

## What to ask an external mathematician (tailored)

1) Can you prove a *uniform* bound on the canonical window for the **specific** `RΛ_smooth` above,
   with main term `((1/800) * (1/(log N)^2)) * mass_even * sigma_trunc_Q0(N)`, of the form
   `C/(log X)^A`?

2) Can you state the bound with `log X` on the RHS (not `log N`), or at least indicate the simple
   monotonicity step needed to replace `log N` by `log X` when `N ∈ [X, X+H]` with `X ≥ 10^6`?

3) Which standard analytic hypothesis do you want to assume for the prime-only weight
   `log n · 1_{prime}` (as opposed to von Mangoldt), and what is the explicit error in switching
   between them (if you prefer to work with von Mangoldt)?
