import Mathlib
import Goldbach.AO_EnvelopeCore
import Goldbach.BankParams
import Goldbach.AO_OffDiag.TailBlock

namespace Goldbach.AO_SigmaModel

open Goldbach
open Goldbach.AO_AssembleEnvelope

/-!
σ-model used by the major-arc interface.

This project’s “banked” correlation functional (`conv_ref` / `RΛ_smooth`) includes:
- the global normalization factor `(1/800) * (1/(log N)^2)` (in the payload), and
- the discrete tent kernel `K_full_raw Ucut` supported on integer offsets, but on even windows
  only even offsets `k = 2n - N` occur.

However, for the downstream closure machinery we want the σ-model itself to be *uniformly bounded
below* on all canonical windows `X ≥ X0`, which is impossible if σ includes a decaying factor like
`1 / (log N)^2`.

So we keep the `1/800` factor (a fixed normalization) but **do not** include the `1/(log N)^2`
factor in `sigma`. The log-normalization mismatch is treated elsewhere (either as part of the
major-arc input, or by absorbing it into the admissible error budget).

So the σ-model used in this file is:

`(1/800) * mass_even * σ≤Q0(N)`,

where `σ≤Q0` is the repo’s fixed truncation of the singular series at `Q0 = 30000`
(`AO_OffDiag.TailBlock.sigma_trunc_Q0`), and `mass_even` is the even-offset tent mass on `[-H,H]`.

This is an `N`-dependent model term; it is *not* the classical Euler-product σ by itself.
-/

namespace Canon

open Goldbach.BankParams

/-!
Kernel parameters.

We duplicate the `Ucut` definition here (instead of importing `BG_Identity`) to avoid import cycles:
`BG_Identity` depends on `AO_SigmaModel` through the constant-reference payload.
-/

@[simp] noncomputable def Ucut : ℕ := H + (H + 99) / 100

-- `H = 10_000` is even in this project; we work with `m = H/2`.
@[simp] noncomputable def m : ℕ := H / 2

-- Even-offset tent mass on `[-H,H]` for `K_full_raw Ucut k = max(1 - |k|/Ucut, 0) / Ucut`.
-- When `H = 2m`, a closed form is:
--   mass_even = (2m+1)/Ucut - (2m(m+1))/Ucut^2.
noncomputable def mass_even : ℝ :=
  ((2 * m + 1 : ℕ) : ℝ) / (Ucut : ℝ)
    - ((2 * m * (m + 1) : ℕ) : ℝ) / ((Ucut : ℝ) ^ 2)

end Canon

open Canon

noncomputable def sigma (N : ℕ) : ℝ :=
  (1 / 800 : ℝ) * Canon.mass_even * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N

end Goldbach.AO_SigmaModel
