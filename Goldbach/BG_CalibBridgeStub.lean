-- Goldbach/BG_CalibBridgeStub.lean
--
-- Purpose: a placeholder module to host a future bridge certificate.
-- It does **not** introduce any axioms.  Instead, it packages a concrete
-- certificate (when available) into the `WeightsBridgeHyp` class used by
-- `BG_Calib`.

import Goldbach.BG_Calib
import Goldbach.Rep
import Goldbach.Windows

namespace Goldbach.BG_Calib.BridgeCert

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/--
Given a concrete bridge certificate (a uniform bound on `R - conv_full` on the
canonical window), produce a `WeightsBridgeHyp` instance.  Supply `hcert` from
checked data or an analytic proof to activate the bridge-dependent results in
`BG_Calib`.
-/
def mk
    (hcert :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N| ≤ δbridge_canon) :
    WeightsBridgeHyp :=
  ⟨by
    intro X N hX hN
    simpa using (hcert (X := X) (N := N) hX hN)⟩

/--
Combinatorial version: if you can split the bridge error into an inner mismatch
(`δswap`) and an outer contamination (`δcontam`), and you know that their sum is
within the canonical budget `δbridge_canon`, you get a `WeightsBridgeHyp`.

This lets you reuse existing L¹–L∞ mismatch bounds and contamination bounds
without duplicating arithmetic at the call site.
-/
def mk_from_split (δswap δcontam : ℝ)
    (hsplit :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N|
          ≤ δswap + δcontam)
    (hbdd : δswap + δcontam ≤ δbridge_canon) :
    WeightsBridgeHyp :=
  mk (by
    intro X N hX hN
    have h := hsplit (X := X) (N := N) hX hN
    exact le_trans h hbdd)

end Goldbach.BG_Calib.BridgeCert
