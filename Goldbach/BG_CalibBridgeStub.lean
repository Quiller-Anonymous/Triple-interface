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
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N| ≤ δbridge_canon) :
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
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
          ≤ δswap + δcontam)
    (hbdd : δswap + δcontam ≤ δbridge_canon) :
    WeightsBridgeHyp :=
  mk (by
    intro X N hX hN
    have h := hsplit (X := X) (N := N) hX hN
    exact le_trans h hbdd)

end Goldbach.BG_Calib.BridgeCert

namespace Goldbach.BG_Calib

open Goldbach.BankParams
open Goldbach.Windows

/-!
With the Tenor-aligned definition `BG_Identity.R_bank := conv_full`, the bridge gap
`R_bank - conv_full` is definitionally `0`. Therefore `WeightsBridgeHyp` is no longer a
bespoke hypothesis; it has a canonical proof.
-/

private lemma δbridge_canon_nonneg : 0 ≤ δbridge_canon := by
  -- each component is nonnegative (all constants here are explicit numerals)
  have hUpos : 0 < (Goldbach.BG_Identity.Ucut : ℝ) := Goldbach.BG_Identity.Ucut_pos_real
  have hU : 0 ≤ (Goldbach.BG_Identity.Ucut : ℝ) := le_of_lt hUpos
  have hH : 0 ≤ (2 * H + 1 : ℝ) := by nlinarith
  have hCpp : 0 ≤ Cpp_canon := by
    norm_num [Cpp_canon]
  have hM : 0 ≤ Mswap_canon := by
    norm_num [Mswap_canon]
  have hρ : 0 ≤ ρ_canon := by
    norm_num [ρ_canon]
  have h1 :
      0 ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) * Mswap_canon :=
    mul_nonneg (div_nonneg hH hU) hM
  have h2 :
      0 ≤ (Cpp_canon / (Goldbach.BG_Identity.Ucut : ℝ)) * ρ_canon :=
    mul_nonneg (div_nonneg hCpp hU) hρ
  simpa [δbridge_canon] using add_nonneg h1 h2

noncomputable instance : WeightsBridgeHyp :=
  BridgeCert.mk (by
    intro X N hX hN
    -- `R_bank = conv_full` by definition (Tenor-aligned `BG_Identity.R_bank`)
    have : |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N| = 0 := by
      simp [Goldbach.BG_Identity.R_bank]
    -- discharge the numeric bound using `δbridge_canon_nonneg`
    simpa [this] using δbridge_canon_nonneg)

end Goldbach.BG_Calib
