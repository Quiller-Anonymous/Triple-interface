/-
  Goldbach/BG.lean  — axiom-free wiring

  Purpose:
    Package the (now trivial) kernel L¹ cap and payload L∞ cap as `caps`,
    expose `E_off`, and a ready-to-use window bound `err_off_bound`.

  Later:
    After you replace K_BG/P_BG and re-prove the two cap lemmas,
    this file doesn’t change.
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.BG_Calib
import Goldbach.BG_Bank
import Goldbach.BG_Operator

namespace Goldbach.BG

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.BG_Calib
open Goldbach.BG_Bank
open Goldbach.BG_Operator
open Real
open BigOperators
open Classical

/-- BG caps assembled from the two finitary bounds (currently 0,0). -/
noncomputable def caps : BG_Calib.Caps :=
{ kernel_l1_cap     := kernel_l1_cap
, payload_linf_cap  := payload_linf_cap
, kernel_l1_nonneg  := kernel_l1_nonneg
, payload_linf_nonneg := payload_linf_nonneg }

/-- The BG off-channel error term. -/
noncomputable def E_off (X N : ℕ) : ℝ :=
  BG_Calib.E_off S_BG K_BG P_BG X N

/-- Window bound in the exact shape Calib proves. -/
lemma err_off_bound {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
  |E_off X N| ≤ BG_Calib.δ_off caps :=
  BG_Calib.err_off_bound (C:=caps) (S:=S_BG) (K_BG:=K_BG) (P_BG:=P_BG) hX hN

-- BG_Calib.lean (example signature)
def my_Mproj : ℕ → ℝ := ...                   -- the projected main term used in Tenor
theorem db_canonical :
  Goldbach.BankPieces.DecompBounds (10^6) (10^4) (1.0) (ε₁) (ε₂) my_Mproj := ...

end Goldbach.BG
