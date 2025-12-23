/-
  Goldbach/PPBound.lean

  Lightweight wiring layer for the prime-power bounds:
  * re-exposes the coarse, axiom-free offset bound `ppInnerCount ≤ 2H+1`;
  * pulls in the square-count lemma (`≤ 8` squares in the inner window)
    from `PPBoundSquares` for later sharpening of the bridge budget.

  This file deliberately keeps the proofs minimal and compositional; the
  tighter “offsets ≤ 16” bound will come from pairing the square count with
  the offset mapping once that combinatorial proof is in place.
-/

import Mathlib
import Goldbach.PPNumerics
import Goldbach.PPBoundSquares
import Goldbach.PPBoundCore
import Goldbach.BG_Identity

open Goldbach.PPNumerics
open Goldbach.PPBoundSquares

namespace Goldbach.PPBound

/-- Coarse but fully formal bound: `ppInnerCount H N ≤ 2H+1`
    (inner band cardinality). -/
theorem ppInnerCount_le_twoHplus1 (H N : Nat) :
    Goldbach.BG_Identity.ppInnerCount H N ≤ 2 * H + 1 :=
  Goldbach.PPBoundCore.ppInnerCount_le_twoHplus1 H N

/-- Squares-in-window bound specialised to the canonical constants.
    With `N ≥ X0`, the summand window of length `H` contains at most 8 squares. -/
theorem squares_window_le_8 {N : Nat} (hN : X0 ≤ N) :
    (innerSquares N).card ≤ 8 :=
  squares_in_lenH_le_8 (N := N) hN

end Goldbach.PPBound
