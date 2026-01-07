import Goldbach.ETIExport
import AltZeta.B2Kernels

/-!
AltZeta/B2GoldbachHook.lean
===========================

Lightweight B2 hook into the Goldbach-side canonical window/schedule exports.

This file deliberately avoids importing the (currently-in-flux) AltZeta barrier/EF
modules.  It exists purely to provide stable, shared parameters for the B2 work:

* a canonical dyadic window and schedule (from `Goldbach.ETIExport`),
* a canonical `BandParams` witness constructor for Fejér kernels.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real
open AltZeta.Analytic

/-- Canonical window `[X,2X]` exported by the Goldbach project. -/
def canonicalWindow : Window :=
  Goldbach.ETIExport.canonicalWindow

/-- Canonical schedule exported by the Goldbach project. -/
def canonicalSchedule : Schedule :=
  Goldbach.ETIExport.canonicalSchedule

/--
Build Fejér-band parameters out of an `AltZeta.Schedule`.

We keep this as a helper so B2 can talk about the `T = 2c/H` half-width consistently.
-/
def bandParamsOfSchedule
    (Sch : Schedule) (τ α : ℝ) (hH : 0 < Sch.H) (hα : 0 < α ∧ α < 1) : BandParams :=
{ H := Sch.H
, c := Sch.c
, τ := τ
, α := α
, hH := hH
, hc := Sch.hc
, hα := hα
}

/-- The Fejér half-width `T = 2c/H` for the canonical schedule (as a `BandParams` field). -/
def canonicalT (τ α : ℝ) (hα : 0 < α ∧ α < 1) : ℝ :=
  (bandParamsOfSchedule canonicalSchedule τ α (by
    -- canonicalSchedule.H = 10^4
    simpa [canonicalSchedule, Goldbach.ETIExport.canonicalSchedule] using
      (by norm_num : (0 : ℝ) < (10^4 : ℝ))) hα).T

end B2
end AltZeta

