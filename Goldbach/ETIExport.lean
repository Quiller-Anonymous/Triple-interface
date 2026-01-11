/-
  Goldbach/ETIExport.lean

  Bridge between the Goldbach pipeline and the AltZeta ETI structure.
  The goal is to keep the arithmetic provenance (pin level, variance scale,
  AO short-shift uniformity) close to the source proofs while presenting a
  small API that AltZeta can depend on.
-/
import AltZeta.ETI
import Goldbach.AO_SigmaPos

noncomputable section

namespace Goldbach
namespace ETIExport

open AltZeta

/-- Proof bundle supplying the ETI(E1–E3) data for a fixed window/schedule. -/
structure Proofs (W : Window) (Sch : Schedule) where
  c0 : ℝ
  hc0 : 0 < c0
  εH : ℝ
  hε : 0 ≤ εH
  C_AO_SSU : ℝ
  hAOSSU : 1 ≤ C_AO_SSU

/-- Package the window, schedule, and arithmetic proofs into an `AltZeta.ETI`. -/
def produceETI (W : Window) (Sch : Schedule) (pf : Proofs W Sch) : ETI :=
{ W := W
, Sch := Sch
, c0 := pf.c0
, hc0 := pf.hc0
, εH := pf.εH
, hε := pf.hε
, C_AO_SSU := pf.C_AO_SSU
, hAOSSU := pf.hAOSSU }

/--
  Canonical window `[X, 2X]` with `X = 10^6`, matching the large-scale
  parameters used throughout the Goldbach analytic files.
-/
def canonicalWindow : Window :=
{ X := (10^6 : ℝ)
, hX := by norm_num }

/--
  Canonical schedule associated to the analytic window:
  `H = 10^4`, `Q = 10^2`, carrier width `c = 1/2`, and band damping `B = 5`.
  These values are placeholders for the eventual AO/Tenor schedule.
-/
def canonicalSchedule : Schedule :=
{ H := (10^4 : ℝ)
, Q := (10^2 : ℝ)
, c := (1 : ℝ) / 2
, B := (5 : ℝ)
, hH := by norm_num
, hQ := by norm_num
, hc := by norm_num
, hB := by norm_num }

/--
  Canonical arithmetic proofs borrowed from the AO/TFA side:
  * pin level `c₀ := σmin` from `AO_SigmaPos.SigmaLowerOnWindow`
  * variance scale `ε_H = 0.01`
  * AO short-shift uniformity `C_AO_SSU = 2`

  All values here are placeholders except `c₀`, which is taken from the σ-lower certificate.
-/
def canonicalProofs :
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] →
    Proofs canonicalWindow canonicalSchedule :=
{ c0 := Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin
, hc0 := Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin_pos
, εH := (0.01 : ℝ)
, hε := by norm_num
, C_AO_SSU := (2 : ℝ)
, hAOSSU := by norm_num }

/-- The ready-to-use canonical ETI package exported to AltZeta. -/
def canonicalETI [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] : ETI :=
  produceETI canonicalWindow canonicalSchedule canonicalProofs

end ETIExport
end Goldbach

end
