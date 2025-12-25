
import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.AnalyticAssemble  -- for TenorInputs
import Goldbach.AO_Core
import Goldbach.AO_Major
import Goldbach.BG_Bank
import Goldbach.TenorCanonDefs

namespace Goldbach.TenorCanon

open Goldbach
open Goldbach.Windows
open Goldbach.Rep
open Goldbach.AnalyticAssemble
open Goldbach.AO_Core
open Goldbach.AO_Major

noncomputable def major_canonical :
  MajorBound (10^6) (10^4) (1.0) (0.05) Mcanon :=
by
  intro X N hX hN
  simpa using Goldbach.AO_Major.major_lb_window (X := X) (N := N) hX hN


/-- Canonical Tenor inputs assembled from the two lemmas above. -/
noncomputable def inputs :
  Goldbach.AnalyticAssemble.TenorInputs (10^6) (10^4) (1.0) (0.05) (0.004) (0.006) :=
{ S_pos           := by norm_num
, c0_pos          := by norm_num
, epsTI_nonneg    := by norm_num
, epsBG_nonneg    := by norm_num
, eps_sum_lt_c0   := by norm_num
, M               := Mcanon
, major_on_window := by
    intro X N hX hN
    -- AO major-arc lower bound (ledger scale)
    simpa using Goldbach.AO_Major.major_lb_window (X:=X) (N:=N) hX hN
, bank_projection_on_window := by
    intro X N hX hN
    -- BG/TFA bank–projection (ledger scale)
    simpa using Goldbach.BG_Bank.bank_proj_window (X:=X) (N:=N) hX hN }
