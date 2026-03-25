import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MajorRoute
import Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic
import Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelEngine
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Pinned-budget aggregator for the turnkey `Q0` certificate route.

This file specializes the current certified/deterministic `Q0` workbench bounds to the pinned
budgets used by the turnkey route, without introducing new analytic assumptions of its own.
-/

namespace Goldbach.Cert.MajorArcModules.Q0TwoBoundsPinnedAxioms

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelEngine
open Goldbach.Cert.MajorArcModules.Q0MajorRoute
open Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

noncomputable abbrev εs : ℝ := (Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData.data.εs : ℝ)
noncomputable abbrev Us : ℝ := (Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData.data.U : ℝ)
noncomputable abbrev Ut : ℝ := Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert.U

/-!
## ε₁ engine (minor / Q0-complement)

Notes provenance: Theorem 9.17 + SSU Theorem 6.27 / (6.7).

Lean interface: `Q0MinorEnergyLedgerEngine Δ C2 C3` with certified `C2,C3`.
The current deterministic route-visible explanation is the weighted-channel decomposition
`minorResidual = zeroMode + meanChannel`.
-/

theorem ssu_minor_energy_ledger_engine :
    Q0MinorEnergyLedgerEngine Δ_canon C2 C3 := by
  have hC2 :
      (2 * Q0MinorSSUFromCert.A2 : ℝ) = C2 := by
    norm_num [C2, Q0MinorSSUFromCert.A2,
      Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData.data,
      Goldbach.Cert.MajorArcModules.Q0MinorSSUCertData.data]
  have hC3 :
      (2 * Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert.A3 : ℝ) = C3 := by
    norm_num [C3, Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert.A3,
      Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData.data,
      Goldbach.Cert.MajorArcModules.Q0MinorTypeICertData.data]
  simpa [hC2, hC3] using
    (ledgerEngine_of_currentWeightedChannelCerts :
      Q0MinorEnergyLedgerEngine Δ_canon
        (2 * Q0MinorSSUFromCert.A2)
        (2 * Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert.A3))

/-!
## ε₂-small engine (small-β major-arc evaluation)

Notes provenance: Lemma 10.1 + Proposition 10.2 + Proposition 11.15.

Lean interface: `Q0MajorSmallBound Δ εs` (here we pin `εs = 2` as in the current Q0 budgeting).
-/
theorem major_arc_small_beta_upperBound :
    Q0MajorSmallUpperBound Δ_canon Us := by
  simpa [Us, Q0MajorSmallUpperBoundFromCert.U] using
    (Q0MajorSmallUpperBoundDeterministic.major_arc_small_beta_upperBound :
      Q0MajorSmallUpperBound Δ_canon Q0MajorSmallUpperBoundFromCert.U)

/-!
## ε₂-large engine (TT*/Parseval control of the β-tail)

This is the option-3 TT*/Parseval analytic payload, packaged as a finite `kSupport` sum bound.
The numeric budget `U` comes from the generated TT* certificate data (currently a placeholder).
-/

theorem innerMajorQ0_full_ttstar_kSupport_upperBound :
    Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon Ut := by
  simpa [Ut, Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz.U_target] using
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz.innerMajorQ0_full_ttstar_kSupport_upperBound

end

end Goldbach.Cert.MajorArcModules.Q0TwoBoundsPinnedAxioms
