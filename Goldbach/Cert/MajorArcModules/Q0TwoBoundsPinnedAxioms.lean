import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineAxiom
import Goldbach.Cert.MajorArcModules.Q0MajorRoute
import Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundTextbookAxiom
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Project-pinned axioms for the turnkey `Q0` certificate route (fool’s gold boundary).

This file is the **temporary** assumption surface used by `Q0TwoBoundsSpec.lean` while we pursue a
checkable major-arc certificate (“platinum” work) via successive approximation.

These assumptions are *not* conventional math under the repo’s “gold” standard, because they pin
project constants/budgets (e.g. `Δ_canon`, `εs = 2`, and the current TT* budget `M2 = 50_000`).

They are kept here (separate from `Q0TwoBoundsConventionalAxioms.lean`) so that:
- the live Goldbach pipeline can remain gold-grade (conventional major-arc boundary), and
- the offline Q0 route can iterate rapidly on certificates without refactoring downstream wiring.
-/

namespace Goldbach.Cert.MajorArcModules.Q0TwoBoundsPinnedAxioms

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MajorRoute
open Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundTextbookAxiom
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
-/

theorem ssu_minor_energy_ledger_engine :
    Q0MinorEnergyLedgerEngine Δ_canon C2 C3 := by
  simpa using
    (Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineAxiom.ssu_minor_energy_ledger_engine :
      Q0MinorEnergyLedgerEngine Δ_canon C2 C3)

/-!
## ε₂-small engine (small-β major-arc evaluation)

Notes provenance: Lemma 10.1 + Proposition 10.2 + Proposition 11.15.

Lean interface: `Q0MajorSmallBound Δ εs` (here we pin `εs = 2` as in the current Q0 budgeting).
-/
theorem major_arc_small_beta_upperBound :
    Q0MajorSmallUpperBound Δ_canon Us := by
  -- The contentful assumption lives in a “textbook axiom” file; this pinned route only re-exports it.
  simpa [Us, Q0MajorSmallUpperBoundTextbookAxiom.Us] using
    (Q0MajorSmallUpperBoundTextbookAxiom.major_arc_small_beta_upperBound : Q0MajorSmallUpperBound Δ_canon (Q0MajorSmallUpperBoundTextbookAxiom.Us))

/-!
## ε₂-large engine (TT*/Parseval control of the β-tail)

This is the option-3 TT*/Parseval analytic payload, packaged as a finite `kSupport` sum bound.
The numeric budget `U` comes from the generated TT* certificate data (currently a placeholder).
-/

-- The remaining pinned assumption is now the Toeplitz expression upper bound (see
-- `Q0MajorTailTTStarUpperBoundFromToeplitz.lean`); the TT* `kSupport` upper bound is derived.
theorem innerMajorQ0_full_ttstar_kSupport_upperBound :
    Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon Ut := by
  simpa [Ut, Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz.U_target] using
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz.innerMajorQ0_full_ttstar_kSupport_upperBound

end

end Goldbach.Cert.MajorArcModules.Q0TwoBoundsPinnedAxioms
