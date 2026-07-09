import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroRightColumns
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup011
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualGroup012

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated assembly for zero-record value-on-record group payloads. -/

def PeriodicMainZeroCoprimeCoreResidualPayloadPairs : Finset (ℕ × ℕ) :=
  ((((((((((((PeriodicMainZeroCoprimeCoreResidualGroup000Pairs ∪ PeriodicMainZeroCoprimeCoreResidualGroup001Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup002Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup003Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup004Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup005Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup006Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup007Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup008Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup009Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup010Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup011Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup012Pairs)

theorem PeriodicMainZeroCoprimeCoreResidualPayloadPairs_eq_target :
    PeriodicMainZeroCoprimeCoreResidualPayloadPairs = PeriodicMainZeroDyadicExceptionCoprimeCoreResidualPairs := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeCoreResidual_value_on_records_payload :
    ∀ p : (ℕ × ℕ), p ∈ PeriodicMainZeroDyadicExceptionCoprimeCoreResidualPairs →
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  have hpPayload : p ∈ PeriodicMainZeroCoprimeCoreResidualPayloadPairs := by
    simpa [PeriodicMainZeroCoprimeCoreResidualPayloadPairs_eq_target] using hp
  change p ∈ ((((((((((((PeriodicMainZeroCoprimeCoreResidualGroup000Pairs ∪ PeriodicMainZeroCoprimeCoreResidualGroup001Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup002Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup003Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup004Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup005Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup006Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup007Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup008Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup009Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup010Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup011Pairs) ∪ PeriodicMainZeroCoprimeCoreResidualGroup012Pairs) at hpPayload
  have hsplit1 := Finset.mem_union.mp hpPayload
  rcases hsplit1 with hprev1 | h12
  ·
    have hsplit2 := Finset.mem_union.mp hprev1
    rcases hsplit2 with hprev2 | h11
    ·
      have hsplit3 := Finset.mem_union.mp hprev2
      rcases hsplit3 with hprev3 | h10
      ·
        have hsplit4 := Finset.mem_union.mp hprev3
        rcases hsplit4 with hprev4 | h9
        ·
          have hsplit5 := Finset.mem_union.mp hprev4
          rcases hsplit5 with hprev5 | h8
          ·
            have hsplit6 := Finset.mem_union.mp hprev5
            rcases hsplit6 with hprev6 | h7
            ·
              have hsplit7 := Finset.mem_union.mp hprev6
              rcases hsplit7 with hprev7 | h6
              ·
                have hsplit8 := Finset.mem_union.mp hprev7
                rcases hsplit8 with hprev8 | h5
                ·
                  have hsplit9 := Finset.mem_union.mp hprev8
                  rcases hsplit9 with hprev9 | h4
                  ·
                    have hsplit10 := Finset.mem_union.mp hprev9
                    rcases hsplit10 with hprev10 | h3
                    ·
                      have hsplit11 := Finset.mem_union.mp hprev10
                      rcases hsplit11 with hprev11 | h2
                      ·
                        have hsplit12 := Finset.mem_union.mp hprev11
                        rcases hsplit12 with h0 | h1
                        · exact PeriodicMainZeroCoprimeCoreResidualGroup000_value_on_records p h0
                        · exact PeriodicMainZeroCoprimeCoreResidualGroup001_value_on_records p h1
                      · exact PeriodicMainZeroCoprimeCoreResidualGroup002_value_on_records p h2
                    · exact PeriodicMainZeroCoprimeCoreResidualGroup003_value_on_records p h3
                  · exact PeriodicMainZeroCoprimeCoreResidualGroup004_value_on_records p h4
                · exact PeriodicMainZeroCoprimeCoreResidualGroup005_value_on_records p h5
              · exact PeriodicMainZeroCoprimeCoreResidualGroup006_value_on_records p h6
            · exact PeriodicMainZeroCoprimeCoreResidualGroup007_value_on_records p h7
          · exact PeriodicMainZeroCoprimeCoreResidualGroup008_value_on_records p h8
        · exact PeriodicMainZeroCoprimeCoreResidualGroup009_value_on_records p h9
      · exact PeriodicMainZeroCoprimeCoreResidualGroup010_value_on_records p h10
    · exact PeriodicMainZeroCoprimeCoreResidualGroup011_value_on_records p h11
  · exact PeriodicMainZeroCoprimeCoreResidualGroup012_value_on_records p h12

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
