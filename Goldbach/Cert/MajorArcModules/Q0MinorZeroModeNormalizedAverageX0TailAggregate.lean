import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000Full
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001First5000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub000First5000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub001First3211

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def SurrogateDiagonalTailChunk000Sub001CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001First5000Sum X0 =
    surrogateDiagTailX0RatChunk000Sub001First5000

def SurrogateDiagonalTailChunk001Sub000CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000First5000Sum X0 =
    surrogateDiagTailX0RatChunk001Sub000First5000

def SurrogateDiagonalTailChunk001Sub001CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001First3211Sum X0 =
    surrogateDiagTailX0RatChunk001Sub001First3211

theorem surrogateDiagTailX0RatChunk000Sub000First5000_eq_global :
    surrogateDiagTailX0RatChunk000Sub000First5000 =
      surrogateDiagTailX0RatChunk000Sub000 := by
  native_decide

theorem surrogateDiagTailX0RatChunk000Sub001First5000_eq_global :
    surrogateDiagTailX0RatChunk000Sub001First5000 =
      surrogateDiagTailX0RatChunk000Sub001 := by
  native_decide

theorem surrogateDiagTailX0RatChunk001Sub000First5000_eq_global :
    surrogateDiagTailX0RatChunk001Sub000First5000 =
      surrogateDiagTailX0RatChunk001Sub000 := by
  native_decide

theorem surrogateDiagTailX0RatChunk001Sub001First3211_eq_global :
    surrogateDiagTailX0RatChunk001Sub001First3211 =
      surrogateDiagTailX0RatChunk001Sub001 := by
  native_decide

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000ArithmeticCertificateAtX0_true :
    CenteredNormalizedSigmaTruncSurrogateDiagonalTailChunk000ArithmeticCertificateAtX0 := by
  native_decide

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001ArithmeticCertificateAtX0_true :
    CenteredNormalizedSigmaTruncSurrogateDiagonalTailChunk001ArithmeticCertificateAtX0 := by
  native_decide

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000RatCertificateAtX0_of_generatedSubchunkCertificates
    (hsub000 : SurrogateDiagonalTailChunk000Sub000CertificateAt X0)
    (hsub001 : SurrogateDiagonalTailChunk000Sub001CertificateAt X0) :
    CenteredNormalizedSigmaTruncSurrogateDiagonalTailChunk000RatCertificateAtX0 := by
  apply surrogateDiagonalTailChunk000_eq_cert_of_subchunkCertificates
  · unfold SurrogateDiagonalTailChunk000Sub000CertificateAt at hsub000
    simpa [surrogateDiagTailX0RatChunk000Sub000First5000_eq_global] using hsub000
  · unfold SurrogateDiagonalTailChunk000Sub001CertificateAt at hsub001
    simpa [surrogateDiagTailX0RatChunk000Sub001First5000_eq_global] using hsub001
  · exact centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000ArithmeticCertificateAtX0_true

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001RatCertificateAtX0_of_generatedSubchunkCertificates
    (hsub000 : SurrogateDiagonalTailChunk001Sub000CertificateAt X0)
    (hsub001 : SurrogateDiagonalTailChunk001Sub001CertificateAt X0) :
    CenteredNormalizedSigmaTruncSurrogateDiagonalTailChunk001RatCertificateAtX0 := by
  apply surrogateDiagonalTailChunk001_eq_cert_of_subchunkCertificates
  · unfold SurrogateDiagonalTailChunk001Sub000CertificateAt at hsub000
    simpa [surrogateDiagTailX0RatChunk001Sub000First5000_eq_global] using hsub000
  · unfold SurrogateDiagonalTailChunk001Sub001CertificateAt at hsub001
    simpa [surrogateDiagTailX0RatChunk001Sub001First3211_eq_global] using hsub001
  · exact centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001ArithmeticCertificateAtX0_true

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunkedRatCertificateAtX0_of_generatedSubchunkCertificates
    (hchunk000_sub000 : SurrogateDiagonalTailChunk000Sub000CertificateAt X0)
    (hchunk000_sub001 : SurrogateDiagonalTailChunk000Sub001CertificateAt X0)
    (hchunk001_sub000 : SurrogateDiagonalTailChunk001Sub000CertificateAt X0)
    (hchunk001_sub001 : SurrogateDiagonalTailChunk001Sub001CertificateAt X0) :
    CenteredNormalizedSigmaTruncSurrogateDiagonalTailChunkedRatCertificateAtX0 := by
  exact centeredNormalizedSigmaTruncSurrogateDiagonalTailChunkedRatCertificateAtX0_of_support_and_chunkCertificates
    centeredNormalizedSigmaTruncSurrogateDiagonalTailChunkSupportCertificateAtX0_true
    (centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000RatCertificateAtX0_of_generatedSubchunkCertificates
      hchunk000_sub000 hchunk000_sub001)
    (centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001RatCertificateAtX0_of_generatedSubchunkCertificates
      hchunk001_sub000 hchunk001_sub001)

theorem surrogateDiagonalTail_X0_le_100_of_generatedSubchunkCertificates
    (hchunk000_sub000 : SurrogateDiagonalTailChunk000Sub000CertificateAt X0)
    (hchunk000_sub001 : SurrogateDiagonalTailChunk000Sub001CertificateAt X0)
    (hchunk001_sub000 : SurrogateDiagonalTailChunk001Sub000CertificateAt X0)
    (hchunk001_sub001 : SurrogateDiagonalTailChunk001Sub001CertificateAt X0) :
    surrogateCenteredNormalizedSigmaTruncDiagonalEnergyDirectTail X0 ≤ 100 := by
  exact centeredNormalizedSigmaTruncSurrogateDiagonalTailExactCheckedRatCertificateAtX0_of_support_and_chunkCertificates
    centeredNormalizedSigmaTruncSurrogateDiagonalTailChunkSupportCertificateAtX0_true
    (centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000RatCertificateAtX0_of_generatedSubchunkCertificates
      hchunk000_sub000 hchunk000_sub001)
    (centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001RatCertificateAtX0_of_generatedSubchunkCertificates
      hchunk001_sub000 hchunk001_sub001)
    centeredNormalizedSigmaTruncSurrogateDiagonalTailExactRatCheckCertificateAtX0_true

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
