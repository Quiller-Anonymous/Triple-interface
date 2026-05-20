import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub000First5000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def SurrogateDiagonalTailChunk000Sub000CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000First5000Sum X0
    = surrogateDiagTailX0RatChunk000Sub000First5000

theorem surrogateDiagonalTailChunk000Sub000_eq_cert_explicit
    (hSub000 : SurrogateDiagonalTailChunk000Sub000CertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000First5000Sum X0
      = surrogateDiagTailX0RatChunk000Sub000First5000 := by
  exact hSub000

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
