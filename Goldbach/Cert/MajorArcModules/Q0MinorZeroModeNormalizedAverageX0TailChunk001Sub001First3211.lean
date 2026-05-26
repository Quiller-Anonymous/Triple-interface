import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub001First3000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub001Band120_128

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def surrogateDiagonalTailChunk001Sub001First3211Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001First3000Sum X0
    + surrogateDiagonalTailChunk001Sub001Block120Sum X0
    + surrogateDiagonalTailChunk001Sub001Block121Sum X0
    + surrogateDiagonalTailChunk001Sub001Block122Sum X0
    + surrogateDiagonalTailChunk001Sub001Block123Sum X0
    + surrogateDiagonalTailChunk001Sub001Block124Sum X0
    + surrogateDiagonalTailChunk001Sub001Block125Sum X0
    + surrogateDiagonalTailChunk001Sub001Block126Sum X0
    + surrogateDiagonalTailChunk001Sub001Block127Sum X0
    + surrogateDiagonalTailChunk001Sub001Block128Sum X0

def surrogateDiagTailX0RatChunk001Sub001First3211 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001First3000
    + surrogateDiagTailX0RatChunk001Sub001Block120
    + surrogateDiagTailX0RatChunk001Sub001Block121
    + surrogateDiagTailX0RatChunk001Sub001Block122
    + surrogateDiagTailX0RatChunk001Sub001Block123
    + surrogateDiagTailX0RatChunk001Sub001Block124
    + surrogateDiagTailX0RatChunk001Sub001Block125
    + surrogateDiagTailX0RatChunk001Sub001Block126
    + surrogateDiagTailX0RatChunk001Sub001Block127
    + surrogateDiagTailX0RatChunk001Sub001Block128

theorem surrogateDiagTailX0RatChunk001Sub001First3211_eq_blocks :
    surrogateDiagTailX0RatChunk001Sub001First3000
      + surrogateDiagTailX0RatChunk001Sub001Block120
      + surrogateDiagTailX0RatChunk001Sub001Block121
      + surrogateDiagTailX0RatChunk001Sub001Block122
      + surrogateDiagTailX0RatChunk001Sub001Block123
      + surrogateDiagTailX0RatChunk001Sub001Block124
      + surrogateDiagTailX0RatChunk001Sub001Block125
      + surrogateDiagTailX0RatChunk001Sub001Block126
      + surrogateDiagTailX0RatChunk001Sub001Block127
      + surrogateDiagTailX0RatChunk001Sub001Block128
      = surrogateDiagTailX0RatChunk001Sub001First3211 := by
  unfold surrogateDiagTailX0RatChunk001Sub001First3211
  ring

def SurrogateDiagonalTailChunk001Sub001Block120CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block120Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block120

def SurrogateDiagonalTailChunk001Sub001Block121CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block121Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block121

def SurrogateDiagonalTailChunk001Sub001Block122CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block122Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block122

def SurrogateDiagonalTailChunk001Sub001Block123CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block123Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block123

def SurrogateDiagonalTailChunk001Sub001Block124CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block124Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block124

def SurrogateDiagonalTailChunk001Sub001Block125CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block125Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block125

def SurrogateDiagonalTailChunk001Sub001Block126CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block126Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block126

def SurrogateDiagonalTailChunk001Sub001Block127CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block127Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block127

def SurrogateDiagonalTailChunk001Sub001Block128CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block128Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block128

theorem surrogateDiagonalTailChunk001Sub001First3211_eq_cert_explicit
    (hFirst3000 : SurrogateDiagonalTailChunk001Sub001First3000CertificateAt X0)
    (hBlock120 : SurrogateDiagonalTailChunk001Sub001Block120CertificateAt X0)
    (hBlock121 : SurrogateDiagonalTailChunk001Sub001Block121CertificateAt X0)
    (hBlock122 : SurrogateDiagonalTailChunk001Sub001Block122CertificateAt X0)
    (hBlock123 : SurrogateDiagonalTailChunk001Sub001Block123CertificateAt X0)
    (hBlock124 : SurrogateDiagonalTailChunk001Sub001Block124CertificateAt X0)
    (hBlock125 : SurrogateDiagonalTailChunk001Sub001Block125CertificateAt X0)
    (hBlock126 : SurrogateDiagonalTailChunk001Sub001Block126CertificateAt X0)
    (hBlock127 : SurrogateDiagonalTailChunk001Sub001Block127CertificateAt X0)
    (hBlock128 : SurrogateDiagonalTailChunk001Sub001Block128CertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001First3211Sum X0 = surrogateDiagTailX0RatChunk001Sub001First3211 := by
  unfold SurrogateDiagonalTailChunk001Sub001First3000CertificateAt at hFirst3000
  unfold SurrogateDiagonalTailChunk001Sub001Block120CertificateAt at hBlock120
  unfold SurrogateDiagonalTailChunk001Sub001Block121CertificateAt at hBlock121
  unfold SurrogateDiagonalTailChunk001Sub001Block122CertificateAt at hBlock122
  unfold SurrogateDiagonalTailChunk001Sub001Block123CertificateAt at hBlock123
  unfold SurrogateDiagonalTailChunk001Sub001Block124CertificateAt at hBlock124
  unfold SurrogateDiagonalTailChunk001Sub001Block125CertificateAt at hBlock125
  unfold SurrogateDiagonalTailChunk001Sub001Block126CertificateAt at hBlock126
  unfold SurrogateDiagonalTailChunk001Sub001Block127CertificateAt at hBlock127
  unfold SurrogateDiagonalTailChunk001Sub001Block128CertificateAt at hBlock128
  unfold surrogateDiagonalTailChunk001Sub001First3211Sum
  rw [hFirst3000, hBlock120, hBlock121, hBlock122, hBlock123]
  rw [hBlock124, hBlock125, hBlock126, hBlock127, hBlock128]
  exact surrogateDiagTailX0RatChunk001Sub001First3211_eq_blocks

def SurrogateDiagonalTailChunk001Sub001First3211CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001First3211Sum X0 = surrogateDiagTailX0RatChunk001Sub001First3211

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
