import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub000First500
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub000Band020_029
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub000Band030_039

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def surrogateDiagonalTailChunk001Sub000First1000Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000First500Sum X0
    + surrogateDiagonalTailChunk001Sub000Block020Sum X0
    + surrogateDiagonalTailChunk001Sub000Block021Sum X0
    + surrogateDiagonalTailChunk001Sub000Block022Sum X0
    + surrogateDiagonalTailChunk001Sub000Block023Sum X0
    + surrogateDiagonalTailChunk001Sub000Block024Sum X0
    + surrogateDiagonalTailChunk001Sub000Block025Sum X0
    + surrogateDiagonalTailChunk001Sub000Block026Sum X0
    + surrogateDiagonalTailChunk001Sub000Block027Sum X0
    + surrogateDiagonalTailChunk001Sub000Block028Sum X0
    + surrogateDiagonalTailChunk001Sub000Block029Sum X0
    + surrogateDiagonalTailChunk001Sub000Block030Sum X0
    + surrogateDiagonalTailChunk001Sub000Block031Sum X0
    + surrogateDiagonalTailChunk001Sub000Block032Sum X0
    + surrogateDiagonalTailChunk001Sub000Block033Sum X0
    + surrogateDiagonalTailChunk001Sub000Block034Sum X0
    + surrogateDiagonalTailChunk001Sub000Block035Sum X0
    + surrogateDiagonalTailChunk001Sub000Block036Sum X0
    + surrogateDiagonalTailChunk001Sub000Block037Sum X0
    + surrogateDiagonalTailChunk001Sub000Block038Sum X0
    + surrogateDiagonalTailChunk001Sub000Block039Sum X0

def surrogateDiagTailX0RatChunk001Sub000First1000 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000First500
    + surrogateDiagTailX0RatChunk001Sub000Block020
    + surrogateDiagTailX0RatChunk001Sub000Block021
    + surrogateDiagTailX0RatChunk001Sub000Block022
    + surrogateDiagTailX0RatChunk001Sub000Block023
    + surrogateDiagTailX0RatChunk001Sub000Block024
    + surrogateDiagTailX0RatChunk001Sub000Block025
    + surrogateDiagTailX0RatChunk001Sub000Block026
    + surrogateDiagTailX0RatChunk001Sub000Block027
    + surrogateDiagTailX0RatChunk001Sub000Block028
    + surrogateDiagTailX0RatChunk001Sub000Block029
    + surrogateDiagTailX0RatChunk001Sub000Block030
    + surrogateDiagTailX0RatChunk001Sub000Block031
    + surrogateDiagTailX0RatChunk001Sub000Block032
    + surrogateDiagTailX0RatChunk001Sub000Block033
    + surrogateDiagTailX0RatChunk001Sub000Block034
    + surrogateDiagTailX0RatChunk001Sub000Block035
    + surrogateDiagTailX0RatChunk001Sub000Block036
    + surrogateDiagTailX0RatChunk001Sub000Block037
    + surrogateDiagTailX0RatChunk001Sub000Block038
    + surrogateDiagTailX0RatChunk001Sub000Block039

theorem surrogateDiagTailX0RatChunk001Sub000First1000_eq_blocks :
    surrogateDiagTailX0RatChunk001Sub000First500
      + surrogateDiagTailX0RatChunk001Sub000Block020
      + surrogateDiagTailX0RatChunk001Sub000Block021
      + surrogateDiagTailX0RatChunk001Sub000Block022
      + surrogateDiagTailX0RatChunk001Sub000Block023
      + surrogateDiagTailX0RatChunk001Sub000Block024
      + surrogateDiagTailX0RatChunk001Sub000Block025
      + surrogateDiagTailX0RatChunk001Sub000Block026
      + surrogateDiagTailX0RatChunk001Sub000Block027
      + surrogateDiagTailX0RatChunk001Sub000Block028
      + surrogateDiagTailX0RatChunk001Sub000Block029
      + surrogateDiagTailX0RatChunk001Sub000Block030
      + surrogateDiagTailX0RatChunk001Sub000Block031
      + surrogateDiagTailX0RatChunk001Sub000Block032
      + surrogateDiagTailX0RatChunk001Sub000Block033
      + surrogateDiagTailX0RatChunk001Sub000Block034
      + surrogateDiagTailX0RatChunk001Sub000Block035
      + surrogateDiagTailX0RatChunk001Sub000Block036
      + surrogateDiagTailX0RatChunk001Sub000Block037
      + surrogateDiagTailX0RatChunk001Sub000Block038
      + surrogateDiagTailX0RatChunk001Sub000Block039
      = surrogateDiagTailX0RatChunk001Sub000First1000 := by
  unfold surrogateDiagTailX0RatChunk001Sub000First1000
  ring

def SurrogateDiagonalTailChunk001Sub000Block020CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block020Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block020
def SurrogateDiagonalTailChunk001Sub000Block021CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block021Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block021
def SurrogateDiagonalTailChunk001Sub000Block022CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block022Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block022
def SurrogateDiagonalTailChunk001Sub000Block023CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block023Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block023
def SurrogateDiagonalTailChunk001Sub000Block024CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block024Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block024
def SurrogateDiagonalTailChunk001Sub000Block025CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block025Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block025
def SurrogateDiagonalTailChunk001Sub000Block026CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block026Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block026
def SurrogateDiagonalTailChunk001Sub000Block027CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block027Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block027
def SurrogateDiagonalTailChunk001Sub000Block028CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block028Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block028
def SurrogateDiagonalTailChunk001Sub000Block029CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block029Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block029
def SurrogateDiagonalTailChunk001Sub000Block030CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block030Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block030
def SurrogateDiagonalTailChunk001Sub000Block031CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block031Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block031
def SurrogateDiagonalTailChunk001Sub000Block032CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block032Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block032
def SurrogateDiagonalTailChunk001Sub000Block033CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block033Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block033
def SurrogateDiagonalTailChunk001Sub000Block034CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block034Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block034
def SurrogateDiagonalTailChunk001Sub000Block035CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block035Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block035
def SurrogateDiagonalTailChunk001Sub000Block036CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block036Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block036
def SurrogateDiagonalTailChunk001Sub000Block037CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block037Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block037
def SurrogateDiagonalTailChunk001Sub000Block038CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block038Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block038
def SurrogateDiagonalTailChunk001Sub000Block039CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub000Block039Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block039

theorem surrogateDiagonalTailChunk001Sub000First1000_eq_cert_explicit
    (hFirst500 : SurrogateDiagonalTailChunk001Sub000First500CertificateAt X0)
    (hBlock020 : SurrogateDiagonalTailChunk001Sub000Block020CertificateAt X0)
    (hBlock021 : SurrogateDiagonalTailChunk001Sub000Block021CertificateAt X0)
    (hBlock022 : SurrogateDiagonalTailChunk001Sub000Block022CertificateAt X0)
    (hBlock023 : SurrogateDiagonalTailChunk001Sub000Block023CertificateAt X0)
    (hBlock024 : SurrogateDiagonalTailChunk001Sub000Block024CertificateAt X0)
    (hBlock025 : SurrogateDiagonalTailChunk001Sub000Block025CertificateAt X0)
    (hBlock026 : SurrogateDiagonalTailChunk001Sub000Block026CertificateAt X0)
    (hBlock027 : SurrogateDiagonalTailChunk001Sub000Block027CertificateAt X0)
    (hBlock028 : SurrogateDiagonalTailChunk001Sub000Block028CertificateAt X0)
    (hBlock029 : SurrogateDiagonalTailChunk001Sub000Block029CertificateAt X0)
    (hBlock030 : SurrogateDiagonalTailChunk001Sub000Block030CertificateAt X0)
    (hBlock031 : SurrogateDiagonalTailChunk001Sub000Block031CertificateAt X0)
    (hBlock032 : SurrogateDiagonalTailChunk001Sub000Block032CertificateAt X0)
    (hBlock033 : SurrogateDiagonalTailChunk001Sub000Block033CertificateAt X0)
    (hBlock034 : SurrogateDiagonalTailChunk001Sub000Block034CertificateAt X0)
    (hBlock035 : SurrogateDiagonalTailChunk001Sub000Block035CertificateAt X0)
    (hBlock036 : SurrogateDiagonalTailChunk001Sub000Block036CertificateAt X0)
    (hBlock037 : SurrogateDiagonalTailChunk001Sub000Block037CertificateAt X0)
    (hBlock038 : SurrogateDiagonalTailChunk001Sub000Block038CertificateAt X0)
    (hBlock039 : SurrogateDiagonalTailChunk001Sub000Block039CertificateAt X0)
    : surrogateDiagonalTailChunk001Sub000First1000Sum X0 = surrogateDiagTailX0RatChunk001Sub000First1000 := by
  unfold SurrogateDiagonalTailChunk001Sub000First500CertificateAt at hFirst500
  unfold SurrogateDiagonalTailChunk001Sub000Block020CertificateAt at hBlock020
  unfold SurrogateDiagonalTailChunk001Sub000Block021CertificateAt at hBlock021
  unfold SurrogateDiagonalTailChunk001Sub000Block022CertificateAt at hBlock022
  unfold SurrogateDiagonalTailChunk001Sub000Block023CertificateAt at hBlock023
  unfold SurrogateDiagonalTailChunk001Sub000Block024CertificateAt at hBlock024
  unfold SurrogateDiagonalTailChunk001Sub000Block025CertificateAt at hBlock025
  unfold SurrogateDiagonalTailChunk001Sub000Block026CertificateAt at hBlock026
  unfold SurrogateDiagonalTailChunk001Sub000Block027CertificateAt at hBlock027
  unfold SurrogateDiagonalTailChunk001Sub000Block028CertificateAt at hBlock028
  unfold SurrogateDiagonalTailChunk001Sub000Block029CertificateAt at hBlock029
  unfold SurrogateDiagonalTailChunk001Sub000Block030CertificateAt at hBlock030
  unfold SurrogateDiagonalTailChunk001Sub000Block031CertificateAt at hBlock031
  unfold SurrogateDiagonalTailChunk001Sub000Block032CertificateAt at hBlock032
  unfold SurrogateDiagonalTailChunk001Sub000Block033CertificateAt at hBlock033
  unfold SurrogateDiagonalTailChunk001Sub000Block034CertificateAt at hBlock034
  unfold SurrogateDiagonalTailChunk001Sub000Block035CertificateAt at hBlock035
  unfold SurrogateDiagonalTailChunk001Sub000Block036CertificateAt at hBlock036
  unfold SurrogateDiagonalTailChunk001Sub000Block037CertificateAt at hBlock037
  unfold SurrogateDiagonalTailChunk001Sub000Block038CertificateAt at hBlock038
  unfold SurrogateDiagonalTailChunk001Sub000Block039CertificateAt at hBlock039
  unfold surrogateDiagonalTailChunk001Sub000First1000Sum
  rw [hFirst500, hBlock020, hBlock021, hBlock022, hBlock023, hBlock024, hBlock025, hBlock026, hBlock027, hBlock028]
  rw [hBlock029, hBlock030, hBlock031, hBlock032, hBlock033, hBlock034, hBlock035, hBlock036, hBlock037, hBlock038]
  rw [hBlock039]
  exact surrogateDiagTailX0RatChunk001Sub000First1000_eq_blocks

def SurrogateDiagonalTailChunk001Sub000First1000CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000First1000Sum X0 = surrogateDiagTailX0RatChunk001Sub000First1000

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
