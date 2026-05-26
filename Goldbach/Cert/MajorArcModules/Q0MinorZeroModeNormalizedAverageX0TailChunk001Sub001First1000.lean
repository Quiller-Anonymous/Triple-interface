import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub001First500
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub001Band020_029
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001Sub001Band030_039

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def surrogateDiagonalTailChunk001Sub001First1000Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001First500Sum X0
    + surrogateDiagonalTailChunk001Sub001Block020Sum X0
    + surrogateDiagonalTailChunk001Sub001Block021Sum X0
    + surrogateDiagonalTailChunk001Sub001Block022Sum X0
    + surrogateDiagonalTailChunk001Sub001Block023Sum X0
    + surrogateDiagonalTailChunk001Sub001Block024Sum X0
    + surrogateDiagonalTailChunk001Sub001Block025Sum X0
    + surrogateDiagonalTailChunk001Sub001Block026Sum X0
    + surrogateDiagonalTailChunk001Sub001Block027Sum X0
    + surrogateDiagonalTailChunk001Sub001Block028Sum X0
    + surrogateDiagonalTailChunk001Sub001Block029Sum X0
    + surrogateDiagonalTailChunk001Sub001Block030Sum X0
    + surrogateDiagonalTailChunk001Sub001Block031Sum X0
    + surrogateDiagonalTailChunk001Sub001Block032Sum X0
    + surrogateDiagonalTailChunk001Sub001Block033Sum X0
    + surrogateDiagonalTailChunk001Sub001Block034Sum X0
    + surrogateDiagonalTailChunk001Sub001Block035Sum X0
    + surrogateDiagonalTailChunk001Sub001Block036Sum X0
    + surrogateDiagonalTailChunk001Sub001Block037Sum X0
    + surrogateDiagonalTailChunk001Sub001Block038Sum X0
    + surrogateDiagonalTailChunk001Sub001Block039Sum X0

def surrogateDiagTailX0RatChunk001Sub001First1000 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001First500
    + surrogateDiagTailX0RatChunk001Sub001Block020
    + surrogateDiagTailX0RatChunk001Sub001Block021
    + surrogateDiagTailX0RatChunk001Sub001Block022
    + surrogateDiagTailX0RatChunk001Sub001Block023
    + surrogateDiagTailX0RatChunk001Sub001Block024
    + surrogateDiagTailX0RatChunk001Sub001Block025
    + surrogateDiagTailX0RatChunk001Sub001Block026
    + surrogateDiagTailX0RatChunk001Sub001Block027
    + surrogateDiagTailX0RatChunk001Sub001Block028
    + surrogateDiagTailX0RatChunk001Sub001Block029
    + surrogateDiagTailX0RatChunk001Sub001Block030
    + surrogateDiagTailX0RatChunk001Sub001Block031
    + surrogateDiagTailX0RatChunk001Sub001Block032
    + surrogateDiagTailX0RatChunk001Sub001Block033
    + surrogateDiagTailX0RatChunk001Sub001Block034
    + surrogateDiagTailX0RatChunk001Sub001Block035
    + surrogateDiagTailX0RatChunk001Sub001Block036
    + surrogateDiagTailX0RatChunk001Sub001Block037
    + surrogateDiagTailX0RatChunk001Sub001Block038
    + surrogateDiagTailX0RatChunk001Sub001Block039

theorem surrogateDiagTailX0RatChunk001Sub001First1000_eq_blocks :
    surrogateDiagTailX0RatChunk001Sub001First500
      + surrogateDiagTailX0RatChunk001Sub001Block020
      + surrogateDiagTailX0RatChunk001Sub001Block021
      + surrogateDiagTailX0RatChunk001Sub001Block022
      + surrogateDiagTailX0RatChunk001Sub001Block023
      + surrogateDiagTailX0RatChunk001Sub001Block024
      + surrogateDiagTailX0RatChunk001Sub001Block025
      + surrogateDiagTailX0RatChunk001Sub001Block026
      + surrogateDiagTailX0RatChunk001Sub001Block027
      + surrogateDiagTailX0RatChunk001Sub001Block028
      + surrogateDiagTailX0RatChunk001Sub001Block029
      + surrogateDiagTailX0RatChunk001Sub001Block030
      + surrogateDiagTailX0RatChunk001Sub001Block031
      + surrogateDiagTailX0RatChunk001Sub001Block032
      + surrogateDiagTailX0RatChunk001Sub001Block033
      + surrogateDiagTailX0RatChunk001Sub001Block034
      + surrogateDiagTailX0RatChunk001Sub001Block035
      + surrogateDiagTailX0RatChunk001Sub001Block036
      + surrogateDiagTailX0RatChunk001Sub001Block037
      + surrogateDiagTailX0RatChunk001Sub001Block038
      + surrogateDiagTailX0RatChunk001Sub001Block039
      = surrogateDiagTailX0RatChunk001Sub001First1000 := by
  unfold surrogateDiagTailX0RatChunk001Sub001First1000
  ring

def SurrogateDiagonalTailChunk001Sub001Block020CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block020Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block020
def SurrogateDiagonalTailChunk001Sub001Block021CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block021Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block021
def SurrogateDiagonalTailChunk001Sub001Block022CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block022Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block022
def SurrogateDiagonalTailChunk001Sub001Block023CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block023Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block023
def SurrogateDiagonalTailChunk001Sub001Block024CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block024Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block024
def SurrogateDiagonalTailChunk001Sub001Block025CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block025Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block025
def SurrogateDiagonalTailChunk001Sub001Block026CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block026Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block026
def SurrogateDiagonalTailChunk001Sub001Block027CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block027Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block027
def SurrogateDiagonalTailChunk001Sub001Block028CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block028Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block028
def SurrogateDiagonalTailChunk001Sub001Block029CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block029Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block029
def SurrogateDiagonalTailChunk001Sub001Block030CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block030Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block030
def SurrogateDiagonalTailChunk001Sub001Block031CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block031Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block031
def SurrogateDiagonalTailChunk001Sub001Block032CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block032Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block032
def SurrogateDiagonalTailChunk001Sub001Block033CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block033Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block033
def SurrogateDiagonalTailChunk001Sub001Block034CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block034Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block034
def SurrogateDiagonalTailChunk001Sub001Block035CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block035Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block035
def SurrogateDiagonalTailChunk001Sub001Block036CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block036Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block036
def SurrogateDiagonalTailChunk001Sub001Block037CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block037Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block037
def SurrogateDiagonalTailChunk001Sub001Block038CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block038Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block038
def SurrogateDiagonalTailChunk001Sub001Block039CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk001Sub001Block039Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block039

theorem surrogateDiagonalTailChunk001Sub001First1000_eq_cert_explicit
    (hFirst500 : SurrogateDiagonalTailChunk001Sub001First500CertificateAt X0)
    (hBlock020 : SurrogateDiagonalTailChunk001Sub001Block020CertificateAt X0)
    (hBlock021 : SurrogateDiagonalTailChunk001Sub001Block021CertificateAt X0)
    (hBlock022 : SurrogateDiagonalTailChunk001Sub001Block022CertificateAt X0)
    (hBlock023 : SurrogateDiagonalTailChunk001Sub001Block023CertificateAt X0)
    (hBlock024 : SurrogateDiagonalTailChunk001Sub001Block024CertificateAt X0)
    (hBlock025 : SurrogateDiagonalTailChunk001Sub001Block025CertificateAt X0)
    (hBlock026 : SurrogateDiagonalTailChunk001Sub001Block026CertificateAt X0)
    (hBlock027 : SurrogateDiagonalTailChunk001Sub001Block027CertificateAt X0)
    (hBlock028 : SurrogateDiagonalTailChunk001Sub001Block028CertificateAt X0)
    (hBlock029 : SurrogateDiagonalTailChunk001Sub001Block029CertificateAt X0)
    (hBlock030 : SurrogateDiagonalTailChunk001Sub001Block030CertificateAt X0)
    (hBlock031 : SurrogateDiagonalTailChunk001Sub001Block031CertificateAt X0)
    (hBlock032 : SurrogateDiagonalTailChunk001Sub001Block032CertificateAt X0)
    (hBlock033 : SurrogateDiagonalTailChunk001Sub001Block033CertificateAt X0)
    (hBlock034 : SurrogateDiagonalTailChunk001Sub001Block034CertificateAt X0)
    (hBlock035 : SurrogateDiagonalTailChunk001Sub001Block035CertificateAt X0)
    (hBlock036 : SurrogateDiagonalTailChunk001Sub001Block036CertificateAt X0)
    (hBlock037 : SurrogateDiagonalTailChunk001Sub001Block037CertificateAt X0)
    (hBlock038 : SurrogateDiagonalTailChunk001Sub001Block038CertificateAt X0)
    (hBlock039 : SurrogateDiagonalTailChunk001Sub001Block039CertificateAt X0)
    : surrogateDiagonalTailChunk001Sub001First1000Sum X0 = surrogateDiagTailX0RatChunk001Sub001First1000 := by
  unfold SurrogateDiagonalTailChunk001Sub001First500CertificateAt at hFirst500
  unfold SurrogateDiagonalTailChunk001Sub001Block020CertificateAt at hBlock020
  unfold SurrogateDiagonalTailChunk001Sub001Block021CertificateAt at hBlock021
  unfold SurrogateDiagonalTailChunk001Sub001Block022CertificateAt at hBlock022
  unfold SurrogateDiagonalTailChunk001Sub001Block023CertificateAt at hBlock023
  unfold SurrogateDiagonalTailChunk001Sub001Block024CertificateAt at hBlock024
  unfold SurrogateDiagonalTailChunk001Sub001Block025CertificateAt at hBlock025
  unfold SurrogateDiagonalTailChunk001Sub001Block026CertificateAt at hBlock026
  unfold SurrogateDiagonalTailChunk001Sub001Block027CertificateAt at hBlock027
  unfold SurrogateDiagonalTailChunk001Sub001Block028CertificateAt at hBlock028
  unfold SurrogateDiagonalTailChunk001Sub001Block029CertificateAt at hBlock029
  unfold SurrogateDiagonalTailChunk001Sub001Block030CertificateAt at hBlock030
  unfold SurrogateDiagonalTailChunk001Sub001Block031CertificateAt at hBlock031
  unfold SurrogateDiagonalTailChunk001Sub001Block032CertificateAt at hBlock032
  unfold SurrogateDiagonalTailChunk001Sub001Block033CertificateAt at hBlock033
  unfold SurrogateDiagonalTailChunk001Sub001Block034CertificateAt at hBlock034
  unfold SurrogateDiagonalTailChunk001Sub001Block035CertificateAt at hBlock035
  unfold SurrogateDiagonalTailChunk001Sub001Block036CertificateAt at hBlock036
  unfold SurrogateDiagonalTailChunk001Sub001Block037CertificateAt at hBlock037
  unfold SurrogateDiagonalTailChunk001Sub001Block038CertificateAt at hBlock038
  unfold SurrogateDiagonalTailChunk001Sub001Block039CertificateAt at hBlock039
  unfold surrogateDiagonalTailChunk001Sub001First1000Sum
  rw [hFirst500, hBlock020, hBlock021, hBlock022, hBlock023, hBlock024, hBlock025, hBlock026, hBlock027, hBlock028]
  rw [hBlock029, hBlock030, hBlock031, hBlock032, hBlock033, hBlock034, hBlock035, hBlock036, hBlock037, hBlock038]
  rw [hBlock039]
  exact surrogateDiagTailX0RatChunk001Sub001First1000_eq_blocks

def SurrogateDiagonalTailChunk001Sub001First1000CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001First1000Sum X0 = surrogateDiagTailX0RatChunk001Sub001First1000

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
