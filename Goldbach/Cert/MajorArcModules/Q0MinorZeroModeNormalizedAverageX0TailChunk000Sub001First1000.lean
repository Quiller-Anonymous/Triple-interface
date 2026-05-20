import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001First500
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Band020_029
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000Sub001Band030_039

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def surrogateDiagonalTailChunk000Sub001First1000Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001First500Sum X0
    + surrogateDiagonalTailChunk000Sub001Block020Sum X0
    + surrogateDiagonalTailChunk000Sub001Block021Sum X0
    + surrogateDiagonalTailChunk000Sub001Block022Sum X0
    + surrogateDiagonalTailChunk000Sub001Block023Sum X0
    + surrogateDiagonalTailChunk000Sub001Block024Sum X0
    + surrogateDiagonalTailChunk000Sub001Block025Sum X0
    + surrogateDiagonalTailChunk000Sub001Block026Sum X0
    + surrogateDiagonalTailChunk000Sub001Block027Sum X0
    + surrogateDiagonalTailChunk000Sub001Block028Sum X0
    + surrogateDiagonalTailChunk000Sub001Block029Sum X0
    + surrogateDiagonalTailChunk000Sub001Block030Sum X0
    + surrogateDiagonalTailChunk000Sub001Block031Sum X0
    + surrogateDiagonalTailChunk000Sub001Block032Sum X0
    + surrogateDiagonalTailChunk000Sub001Block033Sum X0
    + surrogateDiagonalTailChunk000Sub001Block034Sum X0
    + surrogateDiagonalTailChunk000Sub001Block035Sum X0
    + surrogateDiagonalTailChunk000Sub001Block036Sum X0
    + surrogateDiagonalTailChunk000Sub001Block037Sum X0
    + surrogateDiagonalTailChunk000Sub001Block038Sum X0
    + surrogateDiagonalTailChunk000Sub001Block039Sum X0

def surrogateDiagTailX0RatChunk000Sub001First1000 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001First500
    + surrogateDiagTailX0RatChunk000Sub001Block020
    + surrogateDiagTailX0RatChunk000Sub001Block021
    + surrogateDiagTailX0RatChunk000Sub001Block022
    + surrogateDiagTailX0RatChunk000Sub001Block023
    + surrogateDiagTailX0RatChunk000Sub001Block024
    + surrogateDiagTailX0RatChunk000Sub001Block025
    + surrogateDiagTailX0RatChunk000Sub001Block026
    + surrogateDiagTailX0RatChunk000Sub001Block027
    + surrogateDiagTailX0RatChunk000Sub001Block028
    + surrogateDiagTailX0RatChunk000Sub001Block029
    + surrogateDiagTailX0RatChunk000Sub001Block030
    + surrogateDiagTailX0RatChunk000Sub001Block031
    + surrogateDiagTailX0RatChunk000Sub001Block032
    + surrogateDiagTailX0RatChunk000Sub001Block033
    + surrogateDiagTailX0RatChunk000Sub001Block034
    + surrogateDiagTailX0RatChunk000Sub001Block035
    + surrogateDiagTailX0RatChunk000Sub001Block036
    + surrogateDiagTailX0RatChunk000Sub001Block037
    + surrogateDiagTailX0RatChunk000Sub001Block038
    + surrogateDiagTailX0RatChunk000Sub001Block039

theorem surrogateDiagTailX0RatChunk000Sub001First1000_eq_blocks :
    surrogateDiagTailX0RatChunk000Sub001First500
      + surrogateDiagTailX0RatChunk000Sub001Block020
      + surrogateDiagTailX0RatChunk000Sub001Block021
      + surrogateDiagTailX0RatChunk000Sub001Block022
      + surrogateDiagTailX0RatChunk000Sub001Block023
      + surrogateDiagTailX0RatChunk000Sub001Block024
      + surrogateDiagTailX0RatChunk000Sub001Block025
      + surrogateDiagTailX0RatChunk000Sub001Block026
      + surrogateDiagTailX0RatChunk000Sub001Block027
      + surrogateDiagTailX0RatChunk000Sub001Block028
      + surrogateDiagTailX0RatChunk000Sub001Block029
      + surrogateDiagTailX0RatChunk000Sub001Block030
      + surrogateDiagTailX0RatChunk000Sub001Block031
      + surrogateDiagTailX0RatChunk000Sub001Block032
      + surrogateDiagTailX0RatChunk000Sub001Block033
      + surrogateDiagTailX0RatChunk000Sub001Block034
      + surrogateDiagTailX0RatChunk000Sub001Block035
      + surrogateDiagTailX0RatChunk000Sub001Block036
      + surrogateDiagTailX0RatChunk000Sub001Block037
      + surrogateDiagTailX0RatChunk000Sub001Block038
      + surrogateDiagTailX0RatChunk000Sub001Block039
      = surrogateDiagTailX0RatChunk000Sub001First1000 := by
  unfold surrogateDiagTailX0RatChunk000Sub001First1000
  ring

def SurrogateDiagonalTailChunk000Sub001Block020CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block020Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block020
def SurrogateDiagonalTailChunk000Sub001Block021CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block021Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block021
def SurrogateDiagonalTailChunk000Sub001Block022CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block022Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block022
def SurrogateDiagonalTailChunk000Sub001Block023CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block023Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block023
def SurrogateDiagonalTailChunk000Sub001Block024CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block024Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block024
def SurrogateDiagonalTailChunk000Sub001Block025CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block025Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block025
def SurrogateDiagonalTailChunk000Sub001Block026CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block026Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block026
def SurrogateDiagonalTailChunk000Sub001Block027CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block027Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block027
def SurrogateDiagonalTailChunk000Sub001Block028CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block028Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block028
def SurrogateDiagonalTailChunk000Sub001Block029CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block029Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block029
def SurrogateDiagonalTailChunk000Sub001Block030CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block030Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block030
def SurrogateDiagonalTailChunk000Sub001Block031CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block031Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block031
def SurrogateDiagonalTailChunk000Sub001Block032CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block032Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block032
def SurrogateDiagonalTailChunk000Sub001Block033CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block033Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block033
def SurrogateDiagonalTailChunk000Sub001Block034CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block034Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block034
def SurrogateDiagonalTailChunk000Sub001Block035CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block035Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block035
def SurrogateDiagonalTailChunk000Sub001Block036CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block036Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block036
def SurrogateDiagonalTailChunk000Sub001Block037CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block037Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block037
def SurrogateDiagonalTailChunk000Sub001Block038CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block038Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block038
def SurrogateDiagonalTailChunk000Sub001Block039CertificateAt (X0 : ℕ) : Prop := surrogateDiagonalTailChunk000Sub001Block039Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block039

theorem surrogateDiagonalTailChunk000Sub001First1000_eq_cert_explicit
    (hFirst500 : SurrogateDiagonalTailChunk000Sub001First500CertificateAt X0)
    (hBlock020 : SurrogateDiagonalTailChunk000Sub001Block020CertificateAt X0)
    (hBlock021 : SurrogateDiagonalTailChunk000Sub001Block021CertificateAt X0)
    (hBlock022 : SurrogateDiagonalTailChunk000Sub001Block022CertificateAt X0)
    (hBlock023 : SurrogateDiagonalTailChunk000Sub001Block023CertificateAt X0)
    (hBlock024 : SurrogateDiagonalTailChunk000Sub001Block024CertificateAt X0)
    (hBlock025 : SurrogateDiagonalTailChunk000Sub001Block025CertificateAt X0)
    (hBlock026 : SurrogateDiagonalTailChunk000Sub001Block026CertificateAt X0)
    (hBlock027 : SurrogateDiagonalTailChunk000Sub001Block027CertificateAt X0)
    (hBlock028 : SurrogateDiagonalTailChunk000Sub001Block028CertificateAt X0)
    (hBlock029 : SurrogateDiagonalTailChunk000Sub001Block029CertificateAt X0)
    (hBlock030 : SurrogateDiagonalTailChunk000Sub001Block030CertificateAt X0)
    (hBlock031 : SurrogateDiagonalTailChunk000Sub001Block031CertificateAt X0)
    (hBlock032 : SurrogateDiagonalTailChunk000Sub001Block032CertificateAt X0)
    (hBlock033 : SurrogateDiagonalTailChunk000Sub001Block033CertificateAt X0)
    (hBlock034 : SurrogateDiagonalTailChunk000Sub001Block034CertificateAt X0)
    (hBlock035 : SurrogateDiagonalTailChunk000Sub001Block035CertificateAt X0)
    (hBlock036 : SurrogateDiagonalTailChunk000Sub001Block036CertificateAt X0)
    (hBlock037 : SurrogateDiagonalTailChunk000Sub001Block037CertificateAt X0)
    (hBlock038 : SurrogateDiagonalTailChunk000Sub001Block038CertificateAt X0)
    (hBlock039 : SurrogateDiagonalTailChunk000Sub001Block039CertificateAt X0)
    : surrogateDiagonalTailChunk000Sub001First1000Sum X0 = surrogateDiagTailX0RatChunk000Sub001First1000 := by
  unfold SurrogateDiagonalTailChunk000Sub001First500CertificateAt at hFirst500
  unfold SurrogateDiagonalTailChunk000Sub001Block020CertificateAt at hBlock020
  unfold SurrogateDiagonalTailChunk000Sub001Block021CertificateAt at hBlock021
  unfold SurrogateDiagonalTailChunk000Sub001Block022CertificateAt at hBlock022
  unfold SurrogateDiagonalTailChunk000Sub001Block023CertificateAt at hBlock023
  unfold SurrogateDiagonalTailChunk000Sub001Block024CertificateAt at hBlock024
  unfold SurrogateDiagonalTailChunk000Sub001Block025CertificateAt at hBlock025
  unfold SurrogateDiagonalTailChunk000Sub001Block026CertificateAt at hBlock026
  unfold SurrogateDiagonalTailChunk000Sub001Block027CertificateAt at hBlock027
  unfold SurrogateDiagonalTailChunk000Sub001Block028CertificateAt at hBlock028
  unfold SurrogateDiagonalTailChunk000Sub001Block029CertificateAt at hBlock029
  unfold SurrogateDiagonalTailChunk000Sub001Block030CertificateAt at hBlock030
  unfold SurrogateDiagonalTailChunk000Sub001Block031CertificateAt at hBlock031
  unfold SurrogateDiagonalTailChunk000Sub001Block032CertificateAt at hBlock032
  unfold SurrogateDiagonalTailChunk000Sub001Block033CertificateAt at hBlock033
  unfold SurrogateDiagonalTailChunk000Sub001Block034CertificateAt at hBlock034
  unfold SurrogateDiagonalTailChunk000Sub001Block035CertificateAt at hBlock035
  unfold SurrogateDiagonalTailChunk000Sub001Block036CertificateAt at hBlock036
  unfold SurrogateDiagonalTailChunk000Sub001Block037CertificateAt at hBlock037
  unfold SurrogateDiagonalTailChunk000Sub001Block038CertificateAt at hBlock038
  unfold SurrogateDiagonalTailChunk000Sub001Block039CertificateAt at hBlock039
  unfold surrogateDiagonalTailChunk000Sub001First1000Sum
  rw [hFirst500, hBlock020, hBlock021, hBlock022, hBlock023, hBlock024, hBlock025, hBlock026, hBlock027, hBlock028]
  rw [hBlock029, hBlock030, hBlock031, hBlock032, hBlock033, hBlock034, hBlock035, hBlock036, hBlock037, hBlock038]
  rw [hBlock039]
  exact surrogateDiagTailX0RatChunk000Sub001First1000_eq_blocks

def SurrogateDiagonalTailChunk000Sub001First1000CertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001First1000Sum X0 = surrogateDiagTailX0RatChunk000Sub001First1000

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
