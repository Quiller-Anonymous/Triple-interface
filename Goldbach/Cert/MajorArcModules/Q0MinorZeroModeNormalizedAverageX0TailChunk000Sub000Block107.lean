import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [107,108). -/

/- Block 107 covers tail-support indices [2675,2700) and q from 4449 to 4493. -/

def TailChunk000Sub000Block107Part000SupportExplicit : Finset ℕ :=
  ([4449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part000 : ℚ :=
  (27474875 : ℚ) / 6431785483968

def SurrogateDiagonalTailChunk000Sub000Block107Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4449
    = surrogateDiagTailX0RatChunk000Sub000Block107Part000

theorem surrogateDiagonalTailChunk000Sub000Block107Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part000] using hcert

def TailChunk000Sub000Block107Part001SupportExplicit : Finset ℕ :=
  ([4451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part001 : ℚ :=
  (19811401 : ℚ) / 15688697362050

def SurrogateDiagonalTailChunk000Sub000Block107Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4451
    = surrogateDiagTailX0RatChunk000Sub000Block107Part001

theorem surrogateDiagonalTailChunk000Sub000Block107Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part001] using hcert

def TailChunk000Sub000Block107Part002SupportExplicit : Finset ℕ :=
  ([4453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part002 : ℚ :=
  (24137486009 : ℚ) / 17417741539737600

def SurrogateDiagonalTailChunk000Sub000Block107Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4453
    = surrogateDiagTailX0RatChunk000Sub000Block107Part002

theorem surrogateDiagonalTailChunk000Sub000Block107Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part002] using hcert

def TailChunk000Sub000Block107Part003SupportExplicit : Finset ℕ :=
  ([4454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part003 : ℚ :=
  (23356092091 : ℚ) / 1872148050739200

def SurrogateDiagonalTailChunk000Sub000Block107Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4454
    = surrogateDiagTailX0RatChunk000Sub000Block107Part003

theorem surrogateDiagonalTailChunk000Sub000Block107Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part003] using hcert

def TailChunk000Sub000Block107Part004SupportExplicit : Finset ℕ :=
  ([4457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part004 : ℚ :=
  (310388265625 : ℚ) / 246460653796864512

def SurrogateDiagonalTailChunk000Sub000Block107Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4457
    = surrogateDiagTailX0RatChunk000Sub000Block107Part004

theorem surrogateDiagonalTailChunk000Sub000Block107Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part004] using hcert

def TailChunk000Sub000Block107Part005SupportExplicit : Finset ℕ :=
  ([4458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part005 : ℚ :=
  (56005031675 : ℚ) / 1515906711198096

def SurrogateDiagonalTailChunk000Sub000Block107Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4458
    = surrogateDiagTailX0RatChunk000Sub000Block107Part005

theorem surrogateDiagonalTailChunk000Sub000Block107Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part005] using hcert

def TailChunk000Sub000Block107Part006SupportExplicit : Finset ℕ :=
  ([4461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part006 : ℚ :=
  (82869825 : ℚ) / 19504518297664

def SurrogateDiagonalTailChunk000Sub000Block107Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4461
    = surrogateDiagTailX0RatChunk000Sub000Block107Part006

theorem surrogateDiagonalTailChunk000Sub000Block107Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part006] using hcert

def TailChunk000Sub000Block107Part007SupportExplicit : Finset ℕ :=
  ([4462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part007 : ℚ :=
  (593282168725 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub000Block107Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4462
    = surrogateDiagTailX0RatChunk000Sub000Block107Part007

theorem surrogateDiagonalTailChunk000Sub000Block107Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part007] using hcert

def TailChunk000Sub000Block107Part008SupportExplicit : Finset ℕ :=
  ([4463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part008 : ℚ :=
  (311224515625 : ℚ) / 247790773488258642

def SurrogateDiagonalTailChunk000Sub000Block107Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4463
    = surrogateDiagTailX0RatChunk000Sub000Block107Part008

theorem surrogateDiagonalTailChunk000Sub000Block107Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part008] using hcert

def TailChunk000Sub000Block107Part009SupportExplicit : Finset ℕ :=
  ([4465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part009 : ℚ :=
  (807593738375 : ℚ) / 150438216364867584

def SurrogateDiagonalTailChunk000Sub000Block107Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4465
    = surrogateDiagTailX0RatChunk000Sub000Block107Part009

theorem surrogateDiagonalTailChunk000Sub000Block107Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part009] using hcert

def TailChunk000Sub000Block107Part010SupportExplicit : Finset ℕ :=
  ([4466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part010 : ℚ :=
  (1047372499 : ℚ) / 31870139793408

def SurrogateDiagonalTailChunk000Sub000Block107Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4466
    = surrogateDiagTailX0RatChunk000Sub000Block107Part010

theorem surrogateDiagonalTailChunk000Sub000Block107Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part010] using hcert

def TailChunk000Sub000Block107Part011SupportExplicit : Finset ℕ :=
  ([4467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part011 : ℚ :=
  (692315268425 : ℚ) / 98068282789330944

def SurrogateDiagonalTailChunk000Sub000Block107Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4467
    = surrogateDiagTailX0RatChunk000Sub000Block107Part011

theorem surrogateDiagonalTailChunk000Sub000Block107Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part011] using hcert

def TailChunk000Sub000Block107Part012SupportExplicit : Finset ℕ :=
  ([4469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part012 : ℚ :=
  (95098449961 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub000Block107Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4469
    = surrogateDiagTailX0RatChunk000Sub000Block107Part012

theorem surrogateDiagonalTailChunk000Sub000Block107Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part012] using hcert

def TailChunk000Sub000Block107Part013SupportExplicit : Finset ℕ :=
  ([4470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part013 : ℚ :=
  (113565165675 : ℚ) / 1637994403987456

def SurrogateDiagonalTailChunk000Sub000Block107Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4470
    = surrogateDiagTailX0RatChunk000Sub000Block107Part013

theorem surrogateDiagonalTailChunk000Sub000Block107Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part013] using hcert

def TailChunk000Sub000Block107Part014SupportExplicit : Finset ℕ :=
  ([4471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part014 : ℚ :=
  (295185561325 : ℚ) / 193042068920205312

def SurrogateDiagonalTailChunk000Sub000Block107Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4471
    = surrogateDiagTailX0RatChunk000Sub000Block107Part014

theorem surrogateDiagonalTailChunk000Sub000Block107Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part014] using hcert

def TailChunk000Sub000Block107Part015SupportExplicit : Finset ℕ :=
  ([4474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part015 : ℚ :=
  (625396020775 : ℚ) / 62504898711086208

def SurrogateDiagonalTailChunk000Sub000Block107Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4474
    = surrogateDiagTailX0RatChunk000Sub000Block107Part015

theorem surrogateDiagonalTailChunk000Sub000Block107Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part015] using hcert

def TailChunk000Sub000Block107Part016SupportExplicit : Finset ℕ :=
  ([4478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part016 : ℚ :=
  (626514796975 : ℚ) / 62728830054199368

def SurrogateDiagonalTailChunk000Sub000Block107Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4478
    = surrogateDiagTailX0RatChunk000Sub000Block107Part016

theorem surrogateDiagonalTailChunk000Sub000Block107Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part016] using hcert

def TailChunk000Sub000Block107Part017SupportExplicit : Finset ℕ :=
  ([4479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part017 : ℚ :=
  (974694729925 : ℚ) / 198254080171296768

def SurrogateDiagonalTailChunk000Sub000Block107Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4479
    = surrogateDiagTailX0RatChunk000Sub000Block107Part017

theorem surrogateDiagonalTailChunk000Sub000Block107Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part017] using hcert

def TailChunk000Sub000Block107Part018SupportExplicit : Finset ℕ :=
  ([4481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part018 : ℚ :=
  (501984025 : ℚ) / 402901520351232

def SurrogateDiagonalTailChunk000Sub000Block107Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4481
    = surrogateDiagTailX0RatChunk000Sub000Block107Part018

theorem surrogateDiagonalTailChunk000Sub000Block107Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part018] using hcert

def TailChunk000Sub000Block107Part019SupportExplicit : Finset ℕ :=
  ([4483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part019 : ℚ :=
  (314020140625 : ℚ) / 252263418300751122

def SurrogateDiagonalTailChunk000Sub000Block107Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4483
    = surrogateDiagTailX0RatChunk000Sub000Block107Part019

theorem surrogateDiagonalTailChunk000Sub000Block107Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part019] using hcert

def TailChunk000Sub000Block107Part020SupportExplicit : Finset ℕ :=
  ([4485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part020 : ℚ :=
  (604214059975 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub000Block107Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4485
    = surrogateDiagTailX0RatChunk000Sub000Block107Part020

theorem surrogateDiagonalTailChunk000Sub000Block107Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part020] using hcert

def TailChunk000Sub000Block107Part021SupportExplicit : Finset ℕ :=
  ([4486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part021 : ℚ :=
  (314314786275 : ℚ) / 21059499096021016

def SurrogateDiagonalTailChunk000Sub000Block107Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4486
    = surrogateDiagTailX0RatChunk000Sub000Block107Part021

theorem surrogateDiagonalTailChunk000Sub000Block107Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part021] using hcert

def TailChunk000Sub000Block107Part022SupportExplicit : Finset ℕ :=
  ([4487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part022 : ℚ :=
  (478794323 : ℚ) / 241640228782080

def SurrogateDiagonalTailChunk000Sub000Block107Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4487
    = surrogateDiagTailX0RatChunk000Sub000Block107Part022

theorem surrogateDiagonalTailChunk000Sub000Block107Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part022] using hcert

def TailChunk000Sub000Block107Part023SupportExplicit : Finset ℕ :=
  ([4490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part023 : ℚ :=
  (171884327625 : ℚ) / 8595232434159616

def SurrogateDiagonalTailChunk000Sub000Block107Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4490
    = surrogateDiagTailX0RatChunk000Sub000Block107Part023

theorem surrogateDiagonalTailChunk000Sub000Block107Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part023] using hcert

def TailChunk000Sub000Block107Part024SupportExplicit : Finset ℕ :=
  ([4493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block107Part024 : ℚ :=
  (315422640625 : ℚ) / 254522311025908512

def SurrogateDiagonalTailChunk000Sub000Block107Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4493
    = surrogateDiagTailX0RatChunk000Sub000Block107Part024

theorem surrogateDiagonalTailChunk000Sub000Block107Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block107Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block107Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block107Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block107Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block107Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block107Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block107HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block107Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block107Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block107Part000
    + surrogateDiagTailX0RatChunk000Sub000Block107Part001
    + surrogateDiagTailX0RatChunk000Sub000Block107Part002
    + surrogateDiagTailX0RatChunk000Sub000Block107Part003
    + surrogateDiagTailX0RatChunk000Sub000Block107Part004
    + surrogateDiagTailX0RatChunk000Sub000Block107Part005
    + surrogateDiagTailX0RatChunk000Sub000Block107Part006
    + surrogateDiagTailX0RatChunk000Sub000Block107Part007
    + surrogateDiagTailX0RatChunk000Sub000Block107Part008
    + surrogateDiagTailX0RatChunk000Sub000Block107Part009

def surrogateDiagonalTailChunk000Sub000Block107MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block107Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block107Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block107Part010
    + surrogateDiagTailX0RatChunk000Sub000Block107Part011
    + surrogateDiagTailX0RatChunk000Sub000Block107Part012
    + surrogateDiagTailX0RatChunk000Sub000Block107Part013
    + surrogateDiagTailX0RatChunk000Sub000Block107Part014
    + surrogateDiagTailX0RatChunk000Sub000Block107Part015
    + surrogateDiagTailX0RatChunk000Sub000Block107Part016
    + surrogateDiagTailX0RatChunk000Sub000Block107Part017
    + surrogateDiagTailX0RatChunk000Sub000Block107Part018
    + surrogateDiagTailX0RatChunk000Sub000Block107Part019

def surrogateDiagonalTailChunk000Sub000Block107TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block107Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block107Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block107Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block107Part020
    + surrogateDiagTailX0RatChunk000Sub000Block107Part021
    + surrogateDiagTailX0RatChunk000Sub000Block107Part022
    + surrogateDiagTailX0RatChunk000Sub000Block107Part023
    + surrogateDiagTailX0RatChunk000Sub000Block107Part024

def surrogateDiagonalTailChunk000Sub000Block107Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block107HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block107MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block107TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block107 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block107Part000
    + surrogateDiagTailX0RatChunk000Sub000Block107Part001
    + surrogateDiagTailX0RatChunk000Sub000Block107Part002
    + surrogateDiagTailX0RatChunk000Sub000Block107Part003
    + surrogateDiagTailX0RatChunk000Sub000Block107Part004
    + surrogateDiagTailX0RatChunk000Sub000Block107Part005
    + surrogateDiagTailX0RatChunk000Sub000Block107Part006
    + surrogateDiagTailX0RatChunk000Sub000Block107Part007
    + surrogateDiagTailX0RatChunk000Sub000Block107Part008
    + surrogateDiagTailX0RatChunk000Sub000Block107Part009
    + surrogateDiagTailX0RatChunk000Sub000Block107Part010
    + surrogateDiagTailX0RatChunk000Sub000Block107Part011
    + surrogateDiagTailX0RatChunk000Sub000Block107Part012
    + surrogateDiagTailX0RatChunk000Sub000Block107Part013
    + surrogateDiagTailX0RatChunk000Sub000Block107Part014
    + surrogateDiagTailX0RatChunk000Sub000Block107Part015
    + surrogateDiagTailX0RatChunk000Sub000Block107Part016
    + surrogateDiagTailX0RatChunk000Sub000Block107Part017
    + surrogateDiagTailX0RatChunk000Sub000Block107Part018
    + surrogateDiagTailX0RatChunk000Sub000Block107Part019
    + surrogateDiagTailX0RatChunk000Sub000Block107Part020
    + surrogateDiagTailX0RatChunk000Sub000Block107Part021
    + surrogateDiagTailX0RatChunk000Sub000Block107Part022
    + surrogateDiagTailX0RatChunk000Sub000Block107Part023
    + surrogateDiagTailX0RatChunk000Sub000Block107Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block107_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block107Head + surrogateDiagTailX0RatChunk000Sub000Block107Mid + surrogateDiagTailX0RatChunk000Sub000Block107Tail =
      surrogateDiagTailX0RatChunk000Sub000Block107 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block107Head surrogateDiagTailX0RatChunk000Sub000Block107Mid surrogateDiagTailX0RatChunk000Sub000Block107Tail surrogateDiagTailX0RatChunk000Sub000Block107
  ring

def SurrogateDiagonalTailChunk000Sub000Block107HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block107HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block107Head

def SurrogateDiagonalTailChunk000Sub000Block107MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block107MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block107Mid

def SurrogateDiagonalTailChunk000Sub000Block107TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block107TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block107Tail

theorem surrogateDiagonalTailChunk000Sub000Block107_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block107HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block107MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block107TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block107Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block107 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block107HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block107MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block107TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block107Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block107_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
