import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [11,12). -/

/- Block 011 covers tail-support indices [275,300) and q from 501 to 542. -/

def TailChunk000Sub000Block011Part000SupportExplicit : Finset ℕ :=
  ([501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part000 : ℚ :=
  (97085644075 : ℚ) / 30379400105088

def SurrogateDiagonalTailChunk000Sub000Block011Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 501
    = surrogateDiagTailX0RatChunk000Sub000Block011Part000

theorem surrogateDiagonalTailChunk000Sub000Block011Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part000] using hcert

def TailChunk000Sub000Block011Part001SupportExplicit : Finset ℕ :=
  ([502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part001 : ℚ :=
  (2981774329 : ℚ) / 390703125000

def SurrogateDiagonalTailChunk000Sub000Block011Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 502
    = surrogateDiagTailX0RatChunk000Sub000Block011Part001

theorem surrogateDiagonalTailChunk000Sub000Block011Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part001] using hcert

def TailChunk000Sub000Block011Part002SupportExplicit : Finset ℕ :=
  ([503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part002 : ℚ :=
  (5920410600 : ℚ) / 6616533043667

def SurrogateDiagonalTailChunk000Sub000Block011Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 503
    = surrogateDiagTailX0RatChunk000Sub000Block011Part002

theorem surrogateDiagonalTailChunk000Sub000Block011Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part002] using hcert

def TailChunk000Sub000Block011Part003SupportExplicit : Finset ℕ :=
  ([505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part003 : ℚ :=
  (50505499 : ℚ) / 25605120000

def SurrogateDiagonalTailChunk000Sub000Block011Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 505
    = surrogateDiagTailX0RatChunk000Sub000Block011Part003

theorem surrogateDiagonalTailChunk000Sub000Block011Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part003] using hcert

def TailChunk000Sub000Block011Part004SupportExplicit : Finset ℕ :=
  ([506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part004 : ℚ :=
  (1389272993 : ℚ) / 117151425600

def SurrogateDiagonalTailChunk000Sub000Block011Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 506
    = surrogateDiagTailX0RatChunk000Sub000Block011Part004

theorem surrogateDiagonalTailChunk000Sub000Block011Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part004] using hcert

def TailChunk000Sub000Block011Part005SupportExplicit : Finset ℕ :=
  ([509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part005 : ℚ :=
  (161634158875 : ℚ) / 166525868754048

def SurrogateDiagonalTailChunk000Sub000Block011Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 509
    = surrogateDiagTailX0RatChunk000Sub000Block011Part005

theorem surrogateDiagonalTailChunk000Sub000Block011Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part005] using hcert

def TailChunk000Sub000Block011Part006SupportExplicit : Finset ℕ :=
  ([510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part006 : ℚ :=
  (20163881825 : ℚ) / 335611428864

def SurrogateDiagonalTailChunk000Sub000Block011Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 510
    = surrogateDiagTailX0RatChunk000Sub000Block011Part006

theorem surrogateDiagonalTailChunk000Sub000Block011Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part006] using hcert

def TailChunk000Sub000Block011Part007SupportExplicit : Finset ℕ :=
  ([511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part007 : ℚ :=
  (68653745525 : ℚ) / 43544353849344

def SurrogateDiagonalTailChunk000Sub000Block011Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 511
    = surrogateDiagTailX0RatChunk000Sub000Block011Part007

theorem surrogateDiagonalTailChunk000Sub000Block011Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part007] using hcert

def TailChunk000Sub000Block011Part008SupportExplicit : Finset ℕ :=
  ([514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part008 : ℚ :=
  (78150828025 : ℚ) / 10739565723648

def SurrogateDiagonalTailChunk000Sub000Block011Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 514
    = surrogateDiagTailX0RatChunk000Sub000Block011Part008

theorem surrogateDiagonalTailChunk000Sub000Block011Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part008] using hcert

def TailChunk000Sub000Block011Part009SupportExplicit : Finset ℕ :=
  ([515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part009 : ℚ :=
  (130013612575 : ℚ) / 69289513371648

def SurrogateDiagonalTailChunk000Sub000Block011Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 515
    = surrogateDiagTailX0RatChunk000Sub000Block011Part009

theorem surrogateDiagonalTailChunk000Sub000Block011Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part009] using hcert

def TailChunk000Sub000Block011Part010SupportExplicit : Finset ℕ :=
  ([517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part010 : ℚ :=
  (899629401 : ℚ) / 746391915200

def SurrogateDiagonalTailChunk000Sub000Block011Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 517
    = surrogateDiagTailX0RatChunk000Sub000Block011Part010

theorem surrogateDiagonalTailChunk000Sub000Block011Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part010] using hcert

def TailChunk000Sub000Block011Part011SupportExplicit : Finset ℕ :=
  ([518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part011 : ℚ :=
  (66637699375 : ℚ) / 5443044231168

def SurrogateDiagonalTailChunk000Sub000Block011Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 518
    = surrogateDiagTailX0RatChunk000Sub000Block011Part011

theorem surrogateDiagonalTailChunk000Sub000Block011Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part011] using hcert

def TailChunk000Sub000Block011Part012SupportExplicit : Finset ℕ :=
  ([519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part012 : ℚ :=
  (2551953625 : ℚ) / 814314510336

def SurrogateDiagonalTailChunk000Sub000Block011Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 519
    = surrogateDiagTailX0RatChunk000Sub000Block011Part012

theorem surrogateDiagonalTailChunk000Sub000Block011Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part012] using hcert

def TailChunk000Sub000Block011Part013SupportExplicit : Finset ℕ :=
  ([521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part013 : ℚ :=
  (1354762031 : ℚ) / 1462615664640

def SurrogateDiagonalTailChunk000Sub000Block011Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 521
    = surrogateDiagTailX0RatChunk000Sub000Block011Part013

theorem surrogateDiagonalTailChunk000Sub000Block011Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part013] using hcert

def TailChunk000Sub000Block011Part014SupportExplicit : Finset ℕ :=
  ([523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part014 : ℚ :=
  (711175400 : ℚ) / 859518284283

def SurrogateDiagonalTailChunk000Sub000Block011Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 523
    = surrogateDiagTailX0RatChunk000Sub000Block011Part014

theorem surrogateDiagonalTailChunk000Sub000Block011Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part014] using hcert

def TailChunk000Sub000Block011Part015SupportExplicit : Finset ℕ :=
  ([526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part015 : ℚ :=
  (81842490025 : ℚ) / 11782352839368

def SurrogateDiagonalTailChunk000Sub000Block011Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 526
    = surrogateDiagTailX0RatChunk000Sub000Block011Part015

theorem surrogateDiagonalTailChunk000Sub000Block011Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part015] using hcert

def TailChunk000Sub000Block011Part016SupportExplicit : Finset ℕ :=
  ([527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part016 : ℚ :=
  (1049019803 : ℚ) / 884912947200

def SurrogateDiagonalTailChunk000Sub000Block011Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 527
    = surrogateDiagTailX0RatChunk000Sub000Block011Part016

theorem surrogateDiagonalTailChunk000Sub000Block011Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part016] using hcert

def TailChunk000Sub000Block011Part017SupportExplicit : Finset ℕ :=
  ([530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part017 : ℚ :=
  (32730169625 : ℚ) / 2340185063424

def SurrogateDiagonalTailChunk000Sub000Block011Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 530
    = surrogateDiagTailX0RatChunk000Sub000Block011Part017

theorem surrogateDiagonalTailChunk000Sub000Block011Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part017] using hcert

def TailChunk000Sub000Block011Part018SupportExplicit : Finset ℕ :=
  ([533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part018 : ℚ :=
  (5783752183 : ℚ) / 5309477683200

def SurrogateDiagonalTailChunk000Sub000Block011Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 533
    = surrogateDiagTailX0RatChunk000Sub000Block011Part018

theorem surrogateDiagonalTailChunk000Sub000Block011Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part018] using hcert

def TailChunk000Sub000Block011Part019SupportExplicit : Finset ℕ :=
  ([534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part019 : ℚ :=
  (697425 : ℚ) / 29984768

def SurrogateDiagonalTailChunk000Sub000Block011Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 534
    = surrogateDiagTailX0RatChunk000Sub000Block011Part019

theorem surrogateDiagonalTailChunk000Sub000Block011Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part019] using hcert

def TailChunk000Sub000Block011Part020SupportExplicit : Finset ℕ :=
  ([535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part020 : ℚ :=
  (129074340775 : ℚ) / 80814685145088

def SurrogateDiagonalTailChunk000Sub000Block011Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 535
    = surrogateDiagTailX0RatChunk000Sub000Block011Part020

theorem surrogateDiagonalTailChunk000Sub000Block011Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part020] using hcert

def TailChunk000Sub000Block011Part021SupportExplicit : Finset ℕ :=
  ([537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part021 : ℚ :=
  (109556944075 : ℚ) / 40163065246848

def SurrogateDiagonalTailChunk000Sub000Block011Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 537
    = surrogateDiagTailX0RatChunk000Sub000Block011Part021

theorem surrogateDiagonalTailChunk000Sub000Block011Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part021] using hcert

def TailChunk000Sub000Block011Part022SupportExplicit : Finset ℕ :=
  ([538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part022 : ℚ :=
  (85619344225 : ℚ) / 12899296783488

def SurrogateDiagonalTailChunk000Sub000Block011Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 538
    = surrogateDiagTailX0RatChunk000Sub000Block011Part022

theorem surrogateDiagonalTailChunk000Sub000Block011Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part022] using hcert

def TailChunk000Sub000Block011Part023SupportExplicit : Finset ℕ :=
  ([541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part023 : ℚ :=
  (3804853 : ℚ) / 4921734150

def SurrogateDiagonalTailChunk000Sub000Block011Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 541
    = surrogateDiagTailX0RatChunk000Sub000Block011Part023

theorem surrogateDiagonalTailChunk000Sub000Block011Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part023] using hcert

def TailChunk000Sub000Block011Part024SupportExplicit : Finset ℕ :=
  ([542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block011Part024 : ℚ :=
  (121985501 : ℚ) / 19686936600

def SurrogateDiagonalTailChunk000Sub000Block011Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 542
    = surrogateDiagTailX0RatChunk000Sub000Block011Part024

theorem surrogateDiagonalTailChunk000Sub000Block011Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block011Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block011Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block011Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block011Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block011Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block011HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block011Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block011Part000
    + surrogateDiagTailX0RatChunk000Sub000Block011Part001
    + surrogateDiagTailX0RatChunk000Sub000Block011Part002
    + surrogateDiagTailX0RatChunk000Sub000Block011Part003
    + surrogateDiagTailX0RatChunk000Sub000Block011Part004
    + surrogateDiagTailX0RatChunk000Sub000Block011Part005
    + surrogateDiagTailX0RatChunk000Sub000Block011Part006
    + surrogateDiagTailX0RatChunk000Sub000Block011Part007
    + surrogateDiagTailX0RatChunk000Sub000Block011Part008
    + surrogateDiagTailX0RatChunk000Sub000Block011Part009

def surrogateDiagonalTailChunk000Sub000Block011MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block011Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block011Part010
    + surrogateDiagTailX0RatChunk000Sub000Block011Part011
    + surrogateDiagTailX0RatChunk000Sub000Block011Part012
    + surrogateDiagTailX0RatChunk000Sub000Block011Part013
    + surrogateDiagTailX0RatChunk000Sub000Block011Part014
    + surrogateDiagTailX0RatChunk000Sub000Block011Part015
    + surrogateDiagTailX0RatChunk000Sub000Block011Part016
    + surrogateDiagTailX0RatChunk000Sub000Block011Part017
    + surrogateDiagTailX0RatChunk000Sub000Block011Part018
    + surrogateDiagTailX0RatChunk000Sub000Block011Part019

def surrogateDiagonalTailChunk000Sub000Block011TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block011Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block011Part020
    + surrogateDiagTailX0RatChunk000Sub000Block011Part021
    + surrogateDiagTailX0RatChunk000Sub000Block011Part022
    + surrogateDiagTailX0RatChunk000Sub000Block011Part023
    + surrogateDiagTailX0RatChunk000Sub000Block011Part024

def surrogateDiagonalTailChunk000Sub000Block011Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block011HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block011MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block011TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block011 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block011Part000
    + surrogateDiagTailX0RatChunk000Sub000Block011Part001
    + surrogateDiagTailX0RatChunk000Sub000Block011Part002
    + surrogateDiagTailX0RatChunk000Sub000Block011Part003
    + surrogateDiagTailX0RatChunk000Sub000Block011Part004
    + surrogateDiagTailX0RatChunk000Sub000Block011Part005
    + surrogateDiagTailX0RatChunk000Sub000Block011Part006
    + surrogateDiagTailX0RatChunk000Sub000Block011Part007
    + surrogateDiagTailX0RatChunk000Sub000Block011Part008
    + surrogateDiagTailX0RatChunk000Sub000Block011Part009
    + surrogateDiagTailX0RatChunk000Sub000Block011Part010
    + surrogateDiagTailX0RatChunk000Sub000Block011Part011
    + surrogateDiagTailX0RatChunk000Sub000Block011Part012
    + surrogateDiagTailX0RatChunk000Sub000Block011Part013
    + surrogateDiagTailX0RatChunk000Sub000Block011Part014
    + surrogateDiagTailX0RatChunk000Sub000Block011Part015
    + surrogateDiagTailX0RatChunk000Sub000Block011Part016
    + surrogateDiagTailX0RatChunk000Sub000Block011Part017
    + surrogateDiagTailX0RatChunk000Sub000Block011Part018
    + surrogateDiagTailX0RatChunk000Sub000Block011Part019
    + surrogateDiagTailX0RatChunk000Sub000Block011Part020
    + surrogateDiagTailX0RatChunk000Sub000Block011Part021
    + surrogateDiagTailX0RatChunk000Sub000Block011Part022
    + surrogateDiagTailX0RatChunk000Sub000Block011Part023
    + surrogateDiagTailX0RatChunk000Sub000Block011Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block011_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block011Head + surrogateDiagTailX0RatChunk000Sub000Block011Mid + surrogateDiagTailX0RatChunk000Sub000Block011Tail =
      surrogateDiagTailX0RatChunk000Sub000Block011 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block011Head surrogateDiagTailX0RatChunk000Sub000Block011Mid surrogateDiagTailX0RatChunk000Sub000Block011Tail surrogateDiagTailX0RatChunk000Sub000Block011
  ring

def SurrogateDiagonalTailChunk000Sub000Block011HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block011HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block011Head

def SurrogateDiagonalTailChunk000Sub000Block011MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block011MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block011Mid

def SurrogateDiagonalTailChunk000Sub000Block011TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block011TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block011Tail

theorem surrogateDiagonalTailChunk000Sub000Block011_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block011HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block011MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block011TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block011Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block011 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block011HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block011MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block011TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block011Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block011_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
