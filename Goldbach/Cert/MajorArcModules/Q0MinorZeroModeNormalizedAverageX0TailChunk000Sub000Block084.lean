import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [84,85). -/

/- Block 084 covers tail-support indices [2100,2125) and q from 3499 to 3539. -/

def TailChunk000Sub000Block084Part000SupportExplicit : Finset ℕ :=
  ([3499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part000 : ℚ :=
  (1530069049975 : ℚ) / 374374344616984008

def SurrogateDiagonalTailChunk000Sub000Block084Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3499
    = surrogateDiagTailX0RatChunk000Sub000Block084Part000

theorem surrogateDiagonalTailChunk000Sub000Block084Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part000] using hcert

def TailChunk000Sub000Block084Part001SupportExplicit : Finset ℕ :=
  ([3502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part001 : ℚ :=
  (59300680925 : ℚ) / 1970901713682432

def SurrogateDiagonalTailChunk000Sub000Block084Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3502
    = surrogateDiagTailX0RatChunk000Sub000Block084Part001

theorem surrogateDiagonalTailChunk000Sub000Block084Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part001] using hcert

def TailChunk000Sub000Block084Part002SupportExplicit : Finset ℕ :=
  ([3503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part002 : ℚ :=
  (14543997841 : ℚ) / 3187013979340800

def SurrogateDiagonalTailChunk000Sub000Block084Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3503
    = surrogateDiagTailX0RatChunk000Sub000Block084Part002

theorem surrogateDiagonalTailChunk000Sub000Block084Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part002] using hcert

def TailChunk000Sub000Block084Part003SupportExplicit : Finset ℕ :=
  ([3505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part003 : ℚ :=
  (45381819589 : ℚ) / 6147789312000000

def SurrogateDiagonalTailChunk000Sub000Block084Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3505
    = surrogateDiagTailX0RatChunk000Sub000Block084Part003

theorem surrogateDiagonalTailChunk000Sub000Block084Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part003] using hcert

def TailChunk000Sub000Block084Part004SupportExplicit : Finset ℕ :=
  ([3506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part004 : ℚ :=
  (63995412425 : ℚ) / 2617705326938112

def SurrogateDiagonalTailChunk000Sub000Block084Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3506
    = surrogateDiagTailX0RatChunk000Sub000Block084Part004

theorem surrogateDiagonalTailChunk000Sub000Block084Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part004] using hcert

def TailChunk000Sub000Block084Part005SupportExplicit : Finset ℕ :=
  ([3507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part005 : ℚ :=
  (261111511325 : ℚ) / 19685851268097024

def SurrogateDiagonalTailChunk000Sub000Block084Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3507
    = surrogateDiagTailX0RatChunk000Sub000Block084Part005

theorem surrogateDiagonalTailChunk000Sub000Block084Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part005] using hcert

def TailChunk000Sub000Block084Part006SupportExplicit : Finset ℕ :=
  ([3511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part006 : ℚ :=
  (308178025 : ℚ) / 151815220982802

def SurrogateDiagonalTailChunk000Sub000Block084Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3511
    = surrogateDiagTailX0RatChunk000Sub000Block084Part006

theorem surrogateDiagonalTailChunk000Sub000Block084Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part006] using hcert

def TailChunk000Sub000Block084Part007SupportExplicit : Finset ℕ :=
  ([3513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part007 : ℚ :=
  (5481144623 : ℚ) / 599763835981440

def SurrogateDiagonalTailChunk000Sub000Block084Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3513
    = surrogateDiagTailX0RatChunk000Sub000Block084Part007

theorem surrogateDiagonalTailChunk000Sub000Block084Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part007] using hcert

def TailChunk000Sub000Block084Part008SupportExplicit : Finset ℕ :=
  ([3514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part008 : ℚ :=
  (19453429921 : ℚ) / 506351250000000

def SurrogateDiagonalTailChunk000Sub000Block084Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3514
    = surrogateDiagTailX0RatChunk000Sub000Block084Part008

theorem surrogateDiagonalTailChunk000Sub000Block084Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part008] using hcert

def TailChunk000Sub000Block084Part009SupportExplicit : Finset ℕ :=
  ([3515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part009 : ℚ :=
  (641260305625 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block084Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3515
    = surrogateDiagTailX0RatChunk000Sub000Block084Part009

theorem surrogateDiagonalTailChunk000Sub000Block084Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part009] using hcert

def TailChunk000Sub000Block084Part010SupportExplicit : Finset ℕ :=
  ([3517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part010 : ℚ :=
  (193270140625 : ℚ) / 95534961552636192

def SurrogateDiagonalTailChunk000Sub000Block084Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3517
    = surrogateDiagTailX0RatChunk000Sub000Block084Part010

theorem surrogateDiagonalTailChunk000Sub000Block084Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part010] using hcert

def TailChunk000Sub000Block084Part011SupportExplicit : Finset ℕ :=
  ([3518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part011 : ℚ :=
  (64434236825 : ℚ) / 2653748932017672

def SurrogateDiagonalTailChunk000Sub000Block084Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3518
    = surrogateDiagTailX0RatChunk000Sub000Block084Part011

theorem surrogateDiagonalTailChunk000Sub000Block084Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part011] using hcert

def TailChunk000Sub000Block084Part012SupportExplicit : Finset ℕ :=
  ([3521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part012 : ℚ :=
  (695009088925 : ℚ) / 205800643790218368

def SurrogateDiagonalTailChunk000Sub000Block084Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3521
    = surrogateDiagTailX0RatChunk000Sub000Block084Part012

theorem surrogateDiagonalTailChunk000Sub000Block084Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part012] using hcert

def TailChunk000Sub000Block084Part013SupportExplicit : Finset ℕ :=
  ([3522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part013 : ℚ :=
  (19347225 : ℚ) / 235841625632

def SurrogateDiagonalTailChunk000Sub000Block084Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3522
    = surrogateDiagTailX0RatChunk000Sub000Block084Part013

theorem surrogateDiagonalTailChunk000Sub000Block084Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part013] using hcert

def TailChunk000Sub000Block084Part014SupportExplicit : Finset ℕ :=
  ([3523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part014 : ℚ :=
  (13890537307 : ℚ) / 2755541142028800

def SurrogateDiagonalTailChunk000Sub000Block084Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3523
    = surrogateDiagTailX0RatChunk000Sub000Block084Part014

theorem surrogateDiagonalTailChunk000Sub000Block084Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part014] using hcert

def TailChunk000Sub000Block084Part015SupportExplicit : Finset ℕ :=
  ([3526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part015 : ℚ :=
  (11081525603 : ℚ) / 398376747417600

def SurrogateDiagonalTailChunk000Sub000Block084Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3526
    = surrogateDiagTailX0RatChunk000Sub000Block084Part015

theorem surrogateDiagonalTailChunk000Sub000Block084Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part015] using hcert

def TailChunk000Sub000Block084Part016SupportExplicit : Finset ℕ :=
  ([3527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part016 : ℚ :=
  (1554655131775 : ℚ) / 386505867018700488

def SurrogateDiagonalTailChunk000Sub000Block084Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3527
    = surrogateDiagTailX0RatChunk000Sub000Block084Part016

theorem surrogateDiagonalTailChunk000Sub000Block084Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part016] using hcert

def TailChunk000Sub000Block084Part017SupportExplicit : Finset ℕ :=
  ([3529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part017 : ℚ :=
  (1556418778975 : ℚ) / 387383541072611328

def SurrogateDiagonalTailChunk000Sub000Block084Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3529
    = surrogateDiagTailX0RatChunk000Sub000Block084Part017

theorem surrogateDiagonalTailChunk000Sub000Block084Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part017] using hcert

def TailChunk000Sub000Block084Part018SupportExplicit : Finset ℕ :=
  ([3530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part018 : ℚ :=
  (229116709325 : ℚ) / 4913686929997824

def SurrogateDiagonalTailChunk000Sub000Block084Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3530
    = surrogateDiagTailX0RatChunk000Sub000Block084Part018

theorem surrogateDiagonalTailChunk000Sub000Block084Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part018] using hcert

def TailChunk000Sub000Block084Part019SupportExplicit : Finset ℕ :=
  ([3531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part019 : ℚ :=
  (446829573 : ℚ) / 26938228381696

def SurrogateDiagonalTailChunk000Sub000Block084Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3531
    = surrogateDiagTailX0RatChunk000Sub000Block084Part019

theorem surrogateDiagonalTailChunk000Sub000Block084Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part019] using hcert

def TailChunk000Sub000Block084Part020SupportExplicit : Finset ℕ :=
  ([3533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part020 : ℚ :=
  (195032640625 : ℚ) / 97285843153335072

def SurrogateDiagonalTailChunk000Sub000Block084Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3533
    = surrogateDiagTailX0RatChunk000Sub000Block084Part020

theorem surrogateDiagonalTailChunk000Sub000Block084Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part020] using hcert

def TailChunk000Sub000Block084Part021SupportExplicit : Finset ℕ :=
  ([3534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part021 : ℚ :=
  (14246312443 : ℚ) / 136076105779200

def SurrogateDiagonalTailChunk000Sub000Block084Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3534
    = surrogateDiagTailX0RatChunk000Sub000Block084Part021

theorem surrogateDiagonalTailChunk000Sub000Block084Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part021] using hcert

def TailChunk000Sub000Block084Part022SupportExplicit : Finset ℕ :=
  ([3535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part022 : ℚ :=
  (24551683111 : ℚ) / 3318423552000000

def SurrogateDiagonalTailChunk000Sub000Block084Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3535
    = surrogateDiagTailX0RatChunk000Sub000Block084Part022

theorem surrogateDiagonalTailChunk000Sub000Block084Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part022] using hcert

def TailChunk000Sub000Block084Part023SupportExplicit : Finset ℕ :=
  ([3538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part023 : ℚ :=
  (7408836287 : ℚ) / 265584498278400

def SurrogateDiagonalTailChunk000Sub000Block084Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3538
    = surrogateDiagTailX0RatChunk000Sub000Block084Part023

theorem surrogateDiagonalTailChunk000Sub000Block084Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part023] using hcert

def TailChunk000Sub000Block084Part024SupportExplicit : Finset ℕ :=
  ([3539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block084Part024 : ℚ :=
  (195695640625 : ℚ) / 97948588483746642

def SurrogateDiagonalTailChunk000Sub000Block084Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3539
    = surrogateDiagTailX0RatChunk000Sub000Block084Part024

theorem surrogateDiagonalTailChunk000Sub000Block084Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block084Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block084Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block084Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block084Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block084Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block084Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block084HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block084Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block084Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block084Part000
    + surrogateDiagTailX0RatChunk000Sub000Block084Part001
    + surrogateDiagTailX0RatChunk000Sub000Block084Part002
    + surrogateDiagTailX0RatChunk000Sub000Block084Part003
    + surrogateDiagTailX0RatChunk000Sub000Block084Part004
    + surrogateDiagTailX0RatChunk000Sub000Block084Part005
    + surrogateDiagTailX0RatChunk000Sub000Block084Part006
    + surrogateDiagTailX0RatChunk000Sub000Block084Part007
    + surrogateDiagTailX0RatChunk000Sub000Block084Part008
    + surrogateDiagTailX0RatChunk000Sub000Block084Part009

def surrogateDiagonalTailChunk000Sub000Block084MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block084Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block084Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block084Part010
    + surrogateDiagTailX0RatChunk000Sub000Block084Part011
    + surrogateDiagTailX0RatChunk000Sub000Block084Part012
    + surrogateDiagTailX0RatChunk000Sub000Block084Part013
    + surrogateDiagTailX0RatChunk000Sub000Block084Part014
    + surrogateDiagTailX0RatChunk000Sub000Block084Part015
    + surrogateDiagTailX0RatChunk000Sub000Block084Part016
    + surrogateDiagTailX0RatChunk000Sub000Block084Part017
    + surrogateDiagTailX0RatChunk000Sub000Block084Part018
    + surrogateDiagTailX0RatChunk000Sub000Block084Part019

def surrogateDiagonalTailChunk000Sub000Block084TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block084Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block084Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block084Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block084Part020
    + surrogateDiagTailX0RatChunk000Sub000Block084Part021
    + surrogateDiagTailX0RatChunk000Sub000Block084Part022
    + surrogateDiagTailX0RatChunk000Sub000Block084Part023
    + surrogateDiagTailX0RatChunk000Sub000Block084Part024

def surrogateDiagonalTailChunk000Sub000Block084Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block084HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block084MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block084TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block084 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block084Part000
    + surrogateDiagTailX0RatChunk000Sub000Block084Part001
    + surrogateDiagTailX0RatChunk000Sub000Block084Part002
    + surrogateDiagTailX0RatChunk000Sub000Block084Part003
    + surrogateDiagTailX0RatChunk000Sub000Block084Part004
    + surrogateDiagTailX0RatChunk000Sub000Block084Part005
    + surrogateDiagTailX0RatChunk000Sub000Block084Part006
    + surrogateDiagTailX0RatChunk000Sub000Block084Part007
    + surrogateDiagTailX0RatChunk000Sub000Block084Part008
    + surrogateDiagTailX0RatChunk000Sub000Block084Part009
    + surrogateDiagTailX0RatChunk000Sub000Block084Part010
    + surrogateDiagTailX0RatChunk000Sub000Block084Part011
    + surrogateDiagTailX0RatChunk000Sub000Block084Part012
    + surrogateDiagTailX0RatChunk000Sub000Block084Part013
    + surrogateDiagTailX0RatChunk000Sub000Block084Part014
    + surrogateDiagTailX0RatChunk000Sub000Block084Part015
    + surrogateDiagTailX0RatChunk000Sub000Block084Part016
    + surrogateDiagTailX0RatChunk000Sub000Block084Part017
    + surrogateDiagTailX0RatChunk000Sub000Block084Part018
    + surrogateDiagTailX0RatChunk000Sub000Block084Part019
    + surrogateDiagTailX0RatChunk000Sub000Block084Part020
    + surrogateDiagTailX0RatChunk000Sub000Block084Part021
    + surrogateDiagTailX0RatChunk000Sub000Block084Part022
    + surrogateDiagTailX0RatChunk000Sub000Block084Part023
    + surrogateDiagTailX0RatChunk000Sub000Block084Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block084_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block084Head + surrogateDiagTailX0RatChunk000Sub000Block084Mid + surrogateDiagTailX0RatChunk000Sub000Block084Tail =
      surrogateDiagTailX0RatChunk000Sub000Block084 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block084Head surrogateDiagTailX0RatChunk000Sub000Block084Mid surrogateDiagTailX0RatChunk000Sub000Block084Tail surrogateDiagTailX0RatChunk000Sub000Block084
  ring

def SurrogateDiagonalTailChunk000Sub000Block084HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block084HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block084Head

def SurrogateDiagonalTailChunk000Sub000Block084MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block084MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block084Mid

def SurrogateDiagonalTailChunk000Sub000Block084TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block084TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block084Tail

theorem surrogateDiagonalTailChunk000Sub000Block084_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block084HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block084MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block084TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block084Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block084 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block084HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block084MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block084TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block084Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block084_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
