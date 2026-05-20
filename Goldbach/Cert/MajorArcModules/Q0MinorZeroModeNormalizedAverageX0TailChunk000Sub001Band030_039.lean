import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [30,40). -/

/-- Block 030 covers tail-support indices [5750,5775) and q from 9502 to 9542. -/

def TailChunk000Sub001Block030Part000SupportExplicit : Finset ℕ :=
  ([9502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part000 : ℚ :=
  (22572001 : ℚ) / 20366728781250

def SurrogateDiagonalTailChunk000Sub001Block030Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9502
    = surrogateDiagTailX0RatChunk000Sub001Block030Part000

theorem surrogateDiagonalTailChunk000Sub001Block030Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part000] using hcert

def TailChunk000Sub001Block030Part001SupportExplicit : Finset ℕ :=
  ([9503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part001 : ℚ :=
  (1476962357075 : ℚ) / 3524582500032577536

def SurrogateDiagonalTailChunk000Sub001Block030Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9503
    = surrogateDiagTailX0RatChunk000Sub001Block030Part001

theorem surrogateDiagonalTailChunk000Sub001Block030Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part001] using hcert

def TailChunk000Sub001Block030Part002SupportExplicit : Finset ℕ :=
  ([9505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part002 : ℚ :=
  (153489453199 : ℚ) / 333688484352000000

def SurrogateDiagonalTailChunk000Sub001Block030Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9505
    = surrogateDiagTailX0RatChunk000Sub001Block030Part002

theorem surrogateDiagonalTailChunk000Sub001Block030Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part002] using hcert

def TailChunk000Sub001Block030Part003SupportExplicit : Finset ℕ :=
  ([9507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part003 : ℚ :=
  (1568723334725 : ℚ) / 2014918746732232704

def SurrogateDiagonalTailChunk000Sub001Block030Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9507
    = surrogateDiagTailX0RatChunk000Sub001Block030Part003

theorem surrogateDiagonalTailChunk000Sub001Block030Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part003] using hcert

def TailChunk000Sub001Block030Part004SupportExplicit : Finset ℕ :=
  ([9509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part004 : ℚ :=
  (24972738275 : ℚ) / 83510863067086848

def SurrogateDiagonalTailChunk000Sub001Block030Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9509
    = surrogateDiagTailX0RatChunk000Sub001Block030Part004

theorem surrogateDiagonalTailChunk000Sub001Block030Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part004] using hcert

def TailChunk000Sub001Block030Part005SupportExplicit : Finset ℕ :=
  ([9510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part005 : ℚ :=
  (258842261025 : ℚ) / 34041907132235776

def SurrogateDiagonalTailChunk000Sub001Block030Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9510
    = surrogateDiagTailX0RatChunk000Sub001Block030Part005

theorem surrogateDiagonalTailChunk000Sub001Block030Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part005] using hcert

def TailChunk000Sub001Block030Part006SupportExplicit : Finset ℕ :=
  ([9511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part006 : ℚ :=
  (2261478025 : ℚ) / 8181047570347602

def SurrogateDiagonalTailChunk000Sub001Block030Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9511
    = surrogateDiagTailX0RatChunk000Sub001Block030Part006

theorem surrogateDiagonalTailChunk000Sub001Block030Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part006] using hcert

def TailChunk000Sub001Block030Part007SupportExplicit : Finset ℕ :=
  ([9514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part007 : ℚ :=
  (3057512737 : ℚ) / 2531525155790400

def SurrogateDiagonalTailChunk000Sub001Block030Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9514
    = surrogateDiagTailX0RatChunk000Sub001Block030Part007

theorem surrogateDiagonalTailChunk000Sub001Block030Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part007] using hcert

def TailChunk000Sub001Block030Part008SupportExplicit : Finset ℕ :=
  ([9515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part008 : ℚ :=
  (28000439573 : ℚ) / 44819870648893440

def SurrogateDiagonalTailChunk000Sub001Block030Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9515
    = surrogateDiagTailX0RatChunk000Sub001Block030Part008

theorem surrogateDiagonalTailChunk000Sub001Block030Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part008] using hcert

def TailChunk000Sub001Block030Part009SupportExplicit : Finset ℕ :=
  ([9517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part009 : ℚ :=
  (21459667627 : ℚ) / 71032577692403520

def SurrogateDiagonalTailChunk000Sub001Block030Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9517
    = surrogateDiagTailX0RatChunk000Sub001Block030Part009

theorem surrogateDiagonalTailChunk000Sub001Block030Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part009] using hcert

def TailChunk000Sub001Block030Part010SupportExplicit : Finset ℕ :=
  ([9518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part010 : ℚ :=
  (353876265625 : ℚ) / 320379425561307762

def SurrogateDiagonalTailChunk000Sub001Block030Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9518
    = surrogateDiagTailX0RatChunk000Sub001Block030Part010

theorem surrogateDiagonalTailChunk000Sub001Block030Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part010] using hcert

def TailChunk000Sub001Block030Part011SupportExplicit : Finset ℕ :=
  ([9519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part011 : ℚ :=
  (1444732490525 : ℚ) / 1594553952715858944

def SurrogateDiagonalTailChunk000Sub001Block030Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9519
    = surrogateDiagTailX0RatChunk000Sub001Block030Part011

theorem surrogateDiagonalTailChunk000Sub001Block030Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part011] using hcert

def TailChunk000Sub001Block030Part012SupportExplicit : Finset ℕ :=
  ([9521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part012 : ℚ :=
  (2266236025 : ℚ) / 8215512178040832

def SurrogateDiagonalTailChunk000Sub001Block030Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9521
    = surrogateDiagTailX0RatChunk000Sub001Block030Part012

theorem surrogateDiagonalTailChunk000Sub001Block030Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part012] using hcert

def TailChunk000Sub001Block030Part013SupportExplicit : Finset ℕ :=
  ([9523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part013 : ℚ :=
  (1832930928825 : ℚ) / 6310441627782578176

def SurrogateDiagonalTailChunk000Sub001Block030Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9523
    = surrogateDiagTailX0RatChunk000Sub001Block030Part013

theorem surrogateDiagonalTailChunk000Sub001Block030Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part013] using hcert

def TailChunk000Sub001Block030Part014SupportExplicit : Finset ℕ :=
  ([9526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part014 : ℚ :=
  (109013837 : ℚ) / 38706092310528

def SurrogateDiagonalTailChunk000Sub001Block030Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9526
    = surrogateDiagTailX0RatChunk000Sub001Block030Part014

theorem surrogateDiagonalTailChunk000Sub001Block030Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part014] using hcert

def TailChunk000Sub001Block030Part015SupportExplicit : Finset ℕ :=
  ([9527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part015 : ℚ :=
  (10024367471 : ℚ) / 24636271421030400

def SurrogateDiagonalTailChunk000Sub001Block030Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9527
    = surrogateDiagTailX0RatChunk000Sub001Block030Part015

theorem surrogateDiagonalTailChunk000Sub001Block030Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part015] using hcert

def TailChunk000Sub001Block030Part016SupportExplicit : Finset ℕ :=
  ([9529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part016 : ℚ :=
  (204485842375 : ℚ) / 14886622218413703168

def SurrogateDiagonalTailChunk000Sub001Block030Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9529
    = surrogateDiagTailX0RatChunk000Sub001Block030Part016

theorem surrogateDiagonalTailChunk000Sub001Block030Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part016] using hcert

def TailChunk000Sub001Block030Part017SupportExplicit : Finset ℕ :=
  ([9530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part017 : ℚ :=
  (567178287875 : ℚ) / 262896389697306624

def SurrogateDiagonalTailChunk000Sub001Block030Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9530
    = surrogateDiagTailX0RatChunk000Sub001Block030Part017

theorem surrogateDiagonalTailChunk000Sub001Block030Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part017] using hcert

def TailChunk000Sub001Block030Part018SupportExplicit : Finset ℕ :=
  ([9533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block030Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9533
    = surrogateDiagTailX0RatChunk000Sub001Block030Part018

theorem surrogateDiagonalTailChunk000Sub001Block030Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part018] using hcert

def TailChunk000Sub001Block030Part019SupportExplicit : Finset ℕ :=
  ([9534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part019 : ℚ :=
  (405766971425 : ℚ) / 67632525354230784

def SurrogateDiagonalTailChunk000Sub001Block030Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9534
    = surrogateDiagTailX0RatChunk000Sub001Block030Part019

theorem surrogateDiagonalTailChunk000Sub001Block030Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part019] using hcert

def TailChunk000Sub001Block030Part020SupportExplicit : Finset ℕ :=
  ([9535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part020 : ℚ :=
  (455264232025 : ℚ) / 8448087617521010688

def SurrogateDiagonalTailChunk000Sub001Block030Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9535
    = surrogateDiagTailX0RatChunk000Sub001Block030Part020

theorem surrogateDiagonalTailChunk000Sub001Block030Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part020] using hcert

def TailChunk000Sub001Block030Part021SupportExplicit : Finset ℕ :=
  ([9538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part021 : ℚ :=
  (6709031537 : ℚ) / 5126806406250000

def SurrogateDiagonalTailChunk000Sub001Block030Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9538
    = surrogateDiagTailX0RatChunk000Sub001Block030Part021

theorem surrogateDiagonalTailChunk000Sub001Block030Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part021] using hcert

def TailChunk000Sub001Block030Part022SupportExplicit : Finset ℕ :=
  ([9539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block030Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9539
    = surrogateDiagTailX0RatChunk000Sub001Block030Part022

theorem surrogateDiagonalTailChunk000Sub001Block030Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part022] using hcert

def TailChunk000Sub001Block030Part023SupportExplicit : Finset ℕ :=
  ([9541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part023 : ℚ :=
  (30476691575 : ℚ) / 495476210551504896

def SurrogateDiagonalTailChunk000Sub001Block030Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9541
    = surrogateDiagTailX0RatChunk000Sub001Block030Part023

theorem surrogateDiagonalTailChunk000Sub001Block030Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part023] using hcert

def TailChunk000Sub001Block030Part024SupportExplicit : Finset ℕ :=
  ([9542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block030Part024 : ℚ :=
  (1318448854375 : ℚ) / 930413888650856448

def SurrogateDiagonalTailChunk000Sub001Block030Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9542
    = surrogateDiagTailX0RatChunk000Sub001Block030Part024

theorem surrogateDiagonalTailChunk000Sub001Block030Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block030Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block030Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block030Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block030Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block030Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block030Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block030HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block030Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block030Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block030Part000
    + surrogateDiagTailX0RatChunk000Sub001Block030Part001
    + surrogateDiagTailX0RatChunk000Sub001Block030Part002
    + surrogateDiagTailX0RatChunk000Sub001Block030Part003
    + surrogateDiagTailX0RatChunk000Sub001Block030Part004
    + surrogateDiagTailX0RatChunk000Sub001Block030Part005
    + surrogateDiagTailX0RatChunk000Sub001Block030Part006
    + surrogateDiagTailX0RatChunk000Sub001Block030Part007
    + surrogateDiagTailX0RatChunk000Sub001Block030Part008
    + surrogateDiagTailX0RatChunk000Sub001Block030Part009

def surrogateDiagonalTailChunk000Sub001Block030MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block030Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block030Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block030Part010
    + surrogateDiagTailX0RatChunk000Sub001Block030Part011
    + surrogateDiagTailX0RatChunk000Sub001Block030Part012
    + surrogateDiagTailX0RatChunk000Sub001Block030Part013
    + surrogateDiagTailX0RatChunk000Sub001Block030Part014
    + surrogateDiagTailX0RatChunk000Sub001Block030Part015
    + surrogateDiagTailX0RatChunk000Sub001Block030Part016
    + surrogateDiagTailX0RatChunk000Sub001Block030Part017
    + surrogateDiagTailX0RatChunk000Sub001Block030Part018
    + surrogateDiagTailX0RatChunk000Sub001Block030Part019

def surrogateDiagonalTailChunk000Sub001Block030TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block030Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block030Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block030Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block030Part020
    + surrogateDiagTailX0RatChunk000Sub001Block030Part021
    + surrogateDiagTailX0RatChunk000Sub001Block030Part022
    + surrogateDiagTailX0RatChunk000Sub001Block030Part023
    + surrogateDiagTailX0RatChunk000Sub001Block030Part024

def surrogateDiagonalTailChunk000Sub001Block030Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block030HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block030MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block030TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block030 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block030Part000
    + surrogateDiagTailX0RatChunk000Sub001Block030Part001
    + surrogateDiagTailX0RatChunk000Sub001Block030Part002
    + surrogateDiagTailX0RatChunk000Sub001Block030Part003
    + surrogateDiagTailX0RatChunk000Sub001Block030Part004
    + surrogateDiagTailX0RatChunk000Sub001Block030Part005
    + surrogateDiagTailX0RatChunk000Sub001Block030Part006
    + surrogateDiagTailX0RatChunk000Sub001Block030Part007
    + surrogateDiagTailX0RatChunk000Sub001Block030Part008
    + surrogateDiagTailX0RatChunk000Sub001Block030Part009
    + surrogateDiagTailX0RatChunk000Sub001Block030Part010
    + surrogateDiagTailX0RatChunk000Sub001Block030Part011
    + surrogateDiagTailX0RatChunk000Sub001Block030Part012
    + surrogateDiagTailX0RatChunk000Sub001Block030Part013
    + surrogateDiagTailX0RatChunk000Sub001Block030Part014
    + surrogateDiagTailX0RatChunk000Sub001Block030Part015
    + surrogateDiagTailX0RatChunk000Sub001Block030Part016
    + surrogateDiagTailX0RatChunk000Sub001Block030Part017
    + surrogateDiagTailX0RatChunk000Sub001Block030Part018
    + surrogateDiagTailX0RatChunk000Sub001Block030Part019
    + surrogateDiagTailX0RatChunk000Sub001Block030Part020
    + surrogateDiagTailX0RatChunk000Sub001Block030Part021
    + surrogateDiagTailX0RatChunk000Sub001Block030Part022
    + surrogateDiagTailX0RatChunk000Sub001Block030Part023
    + surrogateDiagTailX0RatChunk000Sub001Block030Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block030_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block030Head + surrogateDiagTailX0RatChunk000Sub001Block030Mid + surrogateDiagTailX0RatChunk000Sub001Block030Tail =
      surrogateDiagTailX0RatChunk000Sub001Block030 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block030Head surrogateDiagTailX0RatChunk000Sub001Block030Mid surrogateDiagTailX0RatChunk000Sub001Block030Tail surrogateDiagTailX0RatChunk000Sub001Block030
  ring

def SurrogateDiagonalTailChunk000Sub001Block030HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block030HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block030Head

def SurrogateDiagonalTailChunk000Sub001Block030MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block030MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block030Mid

def SurrogateDiagonalTailChunk000Sub001Block030TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block030TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block030Tail

theorem surrogateDiagonalTailChunk000Sub001Block030_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block030HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block030MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block030TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block030Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block030 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block030HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block030MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block030TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block030Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block030_eq_head_add_mid_add_tail

/-- Block 031 covers tail-support indices [5775,5800) and q from 9543 to 9587. -/

def TailChunk000Sub001Block031Part000SupportExplicit : Finset ℕ :=
  ([9543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part000 : ℚ :=
  (158162527 : ℚ) / 1022810858867520

def SurrogateDiagonalTailChunk000Sub001Block031Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9543
    = surrogateDiagTailX0RatChunk000Sub001Block031Part000

theorem surrogateDiagonalTailChunk000Sub001Block031Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part000] using hcert

def TailChunk000Sub001Block031Part001SupportExplicit : Finset ℕ :=
  ([9545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part001 : ℚ :=
  (737150268625 : ℚ) / 6779738717283975168

def SurrogateDiagonalTailChunk000Sub001Block031Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9545
    = surrogateDiagTailX0RatChunk000Sub001Block031Part001

theorem surrogateDiagonalTailChunk000Sub001Block031Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part001] using hcert

def TailChunk000Sub001Block031Part002SupportExplicit : Finset ℕ :=
  ([9546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part002 : ℚ :=
  (837425 : ℚ) / 193572384768

def SurrogateDiagonalTailChunk000Sub001Block031Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9546
    = surrogateDiagTailX0RatChunk000Sub001Block031Part002

theorem surrogateDiagonalTailChunk000Sub001Block031Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part002] using hcert

def TailChunk000Sub001Block031Part003SupportExplicit : Finset ℕ :=
  ([9547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block031Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9547
    = surrogateDiagTailX0RatChunk000Sub001Block031Part003

theorem surrogateDiagonalTailChunk000Sub001Block031Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part003] using hcert

def TailChunk000Sub001Block031Part004SupportExplicit : Finset ℕ :=
  ([9551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block031Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9551
    = surrogateDiagTailX0RatChunk000Sub001Block031Part004

theorem surrogateDiagonalTailChunk000Sub001Block031Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part004] using hcert

def TailChunk000Sub001Block031Part005SupportExplicit : Finset ℕ :=
  ([9553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part005 : ℚ :=
  (143667147 : ℚ) / 30907758726348800

def SurrogateDiagonalTailChunk000Sub001Block031Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9553
    = surrogateDiagTailX0RatChunk000Sub001Block031Part005

theorem surrogateDiagonalTailChunk000Sub001Block031Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part005] using hcert

def TailChunk000Sub001Block031Part006SupportExplicit : Finset ℕ :=
  ([9554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part006 : ℚ :=
  (53717947807 : ℚ) / 40290152035123200

def SurrogateDiagonalTailChunk000Sub001Block031Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9554
    = surrogateDiagTailX0RatChunk000Sub001Block031Part006

theorem surrogateDiagonalTailChunk000Sub001Block031Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part006] using hcert

def TailChunk000Sub001Block031Part007SupportExplicit : Finset ℕ :=
  ([9557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part007 : ℚ :=
  (36786829525 : ℚ) / 4167463036751921952

def SurrogateDiagonalTailChunk000Sub001Block031Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9557
    = surrogateDiagTailX0RatChunk000Sub001Block031Part007

theorem surrogateDiagonalTailChunk000Sub001Block031Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part007] using hcert

def TailChunk000Sub001Block031Part008SupportExplicit : Finset ℕ :=
  ([9561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part008 : ℚ :=
  (634597770725 : ℚ) / 2061104121500940864

def SurrogateDiagonalTailChunk000Sub001Block031Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9561
    = surrogateDiagTailX0RatChunk000Sub001Block031Part008

theorem surrogateDiagonalTailChunk000Sub001Block031Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part008] using hcert

def TailChunk000Sub001Block031Part009SupportExplicit : Finset ℕ :=
  ([9562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part009 : ℚ :=
  (67948159825 : ℚ) / 38949048619753536

def SurrogateDiagonalTailChunk000Sub001Block031Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9562
    = surrogateDiagTailX0RatChunk000Sub001Block031Part009

theorem surrogateDiagonalTailChunk000Sub001Block031Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part009] using hcert

def TailChunk000Sub001Block031Part010SupportExplicit : Finset ℕ :=
  ([9563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part010 : ℚ :=
  (829103521 : ℚ) / 255899236685414400

def SurrogateDiagonalTailChunk000Sub001Block031Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9563
    = surrogateDiagTailX0RatChunk000Sub001Block031Part010

theorem surrogateDiagonalTailChunk000Sub001Block031Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part010] using hcert

def TailChunk000Sub001Block031Part011SupportExplicit : Finset ℕ :=
  ([9565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part011 : ℚ :=
  (458127157525 : ℚ) / 8554967735279812608

def SurrogateDiagonalTailChunk000Sub001Block031Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9565
    = surrogateDiagTailX0RatChunk000Sub001Block031Part011

theorem surrogateDiagonalTailChunk000Sub001Block031Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part011] using hcert

def TailChunk000Sub001Block031Part012SupportExplicit : Finset ℕ :=
  ([9566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part012 : ℚ :=
  (357454515625 : ℚ) / 326892649138346322

def SurrogateDiagonalTailChunk000Sub001Block031Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9566
    = surrogateDiagTailX0RatChunk000Sub001Block031Part012

theorem surrogateDiagonalTailChunk000Sub001Block031Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part012] using hcert

def TailChunk000Sub001Block031Part013SupportExplicit : Finset ℕ :=
  ([9569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part013 : ℚ :=
  (468083532325 : ℚ) / 11283261613435110528

def SurrogateDiagonalTailChunk000Sub001Block031Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9569
    = surrogateDiagTailX0RatChunk000Sub001Block031Part013

theorem surrogateDiagonalTailChunk000Sub001Block031Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part013] using hcert

def TailChunk000Sub001Block031Part014SupportExplicit : Finset ℕ :=
  ([9570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part014 : ℚ :=
  (483756053 : ℚ) / 44966687539200

def SurrogateDiagonalTailChunk000Sub001Block031Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9570
    = surrogateDiagTailX0RatChunk000Sub001Block031Part014

theorem surrogateDiagonalTailChunk000Sub001Block031Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part014] using hcert

def TailChunk000Sub001Block031Part015SupportExplicit : Finset ℕ :=
  ([9571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part015 : ℚ :=
  (162699033925 : ℚ) / 16347526565473026048

def SurrogateDiagonalTailChunk000Sub001Block031Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9571
    = surrogateDiagTailX0RatChunk000Sub001Block031Part015

theorem surrogateDiagonalTailChunk000Sub001Block031Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part015] using hcert

def TailChunk000Sub001Block031Part016SupportExplicit : Finset ℕ :=
  ([9573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part016 : ℚ :=
  (25447658069 : ℚ) / 82858977449793600

def SurrogateDiagonalTailChunk000Sub001Block031Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9573
    = surrogateDiagTailX0RatChunk000Sub001Block031Part016

theorem surrogateDiagonalTailChunk000Sub001Block031Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part016] using hcert

def TailChunk000Sub001Block031Part017SupportExplicit : Finset ℕ :=
  ([9574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part017 : ℚ :=
  (358052640625 : ℚ) / 327987765932309202

def SurrogateDiagonalTailChunk000Sub001Block031Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9574
    = surrogateDiagTailX0RatChunk000Sub001Block031Part017

theorem surrogateDiagonalTailChunk000Sub001Block031Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part017] using hcert

def TailChunk000Sub001Block031Part018SupportExplicit : Finset ℕ :=
  ([9577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part018 : ℚ :=
  (298334623 : ℚ) / 85299745561804800

def SurrogateDiagonalTailChunk000Sub001Block031Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9577
    = surrogateDiagTailX0RatChunk000Sub001Block031Part018

theorem surrogateDiagonalTailChunk000Sub001Block031Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part018] using hcert

def TailChunk000Sub001Block031Part019SupportExplicit : Finset ℕ :=
  ([9578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part019 : ℚ :=
  (358351890625 : ℚ) / 328536355009135392

def SurrogateDiagonalTailChunk000Sub001Block031Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9578
    = surrogateDiagTailX0RatChunk000Sub001Block031Part019

theorem surrogateDiagonalTailChunk000Sub001Block031Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part019] using hcert

def TailChunk000Sub001Block031Part020SupportExplicit : Finset ℕ :=
  ([9579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part020 : ℚ :=
  (925899359 : ℚ) / 2598356751436800

def SurrogateDiagonalTailChunk000Sub001Block031Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9579
    = surrogateDiagTailX0RatChunk000Sub001Block031Part020

theorem surrogateDiagonalTailChunk000Sub001Block031Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part020] using hcert

def TailChunk000Sub001Block031Part021SupportExplicit : Finset ℕ :=
  ([9581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part021 : ℚ :=
  (2940187403 : ℚ) / 65589802953523200

def SurrogateDiagonalTailChunk000Sub001Block031Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9581
    = surrogateDiagTailX0RatChunk000Sub001Block031Part021

theorem surrogateDiagonalTailChunk000Sub001Block031Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part021] using hcert

def TailChunk000Sub001Block031Part022SupportExplicit : Finset ℕ :=
  ([9582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part022 : ℚ :=
  (650225 : ℚ) / 176552635392

def SurrogateDiagonalTailChunk000Sub001Block031Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9582
    = surrogateDiagTailX0RatChunk000Sub001Block031Part022

theorem surrogateDiagonalTailChunk000Sub001Block031Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part022] using hcert

def TailChunk000Sub001Block031Part023SupportExplicit : Finset ℕ :=
  ([9586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part023 : ℚ :=
  (358950765625 : ℚ) / 329635597395251712

def SurrogateDiagonalTailChunk000Sub001Block031Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9586
    = surrogateDiagTailX0RatChunk000Sub001Block031Part023

theorem surrogateDiagonalTailChunk000Sub001Block031Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part023] using hcert

def TailChunk000Sub001Block031Part024SupportExplicit : Finset ℕ :=
  ([9587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block031Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block031Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9587
    = surrogateDiagTailX0RatChunk000Sub001Block031Part024

theorem surrogateDiagonalTailChunk000Sub001Block031Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block031Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block031Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block031Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block031Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block031Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block031Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block031HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block031Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block031Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block031Part000
    + surrogateDiagTailX0RatChunk000Sub001Block031Part001
    + surrogateDiagTailX0RatChunk000Sub001Block031Part002
    + surrogateDiagTailX0RatChunk000Sub001Block031Part003
    + surrogateDiagTailX0RatChunk000Sub001Block031Part004
    + surrogateDiagTailX0RatChunk000Sub001Block031Part005
    + surrogateDiagTailX0RatChunk000Sub001Block031Part006
    + surrogateDiagTailX0RatChunk000Sub001Block031Part007
    + surrogateDiagTailX0RatChunk000Sub001Block031Part008
    + surrogateDiagTailX0RatChunk000Sub001Block031Part009

def surrogateDiagonalTailChunk000Sub001Block031MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block031Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block031Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block031Part010
    + surrogateDiagTailX0RatChunk000Sub001Block031Part011
    + surrogateDiagTailX0RatChunk000Sub001Block031Part012
    + surrogateDiagTailX0RatChunk000Sub001Block031Part013
    + surrogateDiagTailX0RatChunk000Sub001Block031Part014
    + surrogateDiagTailX0RatChunk000Sub001Block031Part015
    + surrogateDiagTailX0RatChunk000Sub001Block031Part016
    + surrogateDiagTailX0RatChunk000Sub001Block031Part017
    + surrogateDiagTailX0RatChunk000Sub001Block031Part018
    + surrogateDiagTailX0RatChunk000Sub001Block031Part019

def surrogateDiagonalTailChunk000Sub001Block031TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block031Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block031Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block031Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block031Part020
    + surrogateDiagTailX0RatChunk000Sub001Block031Part021
    + surrogateDiagTailX0RatChunk000Sub001Block031Part022
    + surrogateDiagTailX0RatChunk000Sub001Block031Part023
    + surrogateDiagTailX0RatChunk000Sub001Block031Part024

def surrogateDiagonalTailChunk000Sub001Block031Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block031HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block031MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block031TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block031 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block031Part000
    + surrogateDiagTailX0RatChunk000Sub001Block031Part001
    + surrogateDiagTailX0RatChunk000Sub001Block031Part002
    + surrogateDiagTailX0RatChunk000Sub001Block031Part003
    + surrogateDiagTailX0RatChunk000Sub001Block031Part004
    + surrogateDiagTailX0RatChunk000Sub001Block031Part005
    + surrogateDiagTailX0RatChunk000Sub001Block031Part006
    + surrogateDiagTailX0RatChunk000Sub001Block031Part007
    + surrogateDiagTailX0RatChunk000Sub001Block031Part008
    + surrogateDiagTailX0RatChunk000Sub001Block031Part009
    + surrogateDiagTailX0RatChunk000Sub001Block031Part010
    + surrogateDiagTailX0RatChunk000Sub001Block031Part011
    + surrogateDiagTailX0RatChunk000Sub001Block031Part012
    + surrogateDiagTailX0RatChunk000Sub001Block031Part013
    + surrogateDiagTailX0RatChunk000Sub001Block031Part014
    + surrogateDiagTailX0RatChunk000Sub001Block031Part015
    + surrogateDiagTailX0RatChunk000Sub001Block031Part016
    + surrogateDiagTailX0RatChunk000Sub001Block031Part017
    + surrogateDiagTailX0RatChunk000Sub001Block031Part018
    + surrogateDiagTailX0RatChunk000Sub001Block031Part019
    + surrogateDiagTailX0RatChunk000Sub001Block031Part020
    + surrogateDiagTailX0RatChunk000Sub001Block031Part021
    + surrogateDiagTailX0RatChunk000Sub001Block031Part022
    + surrogateDiagTailX0RatChunk000Sub001Block031Part023
    + surrogateDiagTailX0RatChunk000Sub001Block031Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block031_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block031Head + surrogateDiagTailX0RatChunk000Sub001Block031Mid + surrogateDiagTailX0RatChunk000Sub001Block031Tail =
      surrogateDiagTailX0RatChunk000Sub001Block031 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block031Head surrogateDiagTailX0RatChunk000Sub001Block031Mid surrogateDiagTailX0RatChunk000Sub001Block031Tail surrogateDiagTailX0RatChunk000Sub001Block031
  ring

def SurrogateDiagonalTailChunk000Sub001Block031HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block031HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block031Head

def SurrogateDiagonalTailChunk000Sub001Block031MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block031MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block031Mid

def SurrogateDiagonalTailChunk000Sub001Block031TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block031TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block031Tail

theorem surrogateDiagonalTailChunk000Sub001Block031_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block031HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block031MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block031TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block031Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block031 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block031HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block031MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block031TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block031Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block031_eq_head_add_mid_add_tail

/-- Block 032 covers tail-support indices [5800,5825) and q from 9589 to 9627. -/

def TailChunk000Sub001Block032Part000SupportExplicit : Finset ℕ :=
  ([9589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part000 : ℚ :=
  (80680267525 : ℚ) / 18898873508959452288

def SurrogateDiagonalTailChunk000Sub001Block032Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9589
    = surrogateDiagTailX0RatChunk000Sub001Block032Part000

theorem surrogateDiagonalTailChunk000Sub001Block032Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part000] using hcert

def TailChunk000Sub001Block032Part001SupportExplicit : Finset ℕ :=
  ([9590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part001 : ℚ :=
  (55463388125 : ℚ) / 15767213709459456

def SurrogateDiagonalTailChunk000Sub001Block032Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9590
    = surrogateDiagTailX0RatChunk000Sub001Block032Part001

theorem surrogateDiagonalTailChunk000Sub001Block032Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part001] using hcert

def TailChunk000Sub001Block032Part002SupportExplicit : Finset ℕ :=
  ([9591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part002 : ℚ :=
  (74917699625 : ℚ) / 377669054492116992

def SurrogateDiagonalTailChunk000Sub001Block032Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9591
    = surrogateDiagTailX0RatChunk000Sub001Block032Part002

theorem surrogateDiagonalTailChunk000Sub001Block032Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part002] using hcert

def TailChunk000Sub001Block032Part003SupportExplicit : Finset ℕ :=
  ([9593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part003 : ℚ :=
  (2909964277 : ℚ) / 767697710056243200

def SurrogateDiagonalTailChunk000Sub001Block032Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9593
    = surrogateDiagTailX0RatChunk000Sub001Block032Part003

theorem surrogateDiagonalTailChunk000Sub001Block032Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part003] using hcert

def TailChunk000Sub001Block032Part004SupportExplicit : Finset ℕ :=
  ([9595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part004 : ℚ :=
  (1505207033 : ℚ) / 13439615385600000

def SurrogateDiagonalTailChunk000Sub001Block032Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9595
    = surrogateDiagTailX0RatChunk000Sub001Block032Part004

theorem surrogateDiagonalTailChunk000Sub001Block032Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part004] using hcert

def TailChunk000Sub001Block032Part005SupportExplicit : Finset ℕ :=
  ([9597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part005 : ℚ :=
  (378748836725 : ℚ) / 1120937034666737664

def SurrogateDiagonalTailChunk000Sub001Block032Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9597
    = surrogateDiagTailX0RatChunk000Sub001Block032Part005

theorem surrogateDiagonalTailChunk000Sub001Block032Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part005] using hcert

def TailChunk000Sub001Block032Part006SupportExplicit : Finset ℕ :=
  ([9598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part006 : ℚ :=
  (359850015625 : ℚ) / 331289630181110802

def SurrogateDiagonalTailChunk000Sub001Block032Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9598
    = surrogateDiagTailX0RatChunk000Sub001Block032Part006

theorem surrogateDiagonalTailChunk000Sub001Block032Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part006] using hcert

def TailChunk000Sub001Block032Part007SupportExplicit : Finset ℕ :=
  ([9599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part007 : ℚ :=
  (4421530429 : ℚ) / 729079244867635200

def SurrogateDiagonalTailChunk000Sub001Block032Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9599
    = surrogateDiagTailX0RatChunk000Sub001Block032Part007

theorem surrogateDiagonalTailChunk000Sub001Block032Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part007] using hcert

def TailChunk000Sub001Block032Part008SupportExplicit : Finset ℕ :=
  ([9601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block032Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9601
    = surrogateDiagTailX0RatChunk000Sub001Block032Part008

theorem surrogateDiagonalTailChunk000Sub001Block032Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part008] using hcert

def TailChunk000Sub001Block032Part009SupportExplicit : Finset ℕ :=
  ([9602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part009 : ℚ :=
  (23049601 : ℚ) / 21237910732800

def SurrogateDiagonalTailChunk000Sub001Block032Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9602
    = surrogateDiagTailX0RatChunk000Sub001Block032Part009

theorem surrogateDiagonalTailChunk000Sub001Block032Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part009] using hcert

def TailChunk000Sub001Block032Part010SupportExplicit : Finset ℕ :=
  ([9605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part010 : ℚ :=
  (186961538775 : ℚ) / 2200379503144861696

def SurrogateDiagonalTailChunk000Sub001Block032Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9605
    = surrogateDiagTailX0RatChunk000Sub001Block032Part010

theorem surrogateDiagonalTailChunk000Sub001Block032Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part010] using hcert

def TailChunk000Sub001Block032Part011SupportExplicit : Finset ℕ :=
  ([9606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part011 : ℚ :=
  (3842499 : ℚ) / 1048576000000

def SurrogateDiagonalTailChunk000Sub001Block032Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9606
    = surrogateDiagTailX0RatChunk000Sub001Block032Part011

theorem surrogateDiagonalTailChunk000Sub001Block032Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part011] using hcert

def TailChunk000Sub001Block032Part012SupportExplicit : Finset ℕ :=
  ([9607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part012 : ℚ :=
  (120874101425 : ℚ) / 7690371054854759424

def SurrogateDiagonalTailChunk000Sub001Block032Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9607
    = surrogateDiagTailX0RatChunk000Sub001Block032Part012

theorem surrogateDiagonalTailChunk000Sub001Block032Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part012] using hcert

def TailChunk000Sub001Block032Part013SupportExplicit : Finset ℕ :=
  ([9609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part013 : ℚ :=
  (320712678725 : ℚ) / 2102820277207769664

def SurrogateDiagonalTailChunk000Sub001Block032Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9609
    = surrogateDiagTailX0RatChunk000Sub001Block032Part013

theorem surrogateDiagonalTailChunk000Sub001Block032Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part013] using hcert

def TailChunk000Sub001Block032Part014SupportExplicit : Finset ℕ :=
  ([9611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part014 : ℚ :=
  (402132025 : ℚ) / 13019062765814784

def SurrogateDiagonalTailChunk000Sub001Block032Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9611
    = surrogateDiagTailX0RatChunk000Sub001Block032Part014

theorem surrogateDiagonalTailChunk000Sub001Block032Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part014] using hcert

def TailChunk000Sub001Block032Part015SupportExplicit : Finset ℕ :=
  ([9613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block032Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9613
    = surrogateDiagTailX0RatChunk000Sub001Block032Part015

theorem surrogateDiagonalTailChunk000Sub001Block032Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part015] using hcert

def TailChunk000Sub001Block032Part016SupportExplicit : Finset ℕ :=
  ([9614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part016 : ℚ :=
  (3985084897 : ℚ) / 2049681342297600

def SurrogateDiagonalTailChunk000Sub001Block032Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9614
    = surrogateDiagTailX0RatChunk000Sub001Block032Part016

theorem surrogateDiagonalTailChunk000Sub001Block032Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part016] using hcert

def TailChunk000Sub001Block032Part017SupportExplicit : Finset ℕ :=
  ([9615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part017 : ℚ :=
  (28774427929 : ℚ) / 68733220631347200

def SurrogateDiagonalTailChunk000Sub001Block032Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9615
    = surrogateDiagTailX0RatChunk000Sub001Block032Part017

theorem surrogateDiagonalTailChunk000Sub001Block032Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part017] using hcert

def TailChunk000Sub001Block032Part018SupportExplicit : Finset ℕ :=
  ([9617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part018 : ℚ :=
  (5585833088725 : ℚ) / 19489418944752716928

def SurrogateDiagonalTailChunk000Sub001Block032Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9617
    = surrogateDiagTailX0RatChunk000Sub001Block032Part018

theorem surrogateDiagonalTailChunk000Sub001Block032Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part018] using hcert

def TailChunk000Sub001Block032Part019SupportExplicit : Finset ℕ :=
  ([9618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part019 : ℚ :=
  (47795992475 : ℚ) / 5189523308642304

def SurrogateDiagonalTailChunk000Sub001Block032Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9618
    = surrogateDiagTailX0RatChunk000Sub001Block032Part019

theorem surrogateDiagonalTailChunk000Sub001Block032Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part019] using hcert

def TailChunk000Sub001Block032Part020SupportExplicit : Finset ℕ :=
  ([9619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part020 : ℚ :=
  (1445705640625 : ℚ) / 5349410902680496722

def SurrogateDiagonalTailChunk000Sub001Block032Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9619
    = surrogateDiagTailX0RatChunk000Sub001Block032Part020

theorem surrogateDiagonalTailChunk000Sub001Block032Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part020] using hcert

def TailChunk000Sub001Block032Part021SupportExplicit : Finset ℕ :=
  ([9622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part021 : ℚ :=
  (1362130766875 : ℚ) / 1036342294825402368

def SurrogateDiagonalTailChunk000Sub001Block032Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9622
    = surrogateDiagTailX0RatChunk000Sub001Block032Part021

theorem surrogateDiagonalTailChunk000Sub001Block032Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part021] using hcert

def TailChunk000Sub001Block032Part022SupportExplicit : Finset ℕ :=
  ([9623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part022 : ℚ :=
  (1446908265625 : ℚ) / 5358315454899629682

def SurrogateDiagonalTailChunk000Sub001Block032Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9623
    = surrogateDiagTailX0RatChunk000Sub001Block032Part022

theorem surrogateDiagonalTailChunk000Sub001Block032Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part022] using hcert

def TailChunk000Sub001Block032Part023SupportExplicit : Finset ℕ :=
  ([9626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part023 : ℚ :=
  (361952640625 : ℚ) / 335173243593429792

def SurrogateDiagonalTailChunk000Sub001Block032Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9626
    = surrogateDiagTailX0RatChunk000Sub001Block032Part023

theorem surrogateDiagonalTailChunk000Sub001Block032Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part023] using hcert

def TailChunk000Sub001Block032Part024SupportExplicit : Finset ℕ :=
  ([9627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block032Part024 : ℚ :=
  (1608579710225 : ℚ) / 2118625934812790784

def SurrogateDiagonalTailChunk000Sub001Block032Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9627
    = surrogateDiagTailX0RatChunk000Sub001Block032Part024

theorem surrogateDiagonalTailChunk000Sub001Block032Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block032Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block032Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block032Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block032Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block032Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block032Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block032HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block032Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block032Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block032Part000
    + surrogateDiagTailX0RatChunk000Sub001Block032Part001
    + surrogateDiagTailX0RatChunk000Sub001Block032Part002
    + surrogateDiagTailX0RatChunk000Sub001Block032Part003
    + surrogateDiagTailX0RatChunk000Sub001Block032Part004
    + surrogateDiagTailX0RatChunk000Sub001Block032Part005
    + surrogateDiagTailX0RatChunk000Sub001Block032Part006
    + surrogateDiagTailX0RatChunk000Sub001Block032Part007
    + surrogateDiagTailX0RatChunk000Sub001Block032Part008
    + surrogateDiagTailX0RatChunk000Sub001Block032Part009

def surrogateDiagonalTailChunk000Sub001Block032MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block032Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block032Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block032Part010
    + surrogateDiagTailX0RatChunk000Sub001Block032Part011
    + surrogateDiagTailX0RatChunk000Sub001Block032Part012
    + surrogateDiagTailX0RatChunk000Sub001Block032Part013
    + surrogateDiagTailX0RatChunk000Sub001Block032Part014
    + surrogateDiagTailX0RatChunk000Sub001Block032Part015
    + surrogateDiagTailX0RatChunk000Sub001Block032Part016
    + surrogateDiagTailX0RatChunk000Sub001Block032Part017
    + surrogateDiagTailX0RatChunk000Sub001Block032Part018
    + surrogateDiagTailX0RatChunk000Sub001Block032Part019

def surrogateDiagonalTailChunk000Sub001Block032TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block032Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block032Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block032Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block032Part020
    + surrogateDiagTailX0RatChunk000Sub001Block032Part021
    + surrogateDiagTailX0RatChunk000Sub001Block032Part022
    + surrogateDiagTailX0RatChunk000Sub001Block032Part023
    + surrogateDiagTailX0RatChunk000Sub001Block032Part024

def surrogateDiagonalTailChunk000Sub001Block032Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block032HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block032MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block032TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block032 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block032Part000
    + surrogateDiagTailX0RatChunk000Sub001Block032Part001
    + surrogateDiagTailX0RatChunk000Sub001Block032Part002
    + surrogateDiagTailX0RatChunk000Sub001Block032Part003
    + surrogateDiagTailX0RatChunk000Sub001Block032Part004
    + surrogateDiagTailX0RatChunk000Sub001Block032Part005
    + surrogateDiagTailX0RatChunk000Sub001Block032Part006
    + surrogateDiagTailX0RatChunk000Sub001Block032Part007
    + surrogateDiagTailX0RatChunk000Sub001Block032Part008
    + surrogateDiagTailX0RatChunk000Sub001Block032Part009
    + surrogateDiagTailX0RatChunk000Sub001Block032Part010
    + surrogateDiagTailX0RatChunk000Sub001Block032Part011
    + surrogateDiagTailX0RatChunk000Sub001Block032Part012
    + surrogateDiagTailX0RatChunk000Sub001Block032Part013
    + surrogateDiagTailX0RatChunk000Sub001Block032Part014
    + surrogateDiagTailX0RatChunk000Sub001Block032Part015
    + surrogateDiagTailX0RatChunk000Sub001Block032Part016
    + surrogateDiagTailX0RatChunk000Sub001Block032Part017
    + surrogateDiagTailX0RatChunk000Sub001Block032Part018
    + surrogateDiagTailX0RatChunk000Sub001Block032Part019
    + surrogateDiagTailX0RatChunk000Sub001Block032Part020
    + surrogateDiagTailX0RatChunk000Sub001Block032Part021
    + surrogateDiagTailX0RatChunk000Sub001Block032Part022
    + surrogateDiagTailX0RatChunk000Sub001Block032Part023
    + surrogateDiagTailX0RatChunk000Sub001Block032Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block032_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block032Head + surrogateDiagTailX0RatChunk000Sub001Block032Mid + surrogateDiagTailX0RatChunk000Sub001Block032Tail =
      surrogateDiagTailX0RatChunk000Sub001Block032 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block032Head surrogateDiagTailX0RatChunk000Sub001Block032Mid surrogateDiagTailX0RatChunk000Sub001Block032Tail surrogateDiagTailX0RatChunk000Sub001Block032
  ring

def SurrogateDiagonalTailChunk000Sub001Block032HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block032HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block032Head

def SurrogateDiagonalTailChunk000Sub001Block032MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block032MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block032Mid

def SurrogateDiagonalTailChunk000Sub001Block032TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block032TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block032Tail

theorem surrogateDiagonalTailChunk000Sub001Block032_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block032HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block032MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block032TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block032Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block032 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block032HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block032MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block032TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block032Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block032_eq_head_add_mid_add_tail

/-- Block 033 covers tail-support indices [5825,5850) and q from 9629 to 9670. -/

def TailChunk000Sub001Block033Part000SupportExplicit : Finset ℕ :=
  ([9629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part000 : ℚ :=
  (1448713140625 : ℚ) / 5371693121431686432

def SurrogateDiagonalTailChunk000Sub001Block033Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9629
    = surrogateDiagTailX0RatChunk000Sub001Block033Part000

theorem surrogateDiagonalTailChunk000Sub001Block033Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part000] using hcert

def TailChunk000Sub001Block033Part001SupportExplicit : Finset ℕ :=
  ([9631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part001 : ℚ :=
  (2318904025 : ℚ) / 8601852648134322

def SurrogateDiagonalTailChunk000Sub001Block033Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9631
    = surrogateDiagTailX0RatChunk000Sub001Block033Part001

theorem surrogateDiagonalTailChunk000Sub001Block033Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part001] using hcert

def TailChunk000Sub001Block033Part002SupportExplicit : Finset ℕ :=
  ([9634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part002 : ℚ :=
  (362554515625 : ℚ) / 336289091962478592

def SurrogateDiagonalTailChunk000Sub001Block033Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9634
    = surrogateDiagTailX0RatChunk000Sub001Block033Part002

theorem surrogateDiagonalTailChunk000Sub001Block033Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part002] using hcert

def TailChunk000Sub001Block033Part003SupportExplicit : Finset ℕ :=
  ([9635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part003 : ℚ :=
  (10427401797 : ℚ) / 19566216221818880

def SurrogateDiagonalTailChunk000Sub001Block033Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9635
    = surrogateDiagTailX0RatChunk000Sub001Block033Part003

theorem surrogateDiagonalTailChunk000Sub001Block033Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part003] using hcert

def TailChunk000Sub001Block033Part004SupportExplicit : Finset ℕ :=
  ([9637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part004 : ℚ :=
  (676646480525 : ℚ) / 2235284065883772816

def SurrogateDiagonalTailChunk000Sub001Block033Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9637
    = surrogateDiagTailX0RatChunk000Sub001Block033Part004

theorem surrogateDiagonalTailChunk000Sub001Block033Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part004] using hcert

def TailChunk000Sub001Block033Part005SupportExplicit : Finset ℕ :=
  ([9638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part005 : ℚ :=
  (58077611 : ℚ) / 49363278681600

def SurrogateDiagonalTailChunk000Sub001Block033Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9638
    = surrogateDiagTailX0RatChunk000Sub001Block033Part005

theorem surrogateDiagonalTailChunk000Sub001Block033Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part005] using hcert

def TailChunk000Sub001Block033Part006SupportExplicit : Finset ℕ :=
  ([9641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part006 : ℚ :=
  (4404678497 : ℚ) / 14964032408040000

def SurrogateDiagonalTailChunk000Sub001Block033Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9641
    = surrogateDiagTailX0RatChunk000Sub001Block033Part006

theorem surrogateDiagonalTailChunk000Sub001Block033Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part006] using hcert

def TailChunk000Sub001Block033Part007SupportExplicit : Finset ℕ :=
  ([9642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part007 : ℚ :=
  (96783825 : ℚ) / 26609833374784

def SurrogateDiagonalTailChunk000Sub001Block033Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9642
    = surrogateDiagTailX0RatChunk000Sub001Block033Part007

theorem surrogateDiagonalTailChunk000Sub001Block033Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part007] using hcert

def TailChunk000Sub001Block033Part008SupportExplicit : Finset ℕ :=
  ([9643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part008 : ℚ :=
  (1452928890625 : ℚ) / 5403005083396501362

def SurrogateDiagonalTailChunk000Sub001Block033Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9643
    = surrogateDiagTailX0RatChunk000Sub001Block033Part008

theorem surrogateDiagonalTailChunk000Sub001Block033Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part008] using hcert

def TailChunk000Sub001Block033Part009SupportExplicit : Finset ℕ :=
  ([9645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part009 : ℚ :=
  (1147680739925 : ℚ) / 869955270290325504

def SurrogateDiagonalTailChunk000Sub001Block033Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9645
    = surrogateDiagTailX0RatChunk000Sub001Block033Part009

theorem surrogateDiagonalTailChunk000Sub001Block033Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part009] using hcert

def TailChunk000Sub001Block033Part010SupportExplicit : Finset ℕ :=
  ([9646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part010 : ℚ :=
  (126245999375 : ℚ) / 54591837159555072

def SurrogateDiagonalTailChunk000Sub001Block033Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9646
    = surrogateDiagTailX0RatChunk000Sub001Block033Part010

theorem surrogateDiagonalTailChunk000Sub001Block033Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part010] using hcert

def TailChunk000Sub001Block033Part011SupportExplicit : Finset ℕ :=
  ([9647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part011 : ℚ :=
  (199668720241 : ℚ) / 588983698561075200

def SurrogateDiagonalTailChunk000Sub001Block033Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9647
    = surrogateDiagTailX0RatChunk000Sub001Block033Part011

theorem surrogateDiagonalTailChunk000Sub001Block033Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part011] using hcert

def TailChunk000Sub001Block033Part012SupportExplicit : Finset ℕ :=
  ([9649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part012 : ℚ :=
  (1454737515625 : ℚ) / 5416466316573745152

def SurrogateDiagonalTailChunk000Sub001Block033Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9649
    = surrogateDiagTailX0RatChunk000Sub001Block033Part012

theorem surrogateDiagonalTailChunk000Sub001Block033Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part012] using hcert

def TailChunk000Sub001Block033Part013SupportExplicit : Finset ℕ :=
  ([9651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part013 : ℚ :=
  (2586288678325 : ℚ) / 4279677089638514688

def SurrogateDiagonalTailChunk000Sub001Block033Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9651
    = surrogateDiagTailX0RatChunk000Sub001Block033Part013

theorem surrogateDiagonalTailChunk000Sub001Block033Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part013] using hcert

def TailChunk000Sub001Block033Part014SupportExplicit : Finset ℕ :=
  ([9654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part014 : ℚ :=
  (32341625 : ℚ) / 8914211094528

def SurrogateDiagonalTailChunk000Sub001Block033Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9654
    = surrogateDiagTailX0RatChunk000Sub001Block033Part014

theorem surrogateDiagonalTailChunk000Sub001Block033Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part014] using hcert

def TailChunk000Sub001Block033Part015SupportExplicit : Finset ℕ :=
  ([9655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part015 : ℚ :=
  (55898862339 : ℚ) / 118422655880550400

def SurrogateDiagonalTailChunk000Sub001Block033Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9655
    = surrogateDiagTailX0RatChunk000Sub001Block033Part015

theorem surrogateDiagonalTailChunk000Sub001Block033Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part015] using hcert

def TailChunk000Sub001Block033Part016SupportExplicit : Finset ℕ :=
  ([9658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part016 : ℚ :=
  (10674424337 : ℚ) / 7362296232013440

def SurrogateDiagonalTailChunk000Sub001Block033Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9658
    = surrogateDiagTailX0RatChunk000Sub001Block033Part016

theorem surrogateDiagonalTailChunk000Sub001Block033Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part016] using hcert

def TailChunk000Sub001Block033Part017SupportExplicit : Finset ℕ :=
  ([9659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part017 : ℚ :=
  (5166066704875 : ℚ) / 15716920781701859328

def SurrogateDiagonalTailChunk000Sub001Block033Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9659
    = surrogateDiagTailX0RatChunk000Sub001Block033Part017

theorem surrogateDiagonalTailChunk000Sub001Block033Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part017] using hcert

def TailChunk000Sub001Block033Part018SupportExplicit : Finset ℕ :=
  ([9661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part018 : ℚ :=
  (2333373025 : ℚ) / 8709542763600672

def SurrogateDiagonalTailChunk000Sub001Block033Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9661
    = surrogateDiagTailX0RatChunk000Sub001Block033Part018

theorem surrogateDiagonalTailChunk000Sub001Block033Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part018] using hcert

def TailChunk000Sub001Block033Part019SupportExplicit : Finset ℕ :=
  ([9662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part019 : ℚ :=
  (583464025 : ℚ) / 544346422725042

def SurrogateDiagonalTailChunk000Sub001Block033Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9662
    = surrogateDiagTailX0RatChunk000Sub001Block033Part019

theorem surrogateDiagonalTailChunk000Sub001Block033Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part019] using hcert

def TailChunk000Sub001Block033Part020SupportExplicit : Finset ℕ :=
  ([9663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part020 : ℚ :=
  (103708987117 : ℚ) / 172040350885939200

def SurrogateDiagonalTailChunk000Sub001Block033Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9663
    = surrogateDiagTailX0RatChunk000Sub001Block033Part020

theorem surrogateDiagonalTailChunk000Sub001Block033Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part020] using hcert

def TailChunk000Sub001Block033Part021SupportExplicit : Finset ℕ :=
  ([9665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part021 : ℚ :=
  (600157932475 : ℚ) / 1274081684275298304

def SurrogateDiagonalTailChunk000Sub001Block033Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9665
    = surrogateDiagTailX0RatChunk000Sub001Block033Part021

theorem surrogateDiagonalTailChunk000Sub001Block033Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part021] using hcert

def TailChunk000Sub001Block033Part022SupportExplicit : Finset ℕ :=
  ([9667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part022 : ℚ :=
  (45253451803 : ℚ) / 117529856535052800

def SurrogateDiagonalTailChunk000Sub001Block033Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9667
    = surrogateDiagTailX0RatChunk000Sub001Block033Part022

theorem surrogateDiagonalTailChunk000Sub001Block033Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part022] using hcert

def TailChunk000Sub001Block033Part023SupportExplicit : Finset ℕ :=
  ([9669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part023 : ℚ :=
  (9212092219 : ℚ) / 11634245897502720

def SurrogateDiagonalTailChunk000Sub001Block033Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9669
    = surrogateDiagTailX0RatChunk000Sub001Block033Part023

theorem surrogateDiagonalTailChunk000Sub001Block033Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part023] using hcert

def TailChunk000Sub001Block033Part024SupportExplicit : Finset ℕ :=
  ([9670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block033Part024 : ℚ :=
  (583964144375 : ℚ) / 278705368435221504

def SurrogateDiagonalTailChunk000Sub001Block033Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9670
    = surrogateDiagTailX0RatChunk000Sub001Block033Part024

theorem surrogateDiagonalTailChunk000Sub001Block033Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block033Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block033Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block033Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block033Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block033Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block033Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block033HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block033Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block033Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block033Part000
    + surrogateDiagTailX0RatChunk000Sub001Block033Part001
    + surrogateDiagTailX0RatChunk000Sub001Block033Part002
    + surrogateDiagTailX0RatChunk000Sub001Block033Part003
    + surrogateDiagTailX0RatChunk000Sub001Block033Part004
    + surrogateDiagTailX0RatChunk000Sub001Block033Part005
    + surrogateDiagTailX0RatChunk000Sub001Block033Part006
    + surrogateDiagTailX0RatChunk000Sub001Block033Part007
    + surrogateDiagTailX0RatChunk000Sub001Block033Part008
    + surrogateDiagTailX0RatChunk000Sub001Block033Part009

def surrogateDiagonalTailChunk000Sub001Block033MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block033Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block033Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block033Part010
    + surrogateDiagTailX0RatChunk000Sub001Block033Part011
    + surrogateDiagTailX0RatChunk000Sub001Block033Part012
    + surrogateDiagTailX0RatChunk000Sub001Block033Part013
    + surrogateDiagTailX0RatChunk000Sub001Block033Part014
    + surrogateDiagTailX0RatChunk000Sub001Block033Part015
    + surrogateDiagTailX0RatChunk000Sub001Block033Part016
    + surrogateDiagTailX0RatChunk000Sub001Block033Part017
    + surrogateDiagTailX0RatChunk000Sub001Block033Part018
    + surrogateDiagTailX0RatChunk000Sub001Block033Part019

def surrogateDiagonalTailChunk000Sub001Block033TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block033Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block033Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block033Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block033Part020
    + surrogateDiagTailX0RatChunk000Sub001Block033Part021
    + surrogateDiagTailX0RatChunk000Sub001Block033Part022
    + surrogateDiagTailX0RatChunk000Sub001Block033Part023
    + surrogateDiagTailX0RatChunk000Sub001Block033Part024

def surrogateDiagonalTailChunk000Sub001Block033Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block033HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block033MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block033TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block033 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block033Part000
    + surrogateDiagTailX0RatChunk000Sub001Block033Part001
    + surrogateDiagTailX0RatChunk000Sub001Block033Part002
    + surrogateDiagTailX0RatChunk000Sub001Block033Part003
    + surrogateDiagTailX0RatChunk000Sub001Block033Part004
    + surrogateDiagTailX0RatChunk000Sub001Block033Part005
    + surrogateDiagTailX0RatChunk000Sub001Block033Part006
    + surrogateDiagTailX0RatChunk000Sub001Block033Part007
    + surrogateDiagTailX0RatChunk000Sub001Block033Part008
    + surrogateDiagTailX0RatChunk000Sub001Block033Part009
    + surrogateDiagTailX0RatChunk000Sub001Block033Part010
    + surrogateDiagTailX0RatChunk000Sub001Block033Part011
    + surrogateDiagTailX0RatChunk000Sub001Block033Part012
    + surrogateDiagTailX0RatChunk000Sub001Block033Part013
    + surrogateDiagTailX0RatChunk000Sub001Block033Part014
    + surrogateDiagTailX0RatChunk000Sub001Block033Part015
    + surrogateDiagTailX0RatChunk000Sub001Block033Part016
    + surrogateDiagTailX0RatChunk000Sub001Block033Part017
    + surrogateDiagTailX0RatChunk000Sub001Block033Part018
    + surrogateDiagTailX0RatChunk000Sub001Block033Part019
    + surrogateDiagTailX0RatChunk000Sub001Block033Part020
    + surrogateDiagTailX0RatChunk000Sub001Block033Part021
    + surrogateDiagTailX0RatChunk000Sub001Block033Part022
    + surrogateDiagTailX0RatChunk000Sub001Block033Part023
    + surrogateDiagTailX0RatChunk000Sub001Block033Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block033_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block033Head + surrogateDiagTailX0RatChunk000Sub001Block033Mid + surrogateDiagTailX0RatChunk000Sub001Block033Tail =
      surrogateDiagTailX0RatChunk000Sub001Block033 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block033Head surrogateDiagTailX0RatChunk000Sub001Block033Mid surrogateDiagTailX0RatChunk000Sub001Block033Tail surrogateDiagTailX0RatChunk000Sub001Block033
  ring

def SurrogateDiagonalTailChunk000Sub001Block033HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block033HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block033Head

def SurrogateDiagonalTailChunk000Sub001Block033MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block033MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block033Mid

def SurrogateDiagonalTailChunk000Sub001Block033TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block033TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block033Tail

theorem surrogateDiagonalTailChunk000Sub001Block033_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block033HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block033MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block033TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block033Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block033 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block033HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block033MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block033TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block033Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block033_eq_head_add_mid_add_tail

/-- Block 034 covers tail-support indices [5850,5875) and q from 9671 to 9707. -/

def TailChunk000Sub001Block034Part000SupportExplicit : Finset ℕ :=
  ([9671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part000 : ℚ :=
  (1344342649075 : ℚ) / 4370304899581235712

def SurrogateDiagonalTailChunk000Sub001Block034Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9671
    = surrogateDiagTailX0RatChunk000Sub001Block034Part000

theorem surrogateDiagonalTailChunk000Sub001Block034Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part000] using hcert

def TailChunk000Sub001Block034Part001SupportExplicit : Finset ℕ :=
  ([9673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part001 : ℚ :=
  (5329083992725 : ℚ) / 17056901140492320768

def SurrogateDiagonalTailChunk000Sub001Block034Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9673
    = surrogateDiagTailX0RatChunk000Sub001Block034Part001

theorem surrogateDiagonalTailChunk000Sub001Block034Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part001] using hcert

def TailChunk000Sub001Block034Part002SupportExplicit : Finset ℕ :=
  ([9674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part002 : ℚ :=
  (185464391 : ℚ) / 108823941236160

def SurrogateDiagonalTailChunk000Sub001Block034Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9674
    = surrogateDiagTailX0RatChunk000Sub001Block034Part002

theorem surrogateDiagonalTailChunk000Sub001Block034Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part002] using hcert

def TailChunk000Sub001Block034Part003SupportExplicit : Finset ℕ :=
  ([9677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part003 : ℚ :=
  (1463192640625 : ℚ) / 5479618286391735072

def SurrogateDiagonalTailChunk000Sub001Block034Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9677
    = surrogateDiagTailX0RatChunk000Sub001Block034Part003

theorem surrogateDiagonalTailChunk000Sub001Block034Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part003] using hcert

def TailChunk000Sub001Block034Part004SupportExplicit : Finset ℕ :=
  ([9678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part004 : ℚ :=
  (1137682662925 : ℚ) / 270151256244799488

def SurrogateDiagonalTailChunk000Sub001Block034Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9678
    = surrogateDiagTailX0RatChunk000Sub001Block034Part004

theorem surrogateDiagonalTailChunk000Sub001Block034Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part004] using hcert

def TailChunk000Sub001Block034Part005SupportExplicit : Finset ℕ :=
  ([9679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part005 : ℚ :=
  (1463797515625 : ℚ) / 5484150173494966482

def SurrogateDiagonalTailChunk000Sub001Block034Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9679
    = surrogateDiagTailX0RatChunk000Sub001Block034Part005

theorem surrogateDiagonalTailChunk000Sub001Block034Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part005] using hcert

def TailChunk000Sub001Block034Part006SupportExplicit : Finset ℕ :=
  ([9681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part006 : ℚ :=
  (1942752091 : ℚ) / 1719686972620800

def SurrogateDiagonalTailChunk000Sub001Block034Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9681
    = surrogateDiagTailX0RatChunk000Sub001Block034Part006

theorem surrogateDiagonalTailChunk000Sub001Block034Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part006] using hcert

def TailChunk000Sub001Block034Part007SupportExplicit : Finset ℕ :=
  ([9682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part007 : ℚ :=
  (19735611775 : ℚ) / 16831637770343184

def SurrogateDiagonalTailChunk000Sub001Block034Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9682
    = surrogateDiagTailX0RatChunk000Sub001Block034Part007

theorem surrogateDiagonalTailChunk000Sub001Block034Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part007] using hcert

def TailChunk000Sub001Block034Part008SupportExplicit : Finset ℕ :=
  ([9683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part008 : ℚ :=
  (12144513151 : ℚ) / 40504402492646400

def SurrogateDiagonalTailChunk000Sub001Block034Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9683
    = surrogateDiagTailX0RatChunk000Sub001Block034Part008

theorem surrogateDiagonalTailChunk000Sub001Block034Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part008] using hcert

def TailChunk000Sub001Block034Part009SupportExplicit : Finset ℕ :=
  ([9685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part009 : ℚ :=
  (146368284625 : ℚ) / 265355093445967872

def SurrogateDiagonalTailChunk000Sub001Block034Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9685
    = surrogateDiagTailX0RatChunk000Sub001Block034Part009

theorem surrogateDiagonalTailChunk000Sub001Block034Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part009] using hcert

def TailChunk000Sub001Block034Part010SupportExplicit : Finset ℕ :=
  ([9686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part010 : ℚ :=
  (21991054525 : ℚ) / 18235234913079072

def SurrogateDiagonalTailChunk000Sub001Block034Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9686
    = surrogateDiagTailX0RatChunk000Sub001Block034Part010

theorem surrogateDiagonalTailChunk000Sub001Block034Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part010] using hcert

def TailChunk000Sub001Block034Part011SupportExplicit : Finset ℕ :=
  ([9687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part011 : ℚ :=
  (1628695427975 : ℚ) / 2171955635471361024

def SurrogateDiagonalTailChunk000Sub001Block034Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9687
    = surrogateDiagTailX0RatChunk000Sub001Block034Part011

theorem surrogateDiagonalTailChunk000Sub001Block034Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part011] using hcert

def TailChunk000Sub001Block034Part012SupportExplicit : Finset ℕ :=
  ([9689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part012 : ℚ :=
  (1466823765625 : ℚ) / 5506851789336801792

def SurrogateDiagonalTailChunk000Sub001Block034Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9689
    = surrogateDiagTailX0RatChunk000Sub001Block034Part012

theorem surrogateDiagonalTailChunk000Sub001Block034Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part012] using hcert

def TailChunk000Sub001Block034Part013SupportExplicit : Finset ℕ :=
  ([9690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part013 : ℚ :=
  (30025676825 : ℚ) / 2935928779702272

def SurrogateDiagonalTailChunk000Sub001Block034Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9690
    = surrogateDiagTailX0RatChunk000Sub001Block034Part013

theorem surrogateDiagonalTailChunk000Sub001Block034Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part013] using hcert

def TailChunk000Sub001Block034Part014SupportExplicit : Finset ℕ :=
  ([9691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part014 : ℚ :=
  (6781194969 : ℚ) / 19993843302400000

def SurrogateDiagonalTailChunk000Sub001Block034Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9691
    = surrogateDiagTailX0RatChunk000Sub001Block034Part014

theorem surrogateDiagonalTailChunk000Sub001Block034Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part014] using hcert

def TailChunk000Sub001Block034Part015SupportExplicit : Finset ℕ :=
  ([9694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part015 : ℚ :=
  (7097103473 : ℚ) / 5997638359814400

def SurrogateDiagonalTailChunk000Sub001Block034Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9694
    = surrogateDiagTailX0RatChunk000Sub001Block034Part015

theorem surrogateDiagonalTailChunk000Sub001Block034Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part015] using hcert

def TailChunk000Sub001Block034Part016SupportExplicit : Finset ℕ :=
  ([9695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part016 : ℚ :=
  (826804821625 : ℚ) / 1203505730918940672

def SurrogateDiagonalTailChunk000Sub001Block034Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9695
    = surrogateDiagTailX0RatChunk000Sub001Block034Part016

theorem surrogateDiagonalTailChunk000Sub001Block034Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part016] using hcert

def TailChunk000Sub001Block034Part017SupportExplicit : Finset ℕ :=
  ([9697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part017 : ℚ :=
  (1469247015625 : ℚ) / 5525063768143429632

def SurrogateDiagonalTailChunk000Sub001Block034Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9697
    = surrogateDiagTailX0RatChunk000Sub001Block034Part017

theorem surrogateDiagonalTailChunk000Sub001Block034Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part017] using hcert

def TailChunk000Sub001Block034Part018SupportExplicit : Finset ℕ :=
  ([9698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part018 : ℚ :=
  (676629173675 : ℚ) / 496470681620987904

def SurrogateDiagonalTailChunk000Sub001Block034Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9698
    = surrogateDiagTailX0RatChunk000Sub001Block034Part018

theorem surrogateDiagonalTailChunk000Sub001Block034Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part018] using hcert

def TailChunk000Sub001Block034Part019SupportExplicit : Finset ℕ :=
  ([9699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part019 : ℚ :=
  (62201558579 : ℚ) / 75821996054937600

def SurrogateDiagonalTailChunk000Sub001Block034Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9699
    = surrogateDiagTailX0RatChunk000Sub001Block034Part019

theorem surrogateDiagonalTailChunk000Sub001Block034Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part019] using hcert

def TailChunk000Sub001Block034Part020SupportExplicit : Finset ℕ :=
  ([9701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part020 : ℚ :=
  (5706466077925 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk000Sub001Block034Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9701
    = surrogateDiagTailX0RatChunk000Sub001Block034Part020

theorem surrogateDiagonalTailChunk000Sub001Block034Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part020] using hcert

def TailChunk000Sub001Block034Part021SupportExplicit : Finset ℕ :=
  ([9703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part021 : ℚ :=
  (2788500041 : ℚ) / 9596221375703040

def SurrogateDiagonalTailChunk000Sub001Block034Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9703
    = surrogateDiagTailX0RatChunk000Sub001Block034Part021

theorem surrogateDiagonalTailChunk000Sub001Block034Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part021] using hcert

def TailChunk000Sub001Block034Part022SupportExplicit : Finset ℕ :=
  ([9705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part022 : ℚ :=
  (800819139075 : ℚ) / 594559912566685696

def SurrogateDiagonalTailChunk000Sub001Block034Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9705
    = surrogateDiagTailX0RatChunk000Sub001Block034Part022

theorem surrogateDiagonalTailChunk000Sub001Block034Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part022] using hcert

def TailChunk000Sub001Block034Part023SupportExplicit : Finset ℕ :=
  ([9706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part023 : ℚ :=
  (3121179239 : ℚ) / 2531525155790400

def SurrogateDiagonalTailChunk000Sub001Block034Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9706
    = surrogateDiagTailX0RatChunk000Sub001Block034Part023

theorem surrogateDiagonalTailChunk000Sub001Block034Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part023] using hcert

def TailChunk000Sub001Block034Part024SupportExplicit : Finset ℕ :=
  ([9707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block034Part024 : ℚ :=
  (214665747133 : ℚ) / 691936441152307200

def SurrogateDiagonalTailChunk000Sub001Block034Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9707
    = surrogateDiagTailX0RatChunk000Sub001Block034Part024

theorem surrogateDiagonalTailChunk000Sub001Block034Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block034Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block034Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block034Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block034Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block034Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block034Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block034HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block034Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block034Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block034Part000
    + surrogateDiagTailX0RatChunk000Sub001Block034Part001
    + surrogateDiagTailX0RatChunk000Sub001Block034Part002
    + surrogateDiagTailX0RatChunk000Sub001Block034Part003
    + surrogateDiagTailX0RatChunk000Sub001Block034Part004
    + surrogateDiagTailX0RatChunk000Sub001Block034Part005
    + surrogateDiagTailX0RatChunk000Sub001Block034Part006
    + surrogateDiagTailX0RatChunk000Sub001Block034Part007
    + surrogateDiagTailX0RatChunk000Sub001Block034Part008
    + surrogateDiagTailX0RatChunk000Sub001Block034Part009

def surrogateDiagonalTailChunk000Sub001Block034MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block034Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block034Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block034Part010
    + surrogateDiagTailX0RatChunk000Sub001Block034Part011
    + surrogateDiagTailX0RatChunk000Sub001Block034Part012
    + surrogateDiagTailX0RatChunk000Sub001Block034Part013
    + surrogateDiagTailX0RatChunk000Sub001Block034Part014
    + surrogateDiagTailX0RatChunk000Sub001Block034Part015
    + surrogateDiagTailX0RatChunk000Sub001Block034Part016
    + surrogateDiagTailX0RatChunk000Sub001Block034Part017
    + surrogateDiagTailX0RatChunk000Sub001Block034Part018
    + surrogateDiagTailX0RatChunk000Sub001Block034Part019

def surrogateDiagonalTailChunk000Sub001Block034TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block034Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block034Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block034Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block034Part020
    + surrogateDiagTailX0RatChunk000Sub001Block034Part021
    + surrogateDiagTailX0RatChunk000Sub001Block034Part022
    + surrogateDiagTailX0RatChunk000Sub001Block034Part023
    + surrogateDiagTailX0RatChunk000Sub001Block034Part024

def surrogateDiagonalTailChunk000Sub001Block034Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block034HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block034MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block034TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block034 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block034Part000
    + surrogateDiagTailX0RatChunk000Sub001Block034Part001
    + surrogateDiagTailX0RatChunk000Sub001Block034Part002
    + surrogateDiagTailX0RatChunk000Sub001Block034Part003
    + surrogateDiagTailX0RatChunk000Sub001Block034Part004
    + surrogateDiagTailX0RatChunk000Sub001Block034Part005
    + surrogateDiagTailX0RatChunk000Sub001Block034Part006
    + surrogateDiagTailX0RatChunk000Sub001Block034Part007
    + surrogateDiagTailX0RatChunk000Sub001Block034Part008
    + surrogateDiagTailX0RatChunk000Sub001Block034Part009
    + surrogateDiagTailX0RatChunk000Sub001Block034Part010
    + surrogateDiagTailX0RatChunk000Sub001Block034Part011
    + surrogateDiagTailX0RatChunk000Sub001Block034Part012
    + surrogateDiagTailX0RatChunk000Sub001Block034Part013
    + surrogateDiagTailX0RatChunk000Sub001Block034Part014
    + surrogateDiagTailX0RatChunk000Sub001Block034Part015
    + surrogateDiagTailX0RatChunk000Sub001Block034Part016
    + surrogateDiagTailX0RatChunk000Sub001Block034Part017
    + surrogateDiagTailX0RatChunk000Sub001Block034Part018
    + surrogateDiagTailX0RatChunk000Sub001Block034Part019
    + surrogateDiagTailX0RatChunk000Sub001Block034Part020
    + surrogateDiagTailX0RatChunk000Sub001Block034Part021
    + surrogateDiagTailX0RatChunk000Sub001Block034Part022
    + surrogateDiagTailX0RatChunk000Sub001Block034Part023
    + surrogateDiagTailX0RatChunk000Sub001Block034Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block034_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block034Head + surrogateDiagTailX0RatChunk000Sub001Block034Mid + surrogateDiagTailX0RatChunk000Sub001Block034Tail =
      surrogateDiagTailX0RatChunk000Sub001Block034 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block034Head surrogateDiagTailX0RatChunk000Sub001Block034Mid surrogateDiagTailX0RatChunk000Sub001Block034Tail surrogateDiagTailX0RatChunk000Sub001Block034
  ring

def SurrogateDiagonalTailChunk000Sub001Block034HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block034HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block034Head

def SurrogateDiagonalTailChunk000Sub001Block034MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block034MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block034Mid

def SurrogateDiagonalTailChunk000Sub001Block034TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block034TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block034Tail

theorem surrogateDiagonalTailChunk000Sub001Block034_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block034HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block034MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block034TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block034Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block034 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block034HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block034MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block034TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block034Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block034_eq_head_add_mid_add_tail

/-- Block 035 covers tail-support indices [5875,5900) and q from 9709 to 9746. -/

def TailChunk000Sub001Block035Part000SupportExplicit : Finset ℕ :=
  ([9709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part000 : ℚ :=
  (4250014102825 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk000Sub001Block035Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9709
    = surrogateDiagTailX0RatChunk000Sub001Block035Part000

theorem surrogateDiagonalTailChunk000Sub001Block035Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part000] using hcert

def TailChunk000Sub001Block035Part001SupportExplicit : Finset ℕ :=
  ([9710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part001 : ℚ :=
  (8474036899 : ℚ) / 2266802863518720

def SurrogateDiagonalTailChunk000Sub001Block035Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9710
    = surrogateDiagTailX0RatChunk000Sub001Block035Part001

theorem surrogateDiagonalTailChunk000Sub001Block035Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part001] using hcert

def TailChunk000Sub001Block035Part002SupportExplicit : Finset ℕ :=
  ([9713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part002 : ℚ :=
  (65609057 : ℚ) / 4035245219506368

def SurrogateDiagonalTailChunk000Sub001Block035Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9713
    = surrogateDiagTailX0RatChunk000Sub001Block035Part002

theorem surrogateDiagonalTailChunk000Sub001Block035Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part002] using hcert

def TailChunk000Sub001Block035Part003SupportExplicit : Finset ℕ :=
  ([9714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part003 : ℚ :=
  (98234625 : ℚ) / 27414104279104

def SurrogateDiagonalTailChunk000Sub001Block035Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9714
    = surrogateDiagTailX0RatChunk000Sub001Block035Part003

theorem surrogateDiagonalTailChunk000Sub001Block035Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part003] using hcert

def TailChunk000Sub001Block035Part004SupportExplicit : Finset ℕ :=
  ([9715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part004 : ℚ :=
  (271226984225 : ℚ) / 3732885733722292224

def SurrogateDiagonalTailChunk000Sub001Block035Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9715
    = surrogateDiagTailX0RatChunk000Sub001Block035Part004

theorem surrogateDiagonalTailChunk000Sub001Block035Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part004] using hcert

def TailChunk000Sub001Block035Part005SupportExplicit : Finset ℕ :=
  ([9717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part005 : ℚ :=
  (27225799243 : ℚ) / 151643992109875200

def SurrogateDiagonalTailChunk000Sub001Block035Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9717
    = surrogateDiagTailX0RatChunk000Sub001Block035Part005

theorem surrogateDiagonalTailChunk000Sub001Block035Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part005] using hcert

def TailChunk000Sub001Block035Part006SupportExplicit : Finset ℕ :=
  ([9718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part006 : ℚ :=
  (51101742625 : ℚ) / 43725831796555776

def SurrogateDiagonalTailChunk000Sub001Block035Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9718
    = surrogateDiagTailX0RatChunk000Sub001Block035Part006

theorem surrogateDiagonalTailChunk000Sub001Block035Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part006] using hcert

def TailChunk000Sub001Block035Part007SupportExplicit : Finset ℕ :=
  ([9719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block035Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9719
    = surrogateDiagTailX0RatChunk000Sub001Block035Part007

theorem surrogateDiagonalTailChunk000Sub001Block035Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part007] using hcert

def TailChunk000Sub001Block035Part008SupportExplicit : Finset ℕ :=
  ([9721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block035Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9721
    = surrogateDiagTailX0RatChunk000Sub001Block035Part008

theorem surrogateDiagonalTailChunk000Sub001Block035Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part008] using hcert

def TailChunk000Sub001Block035Part009SupportExplicit : Finset ℕ :=
  ([9722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part009 : ℚ :=
  (590733025 : ℚ) / 557997081260832

def SurrogateDiagonalTailChunk000Sub001Block035Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9722
    = surrogateDiagTailX0RatChunk000Sub001Block035Part009

theorem surrogateDiagonalTailChunk000Sub001Block035Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part009] using hcert

def TailChunk000Sub001Block035Part010SupportExplicit : Finset ℕ :=
  ([9723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part010 : ℚ :=
  (388731875375 : ℚ) / 1181108376685569024

def SurrogateDiagonalTailChunk000Sub001Block035Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9723
    = surrogateDiagTailX0RatChunk000Sub001Block035Part010

theorem surrogateDiagonalTailChunk000Sub001Block035Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part010] using hcert

def TailChunk000Sub001Block035Part011SupportExplicit : Finset ℕ :=
  ([9726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part011 : ℚ :=
  (1313033 : ℚ) / 367332019200

def SurrogateDiagonalTailChunk000Sub001Block035Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9726
    = surrogateDiagTailX0RatChunk000Sub001Block035Part011

theorem surrogateDiagonalTailChunk000Sub001Block035Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part011] using hcert

def TailChunk000Sub001Block035Part012SupportExplicit : Finset ℕ :=
  ([9727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part012 : ℚ :=
  (2568440401 : ℚ) / 821551217804083200

def SurrogateDiagonalTailChunk000Sub001Block035Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9727
    = surrogateDiagTailX0RatChunk000Sub001Block035Part012

theorem surrogateDiagonalTailChunk000Sub001Block035Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part012] using hcert

def TailChunk000Sub001Block035Part013SupportExplicit : Finset ℕ :=
  ([9730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part013 : ℚ :=
  (240125875 : ℚ) / 68787478904832

def SurrogateDiagonalTailChunk000Sub001Block035Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9730
    = surrogateDiagTailX0RatChunk000Sub001Block035Part013

theorem surrogateDiagonalTailChunk000Sub001Block035Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part013] using hcert

def TailChunk000Sub001Block035Part014SupportExplicit : Finset ℕ :=
  ([9731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part014 : ℚ :=
  (92459862025 : ℚ) / 19789828346647922688

def SurrogateDiagonalTailChunk000Sub001Block035Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9731
    = surrogateDiagTailX0RatChunk000Sub001Block035Part014

theorem surrogateDiagonalTailChunk000Sub001Block035Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part014] using hcert

def TailChunk000Sub001Block035Part015SupportExplicit : Finset ℕ :=
  ([9733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block035Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9733
    = surrogateDiagTailX0RatChunk000Sub001Block035Part015

theorem surrogateDiagonalTailChunk000Sub001Block035Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part015] using hcert

def TailChunk000Sub001Block035Part016SupportExplicit : Finset ℕ :=
  ([9734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part016 : ℚ :=
  (1584040403 : ℚ) / 1332808524403200

def SurrogateDiagonalTailChunk000Sub001Block035Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9734
    = surrogateDiagTailX0RatChunk000Sub001Block035Part016

theorem surrogateDiagonalTailChunk000Sub001Block035Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part016] using hcert

def TailChunk000Sub001Block035Part017SupportExplicit : Finset ℕ :=
  ([9735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part017 : ℚ :=
  (33491065873 : ℚ) / 46361638089523200

def SurrogateDiagonalTailChunk000Sub001Block035Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9735
    = surrogateDiagTailX0RatChunk000Sub001Block035Part017

theorem surrogateDiagonalTailChunk000Sub001Block035Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part017] using hcert

def TailChunk000Sub001Block035Part018SupportExplicit : Finset ℕ :=
  ([9737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part018 : ℚ :=
  (2911658125 : ℚ) / 39275936980512768

def SurrogateDiagonalTailChunk000Sub001Block035Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9737
    = surrogateDiagTailX0RatChunk000Sub001Block035Part018

theorem surrogateDiagonalTailChunk000Sub001Block035Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part018] using hcert

def TailChunk000Sub001Block035Part019SupportExplicit : Finset ℕ :=
  ([9739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block035Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9739
    = surrogateDiagTailX0RatChunk000Sub001Block035Part019

theorem surrogateDiagonalTailChunk000Sub001Block035Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part019] using hcert

def TailChunk000Sub001Block035Part020SupportExplicit : Finset ℕ :=
  ([9741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part020 : ℚ :=
  (141820207 : ℚ) / 378611643187200

def SurrogateDiagonalTailChunk000Sub001Block035Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9741
    = surrogateDiagTailX0RatChunk000Sub001Block035Part020

theorem surrogateDiagonalTailChunk000Sub001Block035Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part020] using hcert

def TailChunk000Sub001Block035Part021SupportExplicit : Finset ℕ :=
  ([9742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part021 : ℚ :=
  (593166025 : ℚ) / 562603843879122

def SurrogateDiagonalTailChunk000Sub001Block035Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9742
    = surrogateDiagTailX0RatChunk000Sub001Block035Part021

theorem surrogateDiagonalTailChunk000Sub001Block035Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part021] using hcert

def TailChunk000Sub001Block035Part022SupportExplicit : Finset ℕ :=
  ([9743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block035Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9743
    = surrogateDiagTailX0RatChunk000Sub001Block035Part022

theorem surrogateDiagonalTailChunk000Sub001Block035Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part022] using hcert

def TailChunk000Sub001Block035Part023SupportExplicit : Finset ℕ :=
  ([9745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part023 : ℚ :=
  (356236218275 : ℚ) / 4608850689057767424

def SurrogateDiagonalTailChunk000Sub001Block035Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9745
    = surrogateDiagTailX0RatChunk000Sub001Block035Part023

theorem surrogateDiagonalTailChunk000Sub001Block035Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part023] using hcert

def TailChunk000Sub001Block035Part024SupportExplicit : Finset ℕ :=
  ([9746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block035Part024 : ℚ :=
  (2693035499 : ℚ) / 1908736295724960

def SurrogateDiagonalTailChunk000Sub001Block035Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9746
    = surrogateDiagTailX0RatChunk000Sub001Block035Part024

theorem surrogateDiagonalTailChunk000Sub001Block035Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block035Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block035Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block035Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block035Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block035Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block035Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block035HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block035Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block035Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block035Part000
    + surrogateDiagTailX0RatChunk000Sub001Block035Part001
    + surrogateDiagTailX0RatChunk000Sub001Block035Part002
    + surrogateDiagTailX0RatChunk000Sub001Block035Part003
    + surrogateDiagTailX0RatChunk000Sub001Block035Part004
    + surrogateDiagTailX0RatChunk000Sub001Block035Part005
    + surrogateDiagTailX0RatChunk000Sub001Block035Part006
    + surrogateDiagTailX0RatChunk000Sub001Block035Part007
    + surrogateDiagTailX0RatChunk000Sub001Block035Part008
    + surrogateDiagTailX0RatChunk000Sub001Block035Part009

def surrogateDiagonalTailChunk000Sub001Block035MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block035Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block035Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block035Part010
    + surrogateDiagTailX0RatChunk000Sub001Block035Part011
    + surrogateDiagTailX0RatChunk000Sub001Block035Part012
    + surrogateDiagTailX0RatChunk000Sub001Block035Part013
    + surrogateDiagTailX0RatChunk000Sub001Block035Part014
    + surrogateDiagTailX0RatChunk000Sub001Block035Part015
    + surrogateDiagTailX0RatChunk000Sub001Block035Part016
    + surrogateDiagTailX0RatChunk000Sub001Block035Part017
    + surrogateDiagTailX0RatChunk000Sub001Block035Part018
    + surrogateDiagTailX0RatChunk000Sub001Block035Part019

def surrogateDiagonalTailChunk000Sub001Block035TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block035Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block035Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block035Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block035Part020
    + surrogateDiagTailX0RatChunk000Sub001Block035Part021
    + surrogateDiagTailX0RatChunk000Sub001Block035Part022
    + surrogateDiagTailX0RatChunk000Sub001Block035Part023
    + surrogateDiagTailX0RatChunk000Sub001Block035Part024

def surrogateDiagonalTailChunk000Sub001Block035Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block035HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block035MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block035TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block035 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block035Part000
    + surrogateDiagTailX0RatChunk000Sub001Block035Part001
    + surrogateDiagTailX0RatChunk000Sub001Block035Part002
    + surrogateDiagTailX0RatChunk000Sub001Block035Part003
    + surrogateDiagTailX0RatChunk000Sub001Block035Part004
    + surrogateDiagTailX0RatChunk000Sub001Block035Part005
    + surrogateDiagTailX0RatChunk000Sub001Block035Part006
    + surrogateDiagTailX0RatChunk000Sub001Block035Part007
    + surrogateDiagTailX0RatChunk000Sub001Block035Part008
    + surrogateDiagTailX0RatChunk000Sub001Block035Part009
    + surrogateDiagTailX0RatChunk000Sub001Block035Part010
    + surrogateDiagTailX0RatChunk000Sub001Block035Part011
    + surrogateDiagTailX0RatChunk000Sub001Block035Part012
    + surrogateDiagTailX0RatChunk000Sub001Block035Part013
    + surrogateDiagTailX0RatChunk000Sub001Block035Part014
    + surrogateDiagTailX0RatChunk000Sub001Block035Part015
    + surrogateDiagTailX0RatChunk000Sub001Block035Part016
    + surrogateDiagTailX0RatChunk000Sub001Block035Part017
    + surrogateDiagTailX0RatChunk000Sub001Block035Part018
    + surrogateDiagTailX0RatChunk000Sub001Block035Part019
    + surrogateDiagTailX0RatChunk000Sub001Block035Part020
    + surrogateDiagTailX0RatChunk000Sub001Block035Part021
    + surrogateDiagTailX0RatChunk000Sub001Block035Part022
    + surrogateDiagTailX0RatChunk000Sub001Block035Part023
    + surrogateDiagTailX0RatChunk000Sub001Block035Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block035_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block035Head + surrogateDiagTailX0RatChunk000Sub001Block035Mid + surrogateDiagTailX0RatChunk000Sub001Block035Tail =
      surrogateDiagTailX0RatChunk000Sub001Block035 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block035Head surrogateDiagTailX0RatChunk000Sub001Block035Mid surrogateDiagTailX0RatChunk000Sub001Block035Tail surrogateDiagTailX0RatChunk000Sub001Block035
  ring

def SurrogateDiagonalTailChunk000Sub001Block035HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block035HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block035Head

def SurrogateDiagonalTailChunk000Sub001Block035MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block035MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block035Mid

def SurrogateDiagonalTailChunk000Sub001Block035TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block035TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block035Tail

theorem surrogateDiagonalTailChunk000Sub001Block035_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block035HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block035MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block035TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block035Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block035 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block035HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block035MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block035TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block035Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block035_eq_head_add_mid_add_tail

/-- Block 036 covers tail-support indices [5900,5925) and q from 9749 to 9789. -/

def TailChunk000Sub001Block036Part000SupportExplicit : Finset ℕ :=
  ([9749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block036Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9749
    = surrogateDiagTailX0RatChunk000Sub001Block036Part000

theorem surrogateDiagonalTailChunk000Sub001Block036Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part000] using hcert

def TailChunk000Sub001Block036Part001SupportExplicit : Finset ℕ :=
  ([9753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part001 : ℚ :=
  (26413464749 : ℚ) / 89270975625000000

def SurrogateDiagonalTailChunk000Sub001Block036Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9753
    = surrogateDiagTailX0RatChunk000Sub001Block036Part001

theorem surrogateDiagonalTailChunk000Sub001Block036Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part001] using hcert

def TailChunk000Sub001Block036Part002SupportExplicit : Finset ℕ :=
  ([9754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part002 : ℚ :=
  (371642640625 : ℚ) / 353363473526352672

def SurrogateDiagonalTailChunk000Sub001Block036Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9754
    = surrogateDiagTailX0RatChunk000Sub001Block036Part002

theorem surrogateDiagonalTailChunk000Sub001Block036Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part002] using hcert

def TailChunk000Sub001Block036Part003SupportExplicit : Finset ℕ :=
  ([9755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part003 : ℚ :=
  (6352906363 : ℚ) / 123408196704000000

def SurrogateDiagonalTailChunk000Sub001Block036Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9755
    = surrogateDiagTailX0RatChunk000Sub001Block036Part003

theorem surrogateDiagonalTailChunk000Sub001Block036Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part003] using hcert

def TailChunk000Sub001Block036Part004SupportExplicit : Finset ℕ :=
  ([9757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part004 : ℚ :=
  (1188823687 : ℚ) / 61634196376000320

def SurrogateDiagonalTailChunk000Sub001Block036Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9757
    = surrogateDiagTailX0RatChunk000Sub001Block036Part004

theorem surrogateDiagonalTailChunk000Sub001Block036Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part004] using hcert

def TailChunk000Sub001Block036Part005SupportExplicit : Finset ℕ :=
  ([9758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part005 : ℚ :=
  (325613393 : ℚ) / 151025142988800

def SurrogateDiagonalTailChunk000Sub001Block036Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9758
    = surrogateDiagTailX0RatChunk000Sub001Block036Part005

theorem surrogateDiagonalTailChunk000Sub001Block036Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part005] using hcert

def TailChunk000Sub001Block036Part006SupportExplicit : Finset ℕ :=
  ([9759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part006 : ℚ :=
  (661149206075 : ℚ) / 2237273062219736064

def SurrogateDiagonalTailChunk000Sub001Block036Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9759
    = surrogateDiagTailX0RatChunk000Sub001Block036Part006

theorem surrogateDiagonalTailChunk000Sub001Block036Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part006] using hcert

def TailChunk000Sub001Block036Part007SupportExplicit : Finset ℕ :=
  ([9761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part007 : ℚ :=
  (83133804325 : ℚ) / 20298211671938514048

def SurrogateDiagonalTailChunk000Sub001Block036Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9761
    = surrogateDiagTailX0RatChunk000Sub001Block036Part007

theorem surrogateDiagonalTailChunk000Sub001Block036Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part007] using hcert

def TailChunk000Sub001Block036Part008SupportExplicit : Finset ℕ :=
  ([9762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part008 : ℚ :=
  (33069275 : ℚ) / 9320107071168

def SurrogateDiagonalTailChunk000Sub001Block036Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9762
    = surrogateDiagTailX0RatChunk000Sub001Block036Part008

theorem surrogateDiagonalTailChunk000Sub001Block036Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part008] using hcert

def TailChunk000Sub001Block036Part009SupportExplicit : Finset ℕ :=
  ([9763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part009 : ℚ :=
  (4991016107 : ℚ) / 328115610000000000

def SurrogateDiagonalTailChunk000Sub001Block036Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9763
    = surrogateDiagTailX0RatChunk000Sub001Block036Part009

theorem surrogateDiagonalTailChunk000Sub001Block036Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part009] using hcert

def TailChunk000Sub001Block036Part010SupportExplicit : Finset ℕ :=
  ([9766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part010 : ℚ :=
  (351678446575 : ℚ) / 281849162851418112

def SurrogateDiagonalTailChunk000Sub001Block036Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9766
    = surrogateDiagTailX0RatChunk000Sub001Block036Part010

theorem surrogateDiagonalTailChunk000Sub001Block036Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part010] using hcert

def TailChunk000Sub001Block036Part011SupportExplicit : Finset ℕ :=
  ([9767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block036Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9767
    = surrogateDiagTailX0RatChunk000Sub001Block036Part011

theorem surrogateDiagonalTailChunk000Sub001Block036Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part011] using hcert

def TailChunk000Sub001Block036Part012SupportExplicit : Finset ℕ :=
  ([9769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block036Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9769
    = surrogateDiagTailX0RatChunk000Sub001Block036Part012

theorem surrogateDiagonalTailChunk000Sub001Block036Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part012] using hcert

def TailChunk000Sub001Block036Part013SupportExplicit : Finset ℕ :=
  ([9770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part013 : ℚ :=
  (596104071875 : ℚ) / 290426405114609664

def SurrogateDiagonalTailChunk000Sub001Block036Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9770
    = surrogateDiagTailX0RatChunk000Sub001Block036Part013

theorem surrogateDiagonalTailChunk000Sub001Block036Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part013] using hcert

def TailChunk000Sub001Block036Part014SupportExplicit : Finset ℕ :=
  ([9771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part014 : ℚ :=
  (662775880475 : ℚ) / 2248300881448157184

def SurrogateDiagonalTailChunk000Sub001Block036Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9771
    = surrogateDiagTailX0RatChunk000Sub001Block036Part014

theorem surrogateDiagonalTailChunk000Sub001Block036Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part014] using hcert

def TailChunk000Sub001Block036Part015SupportExplicit : Finset ℕ :=
  ([9773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part015 : ℚ :=
  (114274016725 : ℚ) / 19589172644856987648

def SurrogateDiagonalTailChunk000Sub001Block036Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9773
    = surrogateDiagTailX0RatChunk000Sub001Block036Part015

theorem surrogateDiagonalTailChunk000Sub001Block036Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part015] using hcert

def TailChunk000Sub001Block036Part016SupportExplicit : Finset ℕ :=
  ([9777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part016 : ℚ :=
  (332017678025 : ℚ) / 2253830054077560384

def SurrogateDiagonalTailChunk000Sub001Block036Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9777
    = surrogateDiagTailX0RatChunk000Sub001Block036Part016

theorem surrogateDiagonalTailChunk000Sub001Block036Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part016] using hcert

def TailChunk000Sub001Block036Part017SupportExplicit : Finset ℕ :=
  ([9778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part017 : ℚ :=
  (373473765625 : ℚ) / 356854893452308992

def SurrogateDiagonalTailChunk000Sub001Block036Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9778
    = surrogateDiagTailX0RatChunk000Sub001Block036Part017

theorem surrogateDiagonalTailChunk000Sub001Block036Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part017] using hcert

def TailChunk000Sub001Block036Part018SupportExplicit : Finset ℕ :=
  ([9779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part018 : ℚ :=
  (13168263713 : ℚ) / 163359364987929600

def SurrogateDiagonalTailChunk000Sub001Block036Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9779
    = surrogateDiagTailX0RatChunk000Sub001Block036Part018

theorem surrogateDiagonalTailChunk000Sub001Block036Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part018] using hcert

def TailChunk000Sub001Block036Part019SupportExplicit : Finset ℕ :=
  ([9781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block036Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9781
    = surrogateDiagTailX0RatChunk000Sub001Block036Part019

theorem surrogateDiagonalTailChunk000Sub001Block036Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part019] using hcert

def TailChunk000Sub001Block036Part020SupportExplicit : Finset ℕ :=
  ([9782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part020 : ℚ :=
  (1453792770325 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk000Sub001Block036Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9782
    = surrogateDiagTailX0RatChunk000Sub001Block036Part020

theorem surrogateDiagonalTailChunk000Sub001Block036Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part020] using hcert

def TailChunk000Sub001Block036Part021SupportExplicit : Finset ℕ :=
  ([9785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part021 : ℚ :=
  (780779186875 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk000Sub001Block036Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9785
    = surrogateDiagTailX0RatChunk000Sub001Block036Part021

theorem surrogateDiagonalTailChunk000Sub001Block036Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part021] using hcert

def TailChunk000Sub001Block036Part022SupportExplicit : Finset ℕ :=
  ([9786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part022 : ℚ :=
  (213748837225 : ℚ) / 37552926852513792

def SurrogateDiagonalTailChunk000Sub001Block036Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9786
    = surrogateDiagTailX0RatChunk000Sub001Block036Part022

theorem surrogateDiagonalTailChunk000Sub001Block036Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part022] using hcert

def TailChunk000Sub001Block036Part023SupportExplicit : Finset ℕ :=
  ([9787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block036Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9787
    = surrogateDiagTailX0RatChunk000Sub001Block036Part023

theorem surrogateDiagonalTailChunk000Sub001Block036Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part023] using hcert

def TailChunk000Sub001Block036Part024SupportExplicit : Finset ℕ :=
  ([9789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block036Part024 : ℚ :=
  (14212830197 : ℚ) / 64812960000000000

def SurrogateDiagonalTailChunk000Sub001Block036Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9789
    = surrogateDiagTailX0RatChunk000Sub001Block036Part024

theorem surrogateDiagonalTailChunk000Sub001Block036Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block036Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block036Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block036Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block036Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block036Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block036Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block036HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block036Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block036Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block036Part000
    + surrogateDiagTailX0RatChunk000Sub001Block036Part001
    + surrogateDiagTailX0RatChunk000Sub001Block036Part002
    + surrogateDiagTailX0RatChunk000Sub001Block036Part003
    + surrogateDiagTailX0RatChunk000Sub001Block036Part004
    + surrogateDiagTailX0RatChunk000Sub001Block036Part005
    + surrogateDiagTailX0RatChunk000Sub001Block036Part006
    + surrogateDiagTailX0RatChunk000Sub001Block036Part007
    + surrogateDiagTailX0RatChunk000Sub001Block036Part008
    + surrogateDiagTailX0RatChunk000Sub001Block036Part009

def surrogateDiagonalTailChunk000Sub001Block036MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block036Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block036Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block036Part010
    + surrogateDiagTailX0RatChunk000Sub001Block036Part011
    + surrogateDiagTailX0RatChunk000Sub001Block036Part012
    + surrogateDiagTailX0RatChunk000Sub001Block036Part013
    + surrogateDiagTailX0RatChunk000Sub001Block036Part014
    + surrogateDiagTailX0RatChunk000Sub001Block036Part015
    + surrogateDiagTailX0RatChunk000Sub001Block036Part016
    + surrogateDiagTailX0RatChunk000Sub001Block036Part017
    + surrogateDiagTailX0RatChunk000Sub001Block036Part018
    + surrogateDiagTailX0RatChunk000Sub001Block036Part019

def surrogateDiagonalTailChunk000Sub001Block036TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block036Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block036Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block036Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block036Part020
    + surrogateDiagTailX0RatChunk000Sub001Block036Part021
    + surrogateDiagTailX0RatChunk000Sub001Block036Part022
    + surrogateDiagTailX0RatChunk000Sub001Block036Part023
    + surrogateDiagTailX0RatChunk000Sub001Block036Part024

def surrogateDiagonalTailChunk000Sub001Block036Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block036HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block036MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block036TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block036 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block036Part000
    + surrogateDiagTailX0RatChunk000Sub001Block036Part001
    + surrogateDiagTailX0RatChunk000Sub001Block036Part002
    + surrogateDiagTailX0RatChunk000Sub001Block036Part003
    + surrogateDiagTailX0RatChunk000Sub001Block036Part004
    + surrogateDiagTailX0RatChunk000Sub001Block036Part005
    + surrogateDiagTailX0RatChunk000Sub001Block036Part006
    + surrogateDiagTailX0RatChunk000Sub001Block036Part007
    + surrogateDiagTailX0RatChunk000Sub001Block036Part008
    + surrogateDiagTailX0RatChunk000Sub001Block036Part009
    + surrogateDiagTailX0RatChunk000Sub001Block036Part010
    + surrogateDiagTailX0RatChunk000Sub001Block036Part011
    + surrogateDiagTailX0RatChunk000Sub001Block036Part012
    + surrogateDiagTailX0RatChunk000Sub001Block036Part013
    + surrogateDiagTailX0RatChunk000Sub001Block036Part014
    + surrogateDiagTailX0RatChunk000Sub001Block036Part015
    + surrogateDiagTailX0RatChunk000Sub001Block036Part016
    + surrogateDiagTailX0RatChunk000Sub001Block036Part017
    + surrogateDiagTailX0RatChunk000Sub001Block036Part018
    + surrogateDiagTailX0RatChunk000Sub001Block036Part019
    + surrogateDiagTailX0RatChunk000Sub001Block036Part020
    + surrogateDiagTailX0RatChunk000Sub001Block036Part021
    + surrogateDiagTailX0RatChunk000Sub001Block036Part022
    + surrogateDiagTailX0RatChunk000Sub001Block036Part023
    + surrogateDiagTailX0RatChunk000Sub001Block036Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block036_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block036Head + surrogateDiagTailX0RatChunk000Sub001Block036Mid + surrogateDiagTailX0RatChunk000Sub001Block036Tail =
      surrogateDiagTailX0RatChunk000Sub001Block036 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block036Head surrogateDiagTailX0RatChunk000Sub001Block036Mid surrogateDiagTailX0RatChunk000Sub001Block036Tail surrogateDiagTailX0RatChunk000Sub001Block036
  ring

def SurrogateDiagonalTailChunk000Sub001Block036HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block036HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block036Head

def SurrogateDiagonalTailChunk000Sub001Block036MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block036MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block036Mid

def SurrogateDiagonalTailChunk000Sub001Block036TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block036TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block036Tail

theorem surrogateDiagonalTailChunk000Sub001Block036_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block036HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block036MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block036TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block036Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block036 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block036HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block036MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block036TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block036Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block036_eq_head_add_mid_add_tail

/-- Block 037 covers tail-support indices [5925,5950) and q from 9790 to 9830. -/

def TailChunk000Sub001Block037Part000SupportExplicit : Finset ℕ :=
  ([9790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part000 : ℚ :=
  (43134313579 : ℚ) / 15355271656243200

def SurrogateDiagonalTailChunk000Sub001Block037Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9790
    = surrogateDiagTailX0RatChunk000Sub001Block037Part000

theorem surrogateDiagonalTailChunk000Sub001Block037Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part000] using hcert

def TailChunk000Sub001Block037Part001SupportExplicit : Finset ℕ :=
  ([9791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block037Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9791
    = surrogateDiagTailX0RatChunk000Sub001Block037Part001

theorem surrogateDiagonalTailChunk000Sub001Block037Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part001] using hcert

def TailChunk000Sub001Block037Part002SupportExplicit : Finset ℕ :=
  ([9793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part002 : ℚ :=
  (6818125825 : ℚ) / 229227536052902592

def SurrogateDiagonalTailChunk000Sub001Block037Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9793
    = surrogateDiagTailX0RatChunk000Sub001Block037Part002

theorem surrogateDiagonalTailChunk000Sub001Block037Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part002] using hcert

def TailChunk000Sub001Block037Part003SupportExplicit : Finset ℕ :=
  ([9794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part003 : ℚ :=
  (728385745475 : ℚ) / 639682171921333824

def SurrogateDiagonalTailChunk000Sub001Block037Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9794
    = surrogateDiagTailX0RatChunk000Sub001Block037Part003

theorem surrogateDiagonalTailChunk000Sub001Block037Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part003] using hcert

def TailChunk000Sub001Block037Part004SupportExplicit : Finset ℕ :=
  ([9795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part004 : ℚ :=
  (386553214925 : ℚ) / 925437713910595584

def SurrogateDiagonalTailChunk000Sub001Block037Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9795
    = surrogateDiagTailX0RatChunk000Sub001Block037Part004

theorem surrogateDiagonalTailChunk000Sub001Block037Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part004] using hcert

def TailChunk000Sub001Block037Part005SupportExplicit : Finset ℕ :=
  ([9797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part005 : ℚ :=
  (2447850241 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk000Sub001Block037Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9797
    = surrogateDiagTailX0RatChunk000Sub001Block037Part005

theorem surrogateDiagonalTailChunk000Sub001Block037Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part005] using hcert

def TailChunk000Sub001Block037Part006SupportExplicit : Finset ℕ :=
  ([9798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part006 : ℚ :=
  (9437763571 : ℚ) / 2250244582924800

def SurrogateDiagonalTailChunk000Sub001Block037Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9798
    = surrogateDiagTailX0RatChunk000Sub001Block037Part006

theorem surrogateDiagonalTailChunk000Sub001Block037Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part006] using hcert

def TailChunk000Sub001Block037Part007SupportExplicit : Finset ℕ :=
  ([9799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part007 : ℚ :=
  (3321584989 : ℚ) / 821551217804083200

def SurrogateDiagonalTailChunk000Sub001Block037Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9799
    = surrogateDiagTailX0RatChunk000Sub001Block037Part007

theorem surrogateDiagonalTailChunk000Sub001Block037Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part007] using hcert

def TailChunk000Sub001Block037Part008SupportExplicit : Finset ℕ :=
  ([9803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block037Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9803
    = surrogateDiagTailX0RatChunk000Sub001Block037Part008

theorem surrogateDiagonalTailChunk000Sub001Block037Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part008] using hcert

def TailChunk000Sub001Block037Part009SupportExplicit : Finset ℕ :=
  ([9805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part009 : ℚ :=
  (4047703373875 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk000Sub001Block037Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9805
    = surrogateDiagTailX0RatChunk000Sub001Block037Part009

theorem surrogateDiagonalTailChunk000Sub001Block037Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part009] using hcert

def TailChunk000Sub001Block037Part010SupportExplicit : Finset ℕ :=
  ([9806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part010 : ℚ :=
  (375615765625 : ℚ) / 360960845481559602

def SurrogateDiagonalTailChunk000Sub001Block037Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9806
    = surrogateDiagTailX0RatChunk000Sub001Block037Part010

theorem surrogateDiagonalTailChunk000Sub001Block037Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part010] using hcert

def TailChunk000Sub001Block037Part011SupportExplicit : Finset ℕ :=
  ([9807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part011 : ℚ :=
  (49842260525 : ℚ) / 45279513294400512

def SurrogateDiagonalTailChunk000Sub001Block037Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9807
    = surrogateDiagTailX0RatChunk000Sub001Block037Part011

theorem surrogateDiagonalTailChunk000Sub001Block037Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part011] using hcert

def TailChunk000Sub001Block037Part012SupportExplicit : Finset ℕ :=
  ([9809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part012 : ℚ :=
  (5480114855125 : ℚ) / 18038346422490759168

def SurrogateDiagonalTailChunk000Sub001Block037Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9809
    = surrogateDiagTailX0RatChunk000Sub001Block037Part012

theorem surrogateDiagonalTailChunk000Sub001Block037Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part012] using hcert

def TailChunk000Sub001Block037Part013SupportExplicit : Finset ℕ :=
  ([9811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part013 : ℚ :=
  (2406393025 : ℚ) / 9263239220598642

def SurrogateDiagonalTailChunk000Sub001Block037Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9811
    = surrogateDiagTailX0RatChunk000Sub001Block037Part013

theorem surrogateDiagonalTailChunk000Sub001Block037Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part013] using hcert

def TailChunk000Sub001Block037Part014SupportExplicit : Finset ℕ :=
  ([9813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part014 : ℚ :=
  (33426907507 : ℚ) / 45744391212832800

def SurrogateDiagonalTailChunk000Sub001Block037Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9813
    = surrogateDiagTailX0RatChunk000Sub001Block037Part014

theorem surrogateDiagonalTailChunk000Sub001Block037Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part014] using hcert

def TailChunk000Sub001Block037Part015SupportExplicit : Finset ℕ :=
  ([9814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part015 : ℚ :=
  (81801869 : ℚ) / 49401878400000

def SurrogateDiagonalTailChunk000Sub001Block037Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9814
    = surrogateDiagTailX0RatChunk000Sub001Block037Part015

theorem surrogateDiagonalTailChunk000Sub001Block037Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part015] using hcert

def TailChunk000Sub001Block037Part016SupportExplicit : Finset ℕ :=
  ([9815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part016 : ℚ :=
  (2030946029 : ℚ) / 3583897436160000

def SurrogateDiagonalTailChunk000Sub001Block037Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9815
    = surrogateDiagTailX0RatChunk000Sub001Block037Part016

theorem surrogateDiagonalTailChunk000Sub001Block037Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part016] using hcert

def TailChunk000Sub001Block037Part017SupportExplicit : Finset ℕ :=
  ([9817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part017 : ℚ :=
  (1505835765625 : ℚ) / 5803701486988718592

def SurrogateDiagonalTailChunk000Sub001Block037Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9817
    = surrogateDiagTailX0RatChunk000Sub001Block037Part017

theorem surrogateDiagonalTailChunk000Sub001Block037Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part017] using hcert

def TailChunk000Sub001Block037Part018SupportExplicit : Finset ℕ :=
  ([9818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part018 : ℚ :=
  (376535640625 : ℚ) / 362731342936794912

def SurrogateDiagonalTailChunk000Sub001Block037Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9818
    = surrogateDiagTailX0RatChunk000Sub001Block037Part018

theorem surrogateDiagonalTailChunk000Sub001Block037Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part018] using hcert

def TailChunk000Sub001Block037Part019SupportExplicit : Finset ℕ :=
  ([9821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part019 : ℚ :=
  (14276934143 : ℚ) / 32794901476761600

def SurrogateDiagonalTailChunk000Sub001Block037Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9821
    = surrogateDiagTailX0RatChunk000Sub001Block037Part019

theorem surrogateDiagonalTailChunk000Sub001Block037Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part019] using hcert

def TailChunk000Sub001Block037Part020SupportExplicit : Finset ℕ :=
  ([9822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part020 : ℚ :=
  (100431075 : ℚ) / 28654523352064

def SurrogateDiagonalTailChunk000Sub001Block037Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9822
    = surrogateDiagTailX0RatChunk000Sub001Block037Part020

theorem surrogateDiagonalTailChunk000Sub001Block037Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part020] using hcert

def TailChunk000Sub001Block037Part021SupportExplicit : Finset ℕ :=
  ([9823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part021 : ℚ :=
  (62293086247 : ℚ) / 156706475380070400

def SurrogateDiagonalTailChunk000Sub001Block037Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9823
    = surrogateDiagTailX0RatChunk000Sub001Block037Part021

theorem surrogateDiagonalTailChunk000Sub001Block037Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part021] using hcert

def TailChunk000Sub001Block037Part022SupportExplicit : Finset ℕ :=
  ([9827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part022 : ℚ :=
  (11441353421 : ℚ) / 40391520669596160

def SurrogateDiagonalTailChunk000Sub001Block037Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9827
    = surrogateDiagTailX0RatChunk000Sub001Block037Part022

theorem surrogateDiagonalTailChunk000Sub001Block037Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part022] using hcert

def TailChunk000Sub001Block037Part023SupportExplicit : Finset ℕ :=
  ([9829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part023 : ℚ :=
  (1509519390625 : ℚ) / 5832133529275321632

def SurrogateDiagonalTailChunk000Sub001Block037Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9829
    = surrogateDiagTailX0RatChunk000Sub001Block037Part023

theorem surrogateDiagonalTailChunk000Sub001Block037Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part023] using hcert

def TailChunk000Sub001Block037Part024SupportExplicit : Finset ℕ :=
  ([9830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block037Part024 : ℚ :=
  (603448040375 : ℚ) / 297634163562046464

def SurrogateDiagonalTailChunk000Sub001Block037Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9830
    = surrogateDiagTailX0RatChunk000Sub001Block037Part024

theorem surrogateDiagonalTailChunk000Sub001Block037Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block037Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block037Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block037Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block037Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block037Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block037Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block037HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block037Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block037Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block037Part000
    + surrogateDiagTailX0RatChunk000Sub001Block037Part001
    + surrogateDiagTailX0RatChunk000Sub001Block037Part002
    + surrogateDiagTailX0RatChunk000Sub001Block037Part003
    + surrogateDiagTailX0RatChunk000Sub001Block037Part004
    + surrogateDiagTailX0RatChunk000Sub001Block037Part005
    + surrogateDiagTailX0RatChunk000Sub001Block037Part006
    + surrogateDiagTailX0RatChunk000Sub001Block037Part007
    + surrogateDiagTailX0RatChunk000Sub001Block037Part008
    + surrogateDiagTailX0RatChunk000Sub001Block037Part009

def surrogateDiagonalTailChunk000Sub001Block037MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block037Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block037Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block037Part010
    + surrogateDiagTailX0RatChunk000Sub001Block037Part011
    + surrogateDiagTailX0RatChunk000Sub001Block037Part012
    + surrogateDiagTailX0RatChunk000Sub001Block037Part013
    + surrogateDiagTailX0RatChunk000Sub001Block037Part014
    + surrogateDiagTailX0RatChunk000Sub001Block037Part015
    + surrogateDiagTailX0RatChunk000Sub001Block037Part016
    + surrogateDiagTailX0RatChunk000Sub001Block037Part017
    + surrogateDiagTailX0RatChunk000Sub001Block037Part018
    + surrogateDiagTailX0RatChunk000Sub001Block037Part019

def surrogateDiagonalTailChunk000Sub001Block037TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block037Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block037Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block037Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block037Part020
    + surrogateDiagTailX0RatChunk000Sub001Block037Part021
    + surrogateDiagTailX0RatChunk000Sub001Block037Part022
    + surrogateDiagTailX0RatChunk000Sub001Block037Part023
    + surrogateDiagTailX0RatChunk000Sub001Block037Part024

def surrogateDiagonalTailChunk000Sub001Block037Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block037HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block037MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block037TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block037 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block037Part000
    + surrogateDiagTailX0RatChunk000Sub001Block037Part001
    + surrogateDiagTailX0RatChunk000Sub001Block037Part002
    + surrogateDiagTailX0RatChunk000Sub001Block037Part003
    + surrogateDiagTailX0RatChunk000Sub001Block037Part004
    + surrogateDiagTailX0RatChunk000Sub001Block037Part005
    + surrogateDiagTailX0RatChunk000Sub001Block037Part006
    + surrogateDiagTailX0RatChunk000Sub001Block037Part007
    + surrogateDiagTailX0RatChunk000Sub001Block037Part008
    + surrogateDiagTailX0RatChunk000Sub001Block037Part009
    + surrogateDiagTailX0RatChunk000Sub001Block037Part010
    + surrogateDiagTailX0RatChunk000Sub001Block037Part011
    + surrogateDiagTailX0RatChunk000Sub001Block037Part012
    + surrogateDiagTailX0RatChunk000Sub001Block037Part013
    + surrogateDiagTailX0RatChunk000Sub001Block037Part014
    + surrogateDiagTailX0RatChunk000Sub001Block037Part015
    + surrogateDiagTailX0RatChunk000Sub001Block037Part016
    + surrogateDiagTailX0RatChunk000Sub001Block037Part017
    + surrogateDiagTailX0RatChunk000Sub001Block037Part018
    + surrogateDiagTailX0RatChunk000Sub001Block037Part019
    + surrogateDiagTailX0RatChunk000Sub001Block037Part020
    + surrogateDiagTailX0RatChunk000Sub001Block037Part021
    + surrogateDiagTailX0RatChunk000Sub001Block037Part022
    + surrogateDiagTailX0RatChunk000Sub001Block037Part023
    + surrogateDiagTailX0RatChunk000Sub001Block037Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block037_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block037Head + surrogateDiagTailX0RatChunk000Sub001Block037Mid + surrogateDiagTailX0RatChunk000Sub001Block037Tail =
      surrogateDiagTailX0RatChunk000Sub001Block037 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block037Head surrogateDiagTailX0RatChunk000Sub001Block037Mid surrogateDiagTailX0RatChunk000Sub001Block037Tail surrogateDiagTailX0RatChunk000Sub001Block037
  ring

def SurrogateDiagonalTailChunk000Sub001Block037HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block037HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block037Head

def SurrogateDiagonalTailChunk000Sub001Block037MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block037MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block037Mid

def SurrogateDiagonalTailChunk000Sub001Block037TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block037TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block037Tail

theorem surrogateDiagonalTailChunk000Sub001Block037_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block037HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block037MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block037TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block037Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block037 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block037HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block037MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block037TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block037Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block037_eq_head_add_mid_add_tail

/-- Block 038 covers tail-support indices [5950,5975) and q from 9831 to 9870. -/

def TailChunk000Sub001Block038Part000SupportExplicit : Finset ℕ :=
  ([9831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part000 : ℚ :=
  (1052525056875 : ℚ) / 1289822067151077376

def SurrogateDiagonalTailChunk000Sub001Block038Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9831
    = surrogateDiagTailX0RatChunk000Sub001Block038Part000

theorem surrogateDiagonalTailChunk000Sub001Block038Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part000] using hcert

def TailChunk000Sub001Block038Part001SupportExplicit : Finset ℕ :=
  ([9833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part001 : ℚ :=
  (1510748265625 : ℚ) / 5841634050262774272

def SurrogateDiagonalTailChunk000Sub001Block038Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9833
    = surrogateDiagTailX0RatChunk000Sub001Block038Part001

theorem surrogateDiagonalTailChunk000Sub001Block038Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part001] using hcert

def TailChunk000Sub001Block038Part002SupportExplicit : Finset ℕ :=
  ([9834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part002 : ℚ :=
  (2430164301 : ℚ) / 511873251246080

def SurrogateDiagonalTailChunk000Sub001Block038Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9834
    = surrogateDiagTailX0RatChunk000Sub001Block038Part002

theorem surrogateDiagonalTailChunk000Sub001Block038Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part002] using hcert

def TailChunk000Sub001Block038Part003SupportExplicit : Finset ℕ :=
  ([9835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part003 : ℚ :=
  (16527340607 : ℚ) / 25496111834726400

def SurrogateDiagonalTailChunk000Sub001Block038Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9835
    = surrogateDiagTailX0RatChunk000Sub001Block038Part003

theorem surrogateDiagonalTailChunk000Sub001Block038Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part003] using hcert

def TailChunk000Sub001Block038Part004SupportExplicit : Finset ℕ :=
  ([9838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part004 : ℚ :=
  (378071265625 : ℚ) / 365696635859841522

def SurrogateDiagonalTailChunk000Sub001Block038Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9838
    = surrogateDiagTailX0RatChunk000Sub001Block038Part004

theorem surrogateDiagonalTailChunk000Sub001Block038Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part004] using hcert

def TailChunk000Sub001Block038Part005SupportExplicit : Finset ℕ :=
  ([9839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part005 : ℚ :=
  (1512592515625 : ℚ) / 5855906589395663442

def SurrogateDiagonalTailChunk000Sub001Block038Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9839
    = surrogateDiagTailX0RatChunk000Sub001Block038Part005

theorem surrogateDiagonalTailChunk000Sub001Block038Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part005] using hcert

def TailChunk000Sub001Block038Part006SupportExplicit : Finset ℕ :=
  ([9841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part006 : ℚ :=
  (5362709085775 : ℚ) / 16937098961948540928

def SurrogateDiagonalTailChunk000Sub001Block038Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9841
    = surrogateDiagTailX0RatChunk000Sub001Block038Part006

theorem surrogateDiagonalTailChunk000Sub001Block038Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part006] using hcert

def TailChunk000Sub001Block038Part007SupportExplicit : Finset ℕ :=
  ([9842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part007 : ℚ :=
  (132923736925 : ℚ) / 63487667912343552

def SurrogateDiagonalTailChunk000Sub001Block038Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9842
    = surrogateDiagTailX0RatChunk000Sub001Block038Part007

theorem surrogateDiagonalTailChunk000Sub001Block038Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part007] using hcert

def TailChunk000Sub001Block038Part008SupportExplicit : Finset ℕ :=
  ([9843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part008 : ℚ :=
  (413685114125 : ℚ) / 593855026254839808

def SurrogateDiagonalTailChunk000Sub001Block038Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9843
    = surrogateDiagTailX0RatChunk000Sub001Block038Part008

theorem surrogateDiagonalTailChunk000Sub001Block038Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part008] using hcert

def TailChunk000Sub001Block038Part009SupportExplicit : Finset ℕ :=
  ([9845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part009 : ℚ :=
  (7550925821 : ℚ) / 12852180878991360

def SurrogateDiagonalTailChunk000Sub001Block038Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9845
    = surrogateDiagTailX0RatChunk000Sub001Block038Part009

theorem surrogateDiagonalTailChunk000Sub001Block038Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part009] using hcert

def TailChunk000Sub001Block038Part010SupportExplicit : Finset ℕ :=
  ([9847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part010 : ℚ :=
  (645937218175 : ℚ) / 2336258524509407232

def SurrogateDiagonalTailChunk000Sub001Block038Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9847
    = surrogateDiagTailX0RatChunk000Sub001Block038Part010

theorem surrogateDiagonalTailChunk000Sub001Block038Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part010] using hcert

def TailChunk000Sub001Block038Part011SupportExplicit : Finset ℕ :=
  ([9851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part011 : ℚ :=
  (97042201 : ℚ) / 376609927174050

def SurrogateDiagonalTailChunk000Sub001Block038Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9851
    = surrogateDiagTailX0RatChunk000Sub001Block038Part011

theorem surrogateDiagonalTailChunk000Sub001Block038Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part011] using hcert

def TailChunk000Sub001Block038Part012SupportExplicit : Finset ℕ :=
  ([9853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part012 : ℚ :=
  (1465174616875 : ℚ) / 5371693121431686432

def SurrogateDiagonalTailChunk000Sub001Block038Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9853
    = surrogateDiagTailX0RatChunk000Sub001Block038Part012

theorem surrogateDiagonalTailChunk000Sub001Block038Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part012] using hcert

def TailChunk000Sub001Block038Part013SupportExplicit : Finset ℕ :=
  ([9854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part013 : ℚ :=
  (698571061175 : ℚ) / 529284342560891904

def SurrogateDiagonalTailChunk000Sub001Block038Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9854
    = surrogateDiagTailX0RatChunk000Sub001Block038Part013

theorem surrogateDiagonalTailChunk000Sub001Block038Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part013] using hcert

def TailChunk000Sub001Block038Part014SupportExplicit : Finset ℕ :=
  ([9857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part014 : ℚ :=
  (1518132015625 : ℚ) / 5898881159462387712

def SurrogateDiagonalTailChunk000Sub001Block038Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9857
    = surrogateDiagTailX0RatChunk000Sub001Block038Part014

theorem surrogateDiagonalTailChunk000Sub001Block038Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part014] using hcert

def TailChunk000Sub001Block038Part015SupportExplicit : Finset ℕ :=
  ([9858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part015 : ℚ :=
  (12833093263 : ℚ) / 3159249835622400

def SurrogateDiagonalTailChunk000Sub001Block038Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9858
    = surrogateDiagTailX0RatChunk000Sub001Block038Part015

theorem surrogateDiagonalTailChunk000Sub001Block038Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part015] using hcert

def TailChunk000Sub001Block038Part016SupportExplicit : Finset ℕ :=
  ([9859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part016 : ℚ :=
  (1518748140625 : ℚ) / 5903670669951193362

def SurrogateDiagonalTailChunk000Sub001Block038Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9859
    = surrogateDiagTailX0RatChunk000Sub001Block038Part016

theorem surrogateDiagonalTailChunk000Sub001Block038Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part016] using hcert

def TailChunk000Sub001Block038Part017SupportExplicit : Finset ℕ :=
  ([9861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part017 : ℚ :=
  (1254585605825 : ℚ) / 1837894820796186624

def SurrogateDiagonalTailChunk000Sub001Block038Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9861
    = surrogateDiagTailX0RatChunk000Sub001Block038Part017

theorem surrogateDiagonalTailChunk000Sub001Block038Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part017] using hcert

def TailChunk000Sub001Block038Part018SupportExplicit : Finset ℕ :=
  ([9862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part018 : ℚ :=
  (607869025 : ℚ) / 590846309642802

def SurrogateDiagonalTailChunk000Sub001Block038Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9862
    = surrogateDiagTailX0RatChunk000Sub001Block038Part018

theorem surrogateDiagonalTailChunk000Sub001Block038Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part018] using hcert

def TailChunk000Sub001Block038Part019SupportExplicit : Finset ℕ :=
  ([9863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part019 : ℚ :=
  (268603953575 : ℚ) / 707570917919686656

def SurrogateDiagonalTailChunk000Sub001Block038Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9863
    = surrogateDiagTailX0RatChunk000Sub001Block038Part019

theorem surrogateDiagonalTailChunk000Sub001Block038Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part019] using hcert

def TailChunk000Sub001Block038Part020SupportExplicit : Finset ℕ :=
  ([9865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part020 : ℚ :=
  (4133472213775 : ℚ) / 9680425937187667968

def SurrogateDiagonalTailChunk000Sub001Block038Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9865
    = surrogateDiagTailX0RatChunk000Sub001Block038Part020

theorem surrogateDiagonalTailChunk000Sub001Block038Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part020] using hcert

def TailChunk000Sub001Block038Part021SupportExplicit : Finset ℕ :=
  ([9866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part021 : ℚ :=
  (380226390625 : ℚ) / 369878543879952672

def SurrogateDiagonalTailChunk000Sub001Block038Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9866
    = surrogateDiagTailX0RatChunk000Sub001Block038Part021

theorem surrogateDiagonalTailChunk000Sub001Block038Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part021] using hcert

def TailChunk000Sub001Block038Part022SupportExplicit : Finset ℕ :=
  ([9867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part022 : ℚ :=
  (13698184789 : ℚ) / 12956010459955200

def SurrogateDiagonalTailChunk000Sub001Block038Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9867
    = surrogateDiagTailX0RatChunk000Sub001Block038Part022

theorem surrogateDiagonalTailChunk000Sub001Block038Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part022] using hcert

def TailChunk000Sub001Block038Part023SupportExplicit : Finset ℕ :=
  ([9869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part023 : ℚ :=
  (13370069 : ℚ) / 49373825190480

def SurrogateDiagonalTailChunk000Sub001Block038Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9869
    = surrogateDiagTailX0RatChunk000Sub001Block038Part023

theorem surrogateDiagonalTailChunk000Sub001Block038Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part023] using hcert

def TailChunk000Sub001Block038Part024SupportExplicit : Finset ℕ :=
  ([9870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block038Part024 : ℚ :=
  (340767211925 : ℚ) / 29716190886887424

def SurrogateDiagonalTailChunk000Sub001Block038Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9870
    = surrogateDiagTailX0RatChunk000Sub001Block038Part024

theorem surrogateDiagonalTailChunk000Sub001Block038Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block038Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block038Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block038Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block038Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block038Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block038Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block038HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block038Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block038Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block038Part000
    + surrogateDiagTailX0RatChunk000Sub001Block038Part001
    + surrogateDiagTailX0RatChunk000Sub001Block038Part002
    + surrogateDiagTailX0RatChunk000Sub001Block038Part003
    + surrogateDiagTailX0RatChunk000Sub001Block038Part004
    + surrogateDiagTailX0RatChunk000Sub001Block038Part005
    + surrogateDiagTailX0RatChunk000Sub001Block038Part006
    + surrogateDiagTailX0RatChunk000Sub001Block038Part007
    + surrogateDiagTailX0RatChunk000Sub001Block038Part008
    + surrogateDiagTailX0RatChunk000Sub001Block038Part009

def surrogateDiagonalTailChunk000Sub001Block038MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block038Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block038Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block038Part010
    + surrogateDiagTailX0RatChunk000Sub001Block038Part011
    + surrogateDiagTailX0RatChunk000Sub001Block038Part012
    + surrogateDiagTailX0RatChunk000Sub001Block038Part013
    + surrogateDiagTailX0RatChunk000Sub001Block038Part014
    + surrogateDiagTailX0RatChunk000Sub001Block038Part015
    + surrogateDiagTailX0RatChunk000Sub001Block038Part016
    + surrogateDiagTailX0RatChunk000Sub001Block038Part017
    + surrogateDiagTailX0RatChunk000Sub001Block038Part018
    + surrogateDiagTailX0RatChunk000Sub001Block038Part019

def surrogateDiagonalTailChunk000Sub001Block038TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block038Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block038Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block038Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block038Part020
    + surrogateDiagTailX0RatChunk000Sub001Block038Part021
    + surrogateDiagTailX0RatChunk000Sub001Block038Part022
    + surrogateDiagTailX0RatChunk000Sub001Block038Part023
    + surrogateDiagTailX0RatChunk000Sub001Block038Part024

def surrogateDiagonalTailChunk000Sub001Block038Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block038HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block038MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block038TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block038 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block038Part000
    + surrogateDiagTailX0RatChunk000Sub001Block038Part001
    + surrogateDiagTailX0RatChunk000Sub001Block038Part002
    + surrogateDiagTailX0RatChunk000Sub001Block038Part003
    + surrogateDiagTailX0RatChunk000Sub001Block038Part004
    + surrogateDiagTailX0RatChunk000Sub001Block038Part005
    + surrogateDiagTailX0RatChunk000Sub001Block038Part006
    + surrogateDiagTailX0RatChunk000Sub001Block038Part007
    + surrogateDiagTailX0RatChunk000Sub001Block038Part008
    + surrogateDiagTailX0RatChunk000Sub001Block038Part009
    + surrogateDiagTailX0RatChunk000Sub001Block038Part010
    + surrogateDiagTailX0RatChunk000Sub001Block038Part011
    + surrogateDiagTailX0RatChunk000Sub001Block038Part012
    + surrogateDiagTailX0RatChunk000Sub001Block038Part013
    + surrogateDiagTailX0RatChunk000Sub001Block038Part014
    + surrogateDiagTailX0RatChunk000Sub001Block038Part015
    + surrogateDiagTailX0RatChunk000Sub001Block038Part016
    + surrogateDiagTailX0RatChunk000Sub001Block038Part017
    + surrogateDiagTailX0RatChunk000Sub001Block038Part018
    + surrogateDiagTailX0RatChunk000Sub001Block038Part019
    + surrogateDiagTailX0RatChunk000Sub001Block038Part020
    + surrogateDiagTailX0RatChunk000Sub001Block038Part021
    + surrogateDiagTailX0RatChunk000Sub001Block038Part022
    + surrogateDiagTailX0RatChunk000Sub001Block038Part023
    + surrogateDiagTailX0RatChunk000Sub001Block038Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block038_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block038Head + surrogateDiagTailX0RatChunk000Sub001Block038Mid + surrogateDiagTailX0RatChunk000Sub001Block038Tail =
      surrogateDiagTailX0RatChunk000Sub001Block038 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block038Head surrogateDiagTailX0RatChunk000Sub001Block038Mid surrogateDiagTailX0RatChunk000Sub001Block038Tail surrogateDiagTailX0RatChunk000Sub001Block038
  ring

def SurrogateDiagonalTailChunk000Sub001Block038HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block038HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block038Head

def SurrogateDiagonalTailChunk000Sub001Block038MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block038MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block038Mid

def SurrogateDiagonalTailChunk000Sub001Block038TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block038TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block038Tail

theorem surrogateDiagonalTailChunk000Sub001Block038_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block038HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block038MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block038TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block038Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block038 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block038HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block038MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block038TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block038Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block038_eq_head_add_mid_add_tail

/-- Block 039 covers tail-support indices [5975,6000) and q from 9871 to 9911. -/

def TailChunk000Sub001Block039Part000SupportExplicit : Finset ℕ :=
  ([9871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part000 : ℚ :=
  (2435916025 : ℚ) / 9491950416091122

def SurrogateDiagonalTailChunk000Sub001Block039Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9871
    = surrogateDiagTailX0RatChunk000Sub001Block039Part000

theorem surrogateDiagonalTailChunk000Sub001Block039Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part000] using hcert

def TailChunk000Sub001Block039Part001SupportExplicit : Finset ℕ :=
  ([9874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part001 : ℚ :=
  (380843265625 : ℚ) / 371079934832497152

def SurrogateDiagonalTailChunk000Sub001Block039Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9874
    = surrogateDiagTailX0RatChunk000Sub001Block039Part001

theorem surrogateDiagonalTailChunk000Sub001Block039Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part001] using hcert

def TailChunk000Sub001Block039Part002SupportExplicit : Finset ℕ :=
  ([9877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part002 : ℚ :=
  (4259663789275 : ℚ) / 9602121579236425728

def SurrogateDiagonalTailChunk000Sub001Block039Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9877
    = surrogateDiagTailX0RatChunk000Sub001Block039Part002

theorem surrogateDiagonalTailChunk000Sub001Block039Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part002] using hcert

def TailChunk000Sub001Block039Part003SupportExplicit : Finset ℕ :=
  ([9878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part003 : ℚ :=
  (172904699 : ℚ) / 125906725109760

def SurrogateDiagonalTailChunk000Sub001Block039Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9878
    = surrogateDiagTailX0RatChunk000Sub001Block039Part003

theorem surrogateDiagonalTailChunk000Sub001Block039Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part003] using hcert

def TailChunk000Sub001Block039Part004SupportExplicit : Finset ℕ :=
  ([9879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part004 : ℚ :=
  (291968101625 : ℚ) / 366348863042224128

def SurrogateDiagonalTailChunk000Sub001Block039Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9879
    = surrogateDiagTailX0RatChunk000Sub001Block039Part004

theorem surrogateDiagonalTailChunk000Sub001Block039Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part004] using hcert

def TailChunk000Sub001Block039Part005SupportExplicit : Finset ℕ :=
  ([9881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part005 : ℚ :=
  (233811291349 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk000Sub001Block039Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9881
    = surrogateDiagTailX0RatChunk000Sub001Block039Part005

theorem surrogateDiagonalTailChunk000Sub001Block039Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part005] using hcert

def TailChunk000Sub001Block039Part006SupportExplicit : Finset ℕ :=
  ([9883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part006 : ℚ :=
  (1526151390625 : ℚ) / 5961372581482684722

def SurrogateDiagonalTailChunk000Sub001Block039Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9883
    = surrogateDiagTailX0RatChunk000Sub001Block039Part006

theorem surrogateDiagonalTailChunk000Sub001Block039Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part006] using hcert

def TailChunk000Sub001Block039Part007SupportExplicit : Finset ℕ :=
  ([9885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part007 : ℚ :=
  (830816088675 : ℚ) / 639984014885748736

def SurrogateDiagonalTailChunk000Sub001Block039Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9885
    = surrogateDiagTailX0RatChunk000Sub001Block039Part007

theorem surrogateDiagonalTailChunk000Sub001Block039Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part007] using hcert

def TailChunk000Sub001Block039Part008SupportExplicit : Finset ℕ :=
  ([9886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part008 : ℚ :=
  (381769515625 : ℚ) / 372887505761444562

def SurrogateDiagonalTailChunk000Sub001Block039Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9886
    = surrogateDiagTailX0RatChunk000Sub001Block039Part008

theorem surrogateDiagonalTailChunk000Sub001Block039Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part008] using hcert

def TailChunk000Sub001Block039Part009SupportExplicit : Finset ℕ :=
  ([9887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part009 : ℚ :=
  (1527387015625 : ℚ) / 5971030534273402002

def SurrogateDiagonalTailChunk000Sub001Block039Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9887
    = surrogateDiagTailX0RatChunk000Sub001Block039Part009

theorem surrogateDiagonalTailChunk000Sub001Block039Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part009] using hcert

def TailChunk000Sub001Block039Part010SupportExplicit : Finset ℕ :=
  ([9889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part010 : ℚ :=
  (63360226519 : ℚ) / 165990311424000000

def SurrogateDiagonalTailChunk000Sub001Block039Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9889
    = surrogateDiagTailX0RatChunk000Sub001Block039Part010

theorem surrogateDiagonalTailChunk000Sub001Block039Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part010] using hcert

def TailChunk000Sub001Block039Part011SupportExplicit : Finset ℕ :=
  ([9890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part011 : ℚ :=
  (63515106425 : ℚ) / 25922817595293696

def SurrogateDiagonalTailChunk000Sub001Block039Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9890
    = surrogateDiagTailX0RatChunk000Sub001Block039Part011

theorem surrogateDiagonalTailChunk000Sub001Block039Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part011] using hcert

def TailChunk000Sub001Block039Part012SupportExplicit : Finset ℕ :=
  ([9893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part012 : ℚ :=
  (215334661489 : ℚ) / 691936441152307200

def SurrogateDiagonalTailChunk000Sub001Block039Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9893
    = surrogateDiagTailX0RatChunk000Sub001Block039Part012

theorem surrogateDiagonalTailChunk000Sub001Block039Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part012] using hcert

def TailChunk000Sub001Block039Part013SupportExplicit : Finset ℕ :=
  ([9894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part013 : ℚ :=
  (475346147675 : ℚ) / 111347817422782464

def SurrogateDiagonalTailChunk000Sub001Block039Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9894
    = surrogateDiagTailX0RatChunk000Sub001Block039Part013

theorem surrogateDiagonalTailChunk000Sub001Block039Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part013] using hcert

def TailChunk000Sub001Block039Part014SupportExplicit : Finset ℕ :=
  ([9895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part014 : ℚ :=
  (1467826502475 : ℚ) / 3266259745379424256

def SurrogateDiagonalTailChunk000Sub001Block039Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9895
    = surrogateDiagTailX0RatChunk000Sub001Block039Part014

theorem surrogateDiagonalTailChunk000Sub001Block039Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part014] using hcert

def TailChunk000Sub001Block039Part015SupportExplicit : Finset ℕ :=
  ([9897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part015 : ℚ :=
  (212510621575 : ℚ) / 295821315568667208

def SurrogateDiagonalTailChunk000Sub001Block039Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9897
    = surrogateDiagTailX0RatChunk000Sub001Block039Part015

theorem surrogateDiagonalTailChunk000Sub001Block039Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part015] using hcert

def TailChunk000Sub001Block039Part016SupportExplicit : Finset ℕ :=
  ([9899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part016 : ℚ :=
  (14085381049 : ℚ) / 47981106878515200

def SurrogateDiagonalTailChunk000Sub001Block039Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9899
    = surrogateDiagTailX0RatChunk000Sub001Block039Part016

theorem surrogateDiagonalTailChunk000Sub001Block039Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part016] using hcert

def TailChunk000Sub001Block039Part017SupportExplicit : Finset ℕ :=
  ([9901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part017 : ℚ :=
  (98029801 : ℚ) / 384315251680800

def SurrogateDiagonalTailChunk000Sub001Block039Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9901
    = surrogateDiagTailX0RatChunk000Sub001Block039Part017

theorem surrogateDiagonalTailChunk000Sub001Block039Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part017] using hcert

def TailChunk000Sub001Block039Part018SupportExplicit : Finset ℕ :=
  ([9902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part018 : ℚ :=
  (24512401 : ℚ) / 24019703230050

def SurrogateDiagonalTailChunk000Sub001Block039Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9902
    = surrogateDiagTailX0RatChunk000Sub001Block039Part018

theorem surrogateDiagonalTailChunk000Sub001Block039Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part018] using hcert

def TailChunk000Sub001Block039Part019SupportExplicit : Finset ℕ :=
  ([9903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part019 : ℚ :=
  (136250021 : ℚ) / 948926547360000

def SurrogateDiagonalTailChunk000Sub001Block039Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9903
    = surrogateDiagTailX0RatChunk000Sub001Block039Part019

theorem surrogateDiagonalTailChunk000Sub001Block039Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part019] using hcert

def TailChunk000Sub001Block039Part020SupportExplicit : Finset ℕ :=
  ([9905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part020 : ℚ :=
  (83569042475 : ℚ) / 655810358444199936

def SurrogateDiagonalTailChunk000Sub001Block039Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9905
    = surrogateDiagTailX0RatChunk000Sub001Block039Part020

theorem surrogateDiagonalTailChunk000Sub001Block039Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part020] using hcert

def TailChunk000Sub001Block039Part021SupportExplicit : Finset ℕ :=
  ([9906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part021 : ℚ :=
  (33441885625 : ℚ) / 7467856685162496

def SurrogateDiagonalTailChunk000Sub001Block039Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9906
    = surrogateDiagTailX0RatChunk000Sub001Block039Part021

theorem surrogateDiagonalTailChunk000Sub001Block039Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part021] using hcert

def TailChunk000Sub001Block039Part022SupportExplicit : Finset ℕ :=
  ([9907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block039Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9907
    = surrogateDiagTailX0RatChunk000Sub001Block039Part022

theorem surrogateDiagonalTailChunk000Sub001Block039Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part022] using hcert

def TailChunk000Sub001Block039Part023SupportExplicit : Finset ℕ :=
  ([9910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part023 : ℚ :=
  (4906480099 : ℚ) / 2459617610757120

def SurrogateDiagonalTailChunk000Sub001Block039Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9910
    = surrogateDiagTailX0RatChunk000Sub001Block039Part023

theorem surrogateDiagonalTailChunk000Sub001Block039Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part023] using hcert

def TailChunk000Sub001Block039Part024SupportExplicit : Finset ℕ :=
  ([9911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block039Part024 : ℚ :=
  (19006205077 : ℚ) / 479269900989235200

def SurrogateDiagonalTailChunk000Sub001Block039Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9911
    = surrogateDiagTailX0RatChunk000Sub001Block039Part024

theorem surrogateDiagonalTailChunk000Sub001Block039Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block039Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block039Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block039Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block039Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block039Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block039Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block039HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block039Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block039Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block039Part000
    + surrogateDiagTailX0RatChunk000Sub001Block039Part001
    + surrogateDiagTailX0RatChunk000Sub001Block039Part002
    + surrogateDiagTailX0RatChunk000Sub001Block039Part003
    + surrogateDiagTailX0RatChunk000Sub001Block039Part004
    + surrogateDiagTailX0RatChunk000Sub001Block039Part005
    + surrogateDiagTailX0RatChunk000Sub001Block039Part006
    + surrogateDiagTailX0RatChunk000Sub001Block039Part007
    + surrogateDiagTailX0RatChunk000Sub001Block039Part008
    + surrogateDiagTailX0RatChunk000Sub001Block039Part009

def surrogateDiagonalTailChunk000Sub001Block039MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block039Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block039Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block039Part010
    + surrogateDiagTailX0RatChunk000Sub001Block039Part011
    + surrogateDiagTailX0RatChunk000Sub001Block039Part012
    + surrogateDiagTailX0RatChunk000Sub001Block039Part013
    + surrogateDiagTailX0RatChunk000Sub001Block039Part014
    + surrogateDiagTailX0RatChunk000Sub001Block039Part015
    + surrogateDiagTailX0RatChunk000Sub001Block039Part016
    + surrogateDiagTailX0RatChunk000Sub001Block039Part017
    + surrogateDiagTailX0RatChunk000Sub001Block039Part018
    + surrogateDiagTailX0RatChunk000Sub001Block039Part019

def surrogateDiagonalTailChunk000Sub001Block039TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block039Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block039Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block039Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block039Part020
    + surrogateDiagTailX0RatChunk000Sub001Block039Part021
    + surrogateDiagTailX0RatChunk000Sub001Block039Part022
    + surrogateDiagTailX0RatChunk000Sub001Block039Part023
    + surrogateDiagTailX0RatChunk000Sub001Block039Part024

def surrogateDiagonalTailChunk000Sub001Block039Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block039HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block039MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block039TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block039 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block039Part000
    + surrogateDiagTailX0RatChunk000Sub001Block039Part001
    + surrogateDiagTailX0RatChunk000Sub001Block039Part002
    + surrogateDiagTailX0RatChunk000Sub001Block039Part003
    + surrogateDiagTailX0RatChunk000Sub001Block039Part004
    + surrogateDiagTailX0RatChunk000Sub001Block039Part005
    + surrogateDiagTailX0RatChunk000Sub001Block039Part006
    + surrogateDiagTailX0RatChunk000Sub001Block039Part007
    + surrogateDiagTailX0RatChunk000Sub001Block039Part008
    + surrogateDiagTailX0RatChunk000Sub001Block039Part009
    + surrogateDiagTailX0RatChunk000Sub001Block039Part010
    + surrogateDiagTailX0RatChunk000Sub001Block039Part011
    + surrogateDiagTailX0RatChunk000Sub001Block039Part012
    + surrogateDiagTailX0RatChunk000Sub001Block039Part013
    + surrogateDiagTailX0RatChunk000Sub001Block039Part014
    + surrogateDiagTailX0RatChunk000Sub001Block039Part015
    + surrogateDiagTailX0RatChunk000Sub001Block039Part016
    + surrogateDiagTailX0RatChunk000Sub001Block039Part017
    + surrogateDiagTailX0RatChunk000Sub001Block039Part018
    + surrogateDiagTailX0RatChunk000Sub001Block039Part019
    + surrogateDiagTailX0RatChunk000Sub001Block039Part020
    + surrogateDiagTailX0RatChunk000Sub001Block039Part021
    + surrogateDiagTailX0RatChunk000Sub001Block039Part022
    + surrogateDiagTailX0RatChunk000Sub001Block039Part023
    + surrogateDiagTailX0RatChunk000Sub001Block039Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block039_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block039Head + surrogateDiagTailX0RatChunk000Sub001Block039Mid + surrogateDiagTailX0RatChunk000Sub001Block039Tail =
      surrogateDiagTailX0RatChunk000Sub001Block039 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block039Head surrogateDiagTailX0RatChunk000Sub001Block039Mid surrogateDiagTailX0RatChunk000Sub001Block039Tail surrogateDiagTailX0RatChunk000Sub001Block039
  ring

def SurrogateDiagonalTailChunk000Sub001Block039HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block039HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block039Head

def SurrogateDiagonalTailChunk000Sub001Block039MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block039MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block039Mid

def SurrogateDiagonalTailChunk000Sub001Block039TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block039TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block039Tail

theorem surrogateDiagonalTailChunk000Sub001Block039_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block039HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block039MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block039TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block039Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block039 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block039HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block039MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block039TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block039Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block039_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
