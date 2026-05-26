import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [100,110). -/

/-- Block 100 covers tail-support indices [12500,12525) and q from 20611 to 20654. -/

def TailChunk001Sub000Block100Part000SupportExplicit : Finset ℕ :=
  ([20611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block100Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20611
    = surrogateDiagTailX0RatChunk001Sub000Block100Part000

theorem surrogateDiagonalTailChunk001Sub000Block100Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part000] using hcert

def TailChunk001Sub000Block100Part001SupportExplicit : Finset ℕ :=
  ([20613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part001 : ℚ :=
  (11801725063 : ℚ) / 356478860653427520

def SurrogateDiagonalTailChunk001Sub000Block100Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20613
    = surrogateDiagTailX0RatChunk001Sub000Block100Part001

theorem surrogateDiagonalTailChunk001Sub000Block100Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part001] using hcert

def TailChunk001Sub000Block100Part002SupportExplicit : Finset ℕ :=
  ([20614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part002 : ℚ :=
  (9222937 : ℚ) / 639748091713536

def SurrogateDiagonalTailChunk001Sub000Block100Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20614
    = surrogateDiagTailX0RatChunk001Sub000Block100Part002

theorem surrogateDiagonalTailChunk001Sub000Block100Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part002] using hcert

def TailChunk001Sub000Block100Part003SupportExplicit : Finset ℕ :=
  ([20615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part003 : ℚ :=
  (22827125407 : ℚ) / 940558043145830400

def SurrogateDiagonalTailChunk001Sub000Block100Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20615
    = surrogateDiagTailX0RatChunk001Sub000Block100Part003

theorem surrogateDiagonalTailChunk001Sub000Block100Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part003] using hcert

def TailChunk001Sub000Block100Part004SupportExplicit : Finset ℕ :=
  ([20617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part004 : ℚ :=
  (23063594925 : ℚ) / 69058300357288706048

def SurrogateDiagonalTailChunk001Sub000Block100Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20617
    = surrogateDiagTailX0RatChunk001Sub000Block100Part004

theorem surrogateDiagonalTailChunk001Sub000Block100Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part004] using hcert

def TailChunk001Sub000Block100Part005SupportExplicit : Finset ℕ :=
  ([20621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part005 : ℚ :=
  (372014474275 : ℚ) / 353604081161179496448

def SurrogateDiagonalTailChunk001Sub000Block100Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20621
    = surrogateDiagTailX0RatChunk001Sub000Block100Part005

theorem surrogateDiagonalTailChunk001Sub000Block100Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part005] using hcert

def TailChunk001Sub000Block100Part006SupportExplicit : Finset ℕ :=
  ([20622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part006 : ℚ :=
  (201021563 : ℚ) / 738042106905600

def SurrogateDiagonalTailChunk001Sub000Block100Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20622
    = surrogateDiagTailX0RatChunk001Sub000Block100Part006

theorem surrogateDiagonalTailChunk001Sub000Block100Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part006] using hcert

def TailChunk001Sub000Block100Part007SupportExplicit : Finset ℕ :=
  ([20623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part007 : ℚ :=
  (6161247661 : ℚ) / 16260791608116019200

def SurrogateDiagonalTailChunk001Sub000Block100Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20623
    = surrogateDiagTailX0RatChunk001Sub000Block100Part007

theorem surrogateDiagonalTailChunk001Sub000Block100Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part007] using hcert

def TailChunk001Sub000Block100Part008SupportExplicit : Finset ℕ :=
  ([20626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block100Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20626
    = surrogateDiagTailX0RatChunk001Sub000Block100Part008

theorem surrogateDiagonalTailChunk001Sub000Block100Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part008] using hcert

def TailChunk001Sub000Block100Part009SupportExplicit : Finset ℕ :=
  ([20627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block100Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20627
    = surrogateDiagTailX0RatChunk001Sub000Block100Part009

theorem surrogateDiagonalTailChunk001Sub000Block100Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part009] using hcert

def TailChunk001Sub000Block100Part010SupportExplicit : Finset ℕ :=
  ([20630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part010 : ℚ :=
  (532624710025 : ℚ) / 11572347542922283008

def SurrogateDiagonalTailChunk001Sub000Block100Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20630
    = surrogateDiagTailX0RatChunk001Sub000Block100Part010

theorem surrogateDiagonalTailChunk001Sub000Block100Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part010] using hcert

def TailChunk001Sub000Block100Part011SupportExplicit : Finset ℕ :=
  ([20633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part011 : ℚ :=
  (157893928825 : ℚ) / 412054467972574612608

def SurrogateDiagonalTailChunk001Sub000Block100Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20633
    = surrogateDiagTailX0RatChunk001Sub000Block100Part011

theorem surrogateDiagonalTailChunk001Sub000Block100Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part011] using hcert

def TailChunk001Sub000Block100Part012SupportExplicit : Finset ℕ :=
  ([20634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part012 : ℚ :=
  (31309570921 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk001Sub000Block100Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20634
    = surrogateDiagTailX0RatChunk001Sub000Block100Part012

theorem surrogateDiagonalTailChunk001Sub000Block100Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part012] using hcert

def TailChunk001Sub000Block100Part013SupportExplicit : Finset ℕ :=
  ([20635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part013 : ℚ :=
  (355080973875 : ℚ) / 61839000860626917376

def SurrogateDiagonalTailChunk001Sub000Block100Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20635
    = surrogateDiagTailX0RatChunk001Sub000Block100Part013

theorem surrogateDiagonalTailChunk001Sub000Block100Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part013] using hcert

def TailChunk001Sub000Block100Part014SupportExplicit : Finset ℕ :=
  ([20638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part014 : ℚ :=
  (188359015525 : ℚ) / 22100255072573718528

def SurrogateDiagonalTailChunk001Sub000Block100Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20638
    = surrogateDiagTailX0RatChunk001Sub000Block100Part014

theorem surrogateDiagonalTailChunk001Sub000Block100Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part014] using hcert

def TailChunk001Sub000Block100Part015SupportExplicit : Finset ℕ :=
  ([20639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block100Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20639
    = surrogateDiagTailX0RatChunk001Sub000Block100Part015

theorem surrogateDiagonalTailChunk001Sub000Block100Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part015] using hcert

def TailChunk001Sub000Block100Part016SupportExplicit : Finset ℕ :=
  ([20641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block100Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20641
    = surrogateDiagTailX0RatChunk001Sub000Block100Part016

theorem surrogateDiagonalTailChunk001Sub000Block100Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part016] using hcert

def TailChunk001Sub000Block100Part017SupportExplicit : Finset ℕ :=
  ([20642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block100Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20642
    = surrogateDiagTailX0RatChunk001Sub000Block100Part017

theorem surrogateDiagonalTailChunk001Sub000Block100Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part017] using hcert

def TailChunk001Sub000Block100Part018SupportExplicit : Finset ℕ :=
  ([20643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part018 : ℚ :=
  (693989926075 : ℚ) / 12054183624262881792

def SurrogateDiagonalTailChunk001Sub000Block100Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20643
    = surrogateDiagTailX0RatChunk001Sub000Block100Part018

theorem surrogateDiagonalTailChunk001Sub000Block100Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part018] using hcert

def TailChunk001Sub000Block100Part019SupportExplicit : Finset ℕ :=
  ([20645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part019 : ℚ :=
  (1066274671375 : ℚ) / 185876967555090874368

def SurrogateDiagonalTailChunk001Sub000Block100Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20645
    = surrogateDiagTailX0RatChunk001Sub000Block100Part019

theorem surrogateDiagonalTailChunk001Sub000Block100Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part019] using hcert

def TailChunk001Sub000Block100Part020SupportExplicit : Finset ℕ :=
  ([20647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part020 : ℚ :=
  (3787122139 : ℚ) / 1769783518694553600

def SurrogateDiagonalTailChunk001Sub000Block100Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20647
    = surrogateDiagTailX0RatChunk001Sub000Block100Part020

theorem surrogateDiagonalTailChunk001Sub000Block100Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part020] using hcert

def TailChunk001Sub000Block100Part021SupportExplicit : Finset ℕ :=
  ([20649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part021 : ℚ :=
  (1480372632725 : ℚ) / 44872009507015447104

def SurrogateDiagonalTailChunk001Sub000Block100Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20649
    = surrogateDiagTailX0RatChunk001Sub000Block100Part021

theorem surrogateDiagonalTailChunk001Sub000Block100Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part021] using hcert

def TailChunk001Sub000Block100Part022SupportExplicit : Finset ℕ :=
  ([20651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part022 : ℚ :=
  (7743176425 : ℚ) / 35749830638262288384

def SurrogateDiagonalTailChunk001Sub000Block100Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20651
    = surrogateDiagTailX0RatChunk001Sub000Block100Part022

theorem surrogateDiagonalTailChunk001Sub000Block100Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part022] using hcert

def TailChunk001Sub000Block100Part023SupportExplicit : Finset ℕ :=
  ([20653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part023 : ℚ :=
  (186944476025 : ℚ) / 182560234380282391104

def SurrogateDiagonalTailChunk001Sub000Block100Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20653
    = surrogateDiagTailX0RatChunk001Sub000Block100Part023

theorem surrogateDiagonalTailChunk001Sub000Block100Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part023] using hcert

def TailChunk001Sub000Block100Part024SupportExplicit : Finset ℕ :=
  ([20654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block100Part024 : ℚ :=
  (6023826825 : ℚ) / 983146859910397952

def SurrogateDiagonalTailChunk001Sub000Block100Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20654
    = surrogateDiagTailX0RatChunk001Sub000Block100Part024

theorem surrogateDiagonalTailChunk001Sub000Block100Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block100Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block100Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block100Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block100Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block100Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block100Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block100HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block100Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block100Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block100Part000
    + surrogateDiagTailX0RatChunk001Sub000Block100Part001
    + surrogateDiagTailX0RatChunk001Sub000Block100Part002
    + surrogateDiagTailX0RatChunk001Sub000Block100Part003
    + surrogateDiagTailX0RatChunk001Sub000Block100Part004
    + surrogateDiagTailX0RatChunk001Sub000Block100Part005
    + surrogateDiagTailX0RatChunk001Sub000Block100Part006
    + surrogateDiagTailX0RatChunk001Sub000Block100Part007
    + surrogateDiagTailX0RatChunk001Sub000Block100Part008
    + surrogateDiagTailX0RatChunk001Sub000Block100Part009

def surrogateDiagonalTailChunk001Sub000Block100MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block100Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block100Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block100Part010
    + surrogateDiagTailX0RatChunk001Sub000Block100Part011
    + surrogateDiagTailX0RatChunk001Sub000Block100Part012
    + surrogateDiagTailX0RatChunk001Sub000Block100Part013
    + surrogateDiagTailX0RatChunk001Sub000Block100Part014
    + surrogateDiagTailX0RatChunk001Sub000Block100Part015
    + surrogateDiagTailX0RatChunk001Sub000Block100Part016
    + surrogateDiagTailX0RatChunk001Sub000Block100Part017
    + surrogateDiagTailX0RatChunk001Sub000Block100Part018
    + surrogateDiagTailX0RatChunk001Sub000Block100Part019

def surrogateDiagonalTailChunk001Sub000Block100TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block100Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block100Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block100Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block100Part020
    + surrogateDiagTailX0RatChunk001Sub000Block100Part021
    + surrogateDiagTailX0RatChunk001Sub000Block100Part022
    + surrogateDiagTailX0RatChunk001Sub000Block100Part023
    + surrogateDiagTailX0RatChunk001Sub000Block100Part024

def surrogateDiagonalTailChunk001Sub000Block100Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block100HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block100MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block100TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block100 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block100Part000
    + surrogateDiagTailX0RatChunk001Sub000Block100Part001
    + surrogateDiagTailX0RatChunk001Sub000Block100Part002
    + surrogateDiagTailX0RatChunk001Sub000Block100Part003
    + surrogateDiagTailX0RatChunk001Sub000Block100Part004
    + surrogateDiagTailX0RatChunk001Sub000Block100Part005
    + surrogateDiagTailX0RatChunk001Sub000Block100Part006
    + surrogateDiagTailX0RatChunk001Sub000Block100Part007
    + surrogateDiagTailX0RatChunk001Sub000Block100Part008
    + surrogateDiagTailX0RatChunk001Sub000Block100Part009
    + surrogateDiagTailX0RatChunk001Sub000Block100Part010
    + surrogateDiagTailX0RatChunk001Sub000Block100Part011
    + surrogateDiagTailX0RatChunk001Sub000Block100Part012
    + surrogateDiagTailX0RatChunk001Sub000Block100Part013
    + surrogateDiagTailX0RatChunk001Sub000Block100Part014
    + surrogateDiagTailX0RatChunk001Sub000Block100Part015
    + surrogateDiagTailX0RatChunk001Sub000Block100Part016
    + surrogateDiagTailX0RatChunk001Sub000Block100Part017
    + surrogateDiagTailX0RatChunk001Sub000Block100Part018
    + surrogateDiagTailX0RatChunk001Sub000Block100Part019
    + surrogateDiagTailX0RatChunk001Sub000Block100Part020
    + surrogateDiagTailX0RatChunk001Sub000Block100Part021
    + surrogateDiagTailX0RatChunk001Sub000Block100Part022
    + surrogateDiagTailX0RatChunk001Sub000Block100Part023
    + surrogateDiagTailX0RatChunk001Sub000Block100Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block100_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block100Head + surrogateDiagTailX0RatChunk001Sub000Block100Mid + surrogateDiagTailX0RatChunk001Sub000Block100Tail =
      surrogateDiagTailX0RatChunk001Sub000Block100 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block100Head surrogateDiagTailX0RatChunk001Sub000Block100Mid surrogateDiagTailX0RatChunk001Sub000Block100Tail surrogateDiagTailX0RatChunk001Sub000Block100
  ring

def SurrogateDiagonalTailChunk001Sub000Block100HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block100HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block100Head

def SurrogateDiagonalTailChunk001Sub000Block100MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block100MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block100Mid

def SurrogateDiagonalTailChunk001Sub000Block100TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block100TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block100Tail

theorem surrogateDiagonalTailChunk001Sub000Block100_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block100HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block100MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block100TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block100Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block100 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block100HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block100MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block100TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block100Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block100_eq_head_add_mid_add_tail

/-- Block 101 covers tail-support indices [12525,12550) and q from 20657 to 20697. -/

def TailChunk001Sub000Block101Part000SupportExplicit : Finset ℕ :=
  ([20657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part000 : ℚ :=
  (670379341325 : ℚ) / 87651752859083096064

def SurrogateDiagonalTailChunk001Sub000Block101Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20657
    = surrogateDiagTailX0RatChunk001Sub000Block101Part000

theorem surrogateDiagonalTailChunk001Sub000Block101Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part000] using hcert

def TailChunk001Sub000Block101Part001SupportExplicit : Finset ℕ :=
  ([20658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part001 : ℚ :=
  (212589313 : ℚ) / 1010959947399168

def SurrogateDiagonalTailChunk001Sub000Block101Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20658
    = surrogateDiagTailX0RatChunk001Sub000Block101Part001

theorem surrogateDiagonalTailChunk001Sub000Block101Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part001] using hcert

def TailChunk001Sub000Block101Part002SupportExplicit : Finset ℕ :=
  ([20659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part002 : ℚ :=
  (111506382625 : ℚ) / 424965112271841558528

def SurrogateDiagonalTailChunk001Sub000Block101Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20659
    = surrogateDiagTailX0RatChunk001Sub000Block101Part002

theorem surrogateDiagonalTailChunk001Sub000Block101Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part002] using hcert

def TailChunk001Sub000Block101Part003SupportExplicit : Finset ℕ :=
  ([20661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part003 : ℚ :=
  (2088603611 : ℚ) / 58276827050803200

def SurrogateDiagonalTailChunk001Sub000Block101Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20661
    = surrogateDiagTailX0RatChunk001Sub000Block101Part003

theorem surrogateDiagonalTailChunk001Sub000Block101Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part003] using hcert

def TailChunk001Sub000Block101Part004SupportExplicit : Finset ℕ :=
  ([20662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block101Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20662
    = surrogateDiagTailX0RatChunk001Sub000Block101Part004

theorem surrogateDiagonalTailChunk001Sub000Block101Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part004] using hcert

def TailChunk001Sub000Block101Part005SupportExplicit : Finset ℕ :=
  ([20663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block101Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20663
    = surrogateDiagTailX0RatChunk001Sub000Block101Part005

theorem surrogateDiagonalTailChunk001Sub000Block101Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part005] using hcert

def TailChunk001Sub000Block101Part006SupportExplicit : Finset ℕ :=
  ([20665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part006 : ℚ :=
  (2135001049525 : ℚ) / 186598468764923363328

def SurrogateDiagonalTailChunk001Sub000Block101Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20665
    = surrogateDiagTailX0RatChunk001Sub000Block101Part006

theorem surrogateDiagonalTailChunk001Sub000Block101Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part006] using hcert

def TailChunk001Sub000Block101Part007SupportExplicit : Finset ℕ :=
  ([20666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block101Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20666
    = surrogateDiagTailX0RatChunk001Sub000Block101Part007

theorem surrogateDiagonalTailChunk001Sub000Block101Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part007] using hcert

def TailChunk001Sub000Block101Part008SupportExplicit : Finset ℕ :=
  ([20669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part008 : ℚ :=
  (369916783 : ℚ) / 259195802741789400

def SurrogateDiagonalTailChunk001Sub000Block101Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20669
    = surrogateDiagTailX0RatChunk001Sub000Block101Part008

theorem surrogateDiagonalTailChunk001Sub000Block101Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part008] using hcert

def TailChunk001Sub000Block101Part009SupportExplicit : Finset ℕ :=
  ([20670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part009 : ℚ :=
  (76010452325 : ℚ) / 129402873267093504

def SurrogateDiagonalTailChunk001Sub000Block101Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20670
    = surrogateDiagTailX0RatChunk001Sub000Block101Part009

theorem surrogateDiagonalTailChunk001Sub000Block101Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part009] using hcert

def TailChunk001Sub000Block101Part010SupportExplicit : Finset ℕ :=
  ([20671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part010 : ℚ :=
  (545472488675 : ℚ) / 123045936877676150784

def SurrogateDiagonalTailChunk001Sub000Block101Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20671
    = surrogateDiagTailX0RatChunk001Sub000Block101Part010

theorem surrogateDiagonalTailChunk001Sub000Block101Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part010] using hcert

def TailChunk001Sub000Block101Part011SupportExplicit : Finset ℕ :=
  ([20674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block101Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20674
    = surrogateDiagTailX0RatChunk001Sub000Block101Part011

theorem surrogateDiagonalTailChunk001Sub000Block101Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part011] using hcert

def TailChunk001Sub000Block101Part012SupportExplicit : Finset ℕ :=
  ([20677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part012 : ℚ :=
  (24927818617 : ℚ) / 11665267917882163200

def SurrogateDiagonalTailChunk001Sub000Block101Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20677
    = surrogateDiagTailX0RatChunk001Sub000Block101Part012

theorem surrogateDiagonalTailChunk001Sub000Block101Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part012] using hcert

def TailChunk001Sub000Block101Part013SupportExplicit : Finset ℕ :=
  ([20679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part013 : ℚ :=
  (117169510771 : ℚ) / 3263502314844979200

def SurrogateDiagonalTailChunk001Sub000Block101Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20679
    = surrogateDiagTailX0RatChunk001Sub000Block101Part013

theorem surrogateDiagonalTailChunk001Sub000Block101Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part013] using hcert

def TailChunk001Sub000Block101Part014SupportExplicit : Finset ℕ :=
  ([20681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block101Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20681
    = surrogateDiagTailX0RatChunk001Sub000Block101Part014

theorem surrogateDiagonalTailChunk001Sub000Block101Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part014] using hcert

def TailChunk001Sub000Block101Part015SupportExplicit : Finset ℕ :=
  ([20683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part015 : ℚ :=
  (79231372475 : ℚ) / 30110398154575183872

def SurrogateDiagonalTailChunk001Sub000Block101Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20683
    = surrogateDiagTailX0RatChunk001Sub000Block101Part015

theorem surrogateDiagonalTailChunk001Sub000Block101Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part015] using hcert

def TailChunk001Sub000Block101Part016SupportExplicit : Finset ℕ :=
  ([20685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part016 : ℚ :=
  (1260669533075 : ℚ) / 9794586322428493824

def SurrogateDiagonalTailChunk001Sub000Block101Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20685
    = surrogateDiagTailX0RatChunk001Sub000Block101Part016

theorem surrogateDiagonalTailChunk001Sub000Block101Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part016] using hcert

def TailChunk001Sub000Block101Part017SupportExplicit : Finset ℕ :=
  ([20686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block101Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20686
    = surrogateDiagTailX0RatChunk001Sub000Block101Part017

theorem surrogateDiagonalTailChunk001Sub000Block101Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part017] using hcert

def TailChunk001Sub000Block101Part018SupportExplicit : Finset ℕ :=
  ([20687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part018 : ℚ :=
  (3567417091 : ℚ) / 17322378342912000000

def SurrogateDiagonalTailChunk001Sub000Block101Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20687
    = surrogateDiagTailX0RatChunk001Sub000Block101Part018

theorem surrogateDiagonalTailChunk001Sub000Block101Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part018] using hcert

def TailChunk001Sub000Block101Part019SupportExplicit : Finset ℕ :=
  ([20689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part019 : ℚ :=
  (374441017075 : ℚ) / 358295281835911938048

def SurrogateDiagonalTailChunk001Sub000Block101Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20689
    = surrogateDiagTailX0RatChunk001Sub000Block101Part019

theorem surrogateDiagonalTailChunk001Sub000Block101Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part019] using hcert

def TailChunk001Sub000Block101Part020SupportExplicit : Finset ℕ :=
  ([20690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part020 : ℚ :=
  (401398114775 : ℚ) / 5853814636781912064

def SurrogateDiagonalTailChunk001Sub000Block101Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20690
    = surrogateDiagTailX0RatChunk001Sub000Block101Part020

theorem surrogateDiagonalTailChunk001Sub000Block101Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part020] using hcert

def TailChunk001Sub000Block101Part021SupportExplicit : Finset ℕ :=
  ([20693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block101Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20693
    = surrogateDiagTailX0RatChunk001Sub000Block101Part021

theorem surrogateDiagonalTailChunk001Sub000Block101Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part021] using hcert

def TailChunk001Sub000Block101Part022SupportExplicit : Finset ℕ :=
  ([20694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part022 : ℚ :=
  (743207781275 : ℚ) / 2827391021123518464

def SurrogateDiagonalTailChunk001Sub000Block101Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20694
    = surrogateDiagTailX0RatChunk001Sub000Block101Part022

theorem surrogateDiagonalTailChunk001Sub000Block101Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part022] using hcert

def TailChunk001Sub000Block101Part023SupportExplicit : Finset ℕ :=
  ([20695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part023 : ℚ :=
  (2141202307225 : ℚ) / 187684656353984759808

def SurrogateDiagonalTailChunk001Sub000Block101Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20695
    = surrogateDiagTailX0RatChunk001Sub000Block101Part023

theorem surrogateDiagonalTailChunk001Sub000Block101Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part023] using hcert

def TailChunk001Sub000Block101Part024SupportExplicit : Finset ℕ :=
  ([20697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block101Part024 : ℚ :=
  (1487262632525 : ℚ) / 45290759749065996864

def SurrogateDiagonalTailChunk001Sub000Block101Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20697
    = surrogateDiagTailX0RatChunk001Sub000Block101Part024

theorem surrogateDiagonalTailChunk001Sub000Block101Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block101Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block101Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block101Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block101Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block101Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block101Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block101HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block101Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block101Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block101Part000
    + surrogateDiagTailX0RatChunk001Sub000Block101Part001
    + surrogateDiagTailX0RatChunk001Sub000Block101Part002
    + surrogateDiagTailX0RatChunk001Sub000Block101Part003
    + surrogateDiagTailX0RatChunk001Sub000Block101Part004
    + surrogateDiagTailX0RatChunk001Sub000Block101Part005
    + surrogateDiagTailX0RatChunk001Sub000Block101Part006
    + surrogateDiagTailX0RatChunk001Sub000Block101Part007
    + surrogateDiagTailX0RatChunk001Sub000Block101Part008
    + surrogateDiagTailX0RatChunk001Sub000Block101Part009

def surrogateDiagonalTailChunk001Sub000Block101MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block101Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block101Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block101Part010
    + surrogateDiagTailX0RatChunk001Sub000Block101Part011
    + surrogateDiagTailX0RatChunk001Sub000Block101Part012
    + surrogateDiagTailX0RatChunk001Sub000Block101Part013
    + surrogateDiagTailX0RatChunk001Sub000Block101Part014
    + surrogateDiagTailX0RatChunk001Sub000Block101Part015
    + surrogateDiagTailX0RatChunk001Sub000Block101Part016
    + surrogateDiagTailX0RatChunk001Sub000Block101Part017
    + surrogateDiagTailX0RatChunk001Sub000Block101Part018
    + surrogateDiagTailX0RatChunk001Sub000Block101Part019

def surrogateDiagonalTailChunk001Sub000Block101TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block101Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block101Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block101Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block101Part020
    + surrogateDiagTailX0RatChunk001Sub000Block101Part021
    + surrogateDiagTailX0RatChunk001Sub000Block101Part022
    + surrogateDiagTailX0RatChunk001Sub000Block101Part023
    + surrogateDiagTailX0RatChunk001Sub000Block101Part024

def surrogateDiagonalTailChunk001Sub000Block101Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block101HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block101MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block101TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block101 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block101Part000
    + surrogateDiagTailX0RatChunk001Sub000Block101Part001
    + surrogateDiagTailX0RatChunk001Sub000Block101Part002
    + surrogateDiagTailX0RatChunk001Sub000Block101Part003
    + surrogateDiagTailX0RatChunk001Sub000Block101Part004
    + surrogateDiagTailX0RatChunk001Sub000Block101Part005
    + surrogateDiagTailX0RatChunk001Sub000Block101Part006
    + surrogateDiagTailX0RatChunk001Sub000Block101Part007
    + surrogateDiagTailX0RatChunk001Sub000Block101Part008
    + surrogateDiagTailX0RatChunk001Sub000Block101Part009
    + surrogateDiagTailX0RatChunk001Sub000Block101Part010
    + surrogateDiagTailX0RatChunk001Sub000Block101Part011
    + surrogateDiagTailX0RatChunk001Sub000Block101Part012
    + surrogateDiagTailX0RatChunk001Sub000Block101Part013
    + surrogateDiagTailX0RatChunk001Sub000Block101Part014
    + surrogateDiagTailX0RatChunk001Sub000Block101Part015
    + surrogateDiagTailX0RatChunk001Sub000Block101Part016
    + surrogateDiagTailX0RatChunk001Sub000Block101Part017
    + surrogateDiagTailX0RatChunk001Sub000Block101Part018
    + surrogateDiagTailX0RatChunk001Sub000Block101Part019
    + surrogateDiagTailX0RatChunk001Sub000Block101Part020
    + surrogateDiagTailX0RatChunk001Sub000Block101Part021
    + surrogateDiagTailX0RatChunk001Sub000Block101Part022
    + surrogateDiagTailX0RatChunk001Sub000Block101Part023
    + surrogateDiagTailX0RatChunk001Sub000Block101Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block101_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block101Head + surrogateDiagTailX0RatChunk001Sub000Block101Mid + surrogateDiagTailX0RatChunk001Sub000Block101Tail =
      surrogateDiagTailX0RatChunk001Sub000Block101 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block101Head surrogateDiagTailX0RatChunk001Sub000Block101Mid surrogateDiagTailX0RatChunk001Sub000Block101Tail surrogateDiagTailX0RatChunk001Sub000Block101
  ring

def SurrogateDiagonalTailChunk001Sub000Block101HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block101HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block101Head

def SurrogateDiagonalTailChunk001Sub000Block101MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block101MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block101Mid

def SurrogateDiagonalTailChunk001Sub000Block101TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block101TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block101Tail

theorem surrogateDiagonalTailChunk001Sub000Block101_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block101HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block101MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block101TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block101Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block101 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block101HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block101MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block101TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block101Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block101_eq_head_add_mid_add_tail

/-- Block 102 covers tail-support indices [12550,12575) and q from 20698 to 20735. -/

def TailChunk001Sub000Block102Part000SupportExplicit : Finset ℕ :=
  ([20698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part000 : ℚ :=
  (1282112069 : ℚ) / 528699225909441600

def SurrogateDiagonalTailChunk001Sub000Block102Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20698
    = surrogateDiagTailX0RatChunk001Sub000Block102Part000

theorem surrogateDiagonalTailChunk001Sub000Block102Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part000] using hcert

def TailChunk001Sub000Block102Part001SupportExplicit : Finset ℕ :=
  ([20699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part001 : ℚ :=
  (547995897625 : ℚ) / 247428418538461022208

def SurrogateDiagonalTailChunk001Sub000Block102Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20699
    = surrogateDiagTailX0RatChunk001Sub000Block102Part001

theorem surrogateDiagonalTailChunk001Sub000Block102Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part001] using hcert

def TailChunk001Sub000Block102Part002SupportExplicit : Finset ℕ :=
  ([20701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part002 : ℚ :=
  (89558532925 : ℚ) / 434079321442751472768

def SurrogateDiagonalTailChunk001Sub000Block102Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20701
    = surrogateDiagTailX0RatChunk001Sub000Block102Part002

theorem surrogateDiagonalTailChunk001Sub000Block102Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part002] using hcert

def TailChunk001Sub000Block102Part003SupportExplicit : Finset ℕ :=
  ([20702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part003 : ℚ :=
  (558062459 : ℚ) / 39045255489600000

def SurrogateDiagonalTailChunk001Sub000Block102Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20702
    = surrogateDiagTailX0RatChunk001Sub000Block102Part003

theorem surrogateDiagonalTailChunk001Sub000Block102Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part003] using hcert

def TailChunk001Sub000Block102Part004SupportExplicit : Finset ℕ :=
  ([20703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part004 : ℚ :=
  (1467714801275 : ℚ) / 41085944493609083904

def SurrogateDiagonalTailChunk001Sub000Block102Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20703
    = surrogateDiagTailX0RatChunk001Sub000Block102Part004

theorem surrogateDiagonalTailChunk001Sub000Block102Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part004] using hcert

def TailChunk001Sub000Block102Part005SupportExplicit : Finset ℕ :=
  ([20705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part005 : ℚ :=
  (9389701091 : ℚ) / 1310982144000000000

def SurrogateDiagonalTailChunk001Sub000Block102Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20705
    = surrogateDiagTailX0RatChunk001Sub000Block102Part005

theorem surrogateDiagonalTailChunk001Sub000Block102Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part005] using hcert

def TailChunk001Sub000Block102Part006SupportExplicit : Finset ℕ :=
  ([20706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part006 : ℚ :=
  (23506468975 : ℚ) / 38678545953718272

def SurrogateDiagonalTailChunk001Sub000Block102Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20706
    = surrogateDiagTailX0RatChunk001Sub000Block102Part006

theorem surrogateDiagonalTailChunk001Sub000Block102Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part006] using hcert

def TailChunk001Sub000Block102Part007SupportExplicit : Finset ℕ :=
  ([20707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block102Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20707
    = surrogateDiagTailX0RatChunk001Sub000Block102Part007

theorem surrogateDiagonalTailChunk001Sub000Block102Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part007] using hcert

def TailChunk001Sub000Block102Part008SupportExplicit : Finset ℕ :=
  ([20710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part008 : ℚ :=
  (208355230925 : ℚ) / 3047408059792490496

def SurrogateDiagonalTailChunk001Sub000Block102Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20710
    = surrogateDiagTailX0RatChunk001Sub000Block102Part008

theorem surrogateDiagonalTailChunk001Sub000Block102Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part008] using hcert

def TailChunk001Sub000Block102Part009SupportExplicit : Finset ℕ :=
  ([20711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part009 : ℚ :=
  (89399943625 : ℚ) / 435100984599686105088

def SurrogateDiagonalTailChunk001Sub000Block102Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20711
    = surrogateDiagTailX0RatChunk001Sub000Block102Part009

theorem surrogateDiagonalTailChunk001Sub000Block102Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part009] using hcert

def TailChunk001Sub000Block102Part010SupportExplicit : Finset ℕ :=
  ([20713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part010 : ℚ :=
  (2168852659 : ℚ) / 247666498242969600

def SurrogateDiagonalTailChunk001Sub000Block102Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20713
    = surrogateDiagTailX0RatChunk001Sub000Block102Part010

theorem surrogateDiagonalTailChunk001Sub000Block102Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part010] using hcert

def TailChunk001Sub000Block102Part011SupportExplicit : Finset ℕ :=
  ([20714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block102Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20714
    = surrogateDiagTailX0RatChunk001Sub000Block102Part011

theorem surrogateDiagonalTailChunk001Sub000Block102Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part011] using hcert

def TailChunk001Sub000Block102Part012SupportExplicit : Finset ℕ :=
  ([20715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part012 : ℚ :=
  (50038599089 : ℚ) / 742904772172185600

def SurrogateDiagonalTailChunk001Sub000Block102Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20715
    = surrogateDiagTailX0RatChunk001Sub000Block102Part012

theorem surrogateDiagonalTailChunk001Sub000Block102Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part012] using hcert

def TailChunk001Sub000Block102Part013SupportExplicit : Finset ℕ :=
  ([20717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block102Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20717
    = surrogateDiagTailX0RatChunk001Sub000Block102Part013

theorem surrogateDiagonalTailChunk001Sub000Block102Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part013] using hcert

def TailChunk001Sub000Block102Part014SupportExplicit : Finset ℕ :=
  ([20719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block102Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20719
    = surrogateDiagTailX0RatChunk001Sub000Block102Part014

theorem surrogateDiagonalTailChunk001Sub000Block102Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part014] using hcert

def TailChunk001Sub000Block102Part015SupportExplicit : Finset ℕ :=
  ([20721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part015 : ℚ :=
  (1490713632425 : ℚ) / 45501230540880811584

def SurrogateDiagonalTailChunk001Sub000Block102Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20721
    = surrogateDiagTailX0RatChunk001Sub000Block102Part015

theorem surrogateDiagonalTailChunk001Sub000Block102Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part015] using hcert

def TailChunk001Sub000Block102Part016SupportExplicit : Finset ℕ :=
  ([20722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part016 : ℚ :=
  (241121074375 : ℚ) / 20816327599072247808

def SurrogateDiagonalTailChunk001Sub000Block102Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20722
    = surrogateDiagTailX0RatChunk001Sub000Block102Part016

theorem surrogateDiagonalTailChunk001Sub000Block102Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part016] using hcert

def TailChunk001Sub000Block102Part017SupportExplicit : Finset ℕ :=
  ([20723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part017 : ℚ :=
  (712316919175 : ℚ) / 280679624815335702528

def SurrogateDiagonalTailChunk001Sub000Block102Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20723
    = surrogateDiagTailX0RatChunk001Sub000Block102Part017

theorem surrogateDiagonalTailChunk001Sub000Block102Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part017] using hcert

def TailChunk001Sub000Block102Part018SupportExplicit : Finset ℕ :=
  ([20726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part018 : ℚ :=
  (78663973 : ℚ) / 22946500651253760

def SurrogateDiagonalTailChunk001Sub000Block102Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20726
    = surrogateDiagTailX0RatChunk001Sub000Block102Part018

theorem surrogateDiagonalTailChunk001Sub000Block102Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part018] using hcert

def TailChunk001Sub000Block102Part019SupportExplicit : Finset ℕ :=
  ([20729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part019 : ℚ :=
  (12098781373 : ℚ) / 14821182752957827200

def SurrogateDiagonalTailChunk001Sub000Block102Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20729
    = surrogateDiagTailX0RatChunk001Sub000Block102Part019

theorem surrogateDiagonalTailChunk001Sub000Block102Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part019] using hcert

def TailChunk001Sub000Block102Part020SupportExplicit : Finset ℕ :=
  ([20730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part020 : ℚ :=
  (51271627789 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk001Sub000Block102Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20730
    = surrogateDiagTailX0RatChunk001Sub000Block102Part020

theorem surrogateDiagonalTailChunk001Sub000Block102Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part020] using hcert

def TailChunk001Sub000Block102Part021SupportExplicit : Finset ℕ :=
  ([20731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block102Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20731
    = surrogateDiagTailX0RatChunk001Sub000Block102Part021

theorem surrogateDiagonalTailChunk001Sub000Block102Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part021] using hcert

def TailChunk001Sub000Block102Part022SupportExplicit : Finset ℕ :=
  ([20733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part022 : ℚ :=
  (11939525059 : ℚ) / 364853924771315520

def SurrogateDiagonalTailChunk001Sub000Block102Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20733
    = surrogateDiagTailX0RatChunk001Sub000Block102Part022

theorem surrogateDiagonalTailChunk001Sub000Block102Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part022] using hcert

def TailChunk001Sub000Block102Part023SupportExplicit : Finset ℕ :=
  ([20734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part023 : ℚ :=
  (916467433 : ℚ) / 34551444459110400

def SurrogateDiagonalTailChunk001Sub000Block102Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20734
    = surrogateDiagTailX0RatChunk001Sub000Block102Part023

theorem surrogateDiagonalTailChunk001Sub000Block102Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part023] using hcert

def TailChunk001Sub000Block102Part024SupportExplicit : Finset ℕ :=
  ([20735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block102Part024 : ℚ :=
  (7364914841 : ℚ) / 407937789355622400

def SurrogateDiagonalTailChunk001Sub000Block102Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20735
    = surrogateDiagTailX0RatChunk001Sub000Block102Part024

theorem surrogateDiagonalTailChunk001Sub000Block102Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block102Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block102Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block102Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block102Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block102Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block102Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block102HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block102Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block102Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block102Part000
    + surrogateDiagTailX0RatChunk001Sub000Block102Part001
    + surrogateDiagTailX0RatChunk001Sub000Block102Part002
    + surrogateDiagTailX0RatChunk001Sub000Block102Part003
    + surrogateDiagTailX0RatChunk001Sub000Block102Part004
    + surrogateDiagTailX0RatChunk001Sub000Block102Part005
    + surrogateDiagTailX0RatChunk001Sub000Block102Part006
    + surrogateDiagTailX0RatChunk001Sub000Block102Part007
    + surrogateDiagTailX0RatChunk001Sub000Block102Part008
    + surrogateDiagTailX0RatChunk001Sub000Block102Part009

def surrogateDiagonalTailChunk001Sub000Block102MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block102Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block102Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block102Part010
    + surrogateDiagTailX0RatChunk001Sub000Block102Part011
    + surrogateDiagTailX0RatChunk001Sub000Block102Part012
    + surrogateDiagTailX0RatChunk001Sub000Block102Part013
    + surrogateDiagTailX0RatChunk001Sub000Block102Part014
    + surrogateDiagTailX0RatChunk001Sub000Block102Part015
    + surrogateDiagTailX0RatChunk001Sub000Block102Part016
    + surrogateDiagTailX0RatChunk001Sub000Block102Part017
    + surrogateDiagTailX0RatChunk001Sub000Block102Part018
    + surrogateDiagTailX0RatChunk001Sub000Block102Part019

def surrogateDiagonalTailChunk001Sub000Block102TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block102Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block102Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block102Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block102Part020
    + surrogateDiagTailX0RatChunk001Sub000Block102Part021
    + surrogateDiagTailX0RatChunk001Sub000Block102Part022
    + surrogateDiagTailX0RatChunk001Sub000Block102Part023
    + surrogateDiagTailX0RatChunk001Sub000Block102Part024

def surrogateDiagonalTailChunk001Sub000Block102Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block102HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block102MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block102TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block102 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block102Part000
    + surrogateDiagTailX0RatChunk001Sub000Block102Part001
    + surrogateDiagTailX0RatChunk001Sub000Block102Part002
    + surrogateDiagTailX0RatChunk001Sub000Block102Part003
    + surrogateDiagTailX0RatChunk001Sub000Block102Part004
    + surrogateDiagTailX0RatChunk001Sub000Block102Part005
    + surrogateDiagTailX0RatChunk001Sub000Block102Part006
    + surrogateDiagTailX0RatChunk001Sub000Block102Part007
    + surrogateDiagTailX0RatChunk001Sub000Block102Part008
    + surrogateDiagTailX0RatChunk001Sub000Block102Part009
    + surrogateDiagTailX0RatChunk001Sub000Block102Part010
    + surrogateDiagTailX0RatChunk001Sub000Block102Part011
    + surrogateDiagTailX0RatChunk001Sub000Block102Part012
    + surrogateDiagTailX0RatChunk001Sub000Block102Part013
    + surrogateDiagTailX0RatChunk001Sub000Block102Part014
    + surrogateDiagTailX0RatChunk001Sub000Block102Part015
    + surrogateDiagTailX0RatChunk001Sub000Block102Part016
    + surrogateDiagTailX0RatChunk001Sub000Block102Part017
    + surrogateDiagTailX0RatChunk001Sub000Block102Part018
    + surrogateDiagTailX0RatChunk001Sub000Block102Part019
    + surrogateDiagTailX0RatChunk001Sub000Block102Part020
    + surrogateDiagTailX0RatChunk001Sub000Block102Part021
    + surrogateDiagTailX0RatChunk001Sub000Block102Part022
    + surrogateDiagTailX0RatChunk001Sub000Block102Part023
    + surrogateDiagTailX0RatChunk001Sub000Block102Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block102_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block102Head + surrogateDiagTailX0RatChunk001Sub000Block102Mid + surrogateDiagTailX0RatChunk001Sub000Block102Tail =
      surrogateDiagTailX0RatChunk001Sub000Block102 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block102Head surrogateDiagTailX0RatChunk001Sub000Block102Mid surrogateDiagTailX0RatChunk001Sub000Block102Tail surrogateDiagTailX0RatChunk001Sub000Block102
  ring

def SurrogateDiagonalTailChunk001Sub000Block102HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block102HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block102Head

def SurrogateDiagonalTailChunk001Sub000Block102MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block102MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block102Mid

def SurrogateDiagonalTailChunk001Sub000Block102TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block102TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block102Tail

theorem surrogateDiagonalTailChunk001Sub000Block102_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block102HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block102MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block102TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block102Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block102 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block102HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block102MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block102TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block102Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block102_eq_head_add_mid_add_tail

/-- Block 103 covers tail-support indices [12575,12600) and q from 20737 to 20774. -/

def TailChunk001Sub000Block103Part000SupportExplicit : Finset ℕ :=
  ([20737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part000 : ℚ :=
  (101586265675 : ℚ) / 434419675691973869568

def SurrogateDiagonalTailChunk001Sub000Block103Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20737
    = surrogateDiagTailX0RatChunk001Sub000Block103Part000

theorem surrogateDiagonalTailChunk001Sub000Block103Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part000] using hcert

def TailChunk001Sub000Block103Part001SupportExplicit : Finset ℕ :=
  ([20738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block103Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20738
    = surrogateDiagTailX0RatChunk001Sub000Block103Part001

theorem surrogateDiagonalTailChunk001Sub000Block103Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part001] using hcert

def TailChunk001Sub000Block103Part002SupportExplicit : Finset ℕ :=
  ([20739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part002 : ℚ :=
  (58406594531 : ℚ) / 1574250188168217600

def SurrogateDiagonalTailChunk001Sub000Block103Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20739
    = surrogateDiagTailX0RatChunk001Sub000Block103Part002

theorem surrogateDiagonalTailChunk001Sub000Block103Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part002] using hcert

def TailChunk001Sub000Block103Part003SupportExplicit : Finset ℕ :=
  ([20741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part003 : ℚ :=
  (549167999675 : ℚ) / 124721717141797568064

def SurrogateDiagonalTailChunk001Sub000Block103Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20741
    = surrogateDiagTailX0RatChunk001Sub000Block103Part003

theorem surrogateDiagonalTailChunk001Sub000Block103Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part003] using hcert

def TailChunk001Sub000Block103Part004SupportExplicit : Finset ℕ :=
  ([20742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part004 : ℚ :=
  (746659090475 : ℚ) / 2853722773870608384

def SurrogateDiagonalTailChunk001Sub000Block103Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20742
    = surrogateDiagTailX0RatChunk001Sub000Block103Part004

theorem surrogateDiagonalTailChunk001Sub000Block103Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part004] using hcert

def TailChunk001Sub000Block103Part005SupportExplicit : Finset ℕ :=
  ([20743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block103Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20743
    = surrogateDiagTailX0RatChunk001Sub000Block103Part005

theorem surrogateDiagonalTailChunk001Sub000Block103Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part005] using hcert

def TailChunk001Sub000Block103Part006SupportExplicit : Finset ℕ :=
  ([20746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part006 : ℚ :=
  (690606121 : ℚ) / 23992611962880000

def SurrogateDiagonalTailChunk001Sub000Block103Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20746
    = surrogateDiagTailX0RatChunk001Sub000Block103Part006

theorem surrogateDiagonalTailChunk001Sub000Block103Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part006] using hcert

def TailChunk001Sub000Block103Part007SupportExplicit : Finset ℕ :=
  ([20747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block103Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20747
    = surrogateDiagTailX0RatChunk001Sub000Block103Part007

theorem surrogateDiagonalTailChunk001Sub000Block103Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part007] using hcert

def TailChunk001Sub000Block103Part008SupportExplicit : Finset ℕ :=
  ([20749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block103Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20749
    = surrogateDiagTailX0RatChunk001Sub000Block103Part008

theorem surrogateDiagonalTailChunk001Sub000Block103Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part008] using hcert

def TailChunk001Sub000Block103Part009SupportExplicit : Finset ℕ :=
  ([20751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part009 : ℚ :=
  (7627719425 : ℚ) / 233496681638648064

def SurrogateDiagonalTailChunk001Sub000Block103Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20751
    = surrogateDiagTailX0RatChunk001Sub000Block103Part009

theorem surrogateDiagonalTailChunk001Sub000Block103Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part009] using hcert

def TailChunk001Sub000Block103Part010SupportExplicit : Finset ℕ :=
  ([20753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block103Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20753
    = surrogateDiagTailX0RatChunk001Sub000Block103Part010

theorem surrogateDiagonalTailChunk001Sub000Block103Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part010] using hcert

def TailChunk001Sub000Block103Part011SupportExplicit : Finset ℕ :=
  ([20755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part011 : ℚ :=
  (14874605125 : ℚ) / 943484776696774656

def SurrogateDiagonalTailChunk001Sub000Block103Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20755
    = surrogateDiagTailX0RatChunk001Sub000Block103Part011

theorem surrogateDiagonalTailChunk001Sub000Block103Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part011] using hcert

def TailChunk001Sub000Block103Part012SupportExplicit : Finset ℕ :=
  ([20757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part012 : ℚ :=
  (82220759 : ℚ) / 5436905147596800

def SurrogateDiagonalTailChunk001Sub000Block103Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20757
    = surrogateDiagTailX0RatChunk001Sub000Block103Part012

theorem surrogateDiagonalTailChunk001Sub000Block103Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part012] using hcert

def TailChunk001Sub000Block103Part013SupportExplicit : Finset ℕ :=
  ([20758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part013 : ℚ :=
  (62955213025 : ℚ) / 26812372978696716288

def SurrogateDiagonalTailChunk001Sub000Block103Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20758
    = surrogateDiagTailX0RatChunk001Sub000Block103Part013

theorem surrogateDiagonalTailChunk001Sub000Block103Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part013] using hcert

def TailChunk001Sub000Block103Part014SupportExplicit : Finset ℕ :=
  ([20759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block103Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20759
    = surrogateDiagTailX0RatChunk001Sub000Block103Part014

theorem surrogateDiagonalTailChunk001Sub000Block103Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part014] using hcert

def TailChunk001Sub000Block103Part015SupportExplicit : Finset ℕ :=
  ([20761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part015 : ℚ :=
  (34368941675 : ℚ) / 24030087680668188672

def SurrogateDiagonalTailChunk001Sub000Block103Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20761
    = surrogateDiagTailX0RatChunk001Sub000Block103Part015

theorem surrogateDiagonalTailChunk001Sub000Block103Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part015] using hcert

def TailChunk001Sub000Block103Part016SupportExplicit : Finset ℕ :=
  ([20762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part016 : ℚ :=
  (7657789825 : ℚ) / 289488232847915712

def SurrogateDiagonalTailChunk001Sub000Block103Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20762
    = surrogateDiagTailX0RatChunk001Sub000Block103Part016

theorem surrogateDiagonalTailChunk001Sub000Block103Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part016] using hcert

def TailChunk001Sub000Block103Part017SupportExplicit : Finset ℕ :=
  ([20765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part017 : ℚ :=
  (1078694668375 : ℚ) / 190237532201062760448

def SurrogateDiagonalTailChunk001Sub000Block103Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20765
    = surrogateDiagTailX0RatChunk001Sub000Block103Part017

theorem surrogateDiagonalTailChunk001Sub000Block103Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part017] using hcert

def TailChunk001Sub000Block103Part018SupportExplicit : Finset ℕ :=
  ([20766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part018 : ℚ :=
  (748850101 : ℚ) / 5733914816052480

def SurrogateDiagonalTailChunk001Sub000Block103Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20766
    = surrogateDiagTailX0RatChunk001Sub000Block103Part018

theorem surrogateDiagonalTailChunk001Sub000Block103Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part018] using hcert

def TailChunk001Sub000Block103Part019SupportExplicit : Finset ℕ :=
  ([20767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part019 : ℚ :=
  (94492358575 : ℚ) / 93314136468405146112

def SurrogateDiagonalTailChunk001Sub000Block103Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20767
    = surrogateDiagTailX0RatChunk001Sub000Block103Part019

theorem surrogateDiagonalTailChunk001Sub000Block103Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part019] using hcert

def TailChunk001Sub000Block103Part020SupportExplicit : Finset ℕ :=
  ([20769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part020 : ℚ :=
  (29419353325 : ℚ) / 1349838144783507456

def SurrogateDiagonalTailChunk001Sub000Block103Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20769
    = surrogateDiagTailX0RatChunk001Sub000Block103Part020

theorem surrogateDiagonalTailChunk001Sub000Block103Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part020] using hcert

def TailChunk001Sub000Block103Part021SupportExplicit : Finset ℕ :=
  ([20770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part021 : ℚ :=
  (11380300249 : ℚ) / 131179605907046400

def SurrogateDiagonalTailChunk001Sub000Block103Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20770
    = surrogateDiagTailX0RatChunk001Sub000Block103Part021

theorem surrogateDiagonalTailChunk001Sub000Block103Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part021] using hcert

def TailChunk001Sub000Block103Part022SupportExplicit : Finset ℕ :=
  ([20771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block103Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20771
    = surrogateDiagTailX0RatChunk001Sub000Block103Part022

theorem surrogateDiagonalTailChunk001Sub000Block103Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part022] using hcert

def TailChunk001Sub000Block103Part023SupportExplicit : Finset ℕ :=
  ([20773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block103Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20773
    = surrogateDiagTailX0RatChunk001Sub000Block103Part023

theorem surrogateDiagonalTailChunk001Sub000Block103Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part023] using hcert

def TailChunk001Sub000Block103Part024SupportExplicit : Finset ℕ :=
  ([20774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block103Part024 : ℚ :=
  (153916609775 : ℚ) / 5071563244695453696

def SurrogateDiagonalTailChunk001Sub000Block103Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20774
    = surrogateDiagTailX0RatChunk001Sub000Block103Part024

theorem surrogateDiagonalTailChunk001Sub000Block103Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block103Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block103Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block103Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block103Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block103Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block103Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block103HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block103Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block103Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block103Part000
    + surrogateDiagTailX0RatChunk001Sub000Block103Part001
    + surrogateDiagTailX0RatChunk001Sub000Block103Part002
    + surrogateDiagTailX0RatChunk001Sub000Block103Part003
    + surrogateDiagTailX0RatChunk001Sub000Block103Part004
    + surrogateDiagTailX0RatChunk001Sub000Block103Part005
    + surrogateDiagTailX0RatChunk001Sub000Block103Part006
    + surrogateDiagTailX0RatChunk001Sub000Block103Part007
    + surrogateDiagTailX0RatChunk001Sub000Block103Part008
    + surrogateDiagTailX0RatChunk001Sub000Block103Part009

def surrogateDiagonalTailChunk001Sub000Block103MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block103Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block103Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block103Part010
    + surrogateDiagTailX0RatChunk001Sub000Block103Part011
    + surrogateDiagTailX0RatChunk001Sub000Block103Part012
    + surrogateDiagTailX0RatChunk001Sub000Block103Part013
    + surrogateDiagTailX0RatChunk001Sub000Block103Part014
    + surrogateDiagTailX0RatChunk001Sub000Block103Part015
    + surrogateDiagTailX0RatChunk001Sub000Block103Part016
    + surrogateDiagTailX0RatChunk001Sub000Block103Part017
    + surrogateDiagTailX0RatChunk001Sub000Block103Part018
    + surrogateDiagTailX0RatChunk001Sub000Block103Part019

def surrogateDiagonalTailChunk001Sub000Block103TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block103Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block103Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block103Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block103Part020
    + surrogateDiagTailX0RatChunk001Sub000Block103Part021
    + surrogateDiagTailX0RatChunk001Sub000Block103Part022
    + surrogateDiagTailX0RatChunk001Sub000Block103Part023
    + surrogateDiagTailX0RatChunk001Sub000Block103Part024

def surrogateDiagonalTailChunk001Sub000Block103Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block103HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block103MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block103TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block103 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block103Part000
    + surrogateDiagTailX0RatChunk001Sub000Block103Part001
    + surrogateDiagTailX0RatChunk001Sub000Block103Part002
    + surrogateDiagTailX0RatChunk001Sub000Block103Part003
    + surrogateDiagTailX0RatChunk001Sub000Block103Part004
    + surrogateDiagTailX0RatChunk001Sub000Block103Part005
    + surrogateDiagTailX0RatChunk001Sub000Block103Part006
    + surrogateDiagTailX0RatChunk001Sub000Block103Part007
    + surrogateDiagTailX0RatChunk001Sub000Block103Part008
    + surrogateDiagTailX0RatChunk001Sub000Block103Part009
    + surrogateDiagTailX0RatChunk001Sub000Block103Part010
    + surrogateDiagTailX0RatChunk001Sub000Block103Part011
    + surrogateDiagTailX0RatChunk001Sub000Block103Part012
    + surrogateDiagTailX0RatChunk001Sub000Block103Part013
    + surrogateDiagTailX0RatChunk001Sub000Block103Part014
    + surrogateDiagTailX0RatChunk001Sub000Block103Part015
    + surrogateDiagTailX0RatChunk001Sub000Block103Part016
    + surrogateDiagTailX0RatChunk001Sub000Block103Part017
    + surrogateDiagTailX0RatChunk001Sub000Block103Part018
    + surrogateDiagTailX0RatChunk001Sub000Block103Part019
    + surrogateDiagTailX0RatChunk001Sub000Block103Part020
    + surrogateDiagTailX0RatChunk001Sub000Block103Part021
    + surrogateDiagTailX0RatChunk001Sub000Block103Part022
    + surrogateDiagTailX0RatChunk001Sub000Block103Part023
    + surrogateDiagTailX0RatChunk001Sub000Block103Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block103_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block103Head + surrogateDiagTailX0RatChunk001Sub000Block103Mid + surrogateDiagTailX0RatChunk001Sub000Block103Tail =
      surrogateDiagTailX0RatChunk001Sub000Block103 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block103Head surrogateDiagTailX0RatChunk001Sub000Block103Mid surrogateDiagTailX0RatChunk001Sub000Block103Tail surrogateDiagTailX0RatChunk001Sub000Block103
  ring

def SurrogateDiagonalTailChunk001Sub000Block103HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block103HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block103Head

def SurrogateDiagonalTailChunk001Sub000Block103MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block103MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block103Mid

def SurrogateDiagonalTailChunk001Sub000Block103TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block103TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block103Tail

theorem surrogateDiagonalTailChunk001Sub000Block103_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block103HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block103MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block103TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block103Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block103 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block103HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block103MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block103TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block103Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block103_eq_head_add_mid_add_tail

/-- Block 104 covers tail-support indices [12600,12625) and q from 20777 to 20814. -/

def TailChunk001Sub000Block104Part000SupportExplicit : Finset ℕ :=
  ([20777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part000 : ℚ :=
  (105489958975 : ℚ) / 436124450160965524608

def SurrogateDiagonalTailChunk001Sub000Block104Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20777
    = surrogateDiagTailX0RatChunk001Sub000Block104Part000

theorem surrogateDiagonalTailChunk001Sub000Block104Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part000] using hcert

def TailChunk001Sub000Block104Part001SupportExplicit : Finset ℕ :=
  ([20778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part001 : ℚ :=
  (374857675475 : ℚ) / 2873591961014228544

def SurrogateDiagonalTailChunk001Sub000Block104Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20778
    = surrogateDiagTailX0RatChunk001Sub000Block104Part001

theorem surrogateDiagonalTailChunk001Sub000Block104Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part001] using hcert

def TailChunk001Sub000Block104Part002SupportExplicit : Finset ℕ :=
  ([20779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part002 : ℚ :=
  (26848479217 : ℚ) / 12708515122721587200

def SurrogateDiagonalTailChunk001Sub000Block104Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20779
    = surrogateDiagTailX0RatChunk001Sub000Block104Part002

theorem surrogateDiagonalTailChunk001Sub000Block104Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part002] using hcert

def TailChunk001Sub000Block104Part003SupportExplicit : Finset ℕ :=
  ([20782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block104Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20782
    = surrogateDiagTailX0RatChunk001Sub000Block104Part003

theorem surrogateDiagonalTailChunk001Sub000Block104Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part003] using hcert

def TailChunk001Sub000Block104Part004SupportExplicit : Finset ℕ :=
  ([20783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part004 : ℚ :=
  (551391305075 : ℚ) / 125735366253614874624

def SurrogateDiagonalTailChunk001Sub000Block104Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20783
    = surrogateDiagTailX0RatChunk001Sub000Block104Part004

theorem surrogateDiagonalTailChunk001Sub000Block104Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part004] using hcert

def TailChunk001Sub000Block104Part005SupportExplicit : Finset ℕ :=
  ([20785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part005 : ℚ :=
  (360257222625 : ℚ) / 63657228291216080896

def SurrogateDiagonalTailChunk001Sub000Block104Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20785
    = surrogateDiagTailX0RatChunk001Sub000Block104Part005

theorem surrogateDiagonalTailChunk001Sub000Block104Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part005] using hcert

def TailChunk001Sub000Block104Part006SupportExplicit : Finset ℕ :=
  ([20786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part006 : ℚ :=
  (21630470975 : ℚ) / 2916066764637660816

def SurrogateDiagonalTailChunk001Sub000Block104Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20786
    = surrogateDiagTailX0RatChunk001Sub000Block104Part006

theorem surrogateDiagonalTailChunk001Sub000Block104Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part006] using hcert

def TailChunk001Sub000Block104Part007SupportExplicit : Finset ℕ :=
  ([20789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block104Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20789
    = surrogateDiagTailX0RatChunk001Sub000Block104Part007

theorem surrogateDiagonalTailChunk001Sub000Block104Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part007] using hcert

def TailChunk001Sub000Block104Part008SupportExplicit : Finset ℕ :=
  ([20791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part008 : ℚ :=
  (378095822275 : ℚ) / 365419410895164407808

def SurrogateDiagonalTailChunk001Sub000Block104Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20791
    = surrogateDiagTailX0RatChunk001Sub000Block104Part008

theorem surrogateDiagonalTailChunk001Sub000Block104Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part008] using hcert

def TailChunk001Sub000Block104Part009SupportExplicit : Finset ℕ :=
  ([20793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part009 : ℚ :=
  (7742396925 : ℚ) / 3757227569424007168

def SurrogateDiagonalTailChunk001Sub000Block104Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20793
    = surrogateDiagTailX0RatChunk001Sub000Block104Part009

theorem surrogateDiagonalTailChunk001Sub000Block104Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part009] using hcert

def TailChunk001Sub000Block104Part010SupportExplicit : Finset ℕ :=
  ([20794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part010 : ℚ :=
  (2622721 : ℚ) / 682931567001600

def SurrogateDiagonalTailChunk001Sub000Block104Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20794
    = surrogateDiagTailX0RatChunk001Sub000Block104Part010

theorem surrogateDiagonalTailChunk001Sub000Block104Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part010] using hcert

def TailChunk001Sub000Block104Part011SupportExplicit : Finset ℕ :=
  ([20795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part011 : ℚ :=
  (1081810917625 : ℚ) / 191339557023062181888

def SurrogateDiagonalTailChunk001Sub000Block104Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20795
    = surrogateDiagTailX0RatChunk001Sub000Block104Part011

theorem surrogateDiagonalTailChunk001Sub000Block104Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part011] using hcert

def TailChunk001Sub000Block104Part012SupportExplicit : Finset ℕ :=
  ([20797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part012 : ℚ :=
  (22127245933 : ℚ) / 10085969465110915200

def SurrogateDiagonalTailChunk001Sub000Block104Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20797
    = surrogateDiagTailX0RatChunk001Sub000Block104Part012

theorem surrogateDiagonalTailChunk001Sub000Block104Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part012] using hcert

def TailChunk001Sub000Block104Part013SupportExplicit : Finset ℕ :=
  ([20798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block104Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20798
    = surrogateDiagTailX0RatChunk001Sub000Block104Part013

theorem surrogateDiagonalTailChunk001Sub000Block104Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part013] using hcert

def TailChunk001Sub000Block104Part014SupportExplicit : Finset ℕ :=
  ([20801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part014 : ℚ :=
  (34835039959 : ℚ) / 10499699520000000000

def SurrogateDiagonalTailChunk001Sub000Block104Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20801
    = surrogateDiagTailX0RatChunk001Sub000Block104Part014

theorem surrogateDiagonalTailChunk001Sub000Block104Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part014] using hcert

def TailChunk001Sub000Block104Part015SupportExplicit : Finset ℕ :=
  ([20802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part015 : ℚ :=
  (375723675425 : ℚ) / 2886895605275041344

def SurrogateDiagonalTailChunk001Sub000Block104Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20802
    = surrogateDiagTailX0RatChunk001Sub000Block104Part015

theorem surrogateDiagonalTailChunk001Sub000Block104Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part015] using hcert

def TailChunk001Sub000Block104Part016SupportExplicit : Finset ℕ :=
  ([20803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part016 : ℚ :=
  (30490833 : ℚ) / 118766260203673600

def SurrogateDiagonalTailChunk001Sub000Block104Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20803
    = surrogateDiagTailX0RatChunk001Sub000Block104Part016

theorem surrogateDiagonalTailChunk001Sub000Block104Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part016] using hcert

def TailChunk001Sub000Block104Part017SupportExplicit : Finset ℕ :=
  ([20805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part017 : ℚ :=
  (480625979675 : ℚ) / 14446971542719954944

def SurrogateDiagonalTailChunk001Sub000Block104Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20805
    = surrogateDiagTailX0RatChunk001Sub000Block104Part017

theorem surrogateDiagonalTailChunk001Sub000Block104Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part017] using hcert

def TailChunk001Sub000Block104Part018SupportExplicit : Finset ℕ :=
  ([20806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part018 : ℚ :=
  (2498774623 : ℚ) / 1082648646432000000

def SurrogateDiagonalTailChunk001Sub000Block104Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20806
    = surrogateDiagTailX0RatChunk001Sub000Block104Part018

theorem surrogateDiagonalTailChunk001Sub000Block104Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part018] using hcert

def TailChunk001Sub000Block104Part019SupportExplicit : Finset ℕ :=
  ([20807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block104Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20807
    = surrogateDiagTailX0RatChunk001Sub000Block104Part019

theorem surrogateDiagonalTailChunk001Sub000Block104Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part019] using hcert

def TailChunk001Sub000Block104Part020SupportExplicit : Finset ℕ :=
  ([20809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block104Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20809
    = surrogateDiagTailX0RatChunk001Sub000Block104Part020

theorem surrogateDiagonalTailChunk001Sub000Block104Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part020] using hcert

def TailChunk001Sub000Block104Part021SupportExplicit : Finset ℕ :=
  ([20810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part021 : ℚ :=
  (21677693629 : ℚ) / 479269900989235200

def SurrogateDiagonalTailChunk001Sub000Block104Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20810
    = surrogateDiagTailX0RatChunk001Sub000Block104Part021

theorem surrogateDiagonalTailChunk001Sub000Block104Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part021] using hcert

def TailChunk001Sub000Block104Part022SupportExplicit : Finset ℕ :=
  ([20811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part022 : ℚ :=
  (790156849 : ℚ) / 79691610588530688

def SurrogateDiagonalTailChunk001Sub000Block104Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20811
    = surrogateDiagTailX0RatChunk001Sub000Block104Part022

theorem surrogateDiagonalTailChunk001Sub000Block104Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part022] using hcert

def TailChunk001Sub000Block104Part023SupportExplicit : Finset ℕ :=
  ([20813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part023 : ℚ :=
  (9671224451 : ℚ) / 6796131434496000000

def SurrogateDiagonalTailChunk001Sub000Block104Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20813
    = surrogateDiagTailX0RatChunk001Sub000Block104Part023

theorem surrogateDiagonalTailChunk001Sub000Block104Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part023] using hcert

def TailChunk001Sub000Block104Part024SupportExplicit : Finset ℕ :=
  ([20814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block104Part024 : ℚ :=
  (11754907825 : ℚ) / 90423897598647072

def SurrogateDiagonalTailChunk001Sub000Block104Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20814
    = surrogateDiagTailX0RatChunk001Sub000Block104Part024

theorem surrogateDiagonalTailChunk001Sub000Block104Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block104Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block104Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block104Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block104Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block104Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block104Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block104HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block104Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block104Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block104Part000
    + surrogateDiagTailX0RatChunk001Sub000Block104Part001
    + surrogateDiagTailX0RatChunk001Sub000Block104Part002
    + surrogateDiagTailX0RatChunk001Sub000Block104Part003
    + surrogateDiagTailX0RatChunk001Sub000Block104Part004
    + surrogateDiagTailX0RatChunk001Sub000Block104Part005
    + surrogateDiagTailX0RatChunk001Sub000Block104Part006
    + surrogateDiagTailX0RatChunk001Sub000Block104Part007
    + surrogateDiagTailX0RatChunk001Sub000Block104Part008
    + surrogateDiagTailX0RatChunk001Sub000Block104Part009

def surrogateDiagonalTailChunk001Sub000Block104MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block104Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block104Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block104Part010
    + surrogateDiagTailX0RatChunk001Sub000Block104Part011
    + surrogateDiagTailX0RatChunk001Sub000Block104Part012
    + surrogateDiagTailX0RatChunk001Sub000Block104Part013
    + surrogateDiagTailX0RatChunk001Sub000Block104Part014
    + surrogateDiagTailX0RatChunk001Sub000Block104Part015
    + surrogateDiagTailX0RatChunk001Sub000Block104Part016
    + surrogateDiagTailX0RatChunk001Sub000Block104Part017
    + surrogateDiagTailX0RatChunk001Sub000Block104Part018
    + surrogateDiagTailX0RatChunk001Sub000Block104Part019

def surrogateDiagonalTailChunk001Sub000Block104TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block104Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block104Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block104Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block104Part020
    + surrogateDiagTailX0RatChunk001Sub000Block104Part021
    + surrogateDiagTailX0RatChunk001Sub000Block104Part022
    + surrogateDiagTailX0RatChunk001Sub000Block104Part023
    + surrogateDiagTailX0RatChunk001Sub000Block104Part024

def surrogateDiagonalTailChunk001Sub000Block104Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block104HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block104MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block104TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block104 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block104Part000
    + surrogateDiagTailX0RatChunk001Sub000Block104Part001
    + surrogateDiagTailX0RatChunk001Sub000Block104Part002
    + surrogateDiagTailX0RatChunk001Sub000Block104Part003
    + surrogateDiagTailX0RatChunk001Sub000Block104Part004
    + surrogateDiagTailX0RatChunk001Sub000Block104Part005
    + surrogateDiagTailX0RatChunk001Sub000Block104Part006
    + surrogateDiagTailX0RatChunk001Sub000Block104Part007
    + surrogateDiagTailX0RatChunk001Sub000Block104Part008
    + surrogateDiagTailX0RatChunk001Sub000Block104Part009
    + surrogateDiagTailX0RatChunk001Sub000Block104Part010
    + surrogateDiagTailX0RatChunk001Sub000Block104Part011
    + surrogateDiagTailX0RatChunk001Sub000Block104Part012
    + surrogateDiagTailX0RatChunk001Sub000Block104Part013
    + surrogateDiagTailX0RatChunk001Sub000Block104Part014
    + surrogateDiagTailX0RatChunk001Sub000Block104Part015
    + surrogateDiagTailX0RatChunk001Sub000Block104Part016
    + surrogateDiagTailX0RatChunk001Sub000Block104Part017
    + surrogateDiagTailX0RatChunk001Sub000Block104Part018
    + surrogateDiagTailX0RatChunk001Sub000Block104Part019
    + surrogateDiagTailX0RatChunk001Sub000Block104Part020
    + surrogateDiagTailX0RatChunk001Sub000Block104Part021
    + surrogateDiagTailX0RatChunk001Sub000Block104Part022
    + surrogateDiagTailX0RatChunk001Sub000Block104Part023
    + surrogateDiagTailX0RatChunk001Sub000Block104Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block104_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block104Head + surrogateDiagTailX0RatChunk001Sub000Block104Mid + surrogateDiagTailX0RatChunk001Sub000Block104Tail =
      surrogateDiagTailX0RatChunk001Sub000Block104 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block104Head surrogateDiagTailX0RatChunk001Sub000Block104Mid surrogateDiagTailX0RatChunk001Sub000Block104Tail surrogateDiagTailX0RatChunk001Sub000Block104
  ring

def SurrogateDiagonalTailChunk001Sub000Block104HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block104HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block104Head

def SurrogateDiagonalTailChunk001Sub000Block104MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block104MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block104Mid

def SurrogateDiagonalTailChunk001Sub000Block104TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block104TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block104Tail

theorem surrogateDiagonalTailChunk001Sub000Block104_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block104HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block104MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block104TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block104Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block104 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block104HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block104MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block104TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block104Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block104_eq_head_add_mid_add_tail

/-- Block 105 covers tail-support indices [12625,12650) and q from 20815 to 20855. -/

def TailChunk001Sub000Block105Part000SupportExplicit : Finset ℕ :=
  ([20815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part000 : ℚ :=
  (16595979551 : ℚ) / 2098873694512742400

def SurrogateDiagonalTailChunk001Sub000Block105Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20815
    = surrogateDiagTailX0RatChunk001Sub000Block105Part000

theorem surrogateDiagonalTailChunk001Sub000Block105Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part000] using hcert

def TailChunk001Sub000Block105Part001SupportExplicit : Finset ℕ :=
  ([20818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part001 : ℚ :=
  (23096986675 : ℚ) / 877878864059558976

def SurrogateDiagonalTailChunk001Sub000Block105Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20818
    = surrogateDiagTailX0RatChunk001Sub000Block105Part001

theorem surrogateDiagonalTailChunk001Sub000Block105Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part001] using hcert

def TailChunk001Sub000Block105Part002SupportExplicit : Finset ℕ :=
  ([20819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part002 : ℚ :=
  (922131829 : ℚ) / 4433393545312780800

def SurrogateDiagonalTailChunk001Sub000Block105Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20819
    = surrogateDiagTailX0RatChunk001Sub000Block105Part002

theorem surrogateDiagonalTailChunk001Sub000Block105Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part002] using hcert

def TailChunk001Sub000Block105Part003SupportExplicit : Finset ℕ :=
  ([20821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part003 : ℚ :=
  (1075157325 : ℚ) / 3096479268011411776

def SurrogateDiagonalTailChunk001Sub000Block105Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20821
    = surrogateDiagTailX0RatChunk001Sub000Block105Part003

theorem surrogateDiagonalTailChunk001Sub000Block105Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part003] using hcert

def TailChunk001Sub000Block105Part004SupportExplicit : Finset ℕ :=
  ([20822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part004 : ℚ :=
  (40194161625 : ℚ) / 8415304518768695296

def SurrogateDiagonalTailChunk001Sub000Block105Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20822
    = surrogateDiagTailX0RatChunk001Sub000Block105Part004

theorem surrogateDiagonalTailChunk001Sub000Block105Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part004] using hcert

def TailChunk001Sub000Block105Part005SupportExplicit : Finset ℕ :=
  ([20823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part005 : ℚ :=
  (1178665699 : ℚ) / 210081487896000000

def SurrogateDiagonalTailChunk001Sub000Block105Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20823
    = surrogateDiagTailX0RatChunk001Sub000Block105Part005

theorem surrogateDiagonalTailChunk001Sub000Block105Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part005] using hcert

def TailChunk001Sub000Block105Part006SupportExplicit : Finset ℕ :=
  ([20827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part006 : ℚ :=
  (3827633925 : ℚ) / 13164232596726480896

def SurrogateDiagonalTailChunk001Sub000Block105Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20827
    = surrogateDiagTailX0RatChunk001Sub000Block105Part006

theorem surrogateDiagonalTailChunk001Sub000Block105Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part006] using hcert

def TailChunk001Sub000Block105Part007SupportExplicit : Finset ℕ :=
  ([20829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part007 : ℚ :=
  (222143453 : ℚ) / 167095063991132160

def SurrogateDiagonalTailChunk001Sub000Block105Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20829
    = surrogateDiagTailX0RatChunk001Sub000Block105Part007

theorem surrogateDiagonalTailChunk001Sub000Block105Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part007] using hcert

def TailChunk001Sub000Block105Part008SupportExplicit : Finset ℕ :=
  ([20830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part008 : ℚ :=
  (180994210675 : ℚ) / 4009299226156210176

def SurrogateDiagonalTailChunk001Sub000Block105Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20830
    = surrogateDiagTailX0RatChunk001Sub000Block105Part008

theorem surrogateDiagonalTailChunk001Sub000Block105Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part008] using hcert

def TailChunk001Sub000Block105Part009SupportExplicit : Finset ℕ :=
  ([20831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part009 : ℚ :=
  (168941557075 : ℚ) / 418969225765892671488

def SurrogateDiagonalTailChunk001Sub000Block105Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20831
    = surrogateDiagTailX0RatChunk001Sub000Block105Part009

theorem surrogateDiagonalTailChunk001Sub000Block105Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part009] using hcert

def TailChunk001Sub000Block105Part010SupportExplicit : Finset ℕ :=
  ([20833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part010 : ℚ :=
  (3979181179 : ℚ) / 17664538451250000000

def SurrogateDiagonalTailChunk001Sub000Block105Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20833
    = surrogateDiagTailX0RatChunk001Sub000Block105Part010

theorem surrogateDiagonalTailChunk001Sub000Block105Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part010] using hcert

def TailChunk001Sub000Block105Part011SupportExplicit : Finset ℕ :=
  ([20834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part011 : ℚ :=
  (3917935323 : ℚ) / 13350580366423520

def SurrogateDiagonalTailChunk001Sub000Block105Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20834
    = surrogateDiagTailX0RatChunk001Sub000Block105Part011

theorem surrogateDiagonalTailChunk001Sub000Block105Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part011] using hcert

def TailChunk001Sub000Block105Part012SupportExplicit : Finset ℕ :=
  ([20837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part012 : ℚ :=
  (116781741377 : ℚ) / 1947452430987676800

def SurrogateDiagonalTailChunk001Sub000Block105Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20837
    = surrogateDiagTailX0RatChunk001Sub000Block105Part012

theorem surrogateDiagonalTailChunk001Sub000Block105Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part012] using hcert

def TailChunk001Sub000Block105Part013SupportExplicit : Finset ℕ :=
  ([20838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part013 : ℚ :=
  (35029952143 : ℚ) / 47446327368000000

def SurrogateDiagonalTailChunk001Sub000Block105Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20838
    = surrogateDiagTailX0RatChunk001Sub000Block105Part013

theorem surrogateDiagonalTailChunk001Sub000Block105Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part013] using hcert

def TailChunk001Sub000Block105Part014SupportExplicit : Finset ℕ :=
  ([20839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part014 : ℚ :=
  (466848505775 : ℚ) / 4778731568842407936

def SurrogateDiagonalTailChunk001Sub000Block105Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20839
    = surrogateDiagTailX0RatChunk001Sub000Block105Part014

theorem surrogateDiagonalTailChunk001Sub000Block105Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part014] using hcert

def TailChunk001Sub000Block105Part015SupportExplicit : Finset ℕ :=
  ([20841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part015 : ℚ :=
  (12062353305325 : ℚ) / 93129218259670328448

def SurrogateDiagonalTailChunk001Sub000Block105Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20841
    = surrogateDiagTailX0RatChunk001Sub000Block105Part015

theorem surrogateDiagonalTailChunk001Sub000Block105Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part015] using hcert

def TailChunk001Sub000Block105Part016SupportExplicit : Finset ℕ :=
  ([20842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part016 : ℚ :=
  (1027066696625 : ℚ) / 3831432931398647808

def SurrogateDiagonalTailChunk001Sub000Block105Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20842
    = surrogateDiagTailX0RatChunk001Sub000Block105Part016

theorem surrogateDiagonalTailChunk001Sub000Block105Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part016] using hcert

def TailChunk001Sub000Block105Part017SupportExplicit : Finset ℕ :=
  ([20843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part017 : ℚ :=
  (24632505592825 : ℚ) / 378755628933071536128

def SurrogateDiagonalTailChunk001Sub000Block105Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20843
    = surrogateDiagTailX0RatChunk001Sub000Block105Part017

theorem surrogateDiagonalTailChunk001Sub000Block105Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part017] using hcert

def TailChunk001Sub000Block105Part018SupportExplicit : Finset ℕ :=
  ([20845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part018 : ℚ :=
  (124490832149 : ℚ) / 1045499935922749440

def SurrogateDiagonalTailChunk001Sub000Block105Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20845
    = surrogateDiagTailX0RatChunk001Sub000Block105Part018

theorem surrogateDiagonalTailChunk001Sub000Block105Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part018] using hcert

def TailChunk001Sub000Block105Part019SupportExplicit : Finset ℕ :=
  ([20846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part019 : ℚ :=
  (299982111575 : ℚ) / 882614545103978496

def SurrogateDiagonalTailChunk001Sub000Block105Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20846
    = surrogateDiagTailX0RatChunk001Sub000Block105Part019

theorem surrogateDiagonalTailChunk001Sub000Block105Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part019] using hcert

def TailChunk001Sub000Block105Part020SupportExplicit : Finset ℕ :=
  ([20847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part020 : ℚ :=
  (12069300305125 : ℚ) / 93236525427874940928

def SurrogateDiagonalTailChunk001Sub000Block105Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20847
    = surrogateDiagTailX0RatChunk001Sub000Block105Part020

theorem surrogateDiagonalTailChunk001Sub000Block105Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part020] using hcert

def TailChunk001Sub000Block105Part021SupportExplicit : Finset ℕ :=
  ([20849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part021 : ℚ :=
  (6791887515625 : ℚ) / 118093083097542500352

def SurrogateDiagonalTailChunk001Sub000Block105Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20849
    = surrogateDiagTailX0RatChunk001Sub000Block105Part021

theorem surrogateDiagonalTailChunk001Sub000Block105Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part021] using hcert

def TailChunk001Sub000Block105Part022SupportExplicit : Finset ℕ :=
  ([20851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part022 : ℚ :=
  (8488212572025 : ℚ) / 136155599429839230976

def SurrogateDiagonalTailChunk001Sub000Block105Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20851
    = surrogateDiagTailX0RatChunk001Sub000Block105Part022

theorem surrogateDiagonalTailChunk001Sub000Block105Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part022] using hcert

def TailChunk001Sub000Block105Part023SupportExplicit : Finset ℕ :=
  ([20854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part023 : ℚ :=
  (1698786390625 : ℚ) / 7386483804222182322

def SurrogateDiagonalTailChunk001Sub000Block105Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20854
    = surrogateDiagTailX0RatChunk001Sub000Block105Part023

theorem surrogateDiagonalTailChunk001Sub000Block105Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part023] using hcert

def TailChunk001Sub000Block105Part024SupportExplicit : Finset ℕ :=
  ([20855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block105Part024 : ℚ :=
  (5813383923325 : ℚ) / 56393320000521240576

def SurrogateDiagonalTailChunk001Sub000Block105Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20855
    = surrogateDiagTailX0RatChunk001Sub000Block105Part024

theorem surrogateDiagonalTailChunk001Sub000Block105Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block105Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block105Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block105Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block105Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block105Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block105Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block105HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block105Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block105Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block105Part000
    + surrogateDiagTailX0RatChunk001Sub000Block105Part001
    + surrogateDiagTailX0RatChunk001Sub000Block105Part002
    + surrogateDiagTailX0RatChunk001Sub000Block105Part003
    + surrogateDiagTailX0RatChunk001Sub000Block105Part004
    + surrogateDiagTailX0RatChunk001Sub000Block105Part005
    + surrogateDiagTailX0RatChunk001Sub000Block105Part006
    + surrogateDiagTailX0RatChunk001Sub000Block105Part007
    + surrogateDiagTailX0RatChunk001Sub000Block105Part008
    + surrogateDiagTailX0RatChunk001Sub000Block105Part009

def surrogateDiagonalTailChunk001Sub000Block105MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block105Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block105Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block105Part010
    + surrogateDiagTailX0RatChunk001Sub000Block105Part011
    + surrogateDiagTailX0RatChunk001Sub000Block105Part012
    + surrogateDiagTailX0RatChunk001Sub000Block105Part013
    + surrogateDiagTailX0RatChunk001Sub000Block105Part014
    + surrogateDiagTailX0RatChunk001Sub000Block105Part015
    + surrogateDiagTailX0RatChunk001Sub000Block105Part016
    + surrogateDiagTailX0RatChunk001Sub000Block105Part017
    + surrogateDiagTailX0RatChunk001Sub000Block105Part018
    + surrogateDiagTailX0RatChunk001Sub000Block105Part019

def surrogateDiagonalTailChunk001Sub000Block105TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block105Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block105Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block105Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block105Part020
    + surrogateDiagTailX0RatChunk001Sub000Block105Part021
    + surrogateDiagTailX0RatChunk001Sub000Block105Part022
    + surrogateDiagTailX0RatChunk001Sub000Block105Part023
    + surrogateDiagTailX0RatChunk001Sub000Block105Part024

def surrogateDiagonalTailChunk001Sub000Block105Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block105HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block105MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block105TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block105 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block105Part000
    + surrogateDiagTailX0RatChunk001Sub000Block105Part001
    + surrogateDiagTailX0RatChunk001Sub000Block105Part002
    + surrogateDiagTailX0RatChunk001Sub000Block105Part003
    + surrogateDiagTailX0RatChunk001Sub000Block105Part004
    + surrogateDiagTailX0RatChunk001Sub000Block105Part005
    + surrogateDiagTailX0RatChunk001Sub000Block105Part006
    + surrogateDiagTailX0RatChunk001Sub000Block105Part007
    + surrogateDiagTailX0RatChunk001Sub000Block105Part008
    + surrogateDiagTailX0RatChunk001Sub000Block105Part009
    + surrogateDiagTailX0RatChunk001Sub000Block105Part010
    + surrogateDiagTailX0RatChunk001Sub000Block105Part011
    + surrogateDiagTailX0RatChunk001Sub000Block105Part012
    + surrogateDiagTailX0RatChunk001Sub000Block105Part013
    + surrogateDiagTailX0RatChunk001Sub000Block105Part014
    + surrogateDiagTailX0RatChunk001Sub000Block105Part015
    + surrogateDiagTailX0RatChunk001Sub000Block105Part016
    + surrogateDiagTailX0RatChunk001Sub000Block105Part017
    + surrogateDiagTailX0RatChunk001Sub000Block105Part018
    + surrogateDiagTailX0RatChunk001Sub000Block105Part019
    + surrogateDiagTailX0RatChunk001Sub000Block105Part020
    + surrogateDiagTailX0RatChunk001Sub000Block105Part021
    + surrogateDiagTailX0RatChunk001Sub000Block105Part022
    + surrogateDiagTailX0RatChunk001Sub000Block105Part023
    + surrogateDiagTailX0RatChunk001Sub000Block105Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block105_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block105Head + surrogateDiagTailX0RatChunk001Sub000Block105Mid + surrogateDiagTailX0RatChunk001Sub000Block105Tail =
      surrogateDiagTailX0RatChunk001Sub000Block105 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block105Head surrogateDiagTailX0RatChunk001Sub000Block105Mid surrogateDiagTailX0RatChunk001Sub000Block105Tail surrogateDiagTailX0RatChunk001Sub000Block105
  ring

def SurrogateDiagonalTailChunk001Sub000Block105HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block105HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block105Head

def SurrogateDiagonalTailChunk001Sub000Block105MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block105MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block105Mid

def SurrogateDiagonalTailChunk001Sub000Block105TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block105TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block105Tail

theorem surrogateDiagonalTailChunk001Sub000Block105_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block105HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block105MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block105TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block105Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block105 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block105HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block105MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block105TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block105Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block105_eq_head_add_mid_add_tail

/-- Block 106 covers tail-support indices [12650,12675) and q from 20857 to 20897. -/

def TailChunk001Sub000Block106Part000SupportExplicit : Finset ℕ :=
  ([20857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part000 : ℚ :=
  (6797100765625 : ℚ) / 118274450824711475712

def SurrogateDiagonalTailChunk001Sub000Block106Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20857
    = surrogateDiagTailX0RatChunk001Sub000Block106Part000

theorem surrogateDiagonalTailChunk001Sub000Block106Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part000] using hcert

def TailChunk001Sub000Block106Part001SupportExplicit : Finset ℕ :=
  ([20858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part001 : ℚ :=
  (1699438140625 : ℚ) / 7392153176544467232

def SurrogateDiagonalTailChunk001Sub000Block106Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20858
    = surrogateDiagTailX0RatChunk001Sub000Block106Part001

theorem surrogateDiagonalTailChunk001Sub000Block106Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part001] using hcert

def TailChunk001Sub000Block106Part002SupportExplicit : Finset ℕ :=
  ([20859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part002 : ℚ :=
  (10871464255975 : ℚ) / 72655320773189173248

def SurrogateDiagonalTailChunk001Sub000Block106Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20859
    = surrogateDiagTailX0RatChunk001Sub000Block106Part002

theorem surrogateDiagonalTailChunk001Sub000Block106Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part002] using hcert

def TailChunk001Sub000Block106Part003SupportExplicit : Finset ℕ :=
  ([20861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part003 : ℚ :=
  (12522001702475 : ℚ) / 197333299351643425344

def SurrogateDiagonalTailChunk001Sub000Block106Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20861
    = surrogateDiagTailX0RatChunk001Sub000Block106Part003

theorem surrogateDiagonalTailChunk001Sub000Block106Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part003] using hcert

def TailChunk001Sub000Block106Part004SupportExplicit : Finset ℕ :=
  ([20863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part004 : ℚ :=
  (54202313 : ℚ) / 874152405762048

def SurrogateDiagonalTailChunk001Sub000Block106Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20863
    = surrogateDiagTailX0RatChunk001Sub000Block106Part004

theorem surrogateDiagonalTailChunk001Sub000Block106Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part004] using hcert

def TailChunk001Sub000Block106Part005SupportExplicit : Finset ℕ :=
  ([20865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part005 : ℚ :=
  (7314800852125 : ℚ) / 26812372978696716288

def SurrogateDiagonalTailChunk001Sub000Block106Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20865
    = surrogateDiagTailX0RatChunk001Sub000Block106Part005

theorem surrogateDiagonalTailChunk001Sub000Block106Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part005] using hcert

def TailChunk001Sub000Block106Part006SupportExplicit : Finset ℕ :=
  ([20866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part006 : ℚ :=
  (1700742015625 : ℚ) / 7403501711284764672

def SurrogateDiagonalTailChunk001Sub000Block106Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20866
    = surrogateDiagTailX0RatChunk001Sub000Block106Part006

theorem surrogateDiagonalTailChunk001Sub000Block106Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part006] using hcert

def TailChunk001Sub000Block106Part007SupportExplicit : Finset ℕ :=
  ([20867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part007 : ℚ :=
  (690778585477 : ℚ) / 6888852855072000000

def SurrogateDiagonalTailChunk001Sub000Block106Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20867
    = surrogateDiagTailX0RatChunk001Sub000Block106Part007

theorem surrogateDiagonalTailChunk001Sub000Block106Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part007] using hcert

def TailChunk001Sub000Block106Part008SupportExplicit : Finset ℕ :=
  ([20869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part008 : ℚ :=
  (1038641854081 : ℚ) / 17052248960414515200

def SurrogateDiagonalTailChunk001Sub000Block106Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20869
    = surrogateDiagTailX0RatChunk001Sub000Block106Part008

theorem surrogateDiagonalTailChunk001Sub000Block106Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part008] using hcert

def TailChunk001Sub000Block106Part009SupportExplicit : Finset ℕ :=
  ([20870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part009 : ℚ :=
  (4625043733525 : ℚ) / 12120597810077288448

def SurrogateDiagonalTailChunk001Sub000Block106Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20870
    = surrogateDiagTailX0RatChunk001Sub000Block106Part009

theorem surrogateDiagonalTailChunk001Sub000Block106Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part009] using hcert

def TailChunk001Sub000Block106Part010SupportExplicit : Finset ℕ :=
  ([20873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part010 : ℚ :=
  (6807533265625 : ℚ) / 118637812925313618432

def SurrogateDiagonalTailChunk001Sub000Block106Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20873
    = surrogateDiagTailX0RatChunk001Sub000Block106Part010

theorem surrogateDiagonalTailChunk001Sub000Block106Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part010] using hcert

def TailChunk001Sub000Block106Part011SupportExplicit : Finset ℕ :=
  ([20877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part011 : ℚ :=
  (12104065304125 : ℚ) / 93774452926265021568

def SurrogateDiagonalTailChunk001Sub000Block106Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20877
    = surrogateDiagTailX0RatChunk001Sub000Block106Part011

theorem surrogateDiagonalTailChunk001Sub000Block106Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part011] using hcert

def TailChunk001Sub000Block106Part012SupportExplicit : Finset ℕ :=
  ([20878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part012 : ℚ :=
  (204665164231 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk001Sub000Block106Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20878
    = surrogateDiagTailX0RatChunk001Sub000Block106Part012

theorem surrogateDiagonalTailChunk001Sub000Block106Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part012] using hcert

def TailChunk001Sub000Block106Part013SupportExplicit : Finset ℕ :=
  ([20879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part013 : ℚ :=
  (6811447515625 : ℚ) / 118774289329282697682

def SurrogateDiagonalTailChunk001Sub000Block106Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20879
    = surrogateDiagTailX0RatChunk001Sub000Block106Part013

theorem surrogateDiagonalTailChunk001Sub000Block106Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part013] using hcert

def TailChunk001Sub000Block106Part014SupportExplicit : Finset ℕ :=
  ([20881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part014 : ℚ :=
  (2058439485925 : ℚ) / 22386065225240051712

def SurrogateDiagonalTailChunk001Sub000Block106Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20881
    = surrogateDiagTailX0RatChunk001Sub000Block106Part014

theorem surrogateDiagonalTailChunk001Sub000Block106Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part014] using hcert

def TailChunk001Sub000Block106Part015SupportExplicit : Finset ℕ :=
  ([20882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part015 : ℚ :=
  (6567056694775 : ℚ) / 26981402387623477248

def SurrogateDiagonalTailChunk001Sub000Block106Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20882
    = surrogateDiagTailX0RatChunk001Sub000Block106Part015

theorem surrogateDiagonalTailChunk001Sub000Block106Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part015] using hcert

def TailChunk001Sub000Block106Part016SupportExplicit : Finset ℕ :=
  ([20883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part016 : ℚ :=
  (484440972157 : ℚ) / 3755292685251379200

def SurrogateDiagonalTailChunk001Sub000Block106Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20883
    = surrogateDiagTailX0RatChunk001Sub000Block106Part016

theorem surrogateDiagonalTailChunk001Sub000Block106Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part016] using hcert

def TailChunk001Sub000Block106Part017SupportExplicit : Finset ℕ :=
  ([20885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part017 : ℚ :=
  (363338046875 : ℚ) / 4055716100071489536

def SurrogateDiagonalTailChunk001Sub000Block106Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20885
    = surrogateDiagTailX0RatChunk001Sub000Block106Part017

theorem surrogateDiagonalTailChunk001Sub000Block106Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part017] using hcert

def TailChunk001Sub000Block106Part018SupportExplicit : Finset ℕ :=
  ([20887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part018 : ℚ :=
  (6816668265625 : ℚ) / 118956440990391910002

def SurrogateDiagonalTailChunk001Sub000Block106Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20887
    = surrogateDiagTailX0RatChunk001Sub000Block106Part018

theorem surrogateDiagonalTailChunk001Sub000Block106Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part018] using hcert

def TailChunk001Sub000Block106Part019SupportExplicit : Finset ℕ :=
  ([20890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part019 : ℚ :=
  (4633914318475 : ℚ) / 12167148300214468608

def SurrogateDiagonalTailChunk001Sub000Block106Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20890
    = surrogateDiagTailX0RatChunk001Sub000Block106Part019

theorem surrogateDiagonalTailChunk001Sub000Block106Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part019] using hcert

def TailChunk001Sub000Block106Part020SupportExplicit : Finset ℕ :=
  ([20891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part020 : ℚ :=
  (23540754275125 : ℚ) / 344932413225308080128

def SurrogateDiagonalTailChunk001Sub000Block106Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20891
    = surrogateDiagTailX0RatChunk001Sub000Block106Part020

theorem surrogateDiagonalTailChunk001Sub000Block106Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part020] using hcert

def TailChunk001Sub000Block106Part021SupportExplicit : Finset ℕ :=
  ([20893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part021 : ℚ :=
  (95379547225 : ℚ) / 1455661150339104768

def SurrogateDiagonalTailChunk001Sub000Block106Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20893
    = surrogateDiagTailX0RatChunk001Sub000Block106Part021

theorem surrogateDiagonalTailChunk001Sub000Block106Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part021] using hcert

def TailChunk001Sub000Block106Part022SupportExplicit : Finset ℕ :=
  ([20894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part022 : ℚ :=
  (36910928869 : ℚ) / 147513218472345600

def SurrogateDiagonalTailChunk001Sub000Block106Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20894
    = surrogateDiagTailX0RatChunk001Sub000Block106Part022

theorem surrogateDiagonalTailChunk001Sub000Block106Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part022] using hcert

def TailChunk001Sub000Block106Part023SupportExplicit : Finset ℕ :=
  ([20895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part023 : ℚ :=
  (6283848400975 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk001Sub000Block106Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20895
    = surrogateDiagTailX0RatChunk001Sub000Block106Part023

theorem surrogateDiagonalTailChunk001Sub000Block106Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part023] using hcert

def TailChunk001Sub000Block106Part024SupportExplicit : Finset ℕ :=
  ([20897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block106Part024 : ℚ :=
  (6823197015625 : ℚ) / 119184425096351711232

def SurrogateDiagonalTailChunk001Sub000Block106Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20897
    = surrogateDiagTailX0RatChunk001Sub000Block106Part024

theorem surrogateDiagonalTailChunk001Sub000Block106Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block106Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block106Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block106Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block106Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block106Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block106Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block106HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block106Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block106Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block106Part000
    + surrogateDiagTailX0RatChunk001Sub000Block106Part001
    + surrogateDiagTailX0RatChunk001Sub000Block106Part002
    + surrogateDiagTailX0RatChunk001Sub000Block106Part003
    + surrogateDiagTailX0RatChunk001Sub000Block106Part004
    + surrogateDiagTailX0RatChunk001Sub000Block106Part005
    + surrogateDiagTailX0RatChunk001Sub000Block106Part006
    + surrogateDiagTailX0RatChunk001Sub000Block106Part007
    + surrogateDiagTailX0RatChunk001Sub000Block106Part008
    + surrogateDiagTailX0RatChunk001Sub000Block106Part009

def surrogateDiagonalTailChunk001Sub000Block106MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block106Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block106Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block106Part010
    + surrogateDiagTailX0RatChunk001Sub000Block106Part011
    + surrogateDiagTailX0RatChunk001Sub000Block106Part012
    + surrogateDiagTailX0RatChunk001Sub000Block106Part013
    + surrogateDiagTailX0RatChunk001Sub000Block106Part014
    + surrogateDiagTailX0RatChunk001Sub000Block106Part015
    + surrogateDiagTailX0RatChunk001Sub000Block106Part016
    + surrogateDiagTailX0RatChunk001Sub000Block106Part017
    + surrogateDiagTailX0RatChunk001Sub000Block106Part018
    + surrogateDiagTailX0RatChunk001Sub000Block106Part019

def surrogateDiagonalTailChunk001Sub000Block106TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block106Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block106Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block106Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block106Part020
    + surrogateDiagTailX0RatChunk001Sub000Block106Part021
    + surrogateDiagTailX0RatChunk001Sub000Block106Part022
    + surrogateDiagTailX0RatChunk001Sub000Block106Part023
    + surrogateDiagTailX0RatChunk001Sub000Block106Part024

def surrogateDiagonalTailChunk001Sub000Block106Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block106HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block106MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block106TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block106 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block106Part000
    + surrogateDiagTailX0RatChunk001Sub000Block106Part001
    + surrogateDiagTailX0RatChunk001Sub000Block106Part002
    + surrogateDiagTailX0RatChunk001Sub000Block106Part003
    + surrogateDiagTailX0RatChunk001Sub000Block106Part004
    + surrogateDiagTailX0RatChunk001Sub000Block106Part005
    + surrogateDiagTailX0RatChunk001Sub000Block106Part006
    + surrogateDiagTailX0RatChunk001Sub000Block106Part007
    + surrogateDiagTailX0RatChunk001Sub000Block106Part008
    + surrogateDiagTailX0RatChunk001Sub000Block106Part009
    + surrogateDiagTailX0RatChunk001Sub000Block106Part010
    + surrogateDiagTailX0RatChunk001Sub000Block106Part011
    + surrogateDiagTailX0RatChunk001Sub000Block106Part012
    + surrogateDiagTailX0RatChunk001Sub000Block106Part013
    + surrogateDiagTailX0RatChunk001Sub000Block106Part014
    + surrogateDiagTailX0RatChunk001Sub000Block106Part015
    + surrogateDiagTailX0RatChunk001Sub000Block106Part016
    + surrogateDiagTailX0RatChunk001Sub000Block106Part017
    + surrogateDiagTailX0RatChunk001Sub000Block106Part018
    + surrogateDiagTailX0RatChunk001Sub000Block106Part019
    + surrogateDiagTailX0RatChunk001Sub000Block106Part020
    + surrogateDiagTailX0RatChunk001Sub000Block106Part021
    + surrogateDiagTailX0RatChunk001Sub000Block106Part022
    + surrogateDiagTailX0RatChunk001Sub000Block106Part023
    + surrogateDiagTailX0RatChunk001Sub000Block106Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block106_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block106Head + surrogateDiagTailX0RatChunk001Sub000Block106Mid + surrogateDiagTailX0RatChunk001Sub000Block106Tail =
      surrogateDiagTailX0RatChunk001Sub000Block106 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block106Head surrogateDiagTailX0RatChunk001Sub000Block106Mid surrogateDiagTailX0RatChunk001Sub000Block106Tail surrogateDiagTailX0RatChunk001Sub000Block106
  ring

def SurrogateDiagonalTailChunk001Sub000Block106HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block106HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block106Head

def SurrogateDiagonalTailChunk001Sub000Block106MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block106MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block106Mid

def SurrogateDiagonalTailChunk001Sub000Block106TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block106TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block106Tail

theorem surrogateDiagonalTailChunk001Sub000Block106_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block106HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block106MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block106TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block106Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block106 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block106HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block106MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block106TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block106Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block106_eq_head_add_mid_add_tail

/-- Block 107 covers tail-support indices [12675,12700) and q from 20899 to 20939. -/

def TailChunk001Sub000Block107Part000SupportExplicit : Finset ℕ :=
  ([20899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part000 : ℚ :=
  (6824503140625 : ℚ) / 119230061213225856402

def SurrogateDiagonalTailChunk001Sub000Block107Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20899
    = surrogateDiagTailX0RatChunk001Sub000Block107Part000

theorem surrogateDiagonalTailChunk001Sub000Block107Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part000] using hcert

def TailChunk001Sub000Block107Part001SupportExplicit : Finset ℕ :=
  ([20901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part001 : ℚ :=
  (12131913303325 : ℚ) / 94206468119092034688

def SurrogateDiagonalTailChunk001Sub000Block107Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20901
    = surrogateDiagTailX0RatChunk001Sub000Block107Part001

theorem surrogateDiagonalTailChunk001Sub000Block107Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part001] using hcert

def TailChunk001Sub000Block107Part002SupportExplicit : Finset ℕ :=
  ([20902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part002 : ℚ :=
  (301596526475 : ℚ) / 892143360770835456

def SurrogateDiagonalTailChunk001Sub000Block107Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20902
    = surrogateDiagTailX0RatChunk001Sub000Block107Part002

theorem surrogateDiagonalTailChunk001Sub000Block107Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part002] using hcert

def TailChunk001Sub000Block107Part003SupportExplicit : Finset ℕ :=
  ([20903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part003 : ℚ :=
  (6827115765625 : ℚ) / 119321372762720023602

def SurrogateDiagonalTailChunk001Sub000Block107Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20903
    = surrogateDiagTailX0RatChunk001Sub000Block107Part003

theorem surrogateDiagonalTailChunk001Sub000Block107Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part003] using hcert

def TailChunk001Sub000Block107Part004SupportExplicit : Finset ℕ :=
  ([20905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part004 : ℚ :=
  (228181097575 : ℚ) / 2349721666688385024

def SurrogateDiagonalTailChunk001Sub000Block107Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20905
    = surrogateDiagTailX0RatChunk001Sub000Block107Part004

theorem surrogateDiagonalTailChunk001Sub000Block107Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part004] using hcert

def TailChunk001Sub000Block107Part005SupportExplicit : Finset ℕ :=
  ([20906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part005 : ℚ :=
  (1707268890625 : ℚ) / 7460440512522315552

def SurrogateDiagonalTailChunk001Sub000Block107Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20906
    = surrogateDiagTailX0RatChunk001Sub000Block107Part005

theorem surrogateDiagonalTailChunk001Sub000Block107Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part005] using hcert

def TailChunk001Sub000Block107Part006SupportExplicit : Finset ℕ :=
  ([20909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part006 : ℚ :=
  (19079509971925 : ℚ) / 215607901600503595008

def SurrogateDiagonalTailChunk001Sub000Block107Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20909
    = surrogateDiagTailX0RatChunk001Sub000Block107Part006

theorem surrogateDiagonalTailChunk001Sub000Block107Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part006] using hcert

def TailChunk001Sub000Block107Part007SupportExplicit : Finset ℕ :=
  ([20910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part007 : ℚ :=
  (998247179 : ℚ) / 859165257891840

def SurrogateDiagonalTailChunk001Sub000Block107Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20910
    = surrogateDiagTailX0RatChunk001Sub000Block107Part007

theorem surrogateDiagonalTailChunk001Sub000Block107Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part007] using hcert

def TailChunk001Sub000Block107Part008SupportExplicit : Finset ℕ :=
  ([20911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part008 : ℚ :=
  (22792147549 : ℚ) / 325867660500000000

def SurrogateDiagonalTailChunk001Sub000Block107Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20911
    = surrogateDiagTailX0RatChunk001Sub000Block107Part008

theorem surrogateDiagonalTailChunk001Sub000Block107Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part008] using hcert

def TailChunk001Sub000Block107Part009SupportExplicit : Finset ℕ :=
  ([20913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part009 : ℚ :=
  (485833972117 : ℚ) / 3776921384926339200

def SurrogateDiagonalTailChunk001Sub000Block107Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20913
    = surrogateDiagTailX0RatChunk001Sub000Block107Part009

theorem surrogateDiagonalTailChunk001Sub000Block107Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part009] using hcert

def TailChunk001Sub000Block107Part010SupportExplicit : Finset ℕ :=
  ([20914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part010 : ℚ :=
  (1708575765625 : ℚ) / 7471867568461312512

def SurrogateDiagonalTailChunk001Sub000Block107Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20914
    = surrogateDiagTailX0RatChunk001Sub000Block107Part010

theorem surrogateDiagonalTailChunk001Sub000Block107Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part010] using hcert

def TailChunk001Sub000Block107Part011SupportExplicit : Finset ℕ :=
  ([20915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part011 : ℚ :=
  (4135123318675 : ℚ) / 42970345755547533312

def SurrogateDiagonalTailChunk001Sub000Block107Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20915
    = surrogateDiagTailX0RatChunk001Sub000Block107Part011

theorem surrogateDiagonalTailChunk001Sub000Block107Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part011] using hcert

def TailChunk001Sub000Block107Part012SupportExplicit : Finset ℕ :=
  ([20917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part012 : ℚ :=
  (874052350675 : ℚ) / 12839031268915544064

def SurrogateDiagonalTailChunk001Sub000Block107Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20917
    = surrogateDiagTailX0RatChunk001Sub000Block107Part012

theorem surrogateDiagonalTailChunk001Sub000Block107Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part012] using hcert

def TailChunk001Sub000Block107Part013SupportExplicit : Finset ℕ :=
  ([20918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part013 : ℚ :=
  (1709229390625 : ℚ) / 7477586016544486962

def SurrogateDiagonalTailChunk001Sub000Block107Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20918
    = surrogateDiagTailX0RatChunk001Sub000Block107Part013

theorem surrogateDiagonalTailChunk001Sub000Block107Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part013] using hcert

def TailChunk001Sub000Block107Part014SupportExplicit : Finset ℕ :=
  ([20919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part014 : ℚ :=
  (76703676475 : ℚ) / 523357812366106752

def SurrogateDiagonalTailChunk001Sub000Block107Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20919
    = surrogateDiagTailX0RatChunk001Sub000Block107Part014

theorem surrogateDiagonalTailChunk001Sub000Block107Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part014] using hcert

def TailChunk001Sub000Block107Part015SupportExplicit : Finset ℕ :=
  ([20921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part015 : ℚ :=
  (10942206025 : ℚ) / 191572678307246592

def SurrogateDiagonalTailChunk001Sub000Block107Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20921
    = surrogateDiagTailX0RatChunk001Sub000Block107Part015

theorem surrogateDiagonalTailChunk001Sub000Block107Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part015] using hcert

def TailChunk001Sub000Block107Part016SupportExplicit : Finset ℕ :=
  ([20922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part016 : ℚ :=
  (1075960933 : ℚ) / 1595714396823552

def SurrogateDiagonalTailChunk001Sub000Block107Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20922
    = surrogateDiagTailX0RatChunk001Sub000Block107Part016

theorem surrogateDiagonalTailChunk001Sub000Block107Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part016] using hcert

def TailChunk001Sub000Block107Part017SupportExplicit : Finset ℕ :=
  ([20926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part017 : ℚ :=
  (1710537015625 : ℚ) / 7489032759213642642

def SurrogateDiagonalTailChunk001Sub000Block107Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20926
    = surrogateDiagTailX0RatChunk001Sub000Block107Part017

theorem surrogateDiagonalTailChunk001Sub000Block107Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part017] using hcert

def TailChunk001Sub000Block107Part018SupportExplicit : Finset ℕ :=
  ([20927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part018 : ℚ :=
  (244967473597 : ℚ) / 3750828741889228800

def SurrogateDiagonalTailChunk001Sub000Block107Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20927
    = surrogateDiagTailX0RatChunk001Sub000Block107Part018

theorem surrogateDiagonalTailChunk001Sub000Block107Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part018] using hcert

def TailChunk001Sub000Block107Part019SupportExplicit : Finset ℕ :=
  ([20929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part019 : ℚ :=
  (6844110015625 : ℚ) / 119916176900968415232

def SurrogateDiagonalTailChunk001Sub000Block107Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20929
    = surrogateDiagTailX0RatChunk001Sub000Block107Part019

theorem surrogateDiagonalTailChunk001Sub000Block107Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part019] using hcert

def TailChunk001Sub000Block107Part020SupportExplicit : Finset ℕ :=
  ([20930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part020 : ℚ :=
  (146713214575 : ℚ) / 183174431521112064

def SurrogateDiagonalTailChunk001Sub000Block107Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20930
    = surrogateDiagTailX0RatChunk001Sub000Block107Part020

theorem surrogateDiagonalTailChunk001Sub000Block107Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part020] using hcert

def TailChunk001Sub000Block107Part021SupportExplicit : Finset ℕ :=
  ([20931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part021 : ℚ :=
  (12166768302325 : ℚ) / 94748584218049118208

def SurrogateDiagonalTailChunk001Sub000Block107Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20931
    = surrogateDiagTailX0RatChunk001Sub000Block107Part021

theorem surrogateDiagonalTailChunk001Sub000Block107Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part021] using hcert

def TailChunk001Sub000Block107Part022SupportExplicit : Finset ℕ :=
  ([20935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part022 : ℚ :=
  (16605763791475 : ℚ) / 173244162346005823488

def SurrogateDiagonalTailChunk001Sub000Block107Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20935
    = surrogateDiagTailX0RatChunk001Sub000Block107Part022

theorem surrogateDiagonalTailChunk001Sub000Block107Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part022] using hcert

def TailChunk001Sub000Block107Part023SupportExplicit : Finset ℕ :=
  ([20937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part023 : ℚ :=
  (9178542773725 : ℚ) / 51025726486907486208

def SurrogateDiagonalTailChunk001Sub000Block107Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20937
    = surrogateDiagTailX0RatChunk001Sub000Block107Part023

theorem surrogateDiagonalTailChunk001Sub000Block107Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part023] using hcert

def TailChunk001Sub000Block107Part024SupportExplicit : Finset ℕ :=
  ([20939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block107Part024 : ℚ :=
  (6850651890625 : ℚ) / 120145538814917613042

def SurrogateDiagonalTailChunk001Sub000Block107Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20939
    = surrogateDiagTailX0RatChunk001Sub000Block107Part024

theorem surrogateDiagonalTailChunk001Sub000Block107Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block107Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block107Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block107Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block107Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block107Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block107Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block107HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block107Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block107Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block107Part000
    + surrogateDiagTailX0RatChunk001Sub000Block107Part001
    + surrogateDiagTailX0RatChunk001Sub000Block107Part002
    + surrogateDiagTailX0RatChunk001Sub000Block107Part003
    + surrogateDiagTailX0RatChunk001Sub000Block107Part004
    + surrogateDiagTailX0RatChunk001Sub000Block107Part005
    + surrogateDiagTailX0RatChunk001Sub000Block107Part006
    + surrogateDiagTailX0RatChunk001Sub000Block107Part007
    + surrogateDiagTailX0RatChunk001Sub000Block107Part008
    + surrogateDiagTailX0RatChunk001Sub000Block107Part009

def surrogateDiagonalTailChunk001Sub000Block107MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block107Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block107Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block107Part010
    + surrogateDiagTailX0RatChunk001Sub000Block107Part011
    + surrogateDiagTailX0RatChunk001Sub000Block107Part012
    + surrogateDiagTailX0RatChunk001Sub000Block107Part013
    + surrogateDiagTailX0RatChunk001Sub000Block107Part014
    + surrogateDiagTailX0RatChunk001Sub000Block107Part015
    + surrogateDiagTailX0RatChunk001Sub000Block107Part016
    + surrogateDiagTailX0RatChunk001Sub000Block107Part017
    + surrogateDiagTailX0RatChunk001Sub000Block107Part018
    + surrogateDiagTailX0RatChunk001Sub000Block107Part019

def surrogateDiagonalTailChunk001Sub000Block107TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block107Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block107Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block107Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block107Part020
    + surrogateDiagTailX0RatChunk001Sub000Block107Part021
    + surrogateDiagTailX0RatChunk001Sub000Block107Part022
    + surrogateDiagTailX0RatChunk001Sub000Block107Part023
    + surrogateDiagTailX0RatChunk001Sub000Block107Part024

def surrogateDiagonalTailChunk001Sub000Block107Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block107HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block107MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block107TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block107 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block107Part000
    + surrogateDiagTailX0RatChunk001Sub000Block107Part001
    + surrogateDiagTailX0RatChunk001Sub000Block107Part002
    + surrogateDiagTailX0RatChunk001Sub000Block107Part003
    + surrogateDiagTailX0RatChunk001Sub000Block107Part004
    + surrogateDiagTailX0RatChunk001Sub000Block107Part005
    + surrogateDiagTailX0RatChunk001Sub000Block107Part006
    + surrogateDiagTailX0RatChunk001Sub000Block107Part007
    + surrogateDiagTailX0RatChunk001Sub000Block107Part008
    + surrogateDiagTailX0RatChunk001Sub000Block107Part009
    + surrogateDiagTailX0RatChunk001Sub000Block107Part010
    + surrogateDiagTailX0RatChunk001Sub000Block107Part011
    + surrogateDiagTailX0RatChunk001Sub000Block107Part012
    + surrogateDiagTailX0RatChunk001Sub000Block107Part013
    + surrogateDiagTailX0RatChunk001Sub000Block107Part014
    + surrogateDiagTailX0RatChunk001Sub000Block107Part015
    + surrogateDiagTailX0RatChunk001Sub000Block107Part016
    + surrogateDiagTailX0RatChunk001Sub000Block107Part017
    + surrogateDiagTailX0RatChunk001Sub000Block107Part018
    + surrogateDiagTailX0RatChunk001Sub000Block107Part019
    + surrogateDiagTailX0RatChunk001Sub000Block107Part020
    + surrogateDiagTailX0RatChunk001Sub000Block107Part021
    + surrogateDiagTailX0RatChunk001Sub000Block107Part022
    + surrogateDiagTailX0RatChunk001Sub000Block107Part023
    + surrogateDiagTailX0RatChunk001Sub000Block107Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block107_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block107Head + surrogateDiagTailX0RatChunk001Sub000Block107Mid + surrogateDiagTailX0RatChunk001Sub000Block107Tail =
      surrogateDiagTailX0RatChunk001Sub000Block107 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block107Head surrogateDiagTailX0RatChunk001Sub000Block107Mid surrogateDiagTailX0RatChunk001Sub000Block107Tail surrogateDiagTailX0RatChunk001Sub000Block107
  ring

def SurrogateDiagonalTailChunk001Sub000Block107HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block107HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block107Head

def SurrogateDiagonalTailChunk001Sub000Block107MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block107MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block107Mid

def SurrogateDiagonalTailChunk001Sub000Block107TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block107TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block107Tail

theorem surrogateDiagonalTailChunk001Sub000Block107_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block107HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block107MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block107TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block107Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block107 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block107HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block107MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block107TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block107Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block107_eq_head_add_mid_add_tail

/-- Block 108 covers tail-support indices [12700,12725) and q from 20941 to 20981. -/

def TailChunk001Sub000Block108Part000SupportExplicit : Finset ℕ :=
  ([20941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part000 : ℚ :=
  (969947549225 : ℚ) / 16077011905287091584

def SurrogateDiagonalTailChunk001Sub000Block108Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20941
    = surrogateDiagTailX0RatChunk001Sub000Block108Part000

theorem surrogateDiagonalTailChunk001Sub000Block108Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part000] using hcert

def TailChunk001Sub000Block108Part001SupportExplicit : Finset ℕ :=
  ([20942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part001 : ℚ :=
  (3269020261475 : ℚ) / 13280159758495048704

def SurrogateDiagonalTailChunk001Sub000Block108Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20942
    = surrogateDiagTailX0RatChunk001Sub000Block108Part001

theorem surrogateDiagonalTailChunk001Sub000Block108Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part001] using hcert

def TailChunk001Sub000Block108Part002SupportExplicit : Finset ℕ :=
  ([20945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part002 : ℚ :=
  (332671995737 : ℚ) / 3478571657904537600

def SurrogateDiagonalTailChunk001Sub000Block108Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20945
    = surrogateDiagTailX0RatChunk001Sub000Block108Part002

theorem surrogateDiagonalTailChunk001Sub000Block108Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part002] using hcert

def TailChunk001Sub000Block108Part003SupportExplicit : Finset ℕ :=
  ([20946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part003 : ℚ :=
  (121825986037 : ℚ) / 237415211163523200

def SurrogateDiagonalTailChunk001Sub000Block108Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20946
    = surrogateDiagTailX0RatChunk001Sub000Block108Part003

theorem surrogateDiagonalTailChunk001Sub000Block108Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part003] using hcert

def TailChunk001Sub000Block108Part004SupportExplicit : Finset ℕ :=
  ([20947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part004 : ℚ :=
  (6855887640625 : ℚ) / 120329265114269100882

def SurrogateDiagonalTailChunk001Sub000Block108Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20947
    = surrogateDiagTailX0RatChunk001Sub000Block108Part004

theorem surrogateDiagonalTailChunk001Sub000Block108Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part004] using hcert

def TailChunk001Sub000Block108Part005SupportExplicit : Finset ℕ :=
  ([20949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part005 : ℚ :=
  (12187705301725 : ℚ) / 95074974905101511808

def SurrogateDiagonalTailChunk001Sub000Block108Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20949
    = surrogateDiagTailX0RatChunk001Sub000Block108Part005

theorem surrogateDiagonalTailChunk001Sub000Block108Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part005] using hcert

def TailChunk001Sub000Block108Part006SupportExplicit : Finset ℕ :=
  ([20951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part006 : ℚ :=
  (377116510139 : ℚ) / 4458941834172825600

def SurrogateDiagonalTailChunk001Sub000Block108Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20951
    = surrogateDiagTailX0RatChunk001Sub000Block108Part006

theorem surrogateDiagonalTailChunk001Sub000Block108Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part006] using hcert

def TailChunk001Sub000Block108Part007SupportExplicit : Finset ℕ :=
  ([20953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part007 : ℚ :=
  (1012708004107 : ℚ) / 16067308883228803200

def SurrogateDiagonalTailChunk001Sub000Block108Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20953
    = surrogateDiagTailX0RatChunk001Sub000Block108Part007

theorem surrogateDiagonalTailChunk001Sub000Block108Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part007] using hcert

def TailChunk001Sub000Block108Part008SupportExplicit : Finset ℕ :=
  ([20954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part008 : ℚ :=
  (1715117640625 : ℚ) / 7529199878695325472

def SurrogateDiagonalTailChunk001Sub000Block108Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20954
    = surrogateDiagTailX0RatChunk001Sub000Block108Part008

theorem surrogateDiagonalTailChunk001Sub000Block108Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part008] using hcert

def TailChunk001Sub000Block108Part009SupportExplicit : Finset ℕ :=
  ([20955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part009 : ℚ :=
  (39629530663 : ℚ) / 147513218472345600

def SurrogateDiagonalTailChunk001Sub000Block108Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20955
    = surrogateDiagTailX0RatChunk001Sub000Block108Part009

theorem surrogateDiagonalTailChunk001Sub000Block108Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part009] using hcert

def TailChunk001Sub000Block108Part010SupportExplicit : Finset ℕ :=
  ([20957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part010 : ℚ :=
  (1306659200875 : ℚ) / 20374626511516367232

def SurrogateDiagonalTailChunk001Sub000Block108Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20957
    = surrogateDiagTailX0RatChunk001Sub000Block108Part010

theorem surrogateDiagonalTailChunk001Sub000Block108Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part010] using hcert

def TailChunk001Sub000Block108Part011SupportExplicit : Finset ℕ :=
  ([20958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part011 : ℚ :=
  (274230225325 : ℚ) / 354345322825746432

def SurrogateDiagonalTailChunk001Sub000Block108Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20958
    = surrogateDiagTailX0RatChunk001Sub000Block108Part011

theorem surrogateDiagonalTailChunk001Sub000Block108Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part011] using hcert

def TailChunk001Sub000Block108Part012SupportExplicit : Finset ℕ :=
  ([20959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part012 : ℚ :=
  (6863745015625 : ℚ) / 120605249553990274962

def SurrogateDiagonalTailChunk001Sub000Block108Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20959
    = surrogateDiagTailX0RatChunk001Sub000Block108Part012

theorem surrogateDiagonalTailChunk001Sub000Block108Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part012] using hcert

def TailChunk001Sub000Block108Part013SupportExplicit : Finset ℕ :=
  ([20962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part013 : ℚ :=
  (6597613301575 : ℚ) / 27193811537480381568

def SurrogateDiagonalTailChunk001Sub000Block108Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20962
    = surrogateDiagTailX0RatChunk001Sub000Block108Part013

theorem surrogateDiagonalTailChunk001Sub000Block108Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part013] using hcert

def TailChunk001Sub000Block108Part014SupportExplicit : Finset ℕ :=
  ([20963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part014 : ℚ :=
  (6866365140625 : ℚ) / 120697349778550314642

def SurrogateDiagonalTailChunk001Sub000Block108Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20963
    = surrogateDiagTailX0RatChunk001Sub000Block108Part014

theorem surrogateDiagonalTailChunk001Sub000Block108Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part014] using hcert

def TailChunk001Sub000Block108Part015SupportExplicit : Finset ℕ :=
  ([20965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part015 : ℚ :=
  (38161475975 : ℚ) / 302252182307831808

def SurrogateDiagonalTailChunk001Sub000Block108Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20965
    = surrogateDiagTailX0RatChunk001Sub000Block108Part015

theorem surrogateDiagonalTailChunk001Sub000Block108Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part015] using hcert

def TailChunk001Sub000Block108Part016SupportExplicit : Finset ℕ :=
  ([20966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part016 : ℚ :=
  (235794722881 : ℚ) / 821551217804083200

def SurrogateDiagonalTailChunk001Sub000Block108Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20966
    = surrogateDiagTailX0RatChunk001Sub000Block108Part016

theorem surrogateDiagonalTailChunk001Sub000Block108Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part016] using hcert

def TailChunk001Sub000Block108Part017SupportExplicit : Finset ℕ :=
  ([20967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part017 : ℚ :=
  (8476628581 : ℚ) / 60435228052684800

def SurrogateDiagonalTailChunk001Sub000Block108Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20967
    = surrogateDiagTailX0RatChunk001Sub000Block108Part017

theorem surrogateDiagonalTailChunk001Sub000Block108Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part017] using hcert

def TailChunk001Sub000Block108Part018SupportExplicit : Finset ℕ :=
  ([20969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part018 : ℚ :=
  (11940005023175 : ℚ) / 175058014046630068224

def SurrogateDiagonalTailChunk001Sub000Block108Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20969
    = surrogateDiagTailX0RatChunk001Sub000Block108Part018

theorem surrogateDiagonalTailChunk001Sub000Block108Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part018] using hcert

def TailChunk001Sub000Block108Part019SupportExplicit : Finset ℕ :=
  ([20971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part019 : ℚ :=
  (2957307168275 : ℚ) / 49954942990815363072

def SurrogateDiagonalTailChunk001Sub000Block108Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20971
    = surrogateDiagTailX0RatChunk001Sub000Block108Part019

theorem surrogateDiagonalTailChunk001Sub000Block108Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part019] using hcert

def TailChunk001Sub000Block108Part020SupportExplicit : Finset ℕ :=
  ([20973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part020 : ℚ :=
  (488625972037 : ℚ) / 3820458934215043200

def SurrogateDiagonalTailChunk001Sub000Block108Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20973
    = surrogateDiagTailX0RatChunk001Sub000Block108Part020

theorem surrogateDiagonalTailChunk001Sub000Block108Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part020] using hcert

def TailChunk001Sub000Block108Part021SupportExplicit : Finset ℕ :=
  ([20974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part021 : ℚ :=
  (1718393265625 : ℚ) / 7557989444873858802

def SurrogateDiagonalTailChunk001Sub000Block108Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20974
    = surrogateDiagTailX0RatChunk001Sub000Block108Part021

theorem surrogateDiagonalTailChunk001Sub000Block108Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part021] using hcert

def TailChunk001Sub000Block108Part022SupportExplicit : Finset ℕ :=
  ([20977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part022 : ℚ :=
  (18349044401 : ℚ) / 264002738047531584

def SurrogateDiagonalTailChunk001Sub000Block108Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20977
    = surrogateDiagTailX0RatChunk001Sub000Block108Part022

theorem surrogateDiagonalTailChunk001Sub000Block108Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part022] using hcert

def TailChunk001Sub000Block108Part023SupportExplicit : Finset ℕ :=
  ([20978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part023 : ℚ :=
  (148646484375 : ℚ) / 561798205663084544

def SurrogateDiagonalTailChunk001Sub000Block108Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20978
    = surrogateDiagTailX0RatChunk001Sub000Block108Part023

theorem surrogateDiagonalTailChunk001Sub000Block108Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part023] using hcert

def TailChunk001Sub000Block108Part024SupportExplicit : Finset ℕ :=
  ([20981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block108Part024 : ℚ :=
  (11005059025 : ℚ) / 193779925963705632

def SurrogateDiagonalTailChunk001Sub000Block108Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20981
    = surrogateDiagTailX0RatChunk001Sub000Block108Part024

theorem surrogateDiagonalTailChunk001Sub000Block108Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block108Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block108Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block108Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block108Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block108Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block108Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block108HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block108Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block108Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block108Part000
    + surrogateDiagTailX0RatChunk001Sub000Block108Part001
    + surrogateDiagTailX0RatChunk001Sub000Block108Part002
    + surrogateDiagTailX0RatChunk001Sub000Block108Part003
    + surrogateDiagTailX0RatChunk001Sub000Block108Part004
    + surrogateDiagTailX0RatChunk001Sub000Block108Part005
    + surrogateDiagTailX0RatChunk001Sub000Block108Part006
    + surrogateDiagTailX0RatChunk001Sub000Block108Part007
    + surrogateDiagTailX0RatChunk001Sub000Block108Part008
    + surrogateDiagTailX0RatChunk001Sub000Block108Part009

def surrogateDiagonalTailChunk001Sub000Block108MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block108Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block108Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block108Part010
    + surrogateDiagTailX0RatChunk001Sub000Block108Part011
    + surrogateDiagTailX0RatChunk001Sub000Block108Part012
    + surrogateDiagTailX0RatChunk001Sub000Block108Part013
    + surrogateDiagTailX0RatChunk001Sub000Block108Part014
    + surrogateDiagTailX0RatChunk001Sub000Block108Part015
    + surrogateDiagTailX0RatChunk001Sub000Block108Part016
    + surrogateDiagTailX0RatChunk001Sub000Block108Part017
    + surrogateDiagTailX0RatChunk001Sub000Block108Part018
    + surrogateDiagTailX0RatChunk001Sub000Block108Part019

def surrogateDiagonalTailChunk001Sub000Block108TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block108Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block108Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block108Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block108Part020
    + surrogateDiagTailX0RatChunk001Sub000Block108Part021
    + surrogateDiagTailX0RatChunk001Sub000Block108Part022
    + surrogateDiagTailX0RatChunk001Sub000Block108Part023
    + surrogateDiagTailX0RatChunk001Sub000Block108Part024

def surrogateDiagonalTailChunk001Sub000Block108Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block108HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block108MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block108TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block108 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block108Part000
    + surrogateDiagTailX0RatChunk001Sub000Block108Part001
    + surrogateDiagTailX0RatChunk001Sub000Block108Part002
    + surrogateDiagTailX0RatChunk001Sub000Block108Part003
    + surrogateDiagTailX0RatChunk001Sub000Block108Part004
    + surrogateDiagTailX0RatChunk001Sub000Block108Part005
    + surrogateDiagTailX0RatChunk001Sub000Block108Part006
    + surrogateDiagTailX0RatChunk001Sub000Block108Part007
    + surrogateDiagTailX0RatChunk001Sub000Block108Part008
    + surrogateDiagTailX0RatChunk001Sub000Block108Part009
    + surrogateDiagTailX0RatChunk001Sub000Block108Part010
    + surrogateDiagTailX0RatChunk001Sub000Block108Part011
    + surrogateDiagTailX0RatChunk001Sub000Block108Part012
    + surrogateDiagTailX0RatChunk001Sub000Block108Part013
    + surrogateDiagTailX0RatChunk001Sub000Block108Part014
    + surrogateDiagTailX0RatChunk001Sub000Block108Part015
    + surrogateDiagTailX0RatChunk001Sub000Block108Part016
    + surrogateDiagTailX0RatChunk001Sub000Block108Part017
    + surrogateDiagTailX0RatChunk001Sub000Block108Part018
    + surrogateDiagTailX0RatChunk001Sub000Block108Part019
    + surrogateDiagTailX0RatChunk001Sub000Block108Part020
    + surrogateDiagTailX0RatChunk001Sub000Block108Part021
    + surrogateDiagTailX0RatChunk001Sub000Block108Part022
    + surrogateDiagTailX0RatChunk001Sub000Block108Part023
    + surrogateDiagTailX0RatChunk001Sub000Block108Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block108_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block108Head + surrogateDiagTailX0RatChunk001Sub000Block108Mid + surrogateDiagTailX0RatChunk001Sub000Block108Tail =
      surrogateDiagTailX0RatChunk001Sub000Block108 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block108Head surrogateDiagTailX0RatChunk001Sub000Block108Mid surrogateDiagTailX0RatChunk001Sub000Block108Tail surrogateDiagTailX0RatChunk001Sub000Block108
  ring

def SurrogateDiagonalTailChunk001Sub000Block108HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block108HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block108Head

def SurrogateDiagonalTailChunk001Sub000Block108MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block108MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block108Mid

def SurrogateDiagonalTailChunk001Sub000Block108TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block108TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block108Tail

theorem surrogateDiagonalTailChunk001Sub000Block108_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block108HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block108MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block108TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block108Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block108 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block108HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block108MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block108TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block108Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block108_eq_head_add_mid_add_tail

/-- Block 109 covers tail-support indices [12725,12750) and q from 20982 to 21018. -/

def TailChunk001Sub000Block109Part000SupportExplicit : Finset ℕ :=
  ([20982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part000 : ℚ :=
  (422959648475 : ℚ) / 534959636204814336

def SurrogateDiagonalTailChunk001Sub000Block109Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20982
    = surrogateDiagTailX0RatChunk001Sub000Block109Part000

theorem surrogateDiagonalTailChunk001Sub000Block109Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part000] using hcert

def TailChunk001Sub000Block109Part001SupportExplicit : Finset ℕ :=
  ([20983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part001 : ℚ :=
  (6879473265625 : ℚ) / 121158642391987387122

def SurrogateDiagonalTailChunk001Sub000Block109Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20983
    = surrogateDiagTailX0RatChunk001Sub000Block109Part001

theorem surrogateDiagonalTailChunk001Sub000Block109Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part001] using hcert

def TailChunk001Sub000Block109Part002SupportExplicit : Finset ℕ :=
  ([20985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part002 : ℚ :=
  (2015893845625 : ℚ) / 9780374871590510592

def SurrogateDiagonalTailChunk001Sub000Block109Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20985
    = surrogateDiagTailX0RatChunk001Sub000Block109Part002

theorem surrogateDiagonalTailChunk001Sub000Block109Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part002] using hcert

def TailChunk001Sub000Block109Part003SupportExplicit : Finset ℕ :=
  ([20986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part003 : ℚ :=
  (11901781225 : ℚ) / 36425129114939166

def SurrogateDiagonalTailChunk001Sub000Block109Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20986
    = surrogateDiagTailX0RatChunk001Sub000Block109Part003

theorem surrogateDiagonalTailChunk001Sub000Block109Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part003] using hcert

def TailChunk001Sub000Block109Part004SupportExplicit : Finset ℕ :=
  ([20987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part004 : ℚ :=
  (79653665251 : ℚ) / 1301413479161702400

def SurrogateDiagonalTailChunk001Sub000Block109Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20987
    = surrogateDiagTailX0RatChunk001Sub000Block109Part004

theorem surrogateDiagonalTailChunk001Sub000Block109Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part004] using hcert

def TailChunk001Sub000Block109Part005SupportExplicit : Finset ℕ :=
  ([20989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part005 : ℚ :=
  (8396801369 : ℚ) / 143469063153140625

def SurrogateDiagonalTailChunk001Sub000Block109Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20989
    = surrogateDiagTailX0RatChunk001Sub000Block109Part005

theorem surrogateDiagonalTailChunk001Sub000Block109Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part005] using hcert

def TailChunk001Sub000Block109Part006SupportExplicit : Finset ℕ :=
  ([20990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part006 : ℚ :=
  (4678394755225 : ℚ) / 12401915261677160448

def SurrogateDiagonalTailChunk001Sub000Block109Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20990
    = surrogateDiagTailX0RatChunk001Sub000Block109Part006

theorem surrogateDiagonalTailChunk001Sub000Block109Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part006] using hcert

def TailChunk001Sub000Block109Part007SupportExplicit : Finset ℕ :=
  ([20991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part007 : ℚ :=
  (1112420754575 : ℚ) / 8712712020177082368

def SurrogateDiagonalTailChunk001Sub000Block109Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20991
    = surrogateDiagTailX0RatChunk001Sub000Block109Part007

theorem surrogateDiagonalTailChunk001Sub000Block109Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part007] using hcert

def TailChunk001Sub000Block109Part008SupportExplicit : Finset ℕ :=
  ([20993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part008 : ℚ :=
  (20787976951225 : ℚ) / 261793207700917642368

def SurrogateDiagonalTailChunk001Sub000Block109Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20993
    = surrogateDiagTailX0RatChunk001Sub000Block109Part008

theorem surrogateDiagonalTailChunk001Sub000Block109Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part008] using hcert

def TailChunk001Sub000Block109Part009SupportExplicit : Finset ℕ :=
  ([20994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part009 : ℚ :=
  (478123487525 : ℚ) / 748748689233968016

def SurrogateDiagonalTailChunk001Sub000Block109Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20994
    = surrogateDiagTailX0RatChunk001Sub000Block109Part009

theorem surrogateDiagonalTailChunk001Sub000Block109Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part009] using hcert

def TailChunk001Sub000Block109Part010SupportExplicit : Finset ℕ :=
  ([20995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part010 : ℚ :=
  (6300213688475 : ℚ) / 45659564381929734144

def SurrogateDiagonalTailChunk001Sub000Block109Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20995
    = surrogateDiagTailX0RatChunk001Sub000Block109Part010

theorem surrogateDiagonalTailChunk001Sub000Block109Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part010] using hcert

def TailChunk001Sub000Block109Part011SupportExplicit : Finset ℕ :=
  ([20998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part011 : ℚ :=
  (1722328140625 : ℚ) / 7592645816558218002

def SurrogateDiagonalTailChunk001Sub000Block109Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20998
    = surrogateDiagTailX0RatChunk001Sub000Block109Part011

theorem surrogateDiagonalTailChunk001Sub000Block109Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part011] using hcert

def TailChunk001Sub000Block109Part012SupportExplicit : Finset ℕ :=
  ([20999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part012 : ℚ :=
  (140311429473 : ℚ) / 1765556957626035200

def SurrogateDiagonalTailChunk001Sub000Block109Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20999
    = surrogateDiagTailX0RatChunk001Sub000Block109Part012

theorem surrogateDiagonalTailChunk001Sub000Block109Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part012] using hcert

def TailChunk001Sub000Block109Part013SupportExplicit : Finset ℕ :=
  ([21001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part013 : ℚ :=
  (441042001 : ℚ) / 7780795848000000

def SurrogateDiagonalTailChunk001Sub000Block109Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21001
    = surrogateDiagTailX0RatChunk001Sub000Block109Part013

theorem surrogateDiagonalTailChunk001Sub000Block109Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part013] using hcert

def TailChunk001Sub000Block109Part014SupportExplicit : Finset ℕ :=
  ([21002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part014 : ℚ :=
  (110271001 : ℚ) / 486299740500000

def SurrogateDiagonalTailChunk001Sub000Block109Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21002
    = surrogateDiagTailX0RatChunk001Sub000Block109Part014

theorem surrogateDiagonalTailChunk001Sub000Block109Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part014] using hcert

def TailChunk001Sub000Block109Part015SupportExplicit : Finset ℕ :=
  ([21003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part015 : ℚ :=
  (490024971997 : ℚ) / 3842368320000000000

def SurrogateDiagonalTailChunk001Sub000Block109Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21003
    = surrogateDiagTailX0RatChunk001Sub000Block109Part015

theorem surrogateDiagonalTailChunk001Sub000Block109Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part015] using hcert

def TailChunk001Sub000Block109Part016SupportExplicit : Finset ℕ :=
  ([21005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part016 : ℚ :=
  (23521667 : ℚ) / 265584498278400

def SurrogateDiagonalTailChunk001Sub000Block109Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21005
    = surrogateDiagTailX0RatChunk001Sub000Block109Part016

theorem surrogateDiagonalTailChunk001Sub000Block109Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part016] using hcert

def TailChunk001Sub000Block109Part017SupportExplicit : Finset ℕ :=
  ([21007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part017 : ℚ :=
  (166525755989 : ℚ) / 2099939904000000000

def SurrogateDiagonalTailChunk001Sub000Block109Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21007
    = surrogateDiagTailX0RatChunk001Sub000Block109Part017

theorem surrogateDiagonalTailChunk001Sub000Block109Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part017] using hcert

def TailChunk001Sub000Block109Part018SupportExplicit : Finset ℕ :=
  ([21009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part018 : ℚ :=
  (975105485775 : ℚ) / 7162156125097713664

def SurrogateDiagonalTailChunk001Sub000Block109Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21009
    = surrogateDiagTailX0RatChunk001Sub000Block109Part018

theorem surrogateDiagonalTailChunk001Sub000Block109Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part018] using hcert

def TailChunk001Sub000Block109Part019SupportExplicit : Finset ℕ :=
  ([21010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part019 : ℚ :=
  (85230476501 : ℚ) / 166844242176000000

def SurrogateDiagonalTailChunk001Sub000Block109Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21010
    = surrogateDiagTailX0RatChunk001Sub000Block109Part019

theorem surrogateDiagonalTailChunk001Sub000Block109Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part019] using hcert

def TailChunk001Sub000Block109Part020SupportExplicit : Finset ℕ :=
  ([21011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part020 : ℚ :=
  (11036553025 : ℚ) / 194890675024946802

def SurrogateDiagonalTailChunk001Sub000Block109Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21011
    = surrogateDiagTailX0RatChunk001Sub000Block109Part020

theorem surrogateDiagonalTailChunk001Sub000Block109Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part020] using hcert

def TailChunk001Sub000Block109Part021SupportExplicit : Finset ℕ :=
  ([21013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part021 : ℚ :=
  (6899158890625 : ℚ) / 121853058969379106592

def SurrogateDiagonalTailChunk001Sub000Block109Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21013
    = surrogateDiagTailX0RatChunk001Sub000Block109Part021

theorem surrogateDiagonalTailChunk001Sub000Block109Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part021] using hcert

def TailChunk001Sub000Block109Part022SupportExplicit : Finset ℕ :=
  ([21014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part022 : ℚ :=
  (2421982940075 : ℚ) / 6296080844598764544

def SurrogateDiagonalTailChunk001Sub000Block109Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21014
    = surrogateDiagTailX0RatChunk001Sub000Block109Part022

theorem surrogateDiagonalTailChunk001Sub000Block109Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part022] using hcert

def TailChunk001Sub000Block109Part023SupportExplicit : Finset ℕ :=
  ([21017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part023 : ℚ :=
  (6901785765625 : ℚ) / 121945872872795976192

def SurrogateDiagonalTailChunk001Sub000Block109Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21017
    = surrogateDiagTailX0RatChunk001Sub000Block109Part023

theorem surrogateDiagonalTailChunk001Sub000Block109Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part023] using hcert

def TailChunk001Sub000Block109Part024SupportExplicit : Finset ℕ :=
  ([21018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block109Part024 : ℚ :=
  (5781918505 : ℚ) / 8158755787112448

def SurrogateDiagonalTailChunk001Sub000Block109Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21018
    = surrogateDiagTailX0RatChunk001Sub000Block109Part024

theorem surrogateDiagonalTailChunk001Sub000Block109Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block109Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block109Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block109Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block109Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block109Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block109Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block109HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block109Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block109Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block109Part000
    + surrogateDiagTailX0RatChunk001Sub000Block109Part001
    + surrogateDiagTailX0RatChunk001Sub000Block109Part002
    + surrogateDiagTailX0RatChunk001Sub000Block109Part003
    + surrogateDiagTailX0RatChunk001Sub000Block109Part004
    + surrogateDiagTailX0RatChunk001Sub000Block109Part005
    + surrogateDiagTailX0RatChunk001Sub000Block109Part006
    + surrogateDiagTailX0RatChunk001Sub000Block109Part007
    + surrogateDiagTailX0RatChunk001Sub000Block109Part008
    + surrogateDiagTailX0RatChunk001Sub000Block109Part009

def surrogateDiagonalTailChunk001Sub000Block109MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block109Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block109Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block109Part010
    + surrogateDiagTailX0RatChunk001Sub000Block109Part011
    + surrogateDiagTailX0RatChunk001Sub000Block109Part012
    + surrogateDiagTailX0RatChunk001Sub000Block109Part013
    + surrogateDiagTailX0RatChunk001Sub000Block109Part014
    + surrogateDiagTailX0RatChunk001Sub000Block109Part015
    + surrogateDiagTailX0RatChunk001Sub000Block109Part016
    + surrogateDiagTailX0RatChunk001Sub000Block109Part017
    + surrogateDiagTailX0RatChunk001Sub000Block109Part018
    + surrogateDiagTailX0RatChunk001Sub000Block109Part019

def surrogateDiagonalTailChunk001Sub000Block109TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block109Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block109Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block109Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block109Part020
    + surrogateDiagTailX0RatChunk001Sub000Block109Part021
    + surrogateDiagTailX0RatChunk001Sub000Block109Part022
    + surrogateDiagTailX0RatChunk001Sub000Block109Part023
    + surrogateDiagTailX0RatChunk001Sub000Block109Part024

def surrogateDiagonalTailChunk001Sub000Block109Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block109HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block109MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block109TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block109 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block109Part000
    + surrogateDiagTailX0RatChunk001Sub000Block109Part001
    + surrogateDiagTailX0RatChunk001Sub000Block109Part002
    + surrogateDiagTailX0RatChunk001Sub000Block109Part003
    + surrogateDiagTailX0RatChunk001Sub000Block109Part004
    + surrogateDiagTailX0RatChunk001Sub000Block109Part005
    + surrogateDiagTailX0RatChunk001Sub000Block109Part006
    + surrogateDiagTailX0RatChunk001Sub000Block109Part007
    + surrogateDiagTailX0RatChunk001Sub000Block109Part008
    + surrogateDiagTailX0RatChunk001Sub000Block109Part009
    + surrogateDiagTailX0RatChunk001Sub000Block109Part010
    + surrogateDiagTailX0RatChunk001Sub000Block109Part011
    + surrogateDiagTailX0RatChunk001Sub000Block109Part012
    + surrogateDiagTailX0RatChunk001Sub000Block109Part013
    + surrogateDiagTailX0RatChunk001Sub000Block109Part014
    + surrogateDiagTailX0RatChunk001Sub000Block109Part015
    + surrogateDiagTailX0RatChunk001Sub000Block109Part016
    + surrogateDiagTailX0RatChunk001Sub000Block109Part017
    + surrogateDiagTailX0RatChunk001Sub000Block109Part018
    + surrogateDiagTailX0RatChunk001Sub000Block109Part019
    + surrogateDiagTailX0RatChunk001Sub000Block109Part020
    + surrogateDiagTailX0RatChunk001Sub000Block109Part021
    + surrogateDiagTailX0RatChunk001Sub000Block109Part022
    + surrogateDiagTailX0RatChunk001Sub000Block109Part023
    + surrogateDiagTailX0RatChunk001Sub000Block109Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block109_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block109Head + surrogateDiagTailX0RatChunk001Sub000Block109Mid + surrogateDiagTailX0RatChunk001Sub000Block109Tail =
      surrogateDiagTailX0RatChunk001Sub000Block109 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block109Head surrogateDiagTailX0RatChunk001Sub000Block109Mid surrogateDiagTailX0RatChunk001Sub000Block109Tail surrogateDiagTailX0RatChunk001Sub000Block109
  ring

def SurrogateDiagonalTailChunk001Sub000Block109HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block109HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block109Head

def SurrogateDiagonalTailChunk001Sub000Block109MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block109MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block109Mid

def SurrogateDiagonalTailChunk001Sub000Block109TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block109TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block109Tail

theorem surrogateDiagonalTailChunk001Sub000Block109_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block109HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block109MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block109TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block109Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block109 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block109HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block109MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block109TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block109Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block109_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
