import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [159,160). -/

/- Block 159 covers tail-support indices [3975,4000) and q from 6587 to 6626. -/

def TailChunk000Sub000Block159Part000SupportExplicit : Finset ℕ :=
  ([6587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part000 : ℚ :=
  (88450787863 : ℚ) / 101205302229043200

def SurrogateDiagonalTailChunk000Sub000Block159Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6587
    = surrogateDiagTailX0RatChunk000Sub000Block159Part000

theorem surrogateDiagonalTailChunk000Sub000Block159Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part000] using hcert

def TailChunk000Sub000Block159Part001SupportExplicit : Finset ℕ :=
  ([6589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part001 : ℚ :=
  (1401399243 : ℚ) / 1853712999132800

def SurrogateDiagonalTailChunk000Sub000Block159Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6589
    = surrogateDiagTailX0RatChunk000Sub000Block159Part001

theorem surrogateDiagonalTailChunk000Sub000Block159Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part001] using hcert

def TailChunk000Sub000Block159Part002SupportExplicit : Finset ℕ :=
  ([6590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part002 : ℚ :=
  (343240816725 : ℚ) / 39999000930359296

def SurrogateDiagonalTailChunk000Sub000Block159Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6590
    = surrogateDiagTailX0RatChunk000Sub000Block159Part002

theorem surrogateDiagonalTailChunk000Sub000Block159Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part002] using hcert

def TailChunk000Sub000Block159Part003SupportExplicit : Finset ℕ :=
  ([6593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part003 : ℚ :=
  (422513991575 : ℚ) / 627003585135338688

def SurrogateDiagonalTailChunk000Sub000Block159Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6593
    = surrogateDiagTailX0RatChunk000Sub000Block159Part003

theorem surrogateDiagonalTailChunk000Sub000Block159Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part003] using hcert

def TailChunk000Sub000Block159Part004SupportExplicit : Finset ℕ :=
  ([6594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part004 : ℚ :=
  (6373123075 : ℚ) / 284332485206016

def SurrogateDiagonalTailChunk000Sub000Block159Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6594
    = surrogateDiagTailX0RatChunk000Sub000Block159Part004

theorem surrogateDiagonalTailChunk000Sub000Block159Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part004] using hcert

def TailChunk000Sub000Block159Part005SupportExplicit : Finset ℕ :=
  ([6595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part005 : ℚ :=
  (651939584475 : ℚ) / 643883373084645376

def SurrogateDiagonalTailChunk000Sub000Block159Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6595
    = surrogateDiagTailX0RatChunk000Sub000Block159Part005

theorem surrogateDiagonalTailChunk000Sub000Block159Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part005] using hcert

def TailChunk000Sub000Block159Part006SupportExplicit : Finset ℕ :=
  ([6598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part006 : ℚ :=
  (1360153039975 : ℚ) / 295821315568667208

def SurrogateDiagonalTailChunk000Sub000Block159Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6598
    = surrogateDiagTailX0RatChunk000Sub000Block159Part006

theorem surrogateDiagonalTailChunk000Sub000Block159Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part006] using hcert

def TailChunk000Sub000Block159Part007SupportExplicit : Finset ℕ :=
  ([6599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part007 : ℚ :=
  (680418765625 : ℚ) / 1184721070102663602

def SurrogateDiagonalTailChunk000Sub000Block159Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6599
    = surrogateDiagTailX0RatChunk000Sub000Block159Part007

theorem surrogateDiagonalTailChunk000Sub000Block159Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part007] using hcert

def TailChunk000Sub000Block159Part008SupportExplicit : Finset ℕ :=
  ([6601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part008 : ℚ :=
  (5109961687 : ℚ) / 4858503922483200

def SurrogateDiagonalTailChunk000Sub000Block159Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6601
    = surrogateDiagTailX0RatChunk000Sub000Block159Part008

theorem surrogateDiagonalTailChunk000Sub000Block159Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part008] using hcert

def TailChunk000Sub000Block159Part009SupportExplicit : Finset ℕ :=
  ([6602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part009 : ℚ :=
  (10896601 : ℚ) / 4744632736800

def SurrogateDiagonalTailChunk000Sub000Block159Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6602
    = surrogateDiagTailX0RatChunk000Sub000Block159Part009

theorem surrogateDiagonalTailChunk000Sub000Block159Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part009] using hcert

def TailChunk000Sub000Block159Part010SupportExplicit : Finset ℕ :=
  ([6603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part010 : ℚ :=
  (2396452193 : ℚ) / 1296799308000000

def SurrogateDiagonalTailChunk000Sub000Block159Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6603
    = surrogateDiagTailX0RatChunk000Sub000Block159Part010

theorem surrogateDiagonalTailChunk000Sub000Block159Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part010] using hcert

def TailChunk000Sub000Block159Part011SupportExplicit : Finset ℕ :=
  ([6605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part011 : ℚ :=
  (13804948009 : ℚ) / 12956010459955200

def SurrogateDiagonalTailChunk000Sub000Block159Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6605
    = surrogateDiagTailX0RatChunk000Sub000Block159Part011

theorem surrogateDiagonalTailChunk000Sub000Block159Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part011] using hcert

def TailChunk000Sub000Block159Part012SupportExplicit : Finset ℕ :=
  ([6607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part012 : ℚ :=
  (682069515625 : ℚ) / 1190477372029642962

def SurrogateDiagonalTailChunk000Sub000Block159Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6607
    = surrogateDiagTailX0RatChunk000Sub000Block159Part012

theorem surrogateDiagonalTailChunk000Sub000Block159Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part012] using hcert

def TailChunk000Sub000Block159Part013SupportExplicit : Finset ℕ :=
  ([6609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part013 : ℚ :=
  (60630875 : ℚ) / 31347866973888

def SurrogateDiagonalTailChunk000Sub000Block159Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6609
    = surrogateDiagTailX0RatChunk000Sub000Block159Part013

theorem surrogateDiagonalTailChunk000Sub000Block159Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part013] using hcert

def TailChunk000Sub000Block159Part014SupportExplicit : Finset ℕ :=
  ([6610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part014 : ℚ :=
  (8003969153 : ℚ) / 1619501307494400

def SurrogateDiagonalTailChunk000Sub000Block159Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6610
    = surrogateDiagTailX0RatChunk000Sub000Block159Part014

theorem surrogateDiagonalTailChunk000Sub000Block159Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part014] using hcert

def TailChunk000Sub000Block159Part015SupportExplicit : Finset ℕ :=
  ([6611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part015 : ℚ :=
  (97343592367 : ℚ) / 129625920000000000

def SurrogateDiagonalTailChunk000Sub000Block159Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6611
    = surrogateDiagTailX0RatChunk000Sub000Block159Part015

theorem surrogateDiagonalTailChunk000Sub000Block159Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part015] using hcert

def TailChunk000Sub000Block159Part016SupportExplicit : Finset ℕ :=
  ([6613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part016 : ℚ :=
  (2527068375175 : ℚ) / 3713929811589070848

def SurrogateDiagonalTailChunk000Sub000Block159Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6613
    = surrogateDiagTailX0RatChunk000Sub000Block159Part016

theorem surrogateDiagonalTailChunk000Sub000Block159Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part016] using hcert

def TailChunk000Sub000Block159Part017SupportExplicit : Finset ℕ :=
  ([6614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part017 : ℚ :=
  (170878890625 : ℚ) / 74675521550696562

def SurrogateDiagonalTailChunk000Sub000Block159Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6614
    = surrogateDiagTailX0RatChunk000Sub000Block159Part017

theorem surrogateDiagonalTailChunk000Sub000Block159Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part017] using hcert

def TailChunk000Sub000Block159Part018SupportExplicit : Finset ℕ :=
  ([6617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part018 : ℚ :=
  (2471946239575 : ℚ) / 3453080414483939328

def SurrogateDiagonalTailChunk000Sub000Block159Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6617
    = surrogateDiagTailX0RatChunk000Sub000Block159Part018

theorem surrogateDiagonalTailChunk000Sub000Block159Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part018] using hcert

def TailChunk000Sub000Block159Part019SupportExplicit : Finset ℕ :=
  ([6618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part019 : ℚ :=
  (532017615175 : ℚ) / 59002881225241728

def SurrogateDiagonalTailChunk000Sub000Block159Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6618
    = surrogateDiagTailX0RatChunk000Sub000Block159Part019

theorem surrogateDiagonalTailChunk000Sub000Block159Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part019] using hcert

def TailChunk000Sub000Block159Part020SupportExplicit : Finset ℕ :=
  ([6619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part020 : ℚ :=
  (684549390625 : ℚ) / 1199151123961948722

def SurrogateDiagonalTailChunk000Sub000Block159Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6619
    = surrogateDiagTailX0RatChunk000Sub000Block159Part020

theorem surrogateDiagonalTailChunk000Sub000Block159Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part020] using hcert

def TailChunk000Sub000Block159Part021SupportExplicit : Finset ℕ :=
  ([6621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part021 : ℚ :=
  (380407363525 : ℚ) / 236869357819644192

def SurrogateDiagonalTailChunk000Sub000Block159Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6621
    = surrogateDiagTailX0RatChunk000Sub000Block159Part021

theorem surrogateDiagonalTailChunk000Sub000Block159Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part021] using hcert

def TailChunk000Sub000Block159Part022SupportExplicit : Finset ℕ :=
  ([6622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part022 : ℚ :=
  (365217001 : ℚ) / 63024446368800

def SurrogateDiagonalTailChunk000Sub000Block159Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6622
    = surrogateDiagTailX0RatChunk000Sub000Block159Part022

theorem surrogateDiagonalTailChunk000Sub000Block159Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part022] using hcert

def TailChunk000Sub000Block159Part023SupportExplicit : Finset ℕ :=
  ([6623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part023 : ℚ :=
  (97463729975 : ℚ) / 156153997679745024

def SurrogateDiagonalTailChunk000Sub000Block159Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6623
    = surrogateDiagTailX0RatChunk000Sub000Block159Part023

theorem surrogateDiagonalTailChunk000Sub000Block159Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part023] using hcert

def TailChunk000Sub000Block159Part024SupportExplicit : Finset ℕ :=
  ([6626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block159Part024 : ℚ :=
  (1371721725775 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk000Sub000Block159Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6626
    = surrogateDiagTailX0RatChunk000Sub000Block159Part024

theorem surrogateDiagonalTailChunk000Sub000Block159Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block159Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block159Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block159Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block159Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block159Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block159Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block159HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block159Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block159Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block159Part000
    + surrogateDiagTailX0RatChunk000Sub000Block159Part001
    + surrogateDiagTailX0RatChunk000Sub000Block159Part002
    + surrogateDiagTailX0RatChunk000Sub000Block159Part003
    + surrogateDiagTailX0RatChunk000Sub000Block159Part004
    + surrogateDiagTailX0RatChunk000Sub000Block159Part005
    + surrogateDiagTailX0RatChunk000Sub000Block159Part006
    + surrogateDiagTailX0RatChunk000Sub000Block159Part007
    + surrogateDiagTailX0RatChunk000Sub000Block159Part008
    + surrogateDiagTailX0RatChunk000Sub000Block159Part009

def surrogateDiagonalTailChunk000Sub000Block159MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block159Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block159Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block159Part010
    + surrogateDiagTailX0RatChunk000Sub000Block159Part011
    + surrogateDiagTailX0RatChunk000Sub000Block159Part012
    + surrogateDiagTailX0RatChunk000Sub000Block159Part013
    + surrogateDiagTailX0RatChunk000Sub000Block159Part014
    + surrogateDiagTailX0RatChunk000Sub000Block159Part015
    + surrogateDiagTailX0RatChunk000Sub000Block159Part016
    + surrogateDiagTailX0RatChunk000Sub000Block159Part017
    + surrogateDiagTailX0RatChunk000Sub000Block159Part018
    + surrogateDiagTailX0RatChunk000Sub000Block159Part019

def surrogateDiagonalTailChunk000Sub000Block159TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block159Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block159Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block159Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block159Part020
    + surrogateDiagTailX0RatChunk000Sub000Block159Part021
    + surrogateDiagTailX0RatChunk000Sub000Block159Part022
    + surrogateDiagTailX0RatChunk000Sub000Block159Part023
    + surrogateDiagTailX0RatChunk000Sub000Block159Part024

def surrogateDiagonalTailChunk000Sub000Block159Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block159HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block159MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block159TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block159 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block159Part000
    + surrogateDiagTailX0RatChunk000Sub000Block159Part001
    + surrogateDiagTailX0RatChunk000Sub000Block159Part002
    + surrogateDiagTailX0RatChunk000Sub000Block159Part003
    + surrogateDiagTailX0RatChunk000Sub000Block159Part004
    + surrogateDiagTailX0RatChunk000Sub000Block159Part005
    + surrogateDiagTailX0RatChunk000Sub000Block159Part006
    + surrogateDiagTailX0RatChunk000Sub000Block159Part007
    + surrogateDiagTailX0RatChunk000Sub000Block159Part008
    + surrogateDiagTailX0RatChunk000Sub000Block159Part009
    + surrogateDiagTailX0RatChunk000Sub000Block159Part010
    + surrogateDiagTailX0RatChunk000Sub000Block159Part011
    + surrogateDiagTailX0RatChunk000Sub000Block159Part012
    + surrogateDiagTailX0RatChunk000Sub000Block159Part013
    + surrogateDiagTailX0RatChunk000Sub000Block159Part014
    + surrogateDiagTailX0RatChunk000Sub000Block159Part015
    + surrogateDiagTailX0RatChunk000Sub000Block159Part016
    + surrogateDiagTailX0RatChunk000Sub000Block159Part017
    + surrogateDiagTailX0RatChunk000Sub000Block159Part018
    + surrogateDiagTailX0RatChunk000Sub000Block159Part019
    + surrogateDiagTailX0RatChunk000Sub000Block159Part020
    + surrogateDiagTailX0RatChunk000Sub000Block159Part021
    + surrogateDiagTailX0RatChunk000Sub000Block159Part022
    + surrogateDiagTailX0RatChunk000Sub000Block159Part023
    + surrogateDiagTailX0RatChunk000Sub000Block159Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block159_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block159Head + surrogateDiagTailX0RatChunk000Sub000Block159Mid + surrogateDiagTailX0RatChunk000Sub000Block159Tail =
      surrogateDiagTailX0RatChunk000Sub000Block159 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block159Head surrogateDiagTailX0RatChunk000Sub000Block159Mid surrogateDiagTailX0RatChunk000Sub000Block159Tail surrogateDiagTailX0RatChunk000Sub000Block159
  ring

def SurrogateDiagonalTailChunk000Sub000Block159HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block159HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block159Head

def SurrogateDiagonalTailChunk000Sub000Block159MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block159MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block159Mid

def SurrogateDiagonalTailChunk000Sub000Block159TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block159TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block159Tail

theorem surrogateDiagonalTailChunk000Sub000Block159_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block159HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block159MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block159TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block159Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block159 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block159HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block159MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block159TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block159Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block159_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
