import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [144,145). -/

/- Block 144 covers tail-support indices [3600,3625) and q from 5977 to 6014. -/

def TailChunk000Sub000Block144Part000SupportExplicit : Finset ℕ :=
  ([5977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part000 : ℚ :=
  (1077385783625 : ℚ) / 1410945927703308864

def SurrogateDiagonalTailChunk000Sub000Block144Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5977
    = surrogateDiagTailX0RatChunk000Sub000Block144Part000

theorem surrogateDiagonalTailChunk000Sub000Block144Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part000] using hcert

def TailChunk000Sub000Block144Part001SupportExplicit : Finset ℕ :=
  ([5979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part001 : ℚ :=
  (49621625 : ℚ) / 20994042544128

def SurrogateDiagonalTailChunk000Sub000Block144Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5979
    = surrogateDiagTailX0RatChunk000Sub000Block144Part001

theorem surrogateDiagonalTailChunk000Sub000Block144Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part001] using hcert

def TailChunk000Sub000Block144Part002SupportExplicit : Finset ℕ :=
  ([5981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part002 : ℚ :=
  (894309025 : ℚ) / 1279061969401632

def SurrogateDiagonalTailChunk000Sub000Block144Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5981
    = surrogateDiagTailX0RatChunk000Sub000Block144Part002

theorem surrogateDiagonalTailChunk000Sub000Block144Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part002] using hcert

def TailChunk000Sub000Block144Part003SupportExplicit : Finset ℕ :=
  ([5982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part003 : ℚ :=
  (496682251075 : ℚ) / 39371702536194048

def SurrogateDiagonalTailChunk000Sub000Block144Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5982
    = surrogateDiagTailX0RatChunk000Sub000Block144Part003

theorem surrogateDiagonalTailChunk000Sub000Block144Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part003] using hcert

def TailChunk000Sub000Block144Part004SupportExplicit : Finset ℕ :=
  ([5983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part004 : ℚ :=
  (1903037471 : ℚ) / 2446607316418560

def SurrogateDiagonalTailChunk000Sub000Block144Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5983
    = surrogateDiagTailX0RatChunk000Sub000Block144Part004

theorem surrogateDiagonalTailChunk000Sub000Block144Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part004] using hcert

def TailChunk000Sub000Block144Part005SupportExplicit : Finset ℕ :=
  ([5986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part005 : ℚ :=
  (11051412839 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block144Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5986
    = surrogateDiagTailX0RatChunk000Sub000Block144Part005

theorem surrogateDiagonalTailChunk000Sub000Block144Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part005] using hcert

def TailChunk000Sub000Block144Part006SupportExplicit : Finset ℕ :=
  ([5987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part006 : ℚ :=
  (560065140625 : ℚ) / 802626912147782802

def SurrogateDiagonalTailChunk000Sub000Block144Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5987
    = surrogateDiagTailX0RatChunk000Sub000Block144Part006

theorem surrogateDiagonalTailChunk000Sub000Block144Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part006] using hcert

def TailChunk000Sub000Block144Part007SupportExplicit : Finset ℕ :=
  ([5989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part007 : ℚ :=
  (723682179375 : ℚ) / 958939193562628096

def SurrogateDiagonalTailChunk000Sub000Block144Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5989
    = surrogateDiagTailX0RatChunk000Sub000Block144Part007

theorem surrogateDiagonalTailChunk000Sub000Block144Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part007] using hcert

def TailChunk000Sub000Block144Part008SupportExplicit : Finset ℕ :=
  ([5990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part008 : ℚ :=
  (436539234425 : ℚ) / 40929983020852224

def SurrogateDiagonalTailChunk000Sub000Block144Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5990
    = surrogateDiagTailX0RatChunk000Sub000Block144Part008

theorem surrogateDiagonalTailChunk000Sub000Block144Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part008] using hcert

def TailChunk000Sub000Block144Part009SupportExplicit : Finset ℕ :=
  ([5991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part009 : ℚ :=
  (622914544175 : ℚ) / 317511159299073024

def SurrogateDiagonalTailChunk000Sub000Block144Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5991
    = surrogateDiagTailX0RatChunk000Sub000Block144Part009

theorem surrogateDiagonalTailChunk000Sub000Block144Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part009] using hcert

def TailChunk000Sub000Block144Part010SupportExplicit : Finset ℕ :=
  ([5993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part010 : ℚ :=
  (27210552263 : ℚ) / 30954365507174400

def SurrogateDiagonalTailChunk000Sub000Block144Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5993
    = surrogateDiagTailX0RatChunk000Sub000Block144Part010

theorem surrogateDiagonalTailChunk000Sub000Block144Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part010] using hcert

def TailChunk000Sub000Block144Part011SupportExplicit : Finset ℕ :=
  ([5995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part011 : ℚ :=
  (60634518979 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub000Block144Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5995
    = surrogateDiagTailX0RatChunk000Sub000Block144Part011

theorem surrogateDiagonalTailChunk000Sub000Block144Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part011] using hcert

def TailChunk000Sub000Block144Part012SupportExplicit : Finset ℕ :=
  ([5997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part012 : ℚ :=
  (312081434425 : ℚ) / 159392831552032032

def SurrogateDiagonalTailChunk000Sub000Block144Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5997
    = surrogateDiagTailX0RatChunk000Sub000Block144Part012

theorem surrogateDiagonalTailChunk000Sub000Block144Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part012] using hcert

def TailChunk000Sub000Block144Part013SupportExplicit : Finset ℕ :=
  ([5998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part013 : ℚ :=
  (1124025274975 : ℚ) / 202000931867992008

def SurrogateDiagonalTailChunk000Sub000Block144Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5998
    = surrogateDiagTailX0RatChunk000Sub000Block144Part013

theorem surrogateDiagonalTailChunk000Sub000Block144Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part013] using hcert

def TailChunk000Sub000Block144Part014SupportExplicit : Finset ℕ :=
  ([5999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part014 : ℚ :=
  (1879874531575 : ℚ) / 1739910540580651008

def SurrogateDiagonalTailChunk000Sub000Block144Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5999
    = surrogateDiagTailX0RatChunk000Sub000Block144Part014

theorem surrogateDiagonalTailChunk000Sub000Block144Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part014] using hcert

def TailChunk000Sub000Block144Part015SupportExplicit : Finset ℕ :=
  ([6001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part015 : ℚ :=
  (696173633475 : ℚ) / 838602569386295296

def SurrogateDiagonalTailChunk000Sub000Block144Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6001
    = surrogateDiagTailX0RatChunk000Sub000Block144Part015

theorem surrogateDiagonalTailChunk000Sub000Block144Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part015] using hcert

def TailChunk000Sub000Block144Part016SupportExplicit : Finset ℕ :=
  ([6002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part016 : ℚ :=
  (45020998999 : ℚ) / 8101620000000000

def SurrogateDiagonalTailChunk000Sub000Block144Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6002
    = surrogateDiagTailX0RatChunk000Sub000Block144Part016

theorem surrogateDiagonalTailChunk000Sub000Block144Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part016] using hcert

def TailChunk000Sub000Block144Part017SupportExplicit : Finset ℕ :=
  ([6005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part017 : ℚ :=
  (11410494349 : ℚ) / 8849129472000000

def SurrogateDiagonalTailChunk000Sub000Block144Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6005
    = surrogateDiagTailX0RatChunk000Sub000Block144Part017

theorem surrogateDiagonalTailChunk000Sub000Block144Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part017] using hcert

def TailChunk000Sub000Block144Part018SupportExplicit : Finset ℕ :=
  ([6006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part018 : ℚ :=
  (428698981 : ℚ) / 9557059829760

def SurrogateDiagonalTailChunk000Sub000Block144Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6006
    = surrogateDiagTailX0RatChunk000Sub000Block144Part018

theorem surrogateDiagonalTailChunk000Sub000Block144Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part018] using hcert

def TailChunk000Sub000Block144Part019SupportExplicit : Finset ℕ :=
  ([6007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part019 : ℚ :=
  (563813265625 : ℚ) / 813407512213458162

def SurrogateDiagonalTailChunk000Sub000Block144Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6007
    = surrogateDiagTailX0RatChunk000Sub000Block144Part019

theorem surrogateDiagonalTailChunk000Sub000Block144Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part019] using hcert

def TailChunk000Sub000Block144Part020SupportExplicit : Finset ℕ :=
  ([6009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part020 : ℚ :=
  (62625 : ℚ) / 26762342464

def SurrogateDiagonalTailChunk000Sub000Block144Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6009
    = surrogateDiagTailX0RatChunk000Sub000Block144Part020

theorem surrogateDiagonalTailChunk000Sub000Block144Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part020] using hcert

def TailChunk000Sub000Block144Part021SupportExplicit : Finset ℕ :=
  ([6010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part021 : ℚ :=
  (325525873 : ℚ) / 30726144000000

def SurrogateDiagonalTailChunk000Sub000Block144Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6010
    = surrogateDiagTailX0RatChunk000Sub000Block144Part021

theorem surrogateDiagonalTailChunk000Sub000Block144Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part021] using hcert

def TailChunk000Sub000Block144Part022SupportExplicit : Finset ℕ :=
  ([6011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part022 : ℚ :=
  (903303025 : ℚ) / 1304922556334802

def SurrogateDiagonalTailChunk000Sub000Block144Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6011
    = surrogateDiagTailX0RatChunk000Sub000Block144Part022

theorem surrogateDiagonalTailChunk000Sub000Block144Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part022] using hcert

def TailChunk000Sub000Block144Part023SupportExplicit : Finset ℕ :=
  ([6013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part023 : ℚ :=
  (231741494275 : ℚ) / 1756228464520852608

def SurrogateDiagonalTailChunk000Sub000Block144Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6013
    = surrogateDiagTailX0RatChunk000Sub000Block144Part023

theorem surrogateDiagonalTailChunk000Sub000Block144Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part023] using hcert

def TailChunk000Sub000Block144Part024SupportExplicit : Finset ℕ :=
  ([6014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block144Part024 : ℚ :=
  (11142707369 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block144Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6014
    = surrogateDiagTailX0RatChunk000Sub000Block144Part024

theorem surrogateDiagonalTailChunk000Sub000Block144Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block144Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block144Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block144Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block144Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block144Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block144Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block144HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block144Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block144Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block144Part000
    + surrogateDiagTailX0RatChunk000Sub000Block144Part001
    + surrogateDiagTailX0RatChunk000Sub000Block144Part002
    + surrogateDiagTailX0RatChunk000Sub000Block144Part003
    + surrogateDiagTailX0RatChunk000Sub000Block144Part004
    + surrogateDiagTailX0RatChunk000Sub000Block144Part005
    + surrogateDiagTailX0RatChunk000Sub000Block144Part006
    + surrogateDiagTailX0RatChunk000Sub000Block144Part007
    + surrogateDiagTailX0RatChunk000Sub000Block144Part008
    + surrogateDiagTailX0RatChunk000Sub000Block144Part009

def surrogateDiagonalTailChunk000Sub000Block144MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block144Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block144Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block144Part010
    + surrogateDiagTailX0RatChunk000Sub000Block144Part011
    + surrogateDiagTailX0RatChunk000Sub000Block144Part012
    + surrogateDiagTailX0RatChunk000Sub000Block144Part013
    + surrogateDiagTailX0RatChunk000Sub000Block144Part014
    + surrogateDiagTailX0RatChunk000Sub000Block144Part015
    + surrogateDiagTailX0RatChunk000Sub000Block144Part016
    + surrogateDiagTailX0RatChunk000Sub000Block144Part017
    + surrogateDiagTailX0RatChunk000Sub000Block144Part018
    + surrogateDiagTailX0RatChunk000Sub000Block144Part019

def surrogateDiagonalTailChunk000Sub000Block144TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block144Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block144Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block144Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block144Part020
    + surrogateDiagTailX0RatChunk000Sub000Block144Part021
    + surrogateDiagTailX0RatChunk000Sub000Block144Part022
    + surrogateDiagTailX0RatChunk000Sub000Block144Part023
    + surrogateDiagTailX0RatChunk000Sub000Block144Part024

def surrogateDiagonalTailChunk000Sub000Block144Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block144HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block144MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block144TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block144 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block144Part000
    + surrogateDiagTailX0RatChunk000Sub000Block144Part001
    + surrogateDiagTailX0RatChunk000Sub000Block144Part002
    + surrogateDiagTailX0RatChunk000Sub000Block144Part003
    + surrogateDiagTailX0RatChunk000Sub000Block144Part004
    + surrogateDiagTailX0RatChunk000Sub000Block144Part005
    + surrogateDiagTailX0RatChunk000Sub000Block144Part006
    + surrogateDiagTailX0RatChunk000Sub000Block144Part007
    + surrogateDiagTailX0RatChunk000Sub000Block144Part008
    + surrogateDiagTailX0RatChunk000Sub000Block144Part009
    + surrogateDiagTailX0RatChunk000Sub000Block144Part010
    + surrogateDiagTailX0RatChunk000Sub000Block144Part011
    + surrogateDiagTailX0RatChunk000Sub000Block144Part012
    + surrogateDiagTailX0RatChunk000Sub000Block144Part013
    + surrogateDiagTailX0RatChunk000Sub000Block144Part014
    + surrogateDiagTailX0RatChunk000Sub000Block144Part015
    + surrogateDiagTailX0RatChunk000Sub000Block144Part016
    + surrogateDiagTailX0RatChunk000Sub000Block144Part017
    + surrogateDiagTailX0RatChunk000Sub000Block144Part018
    + surrogateDiagTailX0RatChunk000Sub000Block144Part019
    + surrogateDiagTailX0RatChunk000Sub000Block144Part020
    + surrogateDiagTailX0RatChunk000Sub000Block144Part021
    + surrogateDiagTailX0RatChunk000Sub000Block144Part022
    + surrogateDiagTailX0RatChunk000Sub000Block144Part023
    + surrogateDiagTailX0RatChunk000Sub000Block144Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block144_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block144Head + surrogateDiagTailX0RatChunk000Sub000Block144Mid + surrogateDiagTailX0RatChunk000Sub000Block144Tail =
      surrogateDiagTailX0RatChunk000Sub000Block144 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block144Head surrogateDiagTailX0RatChunk000Sub000Block144Mid surrogateDiagTailX0RatChunk000Sub000Block144Tail surrogateDiagTailX0RatChunk000Sub000Block144
  ring

def SurrogateDiagonalTailChunk000Sub000Block144HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block144HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block144Head

def SurrogateDiagonalTailChunk000Sub000Block144MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block144MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block144Mid

def SurrogateDiagonalTailChunk000Sub000Block144TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block144TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block144Tail

theorem surrogateDiagonalTailChunk000Sub000Block144_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block144HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block144MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block144TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block144Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block144 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block144HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block144MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block144TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block144Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block144_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
