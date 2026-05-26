import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [30,40). -/

/-- Block 030 covers tail-support indices [15750,15775) and q from 25957 to 25995. -/

def TailChunk001Sub001Block030Part000SupportExplicit : Finset ℕ :=
  ([25957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part000 : ℚ :=
  (727333791 : ℚ) / 7159710482432000000

def SurrogateDiagonalTailChunk001Sub001Block030Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25957
    = surrogateDiagTailX0RatChunk001Sub001Block030Part000

theorem surrogateDiagonalTailChunk001Sub001Block030Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part000] using hcert

def TailChunk001Sub001Block030Part001SupportExplicit : Finset ℕ :=
  ([25958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block030Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25958
    = surrogateDiagTailX0RatChunk001Sub001Block030Part001

theorem surrogateDiagonalTailChunk001Sub001Block030Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part001] using hcert

def TailChunk001Sub001Block030Part002SupportExplicit : Finset ℕ :=
  ([25959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part002 : ℚ :=
  (2214691027925 : ℚ) / 87307514677322317824

def SurrogateDiagonalTailChunk001Sub001Block030Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25959
    = surrogateDiagTailX0RatChunk001Sub001Block030Part002

theorem surrogateDiagonalTailChunk001Sub001Block030Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part002] using hcert

def TailChunk001Sub001Block030Part003SupportExplicit : Finset ℕ :=
  ([25961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part003 : ℚ :=
  (501655926025 : ℚ) / 822988924903197278208

def SurrogateDiagonalTailChunk001Sub001Block030Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25961
    = surrogateDiagTailX0RatChunk001Sub001Block030Part003

theorem surrogateDiagonalTailChunk001Sub001Block030Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part003] using hcert

def TailChunk001Sub001Block030Part004SupportExplicit : Finset ℕ :=
  ([25962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part004 : ℚ :=
  (83590523525 : ℚ) / 1000840488655476672

def SurrogateDiagonalTailChunk001Sub001Block030Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25962
    = surrogateDiagTailX0RatChunk001Sub001Block030Part004

theorem surrogateDiagonalTailChunk001Sub001Block030Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part004] using hcert

def TailChunk001Sub001Block030Part005SupportExplicit : Finset ℕ :=
  ([25963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part005 : ℚ :=
  (860094570575 : ℚ) / 306309711769963029504

def SurrogateDiagonalTailChunk001Sub001Block030Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25963
    = surrogateDiagTailX0RatChunk001Sub001Block030Part005

theorem surrogateDiagonalTailChunk001Sub001Block030Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part005] using hcert

def TailChunk001Sub001Block030Part006SupportExplicit : Finset ℕ :=
  ([25966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block030Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25966
    = surrogateDiagTailX0RatChunk001Sub001Block030Part006

theorem surrogateDiagonalTailChunk001Sub001Block030Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part006] using hcert

def TailChunk001Sub001Block030Part007SupportExplicit : Finset ℕ :=
  ([25967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part007 : ℚ :=
  (404166918775 : ℚ) / 948317971158669754368

def SurrogateDiagonalTailChunk001Sub001Block030Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25967
    = surrogateDiagTailX0RatChunk001Sub001Block030Part007

theorem surrogateDiagonalTailChunk001Sub001Block030Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part007] using hcert

def TailChunk001Sub001Block030Part008SupportExplicit : Finset ℕ :=
  ([25969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block030Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25969
    = surrogateDiagTailX0RatChunk001Sub001Block030Part008

theorem surrogateDiagonalTailChunk001Sub001Block030Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part008] using hcert

def TailChunk001Sub001Block030Part009SupportExplicit : Finset ℕ :=
  ([25971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part009 : ℚ :=
  (85842680303 : ℚ) / 3053985855964185600

def SurrogateDiagonalTailChunk001Sub001Block030Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25971
    = surrogateDiagTailX0RatChunk001Sub001Block030Part009

theorem surrogateDiagonalTailChunk001Sub001Block030Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part009] using hcert

def TailChunk001Sub001Block030Part010SupportExplicit : Finset ℕ :=
  ([25973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part010 : ℚ :=
  (471831855925 : ℚ) / 913944190688243952768

def SurrogateDiagonalTailChunk001Sub001Block030Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25973
    = surrogateDiagTailX0RatChunk001Sub001Block030Part010

theorem surrogateDiagonalTailChunk001Sub001Block030Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part010] using hcert

def TailChunk001Sub001Block030Part011SupportExplicit : Finset ℕ :=
  ([25977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part011 : ℚ :=
  (59718081175 : ℚ) / 1680711724389371904

def SurrogateDiagonalTailChunk001Sub001Block030Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25977
    = surrogateDiagTailX0RatChunk001Sub001Block030Part011

theorem surrogateDiagonalTailChunk001Sub001Block030Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part011] using hcert

def TailChunk001Sub001Block030Part012SupportExplicit : Finset ℕ :=
  ([25978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part012 : ℚ :=
  (2802286523 : ℚ) / 1236650565785025600

def SurrogateDiagonalTailChunk001Sub001Block030Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25978
    = surrogateDiagTailX0RatChunk001Sub001Block030Part012

theorem surrogateDiagonalTailChunk001Sub001Block030Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part012] using hcert

def TailChunk001Sub001Block030Part013SupportExplicit : Finset ℕ :=
  ([25979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part013 : ℚ :=
  (61290254375 : ℚ) / 535637098485491318784

def SurrogateDiagonalTailChunk001Sub001Block030Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25979
    = surrogateDiagTailX0RatChunk001Sub001Block030Part013

theorem surrogateDiagonalTailChunk001Sub001Block030Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part013] using hcert

def TailChunk001Sub001Block030Part014SupportExplicit : Finset ℕ :=
  ([25981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block030Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25981
    = surrogateDiagTailX0RatChunk001Sub001Block030Part014

theorem surrogateDiagonalTailChunk001Sub001Block030Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part014] using hcert

def TailChunk001Sub001Block030Part015SupportExplicit : Finset ℕ :=
  ([25982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part015 : ℚ :=
  (4680245943 : ℚ) / 646388505184000000

def SurrogateDiagonalTailChunk001Sub001Block030Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25982
    = surrogateDiagTailX0RatChunk001Sub001Block030Part015

theorem surrogateDiagonalTailChunk001Sub001Block030Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part015] using hcert

def TailChunk001Sub001Block030Part016SupportExplicit : Finset ℕ :=
  ([25985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part016 : ℚ :=
  (1688651537875 : ℚ) / 466598559617508999168

def SurrogateDiagonalTailChunk001Sub001Block030Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25985
    = surrogateDiagTailX0RatChunk001Sub001Block030Part016

theorem surrogateDiagonalTailChunk001Sub001Block030Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part016] using hcert

def TailChunk001Sub001Block030Part017SupportExplicit : Finset ℕ :=
  ([25986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part017 : ℚ :=
  (37818713 : ℚ) / 398376747417600

def SurrogateDiagonalTailChunk001Sub001Block030Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25986
    = surrogateDiagTailX0RatChunk001Sub001Block030Part017

theorem surrogateDiagonalTailChunk001Sub001Block030Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part017] using hcert

def TailChunk001Sub001Block030Part018SupportExplicit : Finset ℕ :=
  ([25987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part018 : ℚ :=
  (6205607725 : ℚ) / 10201141219330050048

def SurrogateDiagonalTailChunk001Sub001Block030Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25987
    = surrogateDiagTailX0RatChunk001Sub001Block030Part018

theorem surrogateDiagonalTailChunk001Sub001Block030Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part018] using hcert

def TailChunk001Sub001Block030Part019SupportExplicit : Finset ℕ :=
  ([25989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part019 : ℚ :=
  (2345007610475 : ℚ) / 112613268444049518144

def SurrogateDiagonalTailChunk001Sub001Block030Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25989
    = surrogateDiagTailX0RatChunk001Sub001Block030Part019

theorem surrogateDiagonalTailChunk001Sub001Block030Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part019] using hcert

def TailChunk001Sub001Block030Part020SupportExplicit : Finset ℕ :=
  ([25990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part020 : ℚ :=
  (66139771175 : ℚ) / 1685394616989253632

def SurrogateDiagonalTailChunk001Sub001Block030Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25990
    = surrogateDiagTailX0RatChunk001Sub001Block030Part020

theorem surrogateDiagonalTailChunk001Sub001Block030Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part020] using hcert

def TailChunk001Sub001Block030Part021SupportExplicit : Finset ℕ :=
  ([25991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part021 : ℚ :=
  (459218753425 : ℚ) / 134270809299905720832

def SurrogateDiagonalTailChunk001Sub001Block030Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25991
    = surrogateDiagTailX0RatChunk001Sub001Block030Part021

theorem surrogateDiagonalTailChunk001Sub001Block030Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part021] using hcert

def TailChunk001Sub001Block030Part022SupportExplicit : Finset ℕ :=
  ([25993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part022 : ℚ :=
  (43362801 : ℚ) / 24457770277273600

def SurrogateDiagonalTailChunk001Sub001Block030Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25993
    = surrogateDiagTailX0RatChunk001Sub001Block030Part022

theorem surrogateDiagonalTailChunk001Sub001Block030Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part022] using hcert

def TailChunk001Sub001Block030Part023SupportExplicit : Finset ℕ :=
  ([25994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part023 : ℚ :=
  (298828581 : ℚ) / 170209535661178880

def SurrogateDiagonalTailChunk001Sub001Block030Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25994
    = surrogateDiagTailX0RatChunk001Sub001Block030Part023

theorem surrogateDiagonalTailChunk001Sub001Block030Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part023] using hcert

def TailChunk001Sub001Block030Part024SupportExplicit : Finset ℕ :=
  ([25995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block030Part024 : ℚ :=
  (656603233875 : ℚ) / 15361269452428279808

def SurrogateDiagonalTailChunk001Sub001Block030Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25995
    = surrogateDiagTailX0RatChunk001Sub001Block030Part024

theorem surrogateDiagonalTailChunk001Sub001Block030Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block030Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block030Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block030Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block030Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block030Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block030Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block030HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block030Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block030Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block030Part000
    + surrogateDiagTailX0RatChunk001Sub001Block030Part001
    + surrogateDiagTailX0RatChunk001Sub001Block030Part002
    + surrogateDiagTailX0RatChunk001Sub001Block030Part003
    + surrogateDiagTailX0RatChunk001Sub001Block030Part004
    + surrogateDiagTailX0RatChunk001Sub001Block030Part005
    + surrogateDiagTailX0RatChunk001Sub001Block030Part006
    + surrogateDiagTailX0RatChunk001Sub001Block030Part007
    + surrogateDiagTailX0RatChunk001Sub001Block030Part008
    + surrogateDiagTailX0RatChunk001Sub001Block030Part009

def surrogateDiagonalTailChunk001Sub001Block030MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block030Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block030Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block030Part010
    + surrogateDiagTailX0RatChunk001Sub001Block030Part011
    + surrogateDiagTailX0RatChunk001Sub001Block030Part012
    + surrogateDiagTailX0RatChunk001Sub001Block030Part013
    + surrogateDiagTailX0RatChunk001Sub001Block030Part014
    + surrogateDiagTailX0RatChunk001Sub001Block030Part015
    + surrogateDiagTailX0RatChunk001Sub001Block030Part016
    + surrogateDiagTailX0RatChunk001Sub001Block030Part017
    + surrogateDiagTailX0RatChunk001Sub001Block030Part018
    + surrogateDiagTailX0RatChunk001Sub001Block030Part019

def surrogateDiagonalTailChunk001Sub001Block030TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block030Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block030Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block030Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block030Part020
    + surrogateDiagTailX0RatChunk001Sub001Block030Part021
    + surrogateDiagTailX0RatChunk001Sub001Block030Part022
    + surrogateDiagTailX0RatChunk001Sub001Block030Part023
    + surrogateDiagTailX0RatChunk001Sub001Block030Part024

def surrogateDiagonalTailChunk001Sub001Block030Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block030HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block030MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block030TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block030 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block030Part000
    + surrogateDiagTailX0RatChunk001Sub001Block030Part001
    + surrogateDiagTailX0RatChunk001Sub001Block030Part002
    + surrogateDiagTailX0RatChunk001Sub001Block030Part003
    + surrogateDiagTailX0RatChunk001Sub001Block030Part004
    + surrogateDiagTailX0RatChunk001Sub001Block030Part005
    + surrogateDiagTailX0RatChunk001Sub001Block030Part006
    + surrogateDiagTailX0RatChunk001Sub001Block030Part007
    + surrogateDiagTailX0RatChunk001Sub001Block030Part008
    + surrogateDiagTailX0RatChunk001Sub001Block030Part009
    + surrogateDiagTailX0RatChunk001Sub001Block030Part010
    + surrogateDiagTailX0RatChunk001Sub001Block030Part011
    + surrogateDiagTailX0RatChunk001Sub001Block030Part012
    + surrogateDiagTailX0RatChunk001Sub001Block030Part013
    + surrogateDiagTailX0RatChunk001Sub001Block030Part014
    + surrogateDiagTailX0RatChunk001Sub001Block030Part015
    + surrogateDiagTailX0RatChunk001Sub001Block030Part016
    + surrogateDiagTailX0RatChunk001Sub001Block030Part017
    + surrogateDiagTailX0RatChunk001Sub001Block030Part018
    + surrogateDiagTailX0RatChunk001Sub001Block030Part019
    + surrogateDiagTailX0RatChunk001Sub001Block030Part020
    + surrogateDiagTailX0RatChunk001Sub001Block030Part021
    + surrogateDiagTailX0RatChunk001Sub001Block030Part022
    + surrogateDiagTailX0RatChunk001Sub001Block030Part023
    + surrogateDiagTailX0RatChunk001Sub001Block030Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block030_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block030Head + surrogateDiagTailX0RatChunk001Sub001Block030Mid + surrogateDiagTailX0RatChunk001Sub001Block030Tail =
      surrogateDiagTailX0RatChunk001Sub001Block030 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block030Head surrogateDiagTailX0RatChunk001Sub001Block030Mid surrogateDiagTailX0RatChunk001Sub001Block030Tail surrogateDiagTailX0RatChunk001Sub001Block030
  ring

def SurrogateDiagonalTailChunk001Sub001Block030HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block030HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block030Head

def SurrogateDiagonalTailChunk001Sub001Block030MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block030MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block030Mid

def SurrogateDiagonalTailChunk001Sub001Block030TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block030TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block030Tail

theorem surrogateDiagonalTailChunk001Sub001Block030_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block030HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block030MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block030TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block030Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block030 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block030HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block030MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block030TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block030Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block030_eq_head_add_mid_add_tail

/-- Block 031 covers tail-support indices [15775,15800) and q from 25997 to 26039. -/

def TailChunk001Sub001Block031Part000SupportExplicit : Finset ℕ :=
  ([25997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25997
    = surrogateDiagTailX0RatChunk001Sub001Block031Part000

theorem surrogateDiagonalTailChunk001Sub001Block031Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part000] using hcert

def TailChunk001Sub001Block031Part001SupportExplicit : Finset ℕ :=
  ([25998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part001 : ℚ :=
  (293375750575 : ℚ) / 1890800689938043392

def SurrogateDiagonalTailChunk001Sub001Block031Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25998
    = surrogateDiagTailX0RatChunk001Sub001Block031Part001

theorem surrogateDiagonalTailChunk001Sub001Block031Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part001] using hcert

def TailChunk001Sub001Block031Part002SupportExplicit : Finset ℕ :=
  ([25999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25999
    = surrogateDiagTailX0RatChunk001Sub001Block031Part002

theorem surrogateDiagonalTailChunk001Sub001Block031Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part002] using hcert

def TailChunk001Sub001Block031Part003SupportExplicit : Finset ℕ :=
  ([26002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26002
    = surrogateDiagTailX0RatChunk001Sub001Block031Part003

theorem surrogateDiagonalTailChunk001Sub001Block031Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part003] using hcert

def TailChunk001Sub001Block031Part004SupportExplicit : Finset ℕ :=
  ([26003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26003
    = surrogateDiagTailX0RatChunk001Sub001Block031Part004

theorem surrogateDiagonalTailChunk001Sub001Block031Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part004] using hcert

def TailChunk001Sub001Block031Part005SupportExplicit : Finset ℕ :=
  ([26005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part005 : ℚ :=
  (492276683275 : ℚ) / 62867683126807437312

def SurrogateDiagonalTailChunk001Sub001Block031Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26005
    = surrogateDiagTailX0RatChunk001Sub001Block031Part005

theorem surrogateDiagonalTailChunk001Sub001Block031Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part005] using hcert

def TailChunk001Sub001Block031Part006SupportExplicit : Finset ℕ :=
  ([26006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26006
    = surrogateDiagTailX0RatChunk001Sub001Block031Part006

theorem surrogateDiagonalTailChunk001Sub001Block031Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part006] using hcert

def TailChunk001Sub001Block031Part007SupportExplicit : Finset ℕ :=
  ([26007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part007 : ℚ :=
  (293532123175 : ℚ) / 14115701616013481088

def SurrogateDiagonalTailChunk001Sub001Block031Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26007
    = surrogateDiagTailX0RatChunk001Sub001Block031Part007

theorem surrogateDiagonalTailChunk001Sub001Block031Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part007] using hcert

def TailChunk001Sub001Block031Part008SupportExplicit : Finset ℕ :=
  ([26009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part008 : ℚ :=
  (10897556311 : ℚ) / 39952866453911683200

def SurrogateDiagonalTailChunk001Sub001Block031Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26009
    = surrogateDiagTailX0RatChunk001Sub001Block031Part008

theorem surrogateDiagonalTailChunk001Sub001Block031Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part008] using hcert

def TailChunk001Sub001Block031Part009SupportExplicit : Finset ℕ :=
  ([26013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part009 : ℚ :=
  (171995464975 : ℚ) / 4977180978296389632

def SurrogateDiagonalTailChunk001Sub001Block031Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26013
    = surrogateDiagTailX0RatChunk001Sub001Block031Part009

theorem surrogateDiagonalTailChunk001Sub001Block031Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part009] using hcert

def TailChunk001Sub001Block031Part010SupportExplicit : Finset ℕ :=
  ([26014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26014
    = surrogateDiagTailX0RatChunk001Sub001Block031Part010

theorem surrogateDiagonalTailChunk001Sub001Block031Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part010] using hcert

def TailChunk001Sub001Block031Part011SupportExplicit : Finset ℕ :=
  ([26017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26017
    = surrogateDiagTailX0RatChunk001Sub001Block031Part011

theorem surrogateDiagonalTailChunk001Sub001Block031Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part011] using hcert

def TailChunk001Sub001Block031Part012SupportExplicit : Finset ℕ :=
  ([26018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26018
    = surrogateDiagTailX0RatChunk001Sub001Block031Part012

theorem surrogateDiagonalTailChunk001Sub001Block031Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part012] using hcert

def TailChunk001Sub001Block031Part013SupportExplicit : Finset ℕ :=
  ([26021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26021
    = surrogateDiagTailX0RatChunk001Sub001Block031Part013

theorem surrogateDiagonalTailChunk001Sub001Block031Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part013] using hcert

def TailChunk001Sub001Block031Part014SupportExplicit : Finset ℕ :=
  ([26022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part014 : ℚ :=
  (293920269775 : ℚ) / 3535443851408965632

def SurrogateDiagonalTailChunk001Sub001Block031Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26022
    = surrogateDiagTailX0RatChunk001Sub001Block031Part014

theorem surrogateDiagonalTailChunk001Sub001Block031Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part014] using hcert

def TailChunk001Sub001Block031Part015SupportExplicit : Finset ℕ :=
  ([26023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part015 : ℚ :=
  (110767497 : ℚ) / 702640687177694720

def SurrogateDiagonalTailChunk001Sub001Block031Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26023
    = surrogateDiagTailX0RatChunk001Sub001Block031Part015

theorem surrogateDiagonalTailChunk001Sub001Block031Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part015] using hcert

def TailChunk001Sub001Block031Part016SupportExplicit : Finset ℕ :=
  ([26027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part016 : ℚ :=
  (29002757 : ℚ) / 58692293679513600

def SurrogateDiagonalTailChunk001Sub001Block031Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26027
    = surrogateDiagTailX0RatChunk001Sub001Block031Part016

theorem surrogateDiagonalTailChunk001Sub001Block031Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part016] using hcert

def TailChunk001Sub001Block031Part017SupportExplicit : Finset ℕ :=
  ([26029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block031Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26029
    = surrogateDiagTailX0RatChunk001Sub001Block031Part017

theorem surrogateDiagonalTailChunk001Sub001Block031Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part017] using hcert

def TailChunk001Sub001Block031Part018SupportExplicit : Finset ℕ :=
  ([26030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part018 : ℚ :=
  (18633894425 : ℚ) / 450756815458664448

def SurrogateDiagonalTailChunk001Sub001Block031Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26030
    = surrogateDiagTailX0RatChunk001Sub001Block031Part018

theorem surrogateDiagonalTailChunk001Sub001Block031Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part018] using hcert

def TailChunk001Sub001Block031Part019SupportExplicit : Finset ℕ :=
  ([26031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part019 : ℚ :=
  (588148246325 : ℚ) / 28335770600398776576

def SurrogateDiagonalTailChunk001Sub001Block031Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26031
    = surrogateDiagTailX0RatChunk001Sub001Block031Part019

theorem surrogateDiagonalTailChunk001Sub001Block031Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part019] using hcert

def TailChunk001Sub001Block031Part020SupportExplicit : Finset ℕ :=
  ([26033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part020 : ℚ :=
  (66603475825 : ℚ) / 47634986871016212096

def SurrogateDiagonalTailChunk001Sub001Block031Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26033
    = surrogateDiagTailX0RatChunk001Sub001Block031Part020

theorem surrogateDiagonalTailChunk001Sub001Block031Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part020] using hcert

def TailChunk001Sub001Block031Part021SupportExplicit : Finset ℕ :=
  ([26034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part021 : ℚ :=
  (588382664525 : ℚ) / 7083942650099694144

def SurrogateDiagonalTailChunk001Sub001Block031Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26034
    = surrogateDiagTailX0RatChunk001Sub001Block031Part021

theorem surrogateDiagonalTailChunk001Sub001Block031Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part021] using hcert

def TailChunk001Sub001Block031Part022SupportExplicit : Finset ℕ :=
  ([26035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part022 : ℚ :=
  (8288804089 : ℚ) / 16521480468902707200

def SurrogateDiagonalTailChunk001Sub001Block031Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26035
    = surrogateDiagTailX0RatChunk001Sub001Block031Part022

theorem surrogateDiagonalTailChunk001Sub001Block031Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part022] using hcert

def TailChunk001Sub001Block031Part023SupportExplicit : Finset ℕ :=
  ([26038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part023 : ℚ :=
  (49866464075 : ℚ) / 32483627242099467264

def SurrogateDiagonalTailChunk001Sub001Block031Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26038
    = surrogateDiagTailX0RatChunk001Sub001Block031Part023

theorem surrogateDiagonalTailChunk001Sub001Block031Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part023] using hcert

def TailChunk001Sub001Block031Part024SupportExplicit : Finset ℕ :=
  ([26039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block031Part024 : ℚ :=
  (6740653225 : ℚ) / 7436868683094474624

def SurrogateDiagonalTailChunk001Sub001Block031Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26039
    = surrogateDiagTailX0RatChunk001Sub001Block031Part024

theorem surrogateDiagonalTailChunk001Sub001Block031Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block031Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block031Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block031Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block031Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block031Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block031Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block031HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block031Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block031Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block031Part000
    + surrogateDiagTailX0RatChunk001Sub001Block031Part001
    + surrogateDiagTailX0RatChunk001Sub001Block031Part002
    + surrogateDiagTailX0RatChunk001Sub001Block031Part003
    + surrogateDiagTailX0RatChunk001Sub001Block031Part004
    + surrogateDiagTailX0RatChunk001Sub001Block031Part005
    + surrogateDiagTailX0RatChunk001Sub001Block031Part006
    + surrogateDiagTailX0RatChunk001Sub001Block031Part007
    + surrogateDiagTailX0RatChunk001Sub001Block031Part008
    + surrogateDiagTailX0RatChunk001Sub001Block031Part009

def surrogateDiagonalTailChunk001Sub001Block031MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block031Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block031Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block031Part010
    + surrogateDiagTailX0RatChunk001Sub001Block031Part011
    + surrogateDiagTailX0RatChunk001Sub001Block031Part012
    + surrogateDiagTailX0RatChunk001Sub001Block031Part013
    + surrogateDiagTailX0RatChunk001Sub001Block031Part014
    + surrogateDiagTailX0RatChunk001Sub001Block031Part015
    + surrogateDiagTailX0RatChunk001Sub001Block031Part016
    + surrogateDiagTailX0RatChunk001Sub001Block031Part017
    + surrogateDiagTailX0RatChunk001Sub001Block031Part018
    + surrogateDiagTailX0RatChunk001Sub001Block031Part019

def surrogateDiagonalTailChunk001Sub001Block031TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block031Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block031Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block031Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block031Part020
    + surrogateDiagTailX0RatChunk001Sub001Block031Part021
    + surrogateDiagTailX0RatChunk001Sub001Block031Part022
    + surrogateDiagTailX0RatChunk001Sub001Block031Part023
    + surrogateDiagTailX0RatChunk001Sub001Block031Part024

def surrogateDiagonalTailChunk001Sub001Block031Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block031HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block031MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block031TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block031 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block031Part000
    + surrogateDiagTailX0RatChunk001Sub001Block031Part001
    + surrogateDiagTailX0RatChunk001Sub001Block031Part002
    + surrogateDiagTailX0RatChunk001Sub001Block031Part003
    + surrogateDiagTailX0RatChunk001Sub001Block031Part004
    + surrogateDiagTailX0RatChunk001Sub001Block031Part005
    + surrogateDiagTailX0RatChunk001Sub001Block031Part006
    + surrogateDiagTailX0RatChunk001Sub001Block031Part007
    + surrogateDiagTailX0RatChunk001Sub001Block031Part008
    + surrogateDiagTailX0RatChunk001Sub001Block031Part009
    + surrogateDiagTailX0RatChunk001Sub001Block031Part010
    + surrogateDiagTailX0RatChunk001Sub001Block031Part011
    + surrogateDiagTailX0RatChunk001Sub001Block031Part012
    + surrogateDiagTailX0RatChunk001Sub001Block031Part013
    + surrogateDiagTailX0RatChunk001Sub001Block031Part014
    + surrogateDiagTailX0RatChunk001Sub001Block031Part015
    + surrogateDiagTailX0RatChunk001Sub001Block031Part016
    + surrogateDiagTailX0RatChunk001Sub001Block031Part017
    + surrogateDiagTailX0RatChunk001Sub001Block031Part018
    + surrogateDiagTailX0RatChunk001Sub001Block031Part019
    + surrogateDiagTailX0RatChunk001Sub001Block031Part020
    + surrogateDiagTailX0RatChunk001Sub001Block031Part021
    + surrogateDiagTailX0RatChunk001Sub001Block031Part022
    + surrogateDiagTailX0RatChunk001Sub001Block031Part023
    + surrogateDiagTailX0RatChunk001Sub001Block031Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block031_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block031Head + surrogateDiagTailX0RatChunk001Sub001Block031Mid + surrogateDiagTailX0RatChunk001Sub001Block031Tail =
      surrogateDiagTailX0RatChunk001Sub001Block031 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block031Head surrogateDiagTailX0RatChunk001Sub001Block031Mid surrogateDiagTailX0RatChunk001Sub001Block031Tail surrogateDiagTailX0RatChunk001Sub001Block031
  ring

def SurrogateDiagonalTailChunk001Sub001Block031HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block031HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block031Head

def SurrogateDiagonalTailChunk001Sub001Block031MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block031MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block031Mid

def SurrogateDiagonalTailChunk001Sub001Block031TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block031TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block031Tail

theorem surrogateDiagonalTailChunk001Sub001Block031_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block031HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block031MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block031TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block031Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block031 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block031HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block031MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block031TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block031Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block031_eq_head_add_mid_add_tail

/-- Block 032 covers tail-support indices [15800,15825) and q from 26041 to 26083. -/

def TailChunk001Sub001Block032Part000SupportExplicit : Finset ℕ :=
  ([26041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block032Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26041
    = surrogateDiagTailX0RatChunk001Sub001Block032Part000

theorem surrogateDiagonalTailChunk001Sub001Block032Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part000] using hcert

def TailChunk001Sub001Block032Part001SupportExplicit : Finset ℕ :=
  ([26042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part001 : ℚ :=
  (48813049725 : ℚ) / 20637153074417238016

def SurrogateDiagonalTailChunk001Sub001Block032Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26042
    = surrogateDiagTailX0RatChunk001Sub001Block032Part001

theorem surrogateDiagonalTailChunk001Sub001Block032Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part001] using hcert

def TailChunk001Sub001Block032Part002SupportExplicit : Finset ℕ :=
  ([26043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part002 : ℚ :=
  (27460787 : ℚ) / 1324224497541120

def SurrogateDiagonalTailChunk001Sub001Block032Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26043
    = surrogateDiagTailX0RatChunk001Sub001Block032Part002

theorem surrogateDiagonalTailChunk001Sub001Block032Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part002] using hcert

def TailChunk001Sub001Block032Part003SupportExplicit : Finset ℕ :=
  ([26045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part003 : ℚ :=
  (1696454536375 : ℚ) / 470923893954367193088

def SurrogateDiagonalTailChunk001Sub001Block032Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26045
    = surrogateDiagTailX0RatChunk001Sub001Block032Part003

theorem surrogateDiagonalTailChunk001Sub001Block032Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part003] using hcert

def TailChunk001Sub001Block032Part004SupportExplicit : Finset ℕ :=
  ([26049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part004 : ℚ :=
  (250428405175 : ℚ) / 10088433312000638976

def SurrogateDiagonalTailChunk001Sub001Block032Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26049
    = surrogateDiagTailX0RatChunk001Sub001Block032Part004

theorem surrogateDiagonalTailChunk001Sub001Block032Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part004] using hcert

def TailChunk001Sub001Block032Part005SupportExplicit : Finset ℕ :=
  ([26051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part005 : ℚ :=
  (104381206375 : ℚ) / 1091515001852549449728

def SurrogateDiagonalTailChunk001Sub001Block032Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26051
    = surrogateDiagTailX0RatChunk001Sub001Block032Part005

theorem surrogateDiagonalTailChunk001Sub001Block032Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part005] using hcert

def TailChunk001Sub001Block032Part006SupportExplicit : Finset ℕ :=
  ([26053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block032Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26053
    = surrogateDiagTailX0RatChunk001Sub001Block032Part006

theorem surrogateDiagonalTailChunk001Sub001Block032Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part006] using hcert

def TailChunk001Sub001Block032Part007SupportExplicit : Finset ℕ :=
  ([26054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part007 : ℚ :=
  (481696411 : ℚ) / 28730942223436800

def SurrogateDiagonalTailChunk001Sub001Block032Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26054
    = surrogateDiagTailX0RatChunk001Sub001Block032Part007

theorem surrogateDiagonalTailChunk001Sub001Block032Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part007] using hcert

def TailChunk001Sub001Block032Part008SupportExplicit : Finset ℕ :=
  ([26057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part008 : ℚ :=
  (56595137 : ℚ) / 439721070060686400

def SurrogateDiagonalTailChunk001Sub001Block032Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26057
    = surrogateDiagTailX0RatChunk001Sub001Block032Part008

theorem surrogateDiagonalTailChunk001Sub001Block032Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part008] using hcert

def TailChunk001Sub001Block032Part009SupportExplicit : Finset ℕ :=
  ([26058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part009 : ℚ :=
  (47577648901 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk001Sub001Block032Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26058
    = surrogateDiagTailX0RatChunk001Sub001Block032Part009

theorem surrogateDiagonalTailChunk001Sub001Block032Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part009] using hcert

def TailChunk001Sub001Block032Part010SupportExplicit : Finset ℕ :=
  ([26059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part010 : ℚ :=
  (39446816773 : ℚ) / 25361694131857459200

def SurrogateDiagonalTailChunk001Sub001Block032Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26059
    = surrogateDiagTailX0RatChunk001Sub001Block032Part010

theorem surrogateDiagonalTailChunk001Sub001Block032Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part010] using hcert

def TailChunk001Sub001Block032Part011SupportExplicit : Finset ℕ :=
  ([26061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part011 : ℚ :=
  (947075985025 : ℚ) / 22829782190964867072

def SurrogateDiagonalTailChunk001Sub001Block032Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26061
    = surrogateDiagTailX0RatChunk001Sub001Block032Part011

theorem surrogateDiagonalTailChunk001Sub001Block032Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part011] using hcert

def TailChunk001Sub001Block032Part012SupportExplicit : Finset ℕ :=
  ([26062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part012 : ℚ :=
  (36947888075 : ℚ) / 33477318655343207424

def SurrogateDiagonalTailChunk001Sub001Block032Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26062
    = surrogateDiagTailX0RatChunk001Sub001Block032Part012

theorem surrogateDiagonalTailChunk001Sub001Block032Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part012] using hcert

def TailChunk001Sub001Block032Part013SupportExplicit : Finset ℕ :=
  ([26063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part013 : ℚ :=
  (71374357025 : ℚ) / 537649823741396788224

def SurrogateDiagonalTailChunk001Sub001Block032Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26063
    = surrogateDiagTailX0RatChunk001Sub001Block032Part013

theorem surrogateDiagonalTailChunk001Sub001Block032Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part013] using hcert

def TailChunk001Sub001Block032Part014SupportExplicit : Finset ℕ :=
  ([26065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part014 : ℚ :=
  (75007101007 : ℚ) / 13592262868992000000

def SurrogateDiagonalTailChunk001Sub001Block032Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26065
    = surrogateDiagTailX0RatChunk001Sub001Block032Part014

theorem surrogateDiagonalTailChunk001Sub001Block032Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part014] using hcert

def TailChunk001Sub001Block032Part015SupportExplicit : Finset ℕ :=
  ([26066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block032Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26066
    = surrogateDiagTailX0RatChunk001Sub001Block032Part015

theorem surrogateDiagonalTailChunk001Sub001Block032Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part015] using hcert

def TailChunk001Sub001Block032Part016SupportExplicit : Finset ℕ :=
  ([26067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part016 : ℚ :=
  (1179552242575 : ℚ) / 56985727787047452672

def SurrogateDiagonalTailChunk001Sub001Block032Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26067
    = surrogateDiagTailX0RatChunk001Sub001Block032Part016

theorem surrogateDiagonalTailChunk001Sub001Block032Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part016] using hcert

def TailChunk001Sub001Block032Part017SupportExplicit : Finset ℕ :=
  ([26069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part017 : ℚ :=
  (4056647467 : ℚ) / 43905711613021315200

def SurrogateDiagonalTailChunk001Sub001Block032Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26069
    = surrogateDiagTailX0RatChunk001Sub001Block032Part017

theorem surrogateDiagonalTailChunk001Sub001Block032Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part017] using hcert

def TailChunk001Sub001Block032Part018SupportExplicit : Finset ℕ :=
  ([26070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part018 : ℚ :=
  (693714923 : ℚ) / 2106166557081600

def SurrogateDiagonalTailChunk001Sub001Block032Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26070
    = surrogateDiagTailX0RatChunk001Sub001Block032Part018

theorem surrogateDiagonalTailChunk001Sub001Block032Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part018] using hcert

def TailChunk001Sub001Block032Part019SupportExplicit : Finset ℕ :=
  ([26074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block032Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26074
    = surrogateDiagTailX0RatChunk001Sub001Block032Part019

theorem surrogateDiagonalTailChunk001Sub001Block032Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part019] using hcert

def TailChunk001Sub001Block032Part020SupportExplicit : Finset ℕ :=
  ([26077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part020 : ℚ :=
  (118193475175 : ℚ) / 1090156762786158870528

def SurrogateDiagonalTailChunk001Sub001Block032Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26077
    = surrogateDiagTailX0RatChunk001Sub001Block032Part020

theorem surrogateDiagonalTailChunk001Sub001Block032Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part020] using hcert

def TailChunk001Sub001Block032Part021SupportExplicit : Finset ℕ :=
  ([26078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part021 : ℚ :=
  (34803149425 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk001Sub001Block032Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26078
    = surrogateDiagTailX0RatChunk001Sub001Block032Part021

theorem surrogateDiagonalTailChunk001Sub001Block032Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part021] using hcert

def TailChunk001Sub001Block032Part022SupportExplicit : Finset ℕ :=
  ([26079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part022 : ℚ :=
  (590319246275 : ℚ) / 28545373188783626496

def SurrogateDiagonalTailChunk001Sub001Block032Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26079
    = surrogateDiagTailX0RatChunk001Sub001Block032Part022

theorem surrogateDiagonalTailChunk001Sub001Block032Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part022] using hcert

def TailChunk001Sub001Block032Part023SupportExplicit : Finset ℕ :=
  ([26081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part023 : ℚ :=
  (293791559 : ℚ) / 328707036699187500

def SurrogateDiagonalTailChunk001Sub001Block032Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26081
    = surrogateDiagTailX0RatChunk001Sub001Block032Part023

theorem surrogateDiagonalTailChunk001Sub001Block032Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part023] using hcert

def TailChunk001Sub001Block032Part024SupportExplicit : Finset ℕ :=
  ([26083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block032Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block032Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26083
    = surrogateDiagTailX0RatChunk001Sub001Block032Part024

theorem surrogateDiagonalTailChunk001Sub001Block032Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block032Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block032Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block032Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block032Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block032Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block032Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block032HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block032Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block032Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block032Part000
    + surrogateDiagTailX0RatChunk001Sub001Block032Part001
    + surrogateDiagTailX0RatChunk001Sub001Block032Part002
    + surrogateDiagTailX0RatChunk001Sub001Block032Part003
    + surrogateDiagTailX0RatChunk001Sub001Block032Part004
    + surrogateDiagTailX0RatChunk001Sub001Block032Part005
    + surrogateDiagTailX0RatChunk001Sub001Block032Part006
    + surrogateDiagTailX0RatChunk001Sub001Block032Part007
    + surrogateDiagTailX0RatChunk001Sub001Block032Part008
    + surrogateDiagTailX0RatChunk001Sub001Block032Part009

def surrogateDiagonalTailChunk001Sub001Block032MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block032Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block032Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block032Part010
    + surrogateDiagTailX0RatChunk001Sub001Block032Part011
    + surrogateDiagTailX0RatChunk001Sub001Block032Part012
    + surrogateDiagTailX0RatChunk001Sub001Block032Part013
    + surrogateDiagTailX0RatChunk001Sub001Block032Part014
    + surrogateDiagTailX0RatChunk001Sub001Block032Part015
    + surrogateDiagTailX0RatChunk001Sub001Block032Part016
    + surrogateDiagTailX0RatChunk001Sub001Block032Part017
    + surrogateDiagTailX0RatChunk001Sub001Block032Part018
    + surrogateDiagTailX0RatChunk001Sub001Block032Part019

def surrogateDiagonalTailChunk001Sub001Block032TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block032Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block032Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block032Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block032Part020
    + surrogateDiagTailX0RatChunk001Sub001Block032Part021
    + surrogateDiagTailX0RatChunk001Sub001Block032Part022
    + surrogateDiagTailX0RatChunk001Sub001Block032Part023
    + surrogateDiagTailX0RatChunk001Sub001Block032Part024

def surrogateDiagonalTailChunk001Sub001Block032Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block032HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block032MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block032TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block032 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block032Part000
    + surrogateDiagTailX0RatChunk001Sub001Block032Part001
    + surrogateDiagTailX0RatChunk001Sub001Block032Part002
    + surrogateDiagTailX0RatChunk001Sub001Block032Part003
    + surrogateDiagTailX0RatChunk001Sub001Block032Part004
    + surrogateDiagTailX0RatChunk001Sub001Block032Part005
    + surrogateDiagTailX0RatChunk001Sub001Block032Part006
    + surrogateDiagTailX0RatChunk001Sub001Block032Part007
    + surrogateDiagTailX0RatChunk001Sub001Block032Part008
    + surrogateDiagTailX0RatChunk001Sub001Block032Part009
    + surrogateDiagTailX0RatChunk001Sub001Block032Part010
    + surrogateDiagTailX0RatChunk001Sub001Block032Part011
    + surrogateDiagTailX0RatChunk001Sub001Block032Part012
    + surrogateDiagTailX0RatChunk001Sub001Block032Part013
    + surrogateDiagTailX0RatChunk001Sub001Block032Part014
    + surrogateDiagTailX0RatChunk001Sub001Block032Part015
    + surrogateDiagTailX0RatChunk001Sub001Block032Part016
    + surrogateDiagTailX0RatChunk001Sub001Block032Part017
    + surrogateDiagTailX0RatChunk001Sub001Block032Part018
    + surrogateDiagTailX0RatChunk001Sub001Block032Part019
    + surrogateDiagTailX0RatChunk001Sub001Block032Part020
    + surrogateDiagTailX0RatChunk001Sub001Block032Part021
    + surrogateDiagTailX0RatChunk001Sub001Block032Part022
    + surrogateDiagTailX0RatChunk001Sub001Block032Part023
    + surrogateDiagTailX0RatChunk001Sub001Block032Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block032_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block032Head + surrogateDiagTailX0RatChunk001Sub001Block032Mid + surrogateDiagTailX0RatChunk001Sub001Block032Tail =
      surrogateDiagTailX0RatChunk001Sub001Block032 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block032Head surrogateDiagTailX0RatChunk001Sub001Block032Mid surrogateDiagTailX0RatChunk001Sub001Block032Tail surrogateDiagTailX0RatChunk001Sub001Block032
  ring

def SurrogateDiagonalTailChunk001Sub001Block032HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block032HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block032Head

def SurrogateDiagonalTailChunk001Sub001Block032MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block032MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block032Mid

def SurrogateDiagonalTailChunk001Sub001Block032TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block032TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block032Tail

theorem surrogateDiagonalTailChunk001Sub001Block032_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block032HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block032MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block032TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block032Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block032 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block032HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block032MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block032TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block032Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block032_eq_head_add_mid_add_tail

/-- Block 033 covers tail-support indices [15825,15850) and q from 26085 to 26122. -/

def TailChunk001Sub001Block033Part000SupportExplicit : Finset ℕ :=
  ([26085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part000 : ℚ :=
  (3795723090475 : ℚ) / 77024366778812203008

def SurrogateDiagonalTailChunk001Sub001Block033Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26085
    = surrogateDiagTailX0RatChunk001Sub001Block033Part000

theorem surrogateDiagonalTailChunk001Sub001Block033Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part000] using hcert

def TailChunk001Sub001Block033Part001SupportExplicit : Finset ℕ :=
  ([26086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block033Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26086
    = surrogateDiagTailX0RatChunk001Sub001Block033Part001

theorem surrogateDiagonalTailChunk001Sub001Block033Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part001] using hcert

def TailChunk001Sub001Block033Part002SupportExplicit : Finset ℕ :=
  ([26087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part002 : ℚ :=
  (358428735925 : ℚ) / 930107882115339798528

def SurrogateDiagonalTailChunk001Sub001Block033Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26087
    = surrogateDiagTailX0RatChunk001Sub001Block033Part002

theorem surrogateDiagonalTailChunk001Sub001Block033Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part002] using hcert

def TailChunk001Sub001Block033Part003SupportExplicit : Finset ℕ :=
  ([26089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part003 : ℚ :=
  (869567186125 : ℚ) / 624601844868449950848

def SurrogateDiagonalTailChunk001Sub001Block033Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26089
    = surrogateDiagTailX0RatChunk001Sub001Block033Part003

theorem surrogateDiagonalTailChunk001Sub001Block033Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part003] using hcert

def TailChunk001Sub001Block033Part004SupportExplicit : Finset ℕ :=
  ([26090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part004 : ℚ :=
  (851288300725 : ℚ) / 29614006845139058688

def SurrogateDiagonalTailChunk001Sub001Block033Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26090
    = surrogateDiagTailX0RatChunk001Sub001Block033Part004

theorem surrogateDiagonalTailChunk001Sub001Block033Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part004] using hcert

def TailChunk001Sub001Block033Part005SupportExplicit : Finset ℕ :=
  ([26093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part005 : ℚ :=
  (38414062925 : ℚ) / 365199111649153253376

def SurrogateDiagonalTailChunk001Sub001Block033Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26093
    = surrogateDiagTailX0RatChunk001Sub001Block033Part005

theorem surrogateDiagonalTailChunk001Sub001Block033Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part005] using hcert

def TailChunk001Sub001Block033Part006SupportExplicit : Finset ℕ :=
  ([26094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part006 : ℚ :=
  (1181645031275 : ℚ) / 7149488756845323264

def SurrogateDiagonalTailChunk001Sub001Block033Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26094
    = surrogateDiagTailX0RatChunk001Sub001Block033Part006

theorem surrogateDiagonalTailChunk001Sub001Block033Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part006] using hcert

def TailChunk001Sub001Block033Part007SupportExplicit : Finset ℕ :=
  ([26095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part007 : ℚ :=
  (1617130825 : ℚ) / 318181281500233728

def SurrogateDiagonalTailChunk001Sub001Block033Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26095
    = surrogateDiagTailX0RatChunk001Sub001Block033Part007

theorem surrogateDiagonalTailChunk001Sub001Block033Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part007] using hcert

def TailChunk001Sub001Block033Part008SupportExplicit : Finset ℕ :=
  ([26097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part008 : ℚ :=
  (2364537610025 : ℚ) / 114497092685201446464

def SurrogateDiagonalTailChunk001Sub001Block033Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26097
    = surrogateDiagTailX0RatChunk001Sub001Block033Part008

theorem surrogateDiagonalTailChunk001Sub001Block033Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part008] using hcert

def TailChunk001Sub001Block033Part009SupportExplicit : Finset ℕ :=
  ([26098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block033Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26098
    = surrogateDiagTailX0RatChunk001Sub001Block033Part009

theorem surrogateDiagonalTailChunk001Sub001Block033Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part009] using hcert

def TailChunk001Sub001Block033Part010SupportExplicit : Finset ℕ :=
  ([26099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block033Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26099
    = surrogateDiagTailX0RatChunk001Sub001Block033Part010

theorem surrogateDiagonalTailChunk001Sub001Block033Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part010] using hcert

def TailChunk001Sub001Block033Part011SupportExplicit : Finset ℕ :=
  ([26101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part011 : ℚ :=
  (98281475975 : ℚ) / 524667932955225751104

def SurrogateDiagonalTailChunk001Sub001Block033Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26101
    = surrogateDiagTailX0RatChunk001Sub001Block033Part011

theorem surrogateDiagonalTailChunk001Sub001Block033Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part011] using hcert

def TailChunk001Sub001Block033Part012SupportExplicit : Finset ℕ :=
  ([26102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part012 : ℚ :=
  (2827371191 : ℚ) / 1260488927376000000

def SurrogateDiagonalTailChunk001Sub001Block033Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26102
    = surrogateDiagTailX0RatChunk001Sub001Block033Part012

theorem surrogateDiagonalTailChunk001Sub001Block033Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part012] using hcert

def TailChunk001Sub001Block033Part013SupportExplicit : Finset ℕ :=
  ([26103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part013 : ℚ :=
  (16432033013 : ℚ) / 362611368316108800

def SurrogateDiagonalTailChunk001Sub001Block033Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26103
    = surrogateDiagTailX0RatChunk001Sub001Block033Part013

theorem surrogateDiagonalTailChunk001Sub001Block033Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part013] using hcert

def TailChunk001Sub001Block033Part014SupportExplicit : Finset ℕ :=
  ([26105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part014 : ℚ :=
  (1831385784475 : ℚ) / 391193206404461395968

def SurrogateDiagonalTailChunk001Sub001Block033Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26105
    = surrogateDiagTailX0RatChunk001Sub001Block033Part014

theorem surrogateDiagonalTailChunk001Sub001Block033Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part014] using hcert

def TailChunk001Sub001Block033Part015SupportExplicit : Finset ℕ :=
  ([26106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part015 : ℚ :=
  (2258927417725 : ℚ) / 11349487476000718848

def SurrogateDiagonalTailChunk001Sub001Block033Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26106
    = surrogateDiagTailX0RatChunk001Sub001Block033Part015

theorem surrogateDiagonalTailChunk001Sub001Block033Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part015] using hcert

def TailChunk001Sub001Block033Part016SupportExplicit : Finset ℕ :=
  ([26107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block033Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26107
    = surrogateDiagTailX0RatChunk001Sub001Block033Part016

theorem surrogateDiagonalTailChunk001Sub001Block033Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part016] using hcert

def TailChunk001Sub001Block033Part017SupportExplicit : Finset ℕ :=
  ([26110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part017 : ℚ :=
  (492410613275 : ℚ) / 7943530905935806464

def SurrogateDiagonalTailChunk001Sub001Block033Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26110
    = surrogateDiagTailX0RatChunk001Sub001Block033Part017

theorem surrogateDiagonalTailChunk001Sub001Block033Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part017] using hcert

def TailChunk001Sub001Block033Part018SupportExplicit : Finset ℕ :=
  ([26111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block033Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26111
    = surrogateDiagTailX0RatChunk001Sub001Block033Part018

theorem surrogateDiagonalTailChunk001Sub001Block033Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part018] using hcert

def TailChunk001Sub001Block033Part019SupportExplicit : Finset ℕ :=
  ([26113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block033Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26113
    = surrogateDiagTailX0RatChunk001Sub001Block033Part019

theorem surrogateDiagonalTailChunk001Sub001Block033Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part019] using hcert

def TailChunk001Sub001Block033Part020SupportExplicit : Finset ℕ :=
  ([26114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part020 : ℚ :=
  (4727537487 : ℚ) / 659636003225814400

def SurrogateDiagonalTailChunk001Sub001Block033Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26114
    = surrogateDiagTailX0RatChunk001Sub001Block033Part020

theorem surrogateDiagonalTailChunk001Sub001Block033Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part020] using hcert

def TailChunk001Sub001Block033Part021SupportExplicit : Finset ℕ :=
  ([26115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part021 : ℚ :=
  (79521480389 : ℚ) / 1877646342625689600

def SurrogateDiagonalTailChunk001Sub001Block033Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26115
    = surrogateDiagTailX0RatChunk001Sub001Block033Part021

theorem surrogateDiagonalTailChunk001Sub001Block033Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part021] using hcert

def TailChunk001Sub001Block033Part022SupportExplicit : Finset ℕ :=
  ([26119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block033Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26119
    = surrogateDiagTailX0RatChunk001Sub001Block033Part022

theorem surrogateDiagonalTailChunk001Sub001Block033Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part022] using hcert

def TailChunk001Sub001Block033Part023SupportExplicit : Finset ℕ :=
  ([26121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part023 : ℚ :=
  (41675 : ℚ) / 15319457409488256

def SurrogateDiagonalTailChunk001Sub001Block033Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26121
    = surrogateDiagTailX0RatChunk001Sub001Block033Part023

theorem surrogateDiagonalTailChunk001Sub001Block033Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part023] using hcert

def TailChunk001Sub001Block033Part024SupportExplicit : Finset ℕ :=
  ([26122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block033Part024 : ℚ :=
  (5426074075 : ℚ) / 2930790904337793024

def SurrogateDiagonalTailChunk001Sub001Block033Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26122
    = surrogateDiagTailX0RatChunk001Sub001Block033Part024

theorem surrogateDiagonalTailChunk001Sub001Block033Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block033Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block033Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block033Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block033Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block033Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block033Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block033HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block033Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block033Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block033Part000
    + surrogateDiagTailX0RatChunk001Sub001Block033Part001
    + surrogateDiagTailX0RatChunk001Sub001Block033Part002
    + surrogateDiagTailX0RatChunk001Sub001Block033Part003
    + surrogateDiagTailX0RatChunk001Sub001Block033Part004
    + surrogateDiagTailX0RatChunk001Sub001Block033Part005
    + surrogateDiagTailX0RatChunk001Sub001Block033Part006
    + surrogateDiagTailX0RatChunk001Sub001Block033Part007
    + surrogateDiagTailX0RatChunk001Sub001Block033Part008
    + surrogateDiagTailX0RatChunk001Sub001Block033Part009

def surrogateDiagonalTailChunk001Sub001Block033MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block033Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block033Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block033Part010
    + surrogateDiagTailX0RatChunk001Sub001Block033Part011
    + surrogateDiagTailX0RatChunk001Sub001Block033Part012
    + surrogateDiagTailX0RatChunk001Sub001Block033Part013
    + surrogateDiagTailX0RatChunk001Sub001Block033Part014
    + surrogateDiagTailX0RatChunk001Sub001Block033Part015
    + surrogateDiagTailX0RatChunk001Sub001Block033Part016
    + surrogateDiagTailX0RatChunk001Sub001Block033Part017
    + surrogateDiagTailX0RatChunk001Sub001Block033Part018
    + surrogateDiagTailX0RatChunk001Sub001Block033Part019

def surrogateDiagonalTailChunk001Sub001Block033TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block033Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block033Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block033Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block033Part020
    + surrogateDiagTailX0RatChunk001Sub001Block033Part021
    + surrogateDiagTailX0RatChunk001Sub001Block033Part022
    + surrogateDiagTailX0RatChunk001Sub001Block033Part023
    + surrogateDiagTailX0RatChunk001Sub001Block033Part024

def surrogateDiagonalTailChunk001Sub001Block033Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block033HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block033MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block033TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block033 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block033Part000
    + surrogateDiagTailX0RatChunk001Sub001Block033Part001
    + surrogateDiagTailX0RatChunk001Sub001Block033Part002
    + surrogateDiagTailX0RatChunk001Sub001Block033Part003
    + surrogateDiagTailX0RatChunk001Sub001Block033Part004
    + surrogateDiagTailX0RatChunk001Sub001Block033Part005
    + surrogateDiagTailX0RatChunk001Sub001Block033Part006
    + surrogateDiagTailX0RatChunk001Sub001Block033Part007
    + surrogateDiagTailX0RatChunk001Sub001Block033Part008
    + surrogateDiagTailX0RatChunk001Sub001Block033Part009
    + surrogateDiagTailX0RatChunk001Sub001Block033Part010
    + surrogateDiagTailX0RatChunk001Sub001Block033Part011
    + surrogateDiagTailX0RatChunk001Sub001Block033Part012
    + surrogateDiagTailX0RatChunk001Sub001Block033Part013
    + surrogateDiagTailX0RatChunk001Sub001Block033Part014
    + surrogateDiagTailX0RatChunk001Sub001Block033Part015
    + surrogateDiagTailX0RatChunk001Sub001Block033Part016
    + surrogateDiagTailX0RatChunk001Sub001Block033Part017
    + surrogateDiagTailX0RatChunk001Sub001Block033Part018
    + surrogateDiagTailX0RatChunk001Sub001Block033Part019
    + surrogateDiagTailX0RatChunk001Sub001Block033Part020
    + surrogateDiagTailX0RatChunk001Sub001Block033Part021
    + surrogateDiagTailX0RatChunk001Sub001Block033Part022
    + surrogateDiagTailX0RatChunk001Sub001Block033Part023
    + surrogateDiagTailX0RatChunk001Sub001Block033Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block033_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block033Head + surrogateDiagTailX0RatChunk001Sub001Block033Mid + surrogateDiagTailX0RatChunk001Sub001Block033Tail =
      surrogateDiagTailX0RatChunk001Sub001Block033 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block033Head surrogateDiagTailX0RatChunk001Sub001Block033Mid surrogateDiagTailX0RatChunk001Sub001Block033Tail surrogateDiagTailX0RatChunk001Sub001Block033
  ring

def SurrogateDiagonalTailChunk001Sub001Block033HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block033HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block033Head

def SurrogateDiagonalTailChunk001Sub001Block033MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block033MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block033Mid

def SurrogateDiagonalTailChunk001Sub001Block033TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block033TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block033Tail

theorem surrogateDiagonalTailChunk001Sub001Block033_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block033HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block033MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block033TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block033Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block033 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block033HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block033MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block033TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block033Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block033_eq_head_add_mid_add_tail

/-- Block 034 covers tail-support indices [15850,15875) and q from 26123 to 26162. -/

def TailChunk001Sub001Block034Part000SupportExplicit : Finset ℕ :=
  ([26123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part000 : ℚ :=
  (4001745187 : ℚ) / 44316522492192000000

def SurrogateDiagonalTailChunk001Sub001Block034Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26123
    = surrogateDiagTailX0RatChunk001Sub001Block034Part000

theorem surrogateDiagonalTailChunk001Sub001Block034Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part000] using hcert

def TailChunk001Sub001Block034Part001SupportExplicit : Finset ℕ :=
  ([26126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block034Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26126
    = surrogateDiagTailX0RatChunk001Sub001Block034Part001

theorem surrogateDiagonalTailChunk001Sub001Block034Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part001] using hcert

def TailChunk001Sub001Block034Part002SupportExplicit : Finset ℕ :=
  ([26129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part002 : ℚ :=
  (809422158625 : ℚ) / 736465300656098377728

def SurrogateDiagonalTailChunk001Sub001Block034Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26129
    = surrogateDiagTailX0RatChunk001Sub001Block034Part002

theorem surrogateDiagonalTailChunk001Sub001Block034Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part002] using hcert

def TailChunk001Sub001Block034Part003SupportExplicit : Finset ℕ :=
  ([26130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part003 : ℚ :=
  (1204969646725 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk001Sub001Block034Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26130
    = surrogateDiagTailX0RatChunk001Sub001Block034Part003

theorem surrogateDiagonalTailChunk001Sub001Block034Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part003] using hcert

def TailChunk001Sub001Block034Part004SupportExplicit : Finset ℕ :=
  ([26131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part004 : ℚ :=
  (871252339175 : ℚ) / 314317386734626612224

def SurrogateDiagonalTailChunk001Sub001Block034Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26131
    = surrogateDiagTailX0RatChunk001Sub001Block034Part004

theorem surrogateDiagonalTailChunk001Sub001Block034Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part004] using hcert

def TailChunk001Sub001Block034Part005SupportExplicit : Finset ℕ :=
  ([26133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part005 : ℚ :=
  (7808418391 : ℚ) / 7967534948352000000

def SurrogateDiagonalTailChunk001Sub001Block034Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26133
    = surrogateDiagTailX0RatChunk001Sub001Block034Part005

theorem surrogateDiagonalTailChunk001Sub001Block034Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part005] using hcert

def TailChunk001Sub001Block034Part006SupportExplicit : Finset ℕ :=
  ([26134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part006 : ℚ :=
  (2421616775 : ℚ) / 2108078968676557824

def SurrogateDiagonalTailChunk001Sub001Block034Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26134
    = surrogateDiagTailX0RatChunk001Sub001Block034Part006

theorem surrogateDiagonalTailChunk001Sub001Block034Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part006] using hcert

def TailChunk001Sub001Block034Part007SupportExplicit : Finset ℕ :=
  ([26135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part007 : ℚ :=
  (1708192784125 : ℚ) / 477468192801428195328

def SurrogateDiagonalTailChunk001Sub001Block034Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26135
    = surrogateDiagTailX0RatChunk001Sub001Block034Part007

theorem surrogateDiagonalTailChunk001Sub001Block034Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part007] using hcert

def TailChunk001Sub001Block034Part008SupportExplicit : Finset ℕ :=
  ([26137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part008 : ℚ :=
  (3171302625 : ℚ) / 22500215266277423896

def SurrogateDiagonalTailChunk001Sub001Block034Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26137
    = surrogateDiagTailX0RatChunk001Sub001Block034Part008

theorem surrogateDiagonalTailChunk001Sub001Block034Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part008] using hcert

def TailChunk001Sub001Block034Part009SupportExplicit : Finset ℕ :=
  ([26138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part009 : ℚ :=
  (12120004225 : ℚ) / 727586543367191232

def SurrogateDiagonalTailChunk001Sub001Block034Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26138
    = surrogateDiagTailX0RatChunk001Sub001Block034Part009

theorem surrogateDiagonalTailChunk001Sub001Block034Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part009] using hcert

def TailChunk001Sub001Block034Part010SupportExplicit : Finset ℕ :=
  ([26139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part010 : ℚ :=
  (41675 : ℚ) / 15361732534173696

def SurrogateDiagonalTailChunk001Sub001Block034Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26139
    = surrogateDiagTailX0RatChunk001Sub001Block034Part010

theorem surrogateDiagonalTailChunk001Sub001Block034Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part010] using hcert

def TailChunk001Sub001Block034Part011SupportExplicit : Finset ℕ :=
  ([26141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block034Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26141
    = surrogateDiagTailX0RatChunk001Sub001Block034Part011

theorem surrogateDiagonalTailChunk001Sub001Block034Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part011] using hcert

def TailChunk001Sub001Block034Part012SupportExplicit : Finset ℕ :=
  ([26142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part012 : ℚ :=
  (148318259825 : ℚ) / 1800563071954749696

def SurrogateDiagonalTailChunk001Sub001Block034Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26142
    = surrogateDiagTailX0RatChunk001Sub001Block034Part012

theorem surrogateDiagonalTailChunk001Sub001Block034Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part012] using hcert

def TailChunk001Sub001Block034Part013SupportExplicit : Finset ℕ :=
  ([26143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part013 : ℚ :=
  (3804843749 : ℚ) / 4231614309823238400

def SurrogateDiagonalTailChunk001Sub001Block034Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26143
    = surrogateDiagTailX0RatChunk001Sub001Block034Part013

theorem surrogateDiagonalTailChunk001Sub001Block034Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part013] using hcert

def TailChunk001Sub001Block034Part014SupportExplicit : Finset ℕ :=
  ([26146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part014 : ℚ :=
  (12553404575 : ℚ) / 3167226806692478976

def SurrogateDiagonalTailChunk001Sub001Block034Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26146
    = surrogateDiagTailX0RatChunk001Sub001Block034Part014

theorem surrogateDiagonalTailChunk001Sub001Block034Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part014] using hcert

def TailChunk001Sub001Block034Part015SupportExplicit : Finset ℕ :=
  ([26147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part015 : ℚ :=
  (2362195093 : ℚ) / 2656387019617689600

def SurrogateDiagonalTailChunk001Sub001Block034Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26147
    = surrogateDiagTailX0RatChunk001Sub001Block034Part015

theorem surrogateDiagonalTailChunk001Sub001Block034Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part015] using hcert

def TailChunk001Sub001Block034Part016SupportExplicit : Finset ℕ :=
  ([26149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part016 : ℚ :=
  (186781171 : ℚ) / 1626137467148937600

def SurrogateDiagonalTailChunk001Sub001Block034Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26149
    = surrogateDiagTailX0RatChunk001Sub001Block034Part016

theorem surrogateDiagonalTailChunk001Sub001Block034Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part016] using hcert

def TailChunk001Sub001Block034Part017SupportExplicit : Finset ℕ :=
  ([26151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part017 : ℚ :=
  (5495574125 : ℚ) / 3986240771313795456

def SurrogateDiagonalTailChunk001Sub001Block034Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26151
    = surrogateDiagTailX0RatChunk001Sub001Block034Part017

theorem surrogateDiagonalTailChunk001Sub001Block034Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part017] using hcert

def TailChunk001Sub001Block034Part018SupportExplicit : Finset ℕ :=
  ([26153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block034Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26153
    = surrogateDiagTailX0RatChunk001Sub001Block034Part018

theorem surrogateDiagonalTailChunk001Sub001Block034Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part018] using hcert

def TailChunk001Sub001Block034Part019SupportExplicit : Finset ℕ :=
  ([26155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part019 : ℚ :=
  (4562151423 : ℚ) / 1277151188714977280

def SurrogateDiagonalTailChunk001Sub001Block034Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26155
    = surrogateDiagTailX0RatChunk001Sub001Block034Part019

theorem surrogateDiagonalTailChunk001Sub001Block034Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part019] using hcert

def TailChunk001Sub001Block034Part020SupportExplicit : Finset ℕ :=
  ([26157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part020 : ℚ :=
  (41675 : ℚ) / 15404095094449536

def SurrogateDiagonalTailChunk001Sub001Block034Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26157
    = surrogateDiagTailX0RatChunk001Sub001Block034Part020

theorem surrogateDiagonalTailChunk001Sub001Block034Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part020] using hcert

def TailChunk001Sub001Block034Part021SupportExplicit : Finset ℕ :=
  ([26158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part021 : ℚ :=
  (6972054087 : ℚ) / 524611354624000000

def SurrogateDiagonalTailChunk001Sub001Block034Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26158
    = surrogateDiagTailX0RatChunk001Sub001Block034Part021

theorem surrogateDiagonalTailChunk001Sub001Block034Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part021] using hcert

def TailChunk001Sub001Block034Part022SupportExplicit : Finset ℕ :=
  ([26159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part022 : ℚ :=
  (24923687317 : ℚ) / 7257392308224000000

def SurrogateDiagonalTailChunk001Sub001Block034Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26159
    = surrogateDiagTailX0RatChunk001Sub001Block034Part022

theorem surrogateDiagonalTailChunk001Sub001Block034Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part022] using hcert

def TailChunk001Sub001Block034Part023SupportExplicit : Finset ℕ :=
  ([26161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block034Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26161
    = surrogateDiagTailX0RatChunk001Sub001Block034Part023

theorem surrogateDiagonalTailChunk001Sub001Block034Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part023] using hcert

def TailChunk001Sub001Block034Part024SupportExplicit : Finset ℕ :=
  ([26162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block034Part024 : ℚ :=
  (863349175 : ℚ) / 842218365626967168

def SurrogateDiagonalTailChunk001Sub001Block034Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26162
    = surrogateDiagTailX0RatChunk001Sub001Block034Part024

theorem surrogateDiagonalTailChunk001Sub001Block034Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block034Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block034Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block034Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block034Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block034Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block034Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block034HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block034Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block034Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block034Part000
    + surrogateDiagTailX0RatChunk001Sub001Block034Part001
    + surrogateDiagTailX0RatChunk001Sub001Block034Part002
    + surrogateDiagTailX0RatChunk001Sub001Block034Part003
    + surrogateDiagTailX0RatChunk001Sub001Block034Part004
    + surrogateDiagTailX0RatChunk001Sub001Block034Part005
    + surrogateDiagTailX0RatChunk001Sub001Block034Part006
    + surrogateDiagTailX0RatChunk001Sub001Block034Part007
    + surrogateDiagTailX0RatChunk001Sub001Block034Part008
    + surrogateDiagTailX0RatChunk001Sub001Block034Part009

def surrogateDiagonalTailChunk001Sub001Block034MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block034Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block034Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block034Part010
    + surrogateDiagTailX0RatChunk001Sub001Block034Part011
    + surrogateDiagTailX0RatChunk001Sub001Block034Part012
    + surrogateDiagTailX0RatChunk001Sub001Block034Part013
    + surrogateDiagTailX0RatChunk001Sub001Block034Part014
    + surrogateDiagTailX0RatChunk001Sub001Block034Part015
    + surrogateDiagTailX0RatChunk001Sub001Block034Part016
    + surrogateDiagTailX0RatChunk001Sub001Block034Part017
    + surrogateDiagTailX0RatChunk001Sub001Block034Part018
    + surrogateDiagTailX0RatChunk001Sub001Block034Part019

def surrogateDiagonalTailChunk001Sub001Block034TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block034Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block034Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block034Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block034Part020
    + surrogateDiagTailX0RatChunk001Sub001Block034Part021
    + surrogateDiagTailX0RatChunk001Sub001Block034Part022
    + surrogateDiagTailX0RatChunk001Sub001Block034Part023
    + surrogateDiagTailX0RatChunk001Sub001Block034Part024

def surrogateDiagonalTailChunk001Sub001Block034Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block034HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block034MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block034TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block034 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block034Part000
    + surrogateDiagTailX0RatChunk001Sub001Block034Part001
    + surrogateDiagTailX0RatChunk001Sub001Block034Part002
    + surrogateDiagTailX0RatChunk001Sub001Block034Part003
    + surrogateDiagTailX0RatChunk001Sub001Block034Part004
    + surrogateDiagTailX0RatChunk001Sub001Block034Part005
    + surrogateDiagTailX0RatChunk001Sub001Block034Part006
    + surrogateDiagTailX0RatChunk001Sub001Block034Part007
    + surrogateDiagTailX0RatChunk001Sub001Block034Part008
    + surrogateDiagTailX0RatChunk001Sub001Block034Part009
    + surrogateDiagTailX0RatChunk001Sub001Block034Part010
    + surrogateDiagTailX0RatChunk001Sub001Block034Part011
    + surrogateDiagTailX0RatChunk001Sub001Block034Part012
    + surrogateDiagTailX0RatChunk001Sub001Block034Part013
    + surrogateDiagTailX0RatChunk001Sub001Block034Part014
    + surrogateDiagTailX0RatChunk001Sub001Block034Part015
    + surrogateDiagTailX0RatChunk001Sub001Block034Part016
    + surrogateDiagTailX0RatChunk001Sub001Block034Part017
    + surrogateDiagTailX0RatChunk001Sub001Block034Part018
    + surrogateDiagTailX0RatChunk001Sub001Block034Part019
    + surrogateDiagTailX0RatChunk001Sub001Block034Part020
    + surrogateDiagTailX0RatChunk001Sub001Block034Part021
    + surrogateDiagTailX0RatChunk001Sub001Block034Part022
    + surrogateDiagTailX0RatChunk001Sub001Block034Part023
    + surrogateDiagTailX0RatChunk001Sub001Block034Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block034_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block034Head + surrogateDiagTailX0RatChunk001Sub001Block034Mid + surrogateDiagTailX0RatChunk001Sub001Block034Tail =
      surrogateDiagTailX0RatChunk001Sub001Block034 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block034Head surrogateDiagTailX0RatChunk001Sub001Block034Mid surrogateDiagTailX0RatChunk001Sub001Block034Tail surrogateDiagTailX0RatChunk001Sub001Block034
  ring

def SurrogateDiagonalTailChunk001Sub001Block034HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block034HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block034Head

def SurrogateDiagonalTailChunk001Sub001Block034MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block034MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block034Mid

def SurrogateDiagonalTailChunk001Sub001Block034TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block034TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block034Tail

theorem surrogateDiagonalTailChunk001Sub001Block034_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block034HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block034MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block034TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block034Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block034 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block034HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block034MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block034TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block034Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block034_eq_head_add_mid_add_tail

/-- Block 035 covers tail-support indices [15875,15900) and q from 26165 to 26205. -/

def TailChunk001Sub001Block035Part000SupportExplicit : Finset ℕ :=
  ([26165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part000 : ℚ :=
  (1712114533375 : ℚ) / 479664707603873660928

def SurrogateDiagonalTailChunk001Sub001Block035Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26165
    = surrogateDiagTailX0RatChunk001Sub001Block035Part000

theorem surrogateDiagonalTailChunk001Sub001Block035Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part000] using hcert

def TailChunk001Sub001Block035Part001SupportExplicit : Finset ℕ :=
  ([26167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part001 : ℚ :=
  (1352622789 : ℚ) / 14863997814167142400

def SurrogateDiagonalTailChunk001Sub001Block035Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26167
    = surrogateDiagTailX0RatChunk001Sub001Block035Part001

theorem surrogateDiagonalTailChunk001Sub001Block035Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part001] using hcert

def TailChunk001Sub001Block035Part002SupportExplicit : Finset ℕ :=
  ([26169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part002 : ℚ :=
  (10510181419 : ℚ) / 1433558974464000000

def SurrogateDiagonalTailChunk001Sub001Block035Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26169
    = surrogateDiagTailX0RatChunk001Sub001Block035Part002

theorem surrogateDiagonalTailChunk001Sub001Block035Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part002] using hcert

def TailChunk001Sub001Block035Part003SupportExplicit : Finset ℕ :=
  ([26170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part003 : ℚ :=
  (428966860375 : ℚ) / 29979044225242103808

def SurrogateDiagonalTailChunk001Sub001Block035Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26170
    = surrogateDiagTailX0RatChunk001Sub001Block035Part003

theorem surrogateDiagonalTailChunk001Sub001Block035Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part003] using hcert

def TailChunk001Sub001Block035Part004SupportExplicit : Finset ℕ :=
  ([26171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block035Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26171
    = surrogateDiagTailX0RatChunk001Sub001Block035Part004

theorem surrogateDiagonalTailChunk001Sub001Block035Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part004] using hcert

def TailChunk001Sub001Block035Part005SupportExplicit : Finset ℕ :=
  ([26173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part005 : ℚ :=
  (874053029075 : ℚ) / 316343600237025958464

def SurrogateDiagonalTailChunk001Sub001Block035Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26173
    = surrogateDiagTailX0RatChunk001Sub001Block035Part005

theorem surrogateDiagonalTailChunk001Sub001Block035Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part005] using hcert

def TailChunk001Sub001Block035Part006SupportExplicit : Finset ℕ :=
  ([26174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part006 : ℚ :=
  (188049826225 : ℚ) / 60969260155749040128

def SurrogateDiagonalTailChunk001Sub001Block035Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26174
    = surrogateDiagTailX0RatChunk001Sub001Block035Part006

theorem surrogateDiagonalTailChunk001Sub001Block035Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part006] using hcert

def TailChunk001Sub001Block035Part007SupportExplicit : Finset ℕ :=
  ([26177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block035Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26177
    = surrogateDiagTailX0RatChunk001Sub001Block035Part007

theorem surrogateDiagonalTailChunk001Sub001Block035Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part007] using hcert

def TailChunk001Sub001Block035Part008SupportExplicit : Finset ℕ :=
  ([26178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part008 : ℚ :=
  (594907664225 : ℚ) / 7242016181172231744

def SurrogateDiagonalTailChunk001Sub001Block035Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26178
    = surrogateDiagTailX0RatChunk001Sub001Block035Part008

theorem surrogateDiagonalTailChunk001Sub001Block035Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part008] using hcert

def TailChunk001Sub001Block035Part009SupportExplicit : Finset ℕ :=
  ([26179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part009 : ℚ :=
  (187938767125 : ℚ) / 1069934895122471897088

def SurrogateDiagonalTailChunk001Sub001Block035Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26179
    = surrogateDiagTailX0RatChunk001Sub001Block035Part009

theorem surrogateDiagonalTailChunk001Sub001Block035Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part009] using hcert

def TailChunk001Sub001Block035Part010SupportExplicit : Finset ℕ :=
  ([26182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part010 : ℚ :=
  (40354624975 : ℚ) / 3061342253024280576

def SurrogateDiagonalTailChunk001Sub001Block035Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26182
    = surrogateDiagTailX0RatChunk001Sub001Block035Part010

theorem surrogateDiagonalTailChunk001Sub001Block035Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part010] using hcert

def TailChunk001Sub001Block035Part011SupportExplicit : Finset ℕ :=
  ([26183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block035Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26183
    = surrogateDiagTailX0RatChunk001Sub001Block035Part011

theorem surrogateDiagonalTailChunk001Sub001Block035Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part011] using hcert

def TailChunk001Sub001Block035Part012SupportExplicit : Finset ℕ :=
  ([26185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part012 : ℚ :=
  (571577177625 : ℚ) / 160377751731594428416

def SurrogateDiagonalTailChunk001Sub001Block035Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26185
    = surrogateDiagTailX0RatChunk001Sub001Block035Part012

theorem surrogateDiagonalTailChunk001Sub001Block035Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part012] using hcert

def TailChunk001Sub001Block035Part013SupportExplicit : Finset ℕ :=
  ([26186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block035Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26186
    = surrogateDiagTailX0RatChunk001Sub001Block035Part013

theorem surrogateDiagonalTailChunk001Sub001Block035Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part013] using hcert

def TailChunk001Sub001Block035Part014SupportExplicit : Finset ℕ :=
  ([26187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part014 : ℚ :=
  (863762100625 : ℚ) / 99170186514588499968

def SurrogateDiagonalTailChunk001Sub001Block035Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26187
    = surrogateDiagTailX0RatChunk001Sub001Block035Part014

theorem surrogateDiagonalTailChunk001Sub001Block035Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part014] using hcert

def TailChunk001Sub001Block035Part015SupportExplicit : Finset ℕ :=
  ([26189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block035Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26189
    = surrogateDiagTailX0RatChunk001Sub001Block035Part015

theorem surrogateDiagonalTailChunk001Sub001Block035Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part015] using hcert

def TailChunk001Sub001Block035Part016SupportExplicit : Finset ℕ :=
  ([26191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part016 : ℚ :=
  (6084441331 : ℚ) / 4584549206496000000

def SurrogateDiagonalTailChunk001Sub001Block035Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26191
    = surrogateDiagTailX0RatChunk001Sub001Block035Part016

theorem surrogateDiagonalTailChunk001Sub001Block035Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part016] using hcert

def TailChunk001Sub001Block035Part017SupportExplicit : Finset ℕ :=
  ([26193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part017 : ℚ :=
  (1667 : ℚ) / 619563320150400

def SurrogateDiagonalTailChunk001Sub001Block035Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26193
    = surrogateDiagTailX0RatChunk001Sub001Block035Part017

theorem surrogateDiagonalTailChunk001Sub001Block035Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part017] using hcert

def TailChunk001Sub001Block035Part018SupportExplicit : Finset ℕ :=
  ([26194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part018 : ℚ :=
  (8777997167 : ℚ) / 792552941620545600

def SurrogateDiagonalTailChunk001Sub001Block035Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26194
    = surrogateDiagTailX0RatChunk001Sub001Block035Part018

theorem surrogateDiagonalTailChunk001Sub001Block035Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part018] using hcert

def TailChunk001Sub001Block035Part019SupportExplicit : Finset ℕ :=
  ([26197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part019 : ℚ :=
  (48515836825 : ℚ) / 40466975817430204416

def SurrogateDiagonalTailChunk001Sub001Block035Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26197
    = surrogateDiagTailX0RatChunk001Sub001Block035Part019

theorem surrogateDiagonalTailChunk001Sub001Block035Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part019] using hcert

def TailChunk001Sub001Block035Part020SupportExplicit : Finset ℕ :=
  ([26198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block035Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26198
    = surrogateDiagTailX0RatChunk001Sub001Block035Part020

theorem surrogateDiagonalTailChunk001Sub001Block035Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part020] using hcert

def TailChunk001Sub001Block035Part021SupportExplicit : Finset ℕ :=
  ([26201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part021 : ℚ :=
  (150624763475 : ℚ) / 62756133653763035136

def SurrogateDiagonalTailChunk001Sub001Block035Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26201
    = surrogateDiagTailX0RatChunk001Sub001Block035Part021

theorem surrogateDiagonalTailChunk001Sub001Block035Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part021] using hcert

def TailChunk001Sub001Block035Part022SupportExplicit : Finset ℕ :=
  ([26202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part022 : ℚ :=
  (521207011 : ℚ) / 4099362684595200

def SurrogateDiagonalTailChunk001Sub001Block035Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26202
    = surrogateDiagTailX0RatChunk001Sub001Block035Part022

theorem surrogateDiagonalTailChunk001Sub001Block035Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part022] using hcert

def TailChunk001Sub001Block035Part023SupportExplicit : Finset ℕ :=
  ([26203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block035Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26203
    = surrogateDiagTailX0RatChunk001Sub001Block035Part023

theorem surrogateDiagonalTailChunk001Sub001Block035Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part023] using hcert

def TailChunk001Sub001Block035Part024SupportExplicit : Finset ℕ :=
  ([26205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block035Part024 : ℚ :=
  (143240298425 : ℚ) / 11897994870037057536

def SurrogateDiagonalTailChunk001Sub001Block035Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26205
    = surrogateDiagTailX0RatChunk001Sub001Block035Part024

theorem surrogateDiagonalTailChunk001Sub001Block035Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block035Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block035Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block035Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block035Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block035Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block035Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block035HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block035Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block035Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block035Part000
    + surrogateDiagTailX0RatChunk001Sub001Block035Part001
    + surrogateDiagTailX0RatChunk001Sub001Block035Part002
    + surrogateDiagTailX0RatChunk001Sub001Block035Part003
    + surrogateDiagTailX0RatChunk001Sub001Block035Part004
    + surrogateDiagTailX0RatChunk001Sub001Block035Part005
    + surrogateDiagTailX0RatChunk001Sub001Block035Part006
    + surrogateDiagTailX0RatChunk001Sub001Block035Part007
    + surrogateDiagTailX0RatChunk001Sub001Block035Part008
    + surrogateDiagTailX0RatChunk001Sub001Block035Part009

def surrogateDiagonalTailChunk001Sub001Block035MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block035Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block035Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block035Part010
    + surrogateDiagTailX0RatChunk001Sub001Block035Part011
    + surrogateDiagTailX0RatChunk001Sub001Block035Part012
    + surrogateDiagTailX0RatChunk001Sub001Block035Part013
    + surrogateDiagTailX0RatChunk001Sub001Block035Part014
    + surrogateDiagTailX0RatChunk001Sub001Block035Part015
    + surrogateDiagTailX0RatChunk001Sub001Block035Part016
    + surrogateDiagTailX0RatChunk001Sub001Block035Part017
    + surrogateDiagTailX0RatChunk001Sub001Block035Part018
    + surrogateDiagTailX0RatChunk001Sub001Block035Part019

def surrogateDiagonalTailChunk001Sub001Block035TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block035Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block035Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block035Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block035Part020
    + surrogateDiagTailX0RatChunk001Sub001Block035Part021
    + surrogateDiagTailX0RatChunk001Sub001Block035Part022
    + surrogateDiagTailX0RatChunk001Sub001Block035Part023
    + surrogateDiagTailX0RatChunk001Sub001Block035Part024

def surrogateDiagonalTailChunk001Sub001Block035Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block035HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block035MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block035TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block035 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block035Part000
    + surrogateDiagTailX0RatChunk001Sub001Block035Part001
    + surrogateDiagTailX0RatChunk001Sub001Block035Part002
    + surrogateDiagTailX0RatChunk001Sub001Block035Part003
    + surrogateDiagTailX0RatChunk001Sub001Block035Part004
    + surrogateDiagTailX0RatChunk001Sub001Block035Part005
    + surrogateDiagTailX0RatChunk001Sub001Block035Part006
    + surrogateDiagTailX0RatChunk001Sub001Block035Part007
    + surrogateDiagTailX0RatChunk001Sub001Block035Part008
    + surrogateDiagTailX0RatChunk001Sub001Block035Part009
    + surrogateDiagTailX0RatChunk001Sub001Block035Part010
    + surrogateDiagTailX0RatChunk001Sub001Block035Part011
    + surrogateDiagTailX0RatChunk001Sub001Block035Part012
    + surrogateDiagTailX0RatChunk001Sub001Block035Part013
    + surrogateDiagTailX0RatChunk001Sub001Block035Part014
    + surrogateDiagTailX0RatChunk001Sub001Block035Part015
    + surrogateDiagTailX0RatChunk001Sub001Block035Part016
    + surrogateDiagTailX0RatChunk001Sub001Block035Part017
    + surrogateDiagTailX0RatChunk001Sub001Block035Part018
    + surrogateDiagTailX0RatChunk001Sub001Block035Part019
    + surrogateDiagTailX0RatChunk001Sub001Block035Part020
    + surrogateDiagTailX0RatChunk001Sub001Block035Part021
    + surrogateDiagTailX0RatChunk001Sub001Block035Part022
    + surrogateDiagTailX0RatChunk001Sub001Block035Part023
    + surrogateDiagTailX0RatChunk001Sub001Block035Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block035_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block035Head + surrogateDiagTailX0RatChunk001Sub001Block035Mid + surrogateDiagTailX0RatChunk001Sub001Block035Tail =
      surrogateDiagTailX0RatChunk001Sub001Block035 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block035Head surrogateDiagTailX0RatChunk001Sub001Block035Mid surrogateDiagTailX0RatChunk001Sub001Block035Tail surrogateDiagTailX0RatChunk001Sub001Block035
  ring

def SurrogateDiagonalTailChunk001Sub001Block035HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block035HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block035Head

def SurrogateDiagonalTailChunk001Sub001Block035MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block035MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block035Mid

def SurrogateDiagonalTailChunk001Sub001Block035TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block035TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block035Tail

theorem surrogateDiagonalTailChunk001Sub001Block035_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block035HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block035MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block035TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block035Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block035 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block035HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block035MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block035TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block035Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block035_eq_head_add_mid_add_tail

/-- Block 036 covers tail-support indices [15900,15925) and q from 26206 to 26245. -/

def TailChunk001Sub001Block036Part000SupportExplicit : Finset ℕ :=
  ([26206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block036Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26206
    = surrogateDiagTailX0RatChunk001Sub001Block036Part000

theorem surrogateDiagonalTailChunk001Sub001Block036Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part000] using hcert

def TailChunk001Sub001Block036Part001SupportExplicit : Finset ℕ :=
  ([26207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part001 : ℚ :=
  (44732902525 : ℚ) / 367932114603191402496

def SurrogateDiagonalTailChunk001Sub001Block036Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26207
    = surrogateDiagTailX0RatChunk001Sub001Block036Part001

theorem surrogateDiagonalTailChunk001Sub001Block036Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part001] using hcert

def TailChunk001Sub001Block036Part002SupportExplicit : Finset ℕ :=
  ([26209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block036Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26209
    = surrogateDiagTailX0RatChunk001Sub001Block036Part002

theorem surrogateDiagonalTailChunk001Sub001Block036Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part002] using hcert

def TailChunk001Sub001Block036Part003SupportExplicit : Finset ℕ :=
  ([26210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part003 : ℚ :=
  (34365149149 : ℚ) / 1206512930751283200

def SurrogateDiagonalTailChunk001Sub001Block036Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26210
    = surrogateDiagTailX0RatChunk001Sub001Block036Part003

theorem surrogateDiagonalTailChunk001Sub001Block036Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part003] using hcert

def TailChunk001Sub001Block036Part004SupportExplicit : Finset ℕ :=
  ([26211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part004 : ℚ :=
  (41675 : ℚ) / 15531708593995776

def SurrogateDiagonalTailChunk001Sub001Block036Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26211
    = surrogateDiagTailX0RatChunk001Sub001Block036Part004

theorem surrogateDiagonalTailChunk001Sub001Block036Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part004] using hcert

def TailChunk001Sub001Block036Part005SupportExplicit : Finset ℕ :=
  ([26213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part005 : ℚ :=
  (593521927 : ℚ) / 670830255010157400

def SurrogateDiagonalTailChunk001Sub001Block036Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26213
    = surrogateDiagTailX0RatChunk001Sub001Block036Part005

theorem surrogateDiagonalTailChunk001Sub001Block036Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part005] using hcert

def TailChunk001Sub001Block036Part006SupportExplicit : Finset ℕ :=
  ([26214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part006 : ℚ :=
  (1206039970225 : ℚ) / 11261250868239925248

def SurrogateDiagonalTailChunk001Sub001Block036Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26214
    = surrogateDiagTailX0RatChunk001Sub001Block036Part006

theorem surrogateDiagonalTailChunk001Sub001Block036Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part006] using hcert

def TailChunk001Sub001Block036Part007SupportExplicit : Finset ℕ :=
  ([26218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block036Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26218
    = surrogateDiagTailX0RatChunk001Sub001Block036Part007

theorem surrogateDiagonalTailChunk001Sub001Block036Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part007] using hcert

def TailChunk001Sub001Block036Part008SupportExplicit : Finset ℕ :=
  ([26219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part008 : ℚ :=
  (16441635125 : ℚ) / 187415866022706367488

def SurrogateDiagonalTailChunk001Sub001Block036Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26219
    = surrogateDiagTailX0RatChunk001Sub001Block036Part008

theorem surrogateDiagonalTailChunk001Sub001Block036Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part008] using hcert

def TailChunk001Sub001Block036Part009SupportExplicit : Finset ℕ :=
  ([26221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part009 : ℚ :=
  (54678298925 : ℚ) / 61176681964851167232

def SurrogateDiagonalTailChunk001Sub001Block036Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26221
    = surrogateDiagTailX0RatChunk001Sub001Block036Part009

theorem surrogateDiagonalTailChunk001Sub001Block036Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part009] using hcert

def TailChunk001Sub001Block036Part010SupportExplicit : Finset ℕ :=
  ([26222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part010 : ℚ :=
  (12197848075 : ℚ) / 736989801653993472

def SurrogateDiagonalTailChunk001Sub001Block036Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26222
    = surrogateDiagTailX0RatChunk001Sub001Block036Part010

theorem surrogateDiagonalTailChunk001Sub001Block036Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part010] using hcert

def TailChunk001Sub001Block036Part011SupportExplicit : Finset ℕ :=
  ([26223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part011 : ℚ :=
  (5001 : ℚ) / 1867220938803200

def SurrogateDiagonalTailChunk001Sub001Block036Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26223
    = surrogateDiagTailX0RatChunk001Sub001Block036Part011

theorem surrogateDiagonalTailChunk001Sub001Block036Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part011] using hcert

def TailChunk001Sub001Block036Part012SupportExplicit : Finset ℕ :=
  ([26227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block036Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26227
    = surrogateDiagTailX0RatChunk001Sub001Block036Part012

theorem surrogateDiagonalTailChunk001Sub001Block036Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part012] using hcert

def TailChunk001Sub001Block036Part013SupportExplicit : Finset ℕ :=
  ([26229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part013 : ℚ :=
  (685273968775 : ℚ) / 125779592815614885888

def SurrogateDiagonalTailChunk001Sub001Block036Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26229
    = surrogateDiagTailX0RatChunk001Sub001Block036Part013

theorem surrogateDiagonalTailChunk001Sub001Block036Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part013] using hcert

def TailChunk001Sub001Block036Part014SupportExplicit : Finset ℕ :=
  ([26230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part014 : ℚ :=
  (12234452053 : ℚ) / 344197509768806400

def SurrogateDiagonalTailChunk001Sub001Block036Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26230
    = surrogateDiagTailX0RatChunk001Sub001Block036Part014

theorem surrogateDiagonalTailChunk001Sub001Block036Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part014] using hcert

def TailChunk001Sub001Block036Part015SupportExplicit : Finset ℕ :=
  ([26231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part015 : ℚ :=
  (12518094925 : ℚ) / 25736043597477838848

def SurrogateDiagonalTailChunk001Sub001Block036Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26231
    = surrogateDiagTailX0RatChunk001Sub001Block036Part015

theorem surrogateDiagonalTailChunk001Sub001Block036Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part015] using hcert

def TailChunk001Sub001Block036Part016SupportExplicit : Finset ℕ :=
  ([26233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part016 : ℚ :=
  (230280647725 : ℚ) / 1055285310208481722368

def SurrogateDiagonalTailChunk001Sub001Block036Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26233
    = surrogateDiagTailX0RatChunk001Sub001Block036Part016

theorem surrogateDiagonalTailChunk001Sub001Block036Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part016] using hcert

def TailChunk001Sub001Block036Part017SupportExplicit : Finset ℕ :=
  ([26234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part017 : ℚ :=
  (35668754125 : ℚ) / 5947732968804974592

def SurrogateDiagonalTailChunk001Sub001Block036Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26234
    = surrogateDiagTailX0RatChunk001Sub001Block036Part017

theorem surrogateDiagonalTailChunk001Sub001Block036Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part017] using hcert

def TailChunk001Sub001Block036Part018SupportExplicit : Finset ℕ :=
  ([26237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block036Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26237
    = surrogateDiagTailX0RatChunk001Sub001Block036Part018

theorem surrogateDiagonalTailChunk001Sub001Block036Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part018] using hcert

def TailChunk001Sub001Block036Part019SupportExplicit : Finset ℕ :=
  ([26238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part019 : ℚ :=
  (149409259775 : ℚ) / 1827163738172979456

def SurrogateDiagonalTailChunk001Sub001Block036Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26238
    = surrogateDiagTailX0RatChunk001Sub001Block036Part019

theorem surrogateDiagonalTailChunk001Sub001Block036Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part019] using hcert

def TailChunk001Sub001Block036Part020SupportExplicit : Finset ℕ :=
  ([26239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part020 : ℚ :=
  (14502203413 : ℚ) / 38079673517357107200

def SurrogateDiagonalTailChunk001Sub001Block036Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26239
    = surrogateDiagTailX0RatChunk001Sub001Block036Part020

theorem surrogateDiagonalTailChunk001Sub001Block036Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part020] using hcert

def TailChunk001Sub001Block036Part021SupportExplicit : Finset ℕ :=
  ([26241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part021 : ℚ :=
  (125025 : ℚ) / 46808840032082048

def SurrogateDiagonalTailChunk001Sub001Block036Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26241
    = surrogateDiagTailX0RatChunk001Sub001Block036Part021

theorem surrogateDiagonalTailChunk001Sub001Block036Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part021] using hcert

def TailChunk001Sub001Block036Part022SupportExplicit : Finset ℕ :=
  ([26242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block036Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26242
    = surrogateDiagTailX0RatChunk001Sub001Block036Part022

theorem surrogateDiagonalTailChunk001Sub001Block036Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part022] using hcert

def TailChunk001Sub001Block036Part023SupportExplicit : Finset ℕ :=
  ([26243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part023 : ℚ :=
  (1113950870125 : ℚ) / 522856657071349843968

def SurrogateDiagonalTailChunk001Sub001Block036Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26243
    = surrogateDiagTailX0RatChunk001Sub001Block036Part023

theorem surrogateDiagonalTailChunk001Sub001Block036Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part023] using hcert

def TailChunk001Sub001Block036Part024SupportExplicit : Finset ℕ :=
  ([26245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block036Part024 : ℚ :=
  (1859081989 : ℚ) / 413037011722567680

def SurrogateDiagonalTailChunk001Sub001Block036Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26245
    = surrogateDiagTailX0RatChunk001Sub001Block036Part024

theorem surrogateDiagonalTailChunk001Sub001Block036Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block036Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block036Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block036Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block036Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block036Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block036Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block036HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block036Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block036Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block036Part000
    + surrogateDiagTailX0RatChunk001Sub001Block036Part001
    + surrogateDiagTailX0RatChunk001Sub001Block036Part002
    + surrogateDiagTailX0RatChunk001Sub001Block036Part003
    + surrogateDiagTailX0RatChunk001Sub001Block036Part004
    + surrogateDiagTailX0RatChunk001Sub001Block036Part005
    + surrogateDiagTailX0RatChunk001Sub001Block036Part006
    + surrogateDiagTailX0RatChunk001Sub001Block036Part007
    + surrogateDiagTailX0RatChunk001Sub001Block036Part008
    + surrogateDiagTailX0RatChunk001Sub001Block036Part009

def surrogateDiagonalTailChunk001Sub001Block036MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block036Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block036Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block036Part010
    + surrogateDiagTailX0RatChunk001Sub001Block036Part011
    + surrogateDiagTailX0RatChunk001Sub001Block036Part012
    + surrogateDiagTailX0RatChunk001Sub001Block036Part013
    + surrogateDiagTailX0RatChunk001Sub001Block036Part014
    + surrogateDiagTailX0RatChunk001Sub001Block036Part015
    + surrogateDiagTailX0RatChunk001Sub001Block036Part016
    + surrogateDiagTailX0RatChunk001Sub001Block036Part017
    + surrogateDiagTailX0RatChunk001Sub001Block036Part018
    + surrogateDiagTailX0RatChunk001Sub001Block036Part019

def surrogateDiagonalTailChunk001Sub001Block036TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block036Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block036Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block036Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block036Part020
    + surrogateDiagTailX0RatChunk001Sub001Block036Part021
    + surrogateDiagTailX0RatChunk001Sub001Block036Part022
    + surrogateDiagTailX0RatChunk001Sub001Block036Part023
    + surrogateDiagTailX0RatChunk001Sub001Block036Part024

def surrogateDiagonalTailChunk001Sub001Block036Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block036HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block036MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block036TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block036 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block036Part000
    + surrogateDiagTailX0RatChunk001Sub001Block036Part001
    + surrogateDiagTailX0RatChunk001Sub001Block036Part002
    + surrogateDiagTailX0RatChunk001Sub001Block036Part003
    + surrogateDiagTailX0RatChunk001Sub001Block036Part004
    + surrogateDiagTailX0RatChunk001Sub001Block036Part005
    + surrogateDiagTailX0RatChunk001Sub001Block036Part006
    + surrogateDiagTailX0RatChunk001Sub001Block036Part007
    + surrogateDiagTailX0RatChunk001Sub001Block036Part008
    + surrogateDiagTailX0RatChunk001Sub001Block036Part009
    + surrogateDiagTailX0RatChunk001Sub001Block036Part010
    + surrogateDiagTailX0RatChunk001Sub001Block036Part011
    + surrogateDiagTailX0RatChunk001Sub001Block036Part012
    + surrogateDiagTailX0RatChunk001Sub001Block036Part013
    + surrogateDiagTailX0RatChunk001Sub001Block036Part014
    + surrogateDiagTailX0RatChunk001Sub001Block036Part015
    + surrogateDiagTailX0RatChunk001Sub001Block036Part016
    + surrogateDiagTailX0RatChunk001Sub001Block036Part017
    + surrogateDiagTailX0RatChunk001Sub001Block036Part018
    + surrogateDiagTailX0RatChunk001Sub001Block036Part019
    + surrogateDiagTailX0RatChunk001Sub001Block036Part020
    + surrogateDiagTailX0RatChunk001Sub001Block036Part021
    + surrogateDiagTailX0RatChunk001Sub001Block036Part022
    + surrogateDiagTailX0RatChunk001Sub001Block036Part023
    + surrogateDiagTailX0RatChunk001Sub001Block036Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block036_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block036Head + surrogateDiagTailX0RatChunk001Sub001Block036Mid + surrogateDiagTailX0RatChunk001Sub001Block036Tail =
      surrogateDiagTailX0RatChunk001Sub001Block036 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block036Head surrogateDiagTailX0RatChunk001Sub001Block036Mid surrogateDiagTailX0RatChunk001Sub001Block036Tail surrogateDiagTailX0RatChunk001Sub001Block036
  ring

def SurrogateDiagonalTailChunk001Sub001Block036HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block036HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block036Head

def SurrogateDiagonalTailChunk001Sub001Block036MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block036MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block036Mid

def SurrogateDiagonalTailChunk001Sub001Block036TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block036TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block036Tail

theorem surrogateDiagonalTailChunk001Sub001Block036_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block036HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block036MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block036TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block036Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block036 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block036HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block036MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block036TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block036Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block036_eq_head_add_mid_add_tail

/-- Block 037 covers tail-support indices [15925,15950) and q from 26246 to 26286. -/

def TailChunk001Sub001Block037Part000SupportExplicit : Finset ℕ :=
  ([26246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part000 : ℚ :=
  (4775068887 : ℚ) / 673086092465766400

def SurrogateDiagonalTailChunk001Sub001Block037Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26246
    = surrogateDiagTailX0RatChunk001Sub001Block037Part000

theorem surrogateDiagonalTailChunk001Sub001Block037Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part000] using hcert

def TailChunk001Sub001Block037Part001SupportExplicit : Finset ℕ :=
  ([26247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part001 : ℚ :=
  (846175375 : ℚ) / 293715208336048128

def SurrogateDiagonalTailChunk001Sub001Block037Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26247
    = surrogateDiagTailX0RatChunk001Sub001Block037Part001

theorem surrogateDiagonalTailChunk001Sub001Block037Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part001] using hcert

def TailChunk001Sub001Block037Part002SupportExplicit : Finset ℕ :=
  ([26249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block037Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26249
    = surrogateDiagTailX0RatChunk001Sub001Block037Part002

theorem surrogateDiagonalTailChunk001Sub001Block037Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part002] using hcert

def TailChunk001Sub001Block037Part003SupportExplicit : Finset ℕ :=
  ([26251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block037Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26251
    = surrogateDiagTailX0RatChunk001Sub001Block037Part003

theorem surrogateDiagonalTailChunk001Sub001Block037Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part003] using hcert

def TailChunk001Sub001Block037Part004SupportExplicit : Finset ℕ :=
  ([26254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block037Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26254
    = surrogateDiagTailX0RatChunk001Sub001Block037Part004

theorem surrogateDiagonalTailChunk001Sub001Block037Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part004] using hcert

def TailChunk001Sub001Block037Part005SupportExplicit : Finset ℕ :=
  ([26255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part005 : ℚ :=
  (1807671029125 : ℚ) / 434419675691973869568

def SurrogateDiagonalTailChunk001Sub001Block037Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26255
    = surrogateDiagTailX0RatChunk001Sub001Block037Part005

theorem surrogateDiagonalTailChunk001Sub001Block037Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part005] using hcert

def TailChunk001Sub001Block037Part006SupportExplicit : Finset ℕ :=
  ([26258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part006 : ℚ :=
  (949626653 : ℚ) / 264442177203868800

def SurrogateDiagonalTailChunk001Sub001Block037Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26258
    = surrogateDiagTailX0RatChunk001Sub001Block037Part006

theorem surrogateDiagonalTailChunk001Sub001Block037Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part006] using hcert

def TailChunk001Sub001Block037Part007SupportExplicit : Finset ℕ :=
  ([26259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part007 : ℚ :=
  (125025 : ℚ) / 46937420952240128

def SurrogateDiagonalTailChunk001Sub001Block037Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26259
    = surrogateDiagTailX0RatChunk001Sub001Block037Part007

theorem surrogateDiagonalTailChunk001Sub001Block037Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part007] using hcert

def TailChunk001Sub001Block037Part008SupportExplicit : Finset ℕ :=
  ([26261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block037Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26261
    = surrogateDiagTailX0RatChunk001Sub001Block037Part008

theorem surrogateDiagonalTailChunk001Sub001Block037Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part008] using hcert

def TailChunk001Sub001Block037Part009SupportExplicit : Finset ℕ :=
  ([26263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block037Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26263
    = surrogateDiagTailX0RatChunk001Sub001Block037Part009

theorem surrogateDiagonalTailChunk001Sub001Block037Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part009] using hcert

def TailChunk001Sub001Block037Part010SupportExplicit : Finset ℕ :=
  ([26265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part010 : ℚ :=
  (142564720625 : ℚ) / 8072813419243241472

def SurrogateDiagonalTailChunk001Sub001Block037Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26265
    = surrogateDiagTailX0RatChunk001Sub001Block037Part010

theorem surrogateDiagonalTailChunk001Sub001Block037Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part010] using hcert

def TailChunk001Sub001Block037Part011SupportExplicit : Finset ℕ :=
  ([26266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part011 : ℚ :=
  (7573121131 : ℚ) / 2473301131570051200

def SurrogateDiagonalTailChunk001Sub001Block037Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26266
    = surrogateDiagTailX0RatChunk001Sub001Block037Part011

theorem surrogateDiagonalTailChunk001Sub001Block037Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part011] using hcert

def TailChunk001Sub001Block037Part012SupportExplicit : Finset ℕ :=
  ([26267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block037Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26267
    = surrogateDiagTailX0RatChunk001Sub001Block037Part012

theorem surrogateDiagonalTailChunk001Sub001Block037Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part012] using hcert

def TailChunk001Sub001Block037Part013SupportExplicit : Finset ℕ :=
  ([26269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part013 : ℚ :=
  (4365697801 : ℚ) / 45146786070999859200

def SurrogateDiagonalTailChunk001Sub001Block037Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26269
    = surrogateDiagTailX0RatChunk001Sub001Block037Part013

theorem surrogateDiagonalTailChunk001Sub001Block037Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part013] using hcert

def TailChunk001Sub001Block037Part014SupportExplicit : Finset ℕ :=
  ([26270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part014 : ℚ :=
  (152025611 : ℚ) / 4249351972454400

def SurrogateDiagonalTailChunk001Sub001Block037Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26270
    = surrogateDiagTailX0RatChunk001Sub001Block037Part014

theorem surrogateDiagonalTailChunk001Sub001Block037Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part014] using hcert

def TailChunk001Sub001Block037Part015SupportExplicit : Finset ℕ :=
  ([26273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part015 : ℚ :=
  (394873883825 : ℚ) / 361202157492047069184

def SurrogateDiagonalTailChunk001Sub001Block037Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26273
    = surrogateDiagTailX0RatChunk001Sub001Block037Part015

theorem surrogateDiagonalTailChunk001Sub001Block037Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part015] using hcert

def TailChunk001Sub001Block037Part016SupportExplicit : Finset ℕ :=
  ([26274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part016 : ℚ :=
  (5383420429 : ℚ) / 55330103808000000

def SurrogateDiagonalTailChunk001Sub001Block037Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26274
    = surrogateDiagTailX0RatChunk001Sub001Block037Part016

theorem surrogateDiagonalTailChunk001Sub001Block037Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part016] using hcert

def TailChunk001Sub001Block037Part017SupportExplicit : Finset ℕ :=
  ([26277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part017 : ℚ :=
  (42066361 : ℚ) / 25073036060811264

def SurrogateDiagonalTailChunk001Sub001Block037Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26277
    = surrogateDiagTailX0RatChunk001Sub001Block037Part017

theorem surrogateDiagonalTailChunk001Sub001Block037Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part017] using hcert

def TailChunk001Sub001Block037Part018SupportExplicit : Finset ℕ :=
  ([26278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part018 : ℚ :=
  (749992825 : ℚ) / 45508719052145664

def SurrogateDiagonalTailChunk001Sub001Block037Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26278
    = surrogateDiagTailX0RatChunk001Sub001Block037Part018

theorem surrogateDiagonalTailChunk001Sub001Block037Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part018] using hcert

def TailChunk001Sub001Block037Part019SupportExplicit : Finset ℕ :=
  ([26279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part019 : ℚ :=
  (2386010317 : ℚ) / 2710459322795865600

def SurrogateDiagonalTailChunk001Sub001Block037Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26279
    = surrogateDiagTailX0RatChunk001Sub001Block037Part019

theorem surrogateDiagonalTailChunk001Sub001Block037Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part019] using hcert

def TailChunk001Sub001Block037Part020SupportExplicit : Finset ℕ :=
  ([26281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part020 : ℚ :=
  (638303547 : ℚ) / 3579855241216000000

def SurrogateDiagonalTailChunk001Sub001Block037Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26281
    = surrogateDiagTailX0RatChunk001Sub001Block037Part020

theorem surrogateDiagonalTailChunk001Sub001Block037Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part020] using hcert

def TailChunk001Sub001Block037Part021SupportExplicit : Finset ℕ :=
  ([26282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part021 : ℚ :=
  (132714158675 : ℚ) / 29103551909204066304

def SurrogateDiagonalTailChunk001Sub001Block037Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26282
    = surrogateDiagTailX0RatChunk001Sub001Block037Part021

theorem surrogateDiagonalTailChunk001Sub001Block037Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part021] using hcert

def TailChunk001Sub001Block037Part022SupportExplicit : Finset ℕ :=
  ([26283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part022 : ℚ :=
  (1667 : ℚ) / 628123653734400

def SurrogateDiagonalTailChunk001Sub001Block037Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26283
    = surrogateDiagTailX0RatChunk001Sub001Block037Part022

theorem surrogateDiagonalTailChunk001Sub001Block037Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part022] using hcert

def TailChunk001Sub001Block037Part023SupportExplicit : Finset ℕ :=
  ([26285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part023 : ℚ :=
  (4023266999 : ℚ) / 524984976000000000

def SurrogateDiagonalTailChunk001Sub001Block037Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26285
    = surrogateDiagTailX0RatChunk001Sub001Block037Part023

theorem surrogateDiagonalTailChunk001Sub001Block037Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part023] using hcert

def TailChunk001Sub001Block037Part024SupportExplicit : Finset ℕ :=
  ([26286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block037Part024 : ℚ :=
  (22744118375 : ℚ) / 195810138890698752

def SurrogateDiagonalTailChunk001Sub001Block037Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26286
    = surrogateDiagTailX0RatChunk001Sub001Block037Part024

theorem surrogateDiagonalTailChunk001Sub001Block037Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block037Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block037Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block037Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block037Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block037Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block037Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block037HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block037Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block037Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block037Part000
    + surrogateDiagTailX0RatChunk001Sub001Block037Part001
    + surrogateDiagTailX0RatChunk001Sub001Block037Part002
    + surrogateDiagTailX0RatChunk001Sub001Block037Part003
    + surrogateDiagTailX0RatChunk001Sub001Block037Part004
    + surrogateDiagTailX0RatChunk001Sub001Block037Part005
    + surrogateDiagTailX0RatChunk001Sub001Block037Part006
    + surrogateDiagTailX0RatChunk001Sub001Block037Part007
    + surrogateDiagTailX0RatChunk001Sub001Block037Part008
    + surrogateDiagTailX0RatChunk001Sub001Block037Part009

def surrogateDiagonalTailChunk001Sub001Block037MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block037Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block037Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block037Part010
    + surrogateDiagTailX0RatChunk001Sub001Block037Part011
    + surrogateDiagTailX0RatChunk001Sub001Block037Part012
    + surrogateDiagTailX0RatChunk001Sub001Block037Part013
    + surrogateDiagTailX0RatChunk001Sub001Block037Part014
    + surrogateDiagTailX0RatChunk001Sub001Block037Part015
    + surrogateDiagTailX0RatChunk001Sub001Block037Part016
    + surrogateDiagTailX0RatChunk001Sub001Block037Part017
    + surrogateDiagTailX0RatChunk001Sub001Block037Part018
    + surrogateDiagTailX0RatChunk001Sub001Block037Part019

def surrogateDiagonalTailChunk001Sub001Block037TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block037Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block037Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block037Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block037Part020
    + surrogateDiagTailX0RatChunk001Sub001Block037Part021
    + surrogateDiagTailX0RatChunk001Sub001Block037Part022
    + surrogateDiagTailX0RatChunk001Sub001Block037Part023
    + surrogateDiagTailX0RatChunk001Sub001Block037Part024

def surrogateDiagonalTailChunk001Sub001Block037Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block037HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block037MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block037TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block037 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block037Part000
    + surrogateDiagTailX0RatChunk001Sub001Block037Part001
    + surrogateDiagTailX0RatChunk001Sub001Block037Part002
    + surrogateDiagTailX0RatChunk001Sub001Block037Part003
    + surrogateDiagTailX0RatChunk001Sub001Block037Part004
    + surrogateDiagTailX0RatChunk001Sub001Block037Part005
    + surrogateDiagTailX0RatChunk001Sub001Block037Part006
    + surrogateDiagTailX0RatChunk001Sub001Block037Part007
    + surrogateDiagTailX0RatChunk001Sub001Block037Part008
    + surrogateDiagTailX0RatChunk001Sub001Block037Part009
    + surrogateDiagTailX0RatChunk001Sub001Block037Part010
    + surrogateDiagTailX0RatChunk001Sub001Block037Part011
    + surrogateDiagTailX0RatChunk001Sub001Block037Part012
    + surrogateDiagTailX0RatChunk001Sub001Block037Part013
    + surrogateDiagTailX0RatChunk001Sub001Block037Part014
    + surrogateDiagTailX0RatChunk001Sub001Block037Part015
    + surrogateDiagTailX0RatChunk001Sub001Block037Part016
    + surrogateDiagTailX0RatChunk001Sub001Block037Part017
    + surrogateDiagTailX0RatChunk001Sub001Block037Part018
    + surrogateDiagTailX0RatChunk001Sub001Block037Part019
    + surrogateDiagTailX0RatChunk001Sub001Block037Part020
    + surrogateDiagTailX0RatChunk001Sub001Block037Part021
    + surrogateDiagTailX0RatChunk001Sub001Block037Part022
    + surrogateDiagTailX0RatChunk001Sub001Block037Part023
    + surrogateDiagTailX0RatChunk001Sub001Block037Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block037_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block037Head + surrogateDiagTailX0RatChunk001Sub001Block037Mid + surrogateDiagTailX0RatChunk001Sub001Block037Tail =
      surrogateDiagTailX0RatChunk001Sub001Block037 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block037Head surrogateDiagTailX0RatChunk001Sub001Block037Mid surrogateDiagTailX0RatChunk001Sub001Block037Tail surrogateDiagTailX0RatChunk001Sub001Block037
  ring

def SurrogateDiagonalTailChunk001Sub001Block037HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block037HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block037Head

def SurrogateDiagonalTailChunk001Sub001Block037MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block037MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block037Mid

def SurrogateDiagonalTailChunk001Sub001Block037TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block037TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block037Tail

theorem surrogateDiagonalTailChunk001Sub001Block037_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block037HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block037MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block037TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block037Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block037 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block037HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block037MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block037TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block037Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block037_eq_head_add_mid_add_tail

/-- Block 038 covers tail-support indices [15950,15975) and q from 26287 to 26327. -/

def TailChunk001Sub001Block038Part000SupportExplicit : Finset ℕ :=
  ([26287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part000 : ℚ :=
  (4479697561 : ℚ) / 45146786070999859200

def SurrogateDiagonalTailChunk001Sub001Block038Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26287
    = surrogateDiagTailX0RatChunk001Sub001Block038Part000

theorem surrogateDiagonalTailChunk001Sub001Block038Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part000] using hcert

def TailChunk001Sub001Block038Part001SupportExplicit : Finset ℕ :=
  ([26290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part001 : ℚ :=
  (39861546217 : ℚ) / 821551217804083200

def SurrogateDiagonalTailChunk001Sub001Block038Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26290
    = surrogateDiagTailX0RatChunk001Sub001Block038Part001

theorem surrogateDiagonalTailChunk001Sub001Block038Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part001] using hcert

def TailChunk001Sub001Block038Part002SupportExplicit : Finset ℕ :=
  ([26291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part002 : ℚ :=
  (2912471861 : ℚ) / 22158261246096000000

def SurrogateDiagonalTailChunk001Sub001Block038Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26291
    = surrogateDiagTailX0RatChunk001Sub001Block038Part002

theorem surrogateDiagonalTailChunk001Sub001Block038Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part002] using hcert

def TailChunk001Sub001Block038Part003SupportExplicit : Finset ℕ :=
  ([26293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block038Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26293
    = surrogateDiagTailX0RatChunk001Sub001Block038Part003

theorem surrogateDiagonalTailChunk001Sub001Block038Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part003] using hcert

def TailChunk001Sub001Block038Part004SupportExplicit : Finset ℕ :=
  ([26294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block038Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26294
    = surrogateDiagTailX0RatChunk001Sub001Block038Part004

theorem surrogateDiagonalTailChunk001Sub001Block038Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part004] using hcert

def TailChunk001Sub001Block038Part005SupportExplicit : Finset ℕ :=
  ([26295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part005 : ℚ :=
  (288448615375 : ℚ) / 24124772293061640192

def SurrogateDiagonalTailChunk001Sub001Block038Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26295
    = surrogateDiagTailX0RatChunk001Sub001Block038Part005

theorem surrogateDiagonalTailChunk001Sub001Block038Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part005] using hcert

def TailChunk001Sub001Block038Part006SupportExplicit : Finset ℕ :=
  ([26297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block038Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26297
    = surrogateDiagTailX0RatChunk001Sub001Block038Part006

theorem surrogateDiagonalTailChunk001Sub001Block038Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part006] using hcert

def TailChunk001Sub001Block038Part007SupportExplicit : Finset ℕ :=
  ([26301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part007 : ℚ :=
  (770511169 : ℚ) / 256991698753978368

def SurrogateDiagonalTailChunk001Sub001Block038Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26301
    = surrogateDiagTailX0RatChunk001Sub001Block038Part007

theorem surrogateDiagonalTailChunk001Sub001Block038Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part007] using hcert

def TailChunk001Sub001Block038Part008SupportExplicit : Finset ℕ :=
  ([26302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block038Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26302
    = surrogateDiagTailX0RatChunk001Sub001Block038Part008

theorem surrogateDiagonalTailChunk001Sub001Block038Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part008] using hcert

def TailChunk001Sub001Block038Part009SupportExplicit : Finset ℕ :=
  ([26303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part009 : ℚ :=
  (66259548025 : ℚ) / 258887918444530217472

def SurrogateDiagonalTailChunk001Sub001Block038Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26303
    = surrogateDiagTailX0RatChunk001Sub001Block038Part009

theorem surrogateDiagonalTailChunk001Sub001Block038Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part009] using hcert

def TailChunk001Sub001Block038Part010SupportExplicit : Finset ℕ :=
  ([26305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part010 : ℚ :=
  (125125 : ℚ) / 49001548094588928

def SurrogateDiagonalTailChunk001Sub001Block038Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26305
    = surrogateDiagTailX0RatChunk001Sub001Block038Part010

theorem surrogateDiagonalTailChunk001Sub001Block038Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part010] using hcert

def TailChunk001Sub001Block038Part011SupportExplicit : Finset ℕ :=
  ([26306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part011 : ℚ :=
  (221323554575 : ℚ) / 20155065621201543744

def SurrogateDiagonalTailChunk001Sub001Block038Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26306
    = surrogateDiagTailX0RatChunk001Sub001Block038Part011

theorem surrogateDiagonalTailChunk001Sub001Block038Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part011] using hcert

def TailChunk001Sub001Block038Part012SupportExplicit : Finset ℕ :=
  ([26309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block038Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26309
    = surrogateDiagTailX0RatChunk001Sub001Block038Part012

theorem surrogateDiagonalTailChunk001Sub001Block038Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part012] using hcert

def TailChunk001Sub001Block038Part013SupportExplicit : Finset ℕ :=
  ([26310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part013 : ℚ :=
  (1105736937325 : ℚ) / 6031193073265410048

def SurrogateDiagonalTailChunk001Sub001Block038Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26310
    = surrogateDiagTailX0RatChunk001Sub001Block038Part013

theorem surrogateDiagonalTailChunk001Sub001Block038Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part013] using hcert

def TailChunk001Sub001Block038Part014SupportExplicit : Finset ℕ :=
  ([26311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part014 : ℚ :=
  (62542490375 : ℚ) / 563638438710314640384

def SurrogateDiagonalTailChunk001Sub001Block038Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26311
    = surrogateDiagTailX0RatChunk001Sub001Block038Part014

theorem surrogateDiagonalTailChunk001Sub001Block038Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part014] using hcert

def TailChunk001Sub001Block038Part015SupportExplicit : Finset ℕ :=
  ([26314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part015 : ℚ :=
  (28552411175 : ℚ) / 22910231426703808896

def SurrogateDiagonalTailChunk001Sub001Block038Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26314
    = surrogateDiagTailX0RatChunk001Sub001Block038Part015

theorem surrogateDiagonalTailChunk001Sub001Block038Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part015] using hcert

def TailChunk001Sub001Block038Part016SupportExplicit : Finset ℕ :=
  ([26315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part016 : ℚ :=
  (322300128325 : ℚ) / 389935856817736777728

def SurrogateDiagonalTailChunk001Sub001Block038Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26315
    = surrogateDiagTailX0RatChunk001Sub001Block038Part016

theorem surrogateDiagonalTailChunk001Sub001Block038Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part016] using hcert

def TailChunk001Sub001Block038Part017SupportExplicit : Finset ℕ :=
  ([26317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part017 : ℚ :=
  (10821632640625 : ℚ) / 299810182280699810592

def SurrogateDiagonalTailChunk001Sub001Block038Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26317
    = surrogateDiagTailX0RatChunk001Sub001Block038Part017

theorem surrogateDiagonalTailChunk001Sub001Block038Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part017] using hcert

def TailChunk001Sub001Block038Part018SupportExplicit : Finset ℕ :=
  ([26318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part018 : ℚ :=
  (2705613765625 : ℚ) / 18738136392543738162

def SurrogateDiagonalTailChunk001Sub001Block038Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26318
    = surrogateDiagTailX0RatChunk001Sub001Block038Part018

theorem surrogateDiagonalTailChunk001Sub001Block038Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part018] using hcert

def TailChunk001Sub001Block038Part019SupportExplicit : Finset ℕ :=
  ([26319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part019 : ℚ :=
  (144562192769 : ℚ) / 1639525896110499840

def SurrogateDiagonalTailChunk001Sub001Block038Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26319
    = surrogateDiagTailX0RatChunk001Sub001Block038Part019

theorem surrogateDiagonalTailChunk001Sub001Block038Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part019] using hcert

def TailChunk001Sub001Block038Part020SupportExplicit : Finset ℕ :=
  ([26321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part020 : ℚ :=
  (17319876025 : ℚ) / 479988011164311552

def SurrogateDiagonalTailChunk001Sub001Block038Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26321
    = surrogateDiagTailX0RatChunk001Sub001Block038Part020

theorem surrogateDiagonalTailChunk001Sub001Block038Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part020] using hcert

def TailChunk001Sub001Block038Part021SupportExplicit : Finset ℕ :=
  ([26322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part021 : ℚ :=
  (76085468511 : ℚ) / 172404661642854400

def SurrogateDiagonalTailChunk001Sub001Block038Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26322
    = surrogateDiagTailX0RatChunk001Sub001Block038Part021

theorem surrogateDiagonalTailChunk001Sub001Block038Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part021] using hcert

def TailChunk001Sub001Block038Part022SupportExplicit : Finset ℕ :=
  ([26323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part022 : ℚ :=
  (121604820003 : ℚ) / 2728665534723481600

def SurrogateDiagonalTailChunk001Sub001Block038Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26323
    = surrogateDiagTailX0RatChunk001Sub001Block038Part022

theorem surrogateDiagonalTailChunk001Sub001Block038Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part022] using hcert

def TailChunk001Sub001Block038Part023SupportExplicit : Finset ℕ :=
  ([26326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part023 : ℚ :=
  (2707258890625 : ℚ) / 18760932176275235442

def SurrogateDiagonalTailChunk001Sub001Block038Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26326
    = surrogateDiagTailX0RatChunk001Sub001Block038Part023

theorem surrogateDiagonalTailChunk001Sub001Block038Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part023] using hcert

def TailChunk001Sub001Block038Part024SupportExplicit : Finset ℕ :=
  ([26327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block038Part024 : ℚ :=
  (261577515029 : ℚ) / 5181711474127011840

def SurrogateDiagonalTailChunk001Sub001Block038Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26327
    = surrogateDiagTailX0RatChunk001Sub001Block038Part024

theorem surrogateDiagonalTailChunk001Sub001Block038Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block038Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block038Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block038Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block038Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block038Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block038Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block038HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block038Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block038Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block038Part000
    + surrogateDiagTailX0RatChunk001Sub001Block038Part001
    + surrogateDiagTailX0RatChunk001Sub001Block038Part002
    + surrogateDiagTailX0RatChunk001Sub001Block038Part003
    + surrogateDiagTailX0RatChunk001Sub001Block038Part004
    + surrogateDiagTailX0RatChunk001Sub001Block038Part005
    + surrogateDiagTailX0RatChunk001Sub001Block038Part006
    + surrogateDiagTailX0RatChunk001Sub001Block038Part007
    + surrogateDiagTailX0RatChunk001Sub001Block038Part008
    + surrogateDiagTailX0RatChunk001Sub001Block038Part009

def surrogateDiagonalTailChunk001Sub001Block038MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block038Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block038Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block038Part010
    + surrogateDiagTailX0RatChunk001Sub001Block038Part011
    + surrogateDiagTailX0RatChunk001Sub001Block038Part012
    + surrogateDiagTailX0RatChunk001Sub001Block038Part013
    + surrogateDiagTailX0RatChunk001Sub001Block038Part014
    + surrogateDiagTailX0RatChunk001Sub001Block038Part015
    + surrogateDiagTailX0RatChunk001Sub001Block038Part016
    + surrogateDiagTailX0RatChunk001Sub001Block038Part017
    + surrogateDiagTailX0RatChunk001Sub001Block038Part018
    + surrogateDiagTailX0RatChunk001Sub001Block038Part019

def surrogateDiagonalTailChunk001Sub001Block038TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block038Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block038Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block038Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block038Part020
    + surrogateDiagTailX0RatChunk001Sub001Block038Part021
    + surrogateDiagTailX0RatChunk001Sub001Block038Part022
    + surrogateDiagTailX0RatChunk001Sub001Block038Part023
    + surrogateDiagTailX0RatChunk001Sub001Block038Part024

def surrogateDiagonalTailChunk001Sub001Block038Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block038HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block038MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block038TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block038 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block038Part000
    + surrogateDiagTailX0RatChunk001Sub001Block038Part001
    + surrogateDiagTailX0RatChunk001Sub001Block038Part002
    + surrogateDiagTailX0RatChunk001Sub001Block038Part003
    + surrogateDiagTailX0RatChunk001Sub001Block038Part004
    + surrogateDiagTailX0RatChunk001Sub001Block038Part005
    + surrogateDiagTailX0RatChunk001Sub001Block038Part006
    + surrogateDiagTailX0RatChunk001Sub001Block038Part007
    + surrogateDiagTailX0RatChunk001Sub001Block038Part008
    + surrogateDiagTailX0RatChunk001Sub001Block038Part009
    + surrogateDiagTailX0RatChunk001Sub001Block038Part010
    + surrogateDiagTailX0RatChunk001Sub001Block038Part011
    + surrogateDiagTailX0RatChunk001Sub001Block038Part012
    + surrogateDiagTailX0RatChunk001Sub001Block038Part013
    + surrogateDiagTailX0RatChunk001Sub001Block038Part014
    + surrogateDiagTailX0RatChunk001Sub001Block038Part015
    + surrogateDiagTailX0RatChunk001Sub001Block038Part016
    + surrogateDiagTailX0RatChunk001Sub001Block038Part017
    + surrogateDiagTailX0RatChunk001Sub001Block038Part018
    + surrogateDiagTailX0RatChunk001Sub001Block038Part019
    + surrogateDiagTailX0RatChunk001Sub001Block038Part020
    + surrogateDiagTailX0RatChunk001Sub001Block038Part021
    + surrogateDiagTailX0RatChunk001Sub001Block038Part022
    + surrogateDiagTailX0RatChunk001Sub001Block038Part023
    + surrogateDiagTailX0RatChunk001Sub001Block038Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block038_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block038Head + surrogateDiagTailX0RatChunk001Sub001Block038Mid + surrogateDiagTailX0RatChunk001Sub001Block038Tail =
      surrogateDiagTailX0RatChunk001Sub001Block038 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block038Head surrogateDiagTailX0RatChunk001Sub001Block038Mid surrogateDiagTailX0RatChunk001Sub001Block038Tail surrogateDiagTailX0RatChunk001Sub001Block038
  ring

def SurrogateDiagonalTailChunk001Sub001Block038HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block038HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block038Head

def SurrogateDiagonalTailChunk001Sub001Block038MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block038MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block038Mid

def SurrogateDiagonalTailChunk001Sub001Block038TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block038TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block038Tail

theorem surrogateDiagonalTailChunk001Sub001Block038_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block038HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block038MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block038TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block038Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block038 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block038HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block038MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block038TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block038Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block038_eq_head_add_mid_add_tail

/-- Block 039 covers tail-support indices [15975,16000) and q from 26329 to 26369. -/

def TailChunk001Sub001Block039Part000SupportExplicit : Finset ℕ :=
  ([26329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part000 : ℚ :=
  (6043764282625 : ℚ) / 162836908694594125824

def SurrogateDiagonalTailChunk001Sub001Block039Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26329
    = surrogateDiagTailX0RatChunk001Sub001Block039Part000

theorem surrogateDiagonalTailChunk001Sub001Block039Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part000] using hcert

def TailChunk001Sub001Block039Part001SupportExplicit : Finset ℕ :=
  ([26330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part001 : ℚ :=
  (7362331127275 : ℚ) / 30719232714515939328

def SurrogateDiagonalTailChunk001Sub001Block039Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26330
    = surrogateDiagTailX0RatChunk001Sub001Block039Part001

theorem surrogateDiagonalTailChunk001Sub001Block039Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part001] using hcert

def TailChunk001Sub001Block039Part002SupportExplicit : Finset ℕ :=
  ([26331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part002 : ℚ :=
  (740725337251 : ℚ) / 8672733158127667200

def SurrogateDiagonalTailChunk001Sub001Block039Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26331
    = surrogateDiagTailX0RatChunk001Sub001Block039Part002

theorem surrogateDiagonalTailChunk001Sub001Block039Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part002] using hcert

def TailChunk001Sub001Block039Part003SupportExplicit : Finset ℕ :=
  ([26333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part003 : ℚ :=
  (151554069475 : ℚ) / 3675789641592373248

def SurrogateDiagonalTailChunk001Sub001Block039Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26333
    = surrogateDiagTailX0RatChunk001Sub001Block039Part003

theorem surrogateDiagonalTailChunk001Sub001Block039Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part003] using hcert

def TailChunk001Sub001Block039Part004SupportExplicit : Finset ℕ :=
  ([26335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part004 : ℚ :=
  (8483530753025 : ℚ) / 135075219132145729536

def SurrogateDiagonalTailChunk001Sub001Block039Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26335
    = surrogateDiagTailX0RatChunk001Sub001Block039Part004

theorem surrogateDiagonalTailChunk001Sub001Block039Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part004] using hcert

def TailChunk001Sub001Block039Part005SupportExplicit : Finset ℕ :=
  ([26337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part005 : ℚ :=
  (1751267738375 : ℚ) / 21594167334180701568

def SurrogateDiagonalTailChunk001Sub001Block039Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26337
    = surrogateDiagTailX0RatChunk001Sub001Block039Part005

theorem surrogateDiagonalTailChunk001Sub001Block039Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part005] using hcert

def TailChunk001Sub001Block039Part006SupportExplicit : Finset ℕ :=
  ([26338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part006 : ℚ :=
  (1579691923375 : ℚ) / 9064057307810807808

def SurrogateDiagonalTailChunk001Sub001Block039Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26338
    = surrogateDiagTailX0RatChunk001Sub001Block039Part006

theorem surrogateDiagonalTailChunk001Sub001Block039Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part006] using hcert

def TailChunk001Sub001Block039Part007SupportExplicit : Finset ℕ :=
  ([26339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part007 : ℚ :=
  (10839733140625 : ℚ) / 300813997407314807442

def SurrogateDiagonalTailChunk001Sub001Block039Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26339
    = surrogateDiagTailX0RatChunk001Sub001Block039Part007

theorem surrogateDiagonalTailChunk001Sub001Block039Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part007] using hcert

def TailChunk001Sub001Block039Part008SupportExplicit : Finset ℕ :=
  ([26341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part008 : ℚ :=
  (1234129631653 : ℚ) / 22756076565988147200

def SurrogateDiagonalTailChunk001Sub001Block039Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26341
    = surrogateDiagTailX0RatChunk001Sub001Block039Part008

theorem surrogateDiagonalTailChunk001Sub001Block039Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part008] using hcert

def TailChunk001Sub001Block039Part009SupportExplicit : Finset ℕ :=
  ([26342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part009 : ℚ :=
  (4336881025 : ℚ) / 30090537815392242

def SurrogateDiagonalTailChunk001Sub001Block039Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26342
    = surrogateDiagTailX0RatChunk001Sub001Block039Part009

theorem surrogateDiagonalTailChunk001Sub001Block039Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part009] using hcert

def TailChunk001Sub001Block039Part010SupportExplicit : Finset ℕ :=
  ([26345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part010 : ℚ :=
  (185733204959 : ℚ) / 2673427417274941440

def SurrogateDiagonalTailChunk001Sub001Block039Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26345
    = surrogateDiagTailX0RatChunk001Sub001Block039Part010

theorem surrogateDiagonalTailChunk001Sub001Block039Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part010] using hcert

def TailChunk001Sub001Block039Part011SupportExplicit : Finset ℕ :=
  ([26346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part011 : ℚ :=
  (60241196827 : ℚ) / 148595248471072800

def SurrogateDiagonalTailChunk001Sub001Block039Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26346
    = surrogateDiagTailX0RatChunk001Sub001Block039Part011

theorem surrogateDiagonalTailChunk001Sub001Block039Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part011] using hcert

def TailChunk001Sub001Block039Part012SupportExplicit : Finset ℕ :=
  ([26347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part012 : ℚ :=
  (10846318890625 : ℚ) / 301179645314576468082

def SurrogateDiagonalTailChunk001Sub001Block039Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26347
    = surrogateDiagTailX0RatChunk001Sub001Block039Part012

theorem surrogateDiagonalTailChunk001Sub001Block039Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part012] using hcert

def TailChunk001Sub001Block039Part013SupportExplicit : Finset ℕ :=
  ([26349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part013 : ℚ :=
  (19281505121725 : ℚ) / 237969102470776468608

def SurrogateDiagonalTailChunk001Sub001Block039Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26349
    = surrogateDiagTailX0RatChunk001Sub001Block039Part013

theorem surrogateDiagonalTailChunk001Sub001Block039Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part013] using hcert

def TailChunk001Sub001Block039Part014SupportExplicit : Finset ℕ :=
  ([26351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part014 : ℚ :=
  (37461270773125 : ℚ) / 873593928817349511168

def SurrogateDiagonalTailChunk001Sub001Block039Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26351
    = surrogateDiagTailX0RatChunk001Sub001Block039Part014

theorem surrogateDiagonalTailChunk001Sub001Block039Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part014] using hcert

def TailChunk001Sub001Block039Part015SupportExplicit : Finset ℕ :=
  ([26354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part015 : ℚ :=
  (2713020765625 : ℚ) / 18840881245179843072

def SurrogateDiagonalTailChunk001Sub001Block039Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26354
    = surrogateDiagTailX0RatChunk001Sub001Block039Part015

theorem surrogateDiagonalTailChunk001Sub001Block039Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part015] using hcert

def TailChunk001Sub001Block039Part016SupportExplicit : Finset ℕ :=
  ([26355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part016 : ℚ :=
  (195360406241 : ℚ) / 1037007360000000000

def SurrogateDiagonalTailChunk001Sub001Block039Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26355
    = surrogateDiagTailX0RatChunk001Sub001Block039Part016

theorem surrogateDiagonalTailChunk001Sub001Block039Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part016] using hcert

def TailChunk001Sub001Block039Part017SupportExplicit : Finset ℕ :=
  ([26357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part017 : ℚ :=
  (10854553890625 : ℚ) / 301637173841492519712

def SurrogateDiagonalTailChunk001Sub001Block039Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26357
    = surrogateDiagTailX0RatChunk001Sub001Block039Part017

theorem surrogateDiagonalTailChunk001Sub001Block039Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part017] using hcert

def TailChunk001Sub001Block039Part018SupportExplicit : Finset ℕ :=
  ([26358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part018 : ℚ :=
  (89843971433 : ℚ) / 244276654969881600

def SurrogateDiagonalTailChunk001Sub001Block039Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26358
    = surrogateDiagTailX0RatChunk001Sub001Block039Part018

theorem surrogateDiagonalTailChunk001Sub001Block039Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part018] using hcert

def TailChunk001Sub001Block039Part019SupportExplicit : Finset ℕ :=
  ([26359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part019 : ℚ :=
  (20736494508125 : ℚ) / 545757500926274724864

def SurrogateDiagonalTailChunk001Sub001Block039Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26359
    = surrogateDiagTailX0RatChunk001Sub001Block039Part019

theorem surrogateDiagonalTailChunk001Sub001Block039Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part019] using hcert

def TailChunk001Sub001Block039Part020SupportExplicit : Finset ℕ :=
  ([26363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part020 : ℚ :=
  (1617647677 : ℚ) / 42478284682144800

def SurrogateDiagonalTailChunk001Sub001Block039Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26363
    = surrogateDiagTailX0RatChunk001Sub001Block039Part020

theorem surrogateDiagonalTailChunk001Sub001Block039Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part020] using hcert

def TailChunk001Sub001Block039Part021SupportExplicit : Finset ℕ :=
  ([26365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part021 : ℚ :=
  (1737202140625 : ℚ) / 30906401908062978048

def SurrogateDiagonalTailChunk001Sub001Block039Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26365
    = surrogateDiagTailX0RatChunk001Sub001Block039Part021

theorem surrogateDiagonalTailChunk001Sub001Block039Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part021] using hcert

def TailChunk001Sub001Block039Part022SupportExplicit : Finset ℕ :=
  ([26366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part022 : ℚ :=
  (2715492015625 : ℚ) / 18875223238999451922

def SurrogateDiagonalTailChunk001Sub001Block039Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26366
    = surrogateDiagTailX0RatChunk001Sub001Block039Part022

theorem surrogateDiagonalTailChunk001Sub001Block039Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part022] using hcert

def TailChunk001Sub001Block039Part023SupportExplicit : Finset ℕ :=
  ([26367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part023 : ℚ :=
  (2829881063 : ℚ) / 23479459466182656

def SurrogateDiagonalTailChunk001Sub001Block039Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26367
    = surrogateDiagTailX0RatChunk001Sub001Block039Part023

theorem surrogateDiagonalTailChunk001Sub001Block039Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part023] using hcert

def TailChunk001Sub001Block039Part024SupportExplicit : Finset ℕ :=
  ([26369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block039Part024 : ℚ :=
  (32801619396025 : ℚ) / 651858185095842227328

def SurrogateDiagonalTailChunk001Sub001Block039Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26369
    = surrogateDiagTailX0RatChunk001Sub001Block039Part024

theorem surrogateDiagonalTailChunk001Sub001Block039Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block039Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block039Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block039Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block039Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block039Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block039Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block039HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block039Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block039Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block039Part000
    + surrogateDiagTailX0RatChunk001Sub001Block039Part001
    + surrogateDiagTailX0RatChunk001Sub001Block039Part002
    + surrogateDiagTailX0RatChunk001Sub001Block039Part003
    + surrogateDiagTailX0RatChunk001Sub001Block039Part004
    + surrogateDiagTailX0RatChunk001Sub001Block039Part005
    + surrogateDiagTailX0RatChunk001Sub001Block039Part006
    + surrogateDiagTailX0RatChunk001Sub001Block039Part007
    + surrogateDiagTailX0RatChunk001Sub001Block039Part008
    + surrogateDiagTailX0RatChunk001Sub001Block039Part009

def surrogateDiagonalTailChunk001Sub001Block039MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block039Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block039Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block039Part010
    + surrogateDiagTailX0RatChunk001Sub001Block039Part011
    + surrogateDiagTailX0RatChunk001Sub001Block039Part012
    + surrogateDiagTailX0RatChunk001Sub001Block039Part013
    + surrogateDiagTailX0RatChunk001Sub001Block039Part014
    + surrogateDiagTailX0RatChunk001Sub001Block039Part015
    + surrogateDiagTailX0RatChunk001Sub001Block039Part016
    + surrogateDiagTailX0RatChunk001Sub001Block039Part017
    + surrogateDiagTailX0RatChunk001Sub001Block039Part018
    + surrogateDiagTailX0RatChunk001Sub001Block039Part019

def surrogateDiagonalTailChunk001Sub001Block039TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block039Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block039Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block039Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block039Part020
    + surrogateDiagTailX0RatChunk001Sub001Block039Part021
    + surrogateDiagTailX0RatChunk001Sub001Block039Part022
    + surrogateDiagTailX0RatChunk001Sub001Block039Part023
    + surrogateDiagTailX0RatChunk001Sub001Block039Part024

def surrogateDiagonalTailChunk001Sub001Block039Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block039HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block039MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block039TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block039 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block039Part000
    + surrogateDiagTailX0RatChunk001Sub001Block039Part001
    + surrogateDiagTailX0RatChunk001Sub001Block039Part002
    + surrogateDiagTailX0RatChunk001Sub001Block039Part003
    + surrogateDiagTailX0RatChunk001Sub001Block039Part004
    + surrogateDiagTailX0RatChunk001Sub001Block039Part005
    + surrogateDiagTailX0RatChunk001Sub001Block039Part006
    + surrogateDiagTailX0RatChunk001Sub001Block039Part007
    + surrogateDiagTailX0RatChunk001Sub001Block039Part008
    + surrogateDiagTailX0RatChunk001Sub001Block039Part009
    + surrogateDiagTailX0RatChunk001Sub001Block039Part010
    + surrogateDiagTailX0RatChunk001Sub001Block039Part011
    + surrogateDiagTailX0RatChunk001Sub001Block039Part012
    + surrogateDiagTailX0RatChunk001Sub001Block039Part013
    + surrogateDiagTailX0RatChunk001Sub001Block039Part014
    + surrogateDiagTailX0RatChunk001Sub001Block039Part015
    + surrogateDiagTailX0RatChunk001Sub001Block039Part016
    + surrogateDiagTailX0RatChunk001Sub001Block039Part017
    + surrogateDiagTailX0RatChunk001Sub001Block039Part018
    + surrogateDiagTailX0RatChunk001Sub001Block039Part019
    + surrogateDiagTailX0RatChunk001Sub001Block039Part020
    + surrogateDiagTailX0RatChunk001Sub001Block039Part021
    + surrogateDiagTailX0RatChunk001Sub001Block039Part022
    + surrogateDiagTailX0RatChunk001Sub001Block039Part023
    + surrogateDiagTailX0RatChunk001Sub001Block039Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block039_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block039Head + surrogateDiagTailX0RatChunk001Sub001Block039Mid + surrogateDiagTailX0RatChunk001Sub001Block039Tail =
      surrogateDiagTailX0RatChunk001Sub001Block039 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block039Head surrogateDiagTailX0RatChunk001Sub001Block039Mid surrogateDiagTailX0RatChunk001Sub001Block039Tail surrogateDiagTailX0RatChunk001Sub001Block039
  ring

def SurrogateDiagonalTailChunk001Sub001Block039HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block039HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block039Head

def SurrogateDiagonalTailChunk001Sub001Block039MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block039MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block039Mid

def SurrogateDiagonalTailChunk001Sub001Block039TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block039TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block039Tail

theorem surrogateDiagonalTailChunk001Sub001Block039_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block039HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block039MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block039TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block039Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block039 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block039HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block039MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block039TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block039Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block039_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
