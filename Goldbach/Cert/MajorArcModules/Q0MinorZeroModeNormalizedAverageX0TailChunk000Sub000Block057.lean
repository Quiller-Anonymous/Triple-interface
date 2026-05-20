import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [57,58). -/

/- Block 057 covers tail-support indices [1425,1450) and q from 2395 to 2434. -/

def TailChunk000Sub000Block057Part000SupportExplicit : Finset ℕ :=
  ([2395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part000 : ℚ :=
  (195617706375 : ℚ) / 11139280905312256

def SurrogateDiagonalTailChunk000Sub000Block057Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2395
    = surrogateDiagTailX0RatChunk000Sub000Block057Part000

theorem surrogateDiagonalTailChunk000Sub000Block057Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part000] using hcert

def TailChunk000Sub000Block057Part001SupportExplicit : Finset ℕ :=
  ([2397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part001 : ℚ :=
  (119044412275 : ℚ) / 2934932433272832

def SurrogateDiagonalTailChunk000Sub000Block057Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2397
    = surrogateDiagTailX0RatChunk000Sub000Block057Part001

theorem surrogateDiagonalTailChunk000Sub000Block057Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part001] using hcert

def TailChunk000Sub000Block057Part002SupportExplicit : Finset ℕ :=
  ([2398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part002 : ℚ :=
  (33894031 : ℚ) / 354364858800

def SurrogateDiagonalTailChunk000Sub000Block057Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2398
    = surrogateDiagTailX0RatChunk000Sub000Block057Part002

theorem surrogateDiagonalTailChunk000Sub000Block057Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part002] using hcert

def TailChunk000Sub000Block057Part003SupportExplicit : Finset ℕ :=
  ([2399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part003 : ℚ :=
  (719256244975 : ℚ) / 82684398981121608

def SurrogateDiagonalTailChunk000Sub000Block057Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2399
    = surrogateDiagTailX0RatChunk000Sub000Block057Part003

theorem surrogateDiagonalTailChunk000Sub000Block057Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part003] using hcert

def TailChunk000Sub000Block057Part004SupportExplicit : Finset ℕ :=
  ([2402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part004 : ℚ :=
  (7207677797 : ℚ) / 103700736000000

def SurrogateDiagonalTailChunk000Sub000Block057Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2402
    = surrogateDiagTailX0RatChunk000Sub000Block057Part004

theorem surrogateDiagonalTailChunk000Sub000Block057Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part004] using hcert

def TailChunk000Sub000Block057Part005SupportExplicit : Finset ℕ :=
  ([2405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part005 : ℚ :=
  (130446959125 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk000Sub000Block057Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2405
    = surrogateDiagTailX0RatChunk000Sub000Block057Part005

theorem surrogateDiagonalTailChunk000Sub000Block057Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part005] using hcert

def TailChunk000Sub000Block057Part006SupportExplicit : Finset ℕ :=
  ([2406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part006 : ℚ :=
  (626679193 : ℚ) / 2560512000000

def SurrogateDiagonalTailChunk000Sub000Block057Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2406
    = surrogateDiagTailX0RatChunk000Sub000Block057Part006

theorem surrogateDiagonalTailChunk000Sub000Block057Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part006] using hcert

def TailChunk000Sub000Block057Part007SupportExplicit : Finset ℕ :=
  ([2407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part007 : ℚ :=
  (32956799325 : ℚ) / 3308987290298368

def SurrogateDiagonalTailChunk000Sub000Block057Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2407
    = surrogateDiagTailX0RatChunk000Sub000Block057Part007

theorem surrogateDiagonalTailChunk000Sub000Block057Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part007] using hcert

def TailChunk000Sub000Block057Part008SupportExplicit : Finset ℕ :=
  ([2409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part008 : ℚ :=
  (2897293241 : ℚ) / 71677948723200

def SurrogateDiagonalTailChunk000Sub000Block057Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2409
    = surrogateDiagTailX0RatChunk000Sub000Block057Part008

theorem surrogateDiagonalTailChunk000Sub000Block057Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part008] using hcert

def TailChunk000Sub000Block057Part009SupportExplicit : Finset ℕ :=
  ([2410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part009 : ℚ :=
  (38544761 : ℚ) / 235976785920

def SurrogateDiagonalTailChunk000Sub000Block057Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2410
    = surrogateDiagTailX0RatChunk000Sub000Block057Part009

theorem surrogateDiagonalTailChunk000Sub000Block057Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part009] using hcert

def TailChunk000Sub000Block057Part010SupportExplicit : Finset ℕ :=
  ([2411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part010 : ℚ :=
  (29058792079 : ℚ) / 3374077241512200

def SurrogateDiagonalTailChunk000Sub000Block057Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2411
    = surrogateDiagTailX0RatChunk000Sub000Block057Part010

theorem surrogateDiagonalTailChunk000Sub000Block057Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part010] using hcert

def TailChunk000Sub000Block057Part011SupportExplicit : Finset ℕ :=
  ([2413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part011 : ℚ :=
  (38078176525 : ℚ) / 3675585712228416

def SurrogateDiagonalTailChunk000Sub000Block057Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2413
    = surrogateDiagTailX0RatChunk000Sub000Block057Part011

theorem surrogateDiagonalTailChunk000Sub000Block057Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part011] using hcert

def TailChunk000Sub000Block057Part012SupportExplicit : Finset ℕ :=
  ([2414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part012 : ℚ :=
  (96802877 : ℚ) / 1124167188480

def SurrogateDiagonalTailChunk000Sub000Block057Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2414
    = surrogateDiagTailX0RatChunk000Sub000Block057Part012

theorem surrogateDiagonalTailChunk000Sub000Block057Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part012] using hcert

def TailChunk000Sub000Block057Part013SupportExplicit : Finset ℕ :=
  ([2415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part013 : ℚ :=
  (321748720525 : ℚ) / 3109442510389248

def SurrogateDiagonalTailChunk000Sub000Block057Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2415
    = surrogateDiagTailX0RatChunk000Sub000Block057Part013

theorem surrogateDiagonalTailChunk000Sub000Block057Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part013] using hcert

def TailChunk000Sub000Block057Part014SupportExplicit : Finset ℕ :=
  ([2417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part014 : ℚ :=
  (730090077775 : ℚ) / 85195092479213568

def SurrogateDiagonalTailChunk000Sub000Block057Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2417
    = surrogateDiagTailX0RatChunk000Sub000Block057Part014

theorem surrogateDiagonalTailChunk000Sub000Block057Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part014] using hcert

def TailChunk000Sub000Block057Part015SupportExplicit : Finset ℕ :=
  ([2418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part015 : ℚ :=
  (1812480203 : ℚ) / 5375846154240

def SurrogateDiagonalTailChunk000Sub000Block057Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2418
    = surrogateDiagTailX0RatChunk000Sub000Block057Part015

theorem surrogateDiagonalTailChunk000Sub000Block057Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part015] using hcert

def TailChunk000Sub000Block057Part016SupportExplicit : Finset ℕ :=
  ([2419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part016 : ℚ :=
  (14053812281 : ℚ) / 1448801190297600

def SurrogateDiagonalTailChunk000Sub000Block057Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2419
    = surrogateDiagTailX0RatChunk000Sub000Block057Part016

theorem surrogateDiagonalTailChunk000Sub000Block057Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part016] using hcert

def TailChunk000Sub000Block057Part017SupportExplicit : Finset ℕ :=
  ([2422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part017 : ℚ :=
  (42124439225 : ℚ) / 315139715500032

def SurrogateDiagonalTailChunk000Sub000Block057Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2422
    = surrogateDiagTailX0RatChunk000Sub000Block057Part017

theorem surrogateDiagonalTailChunk000Sub000Block057Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part017] using hcert

def TailChunk000Sub000Block057Part018SupportExplicit : Finset ℕ :=
  ([2423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part018 : ℚ :=
  (733719351775 : ℚ) / 86044559208387528

def SurrogateDiagonalTailChunk000Sub000Block057Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2423
    = surrogateDiagTailX0RatChunk000Sub000Block057Part018

theorem surrogateDiagonalTailChunk000Sub000Block057Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part018] using hcert

def TailChunk000Sub000Block057Part019SupportExplicit : Finset ℕ :=
  ([2426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part019 : ℚ :=
  (183810772325 : ℚ) / 2697785043038784

def SurrogateDiagonalTailChunk000Sub000Block057Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2426
    = surrogateDiagTailX0RatChunk000Sub000Block057Part019

theorem surrogateDiagonalTailChunk000Sub000Block057Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part019] using hcert

def TailChunk000Sub000Block057Part020SupportExplicit : Finset ℕ :=
  ([2427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part020 : ℚ :=
  (98054475 : ℚ) / 3409851219968

def SurrogateDiagonalTailChunk000Sub000Block057Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2427
    = surrogateDiagTailX0RatChunk000Sub000Block057Part020

theorem surrogateDiagonalTailChunk000Sub000Block057Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part020] using hcert

def TailChunk000Sub000Block057Part021SupportExplicit : Finset ℕ :=
  ([2429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part021 : ℚ :=
  (637986467875 : ℚ) / 46444710010025088

def SurrogateDiagonalTailChunk000Sub000Block057Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2429
    = surrogateDiagTailX0RatChunk000Sub000Block057Part021

theorem surrogateDiagonalTailChunk000Sub000Block057Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part021] using hcert

def TailChunk000Sub000Block057Part022SupportExplicit : Finset ℕ :=
  ([2431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part022 : ℚ :=
  (23544537061 : ℚ) / 1359226286899200

def SurrogateDiagonalTailChunk000Sub000Block057Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2431
    = surrogateDiagTailX0RatChunk000Sub000Block057Part022

theorem surrogateDiagonalTailChunk000Sub000Block057Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part022] using hcert

def TailChunk000Sub000Block057Part023SupportExplicit : Finset ℕ :=
  ([2433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part023 : ℚ :=
  (29197 : ℚ) / 1020366720

def SurrogateDiagonalTailChunk000Sub000Block057Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2433
    = surrogateDiagTailX0RatChunk000Sub000Block057Part023

theorem surrogateDiagonalTailChunk000Sub000Block057Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part023] using hcert

def TailChunk000Sub000Block057Part024SupportExplicit : Finset ℕ :=
  ([2434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block057Part024 : ℚ :=
  (9738160175 : ℚ) / 143872424411136

def SurrogateDiagonalTailChunk000Sub000Block057Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2434
    = surrogateDiagTailX0RatChunk000Sub000Block057Part024

theorem surrogateDiagonalTailChunk000Sub000Block057Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block057Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block057Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block057Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block057Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block057Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block057Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block057HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block057Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block057Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block057Part000
    + surrogateDiagTailX0RatChunk000Sub000Block057Part001
    + surrogateDiagTailX0RatChunk000Sub000Block057Part002
    + surrogateDiagTailX0RatChunk000Sub000Block057Part003
    + surrogateDiagTailX0RatChunk000Sub000Block057Part004
    + surrogateDiagTailX0RatChunk000Sub000Block057Part005
    + surrogateDiagTailX0RatChunk000Sub000Block057Part006
    + surrogateDiagTailX0RatChunk000Sub000Block057Part007
    + surrogateDiagTailX0RatChunk000Sub000Block057Part008
    + surrogateDiagTailX0RatChunk000Sub000Block057Part009

def surrogateDiagonalTailChunk000Sub000Block057MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block057Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block057Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block057Part010
    + surrogateDiagTailX0RatChunk000Sub000Block057Part011
    + surrogateDiagTailX0RatChunk000Sub000Block057Part012
    + surrogateDiagTailX0RatChunk000Sub000Block057Part013
    + surrogateDiagTailX0RatChunk000Sub000Block057Part014
    + surrogateDiagTailX0RatChunk000Sub000Block057Part015
    + surrogateDiagTailX0RatChunk000Sub000Block057Part016
    + surrogateDiagTailX0RatChunk000Sub000Block057Part017
    + surrogateDiagTailX0RatChunk000Sub000Block057Part018
    + surrogateDiagTailX0RatChunk000Sub000Block057Part019

def surrogateDiagonalTailChunk000Sub000Block057TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block057Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block057Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block057Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block057Part020
    + surrogateDiagTailX0RatChunk000Sub000Block057Part021
    + surrogateDiagTailX0RatChunk000Sub000Block057Part022
    + surrogateDiagTailX0RatChunk000Sub000Block057Part023
    + surrogateDiagTailX0RatChunk000Sub000Block057Part024

def surrogateDiagonalTailChunk000Sub000Block057Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block057HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block057MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block057TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block057 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block057Part000
    + surrogateDiagTailX0RatChunk000Sub000Block057Part001
    + surrogateDiagTailX0RatChunk000Sub000Block057Part002
    + surrogateDiagTailX0RatChunk000Sub000Block057Part003
    + surrogateDiagTailX0RatChunk000Sub000Block057Part004
    + surrogateDiagTailX0RatChunk000Sub000Block057Part005
    + surrogateDiagTailX0RatChunk000Sub000Block057Part006
    + surrogateDiagTailX0RatChunk000Sub000Block057Part007
    + surrogateDiagTailX0RatChunk000Sub000Block057Part008
    + surrogateDiagTailX0RatChunk000Sub000Block057Part009
    + surrogateDiagTailX0RatChunk000Sub000Block057Part010
    + surrogateDiagTailX0RatChunk000Sub000Block057Part011
    + surrogateDiagTailX0RatChunk000Sub000Block057Part012
    + surrogateDiagTailX0RatChunk000Sub000Block057Part013
    + surrogateDiagTailX0RatChunk000Sub000Block057Part014
    + surrogateDiagTailX0RatChunk000Sub000Block057Part015
    + surrogateDiagTailX0RatChunk000Sub000Block057Part016
    + surrogateDiagTailX0RatChunk000Sub000Block057Part017
    + surrogateDiagTailX0RatChunk000Sub000Block057Part018
    + surrogateDiagTailX0RatChunk000Sub000Block057Part019
    + surrogateDiagTailX0RatChunk000Sub000Block057Part020
    + surrogateDiagTailX0RatChunk000Sub000Block057Part021
    + surrogateDiagTailX0RatChunk000Sub000Block057Part022
    + surrogateDiagTailX0RatChunk000Sub000Block057Part023
    + surrogateDiagTailX0RatChunk000Sub000Block057Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block057_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block057Head + surrogateDiagTailX0RatChunk000Sub000Block057Mid + surrogateDiagTailX0RatChunk000Sub000Block057Tail =
      surrogateDiagTailX0RatChunk000Sub000Block057 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block057Head surrogateDiagTailX0RatChunk000Sub000Block057Mid surrogateDiagTailX0RatChunk000Sub000Block057Tail surrogateDiagTailX0RatChunk000Sub000Block057
  ring

def SurrogateDiagonalTailChunk000Sub000Block057HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block057HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block057Head

def SurrogateDiagonalTailChunk000Sub000Block057MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block057MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block057Mid

def SurrogateDiagonalTailChunk000Sub000Block057TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block057TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block057Tail

theorem surrogateDiagonalTailChunk000Sub000Block057_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block057HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block057MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block057TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block057Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block057 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block057HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block057MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block057TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block057Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block057_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
