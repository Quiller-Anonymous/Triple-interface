import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [92,93). -/

/- Block 092 covers tail-support indices [2300,2325) and q from 3835 to 3874. -/

def TailChunk000Sub000Block092Part000SupportExplicit : Finset ℕ :=
  ([3835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part000 : ℚ :=
  (249282886475 : ℚ) / 50070569136685056

def SurrogateDiagonalTailChunk000Sub000Block092Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3835
    = surrogateDiagTailX0RatChunk000Sub000Block092Part000

theorem surrogateDiagonalTailChunk000Sub000Block092Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part000] using hcert

def TailChunk000Sub000Block092Part001SupportExplicit : Finset ℕ :=
  ([3837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part001 : ℚ :=
  (10074775025 : ℚ) / 1503183181961088

def SurrogateDiagonalTailChunk000Sub000Block092Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3837
    = surrogateDiagTailX0RatChunk000Sub000Block092Part001

theorem surrogateDiagonalTailChunk000Sub000Block092Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part001] using hcert

def TailChunk000Sub000Block092Part002SupportExplicit : Finset ℕ :=
  ([3838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part002 : ℚ :=
  (1713480947 : ℚ) / 69997996800000

def SurrogateDiagonalTailChunk000Sub000Block092Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3838
    = surrogateDiagTailX0RatChunk000Sub000Block092Part002

theorem surrogateDiagonalTailChunk000Sub000Block092Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part002] using hcert

def TailChunk000Sub000Block092Part003SupportExplicit : Finset ℕ :=
  ([3839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part003 : ℚ :=
  (17171513771 : ℚ) / 7334556025881600

def SurrogateDiagonalTailChunk000Sub000Block092Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3839
    = surrogateDiagTailX0RatChunk000Sub000Block092Part003

theorem surrogateDiagonalTailChunk000Sub000Block092Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part003] using hcert

def TailChunk000Sub000Block092Part004SupportExplicit : Finset ℕ :=
  ([3841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part004 : ℚ :=
  (40399485175 : ℚ) / 20217490769936064

def SurrogateDiagonalTailChunk000Sub000Block092Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3841
    = surrogateDiagTailX0RatChunk000Sub000Block092Part004

theorem surrogateDiagonalTailChunk000Sub000Block092Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part004] using hcert

def TailChunk000Sub000Block092Part005SupportExplicit : Finset ℕ :=
  ([3842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part005 : ℚ :=
  (110038074175 : ℚ) / 6446424325619712

def SurrogateDiagonalTailChunk000Sub000Block092Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3842
    = surrogateDiagTailX0RatChunk000Sub000Block092Part005

theorem surrogateDiagonalTailChunk000Sub000Block092Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part005] using hcert

def TailChunk000Sub000Block092Part006SupportExplicit : Finset ℕ :=
  ([3845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part006 : ℚ :=
  (775541297125 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk000Sub000Block092Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3845
    = surrogateDiagTailX0RatChunk000Sub000Block092Part006

theorem surrogateDiagonalTailChunk000Sub000Block092Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part006] using hcert

def TailChunk000Sub000Block092Part007SupportExplicit : Finset ℕ :=
  ([3846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part007 : ℚ :=
  (6669717227 : ℚ) / 134244571545600

def SurrogateDiagonalTailChunk000Sub000Block092Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3846
    = surrogateDiagTailX0RatChunk000Sub000Block092Part007

theorem surrogateDiagonalTailChunk000Sub000Block092Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part007] using hcert

def TailChunk000Sub000Block092Part008SupportExplicit : Finset ℕ :=
  ([3847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part008 : ℚ :=
  (1849556139775 : ℚ) / 547096552992752328

def SurrogateDiagonalTailChunk000Sub000Block092Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3847
    = surrogateDiagTailX0RatChunk000Sub000Block092Part008

theorem surrogateDiagonalTailChunk000Sub000Block092Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part008] using hcert

def TailChunk000Sub000Block092Part009SupportExplicit : Finset ℕ :=
  ([3849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part009 : ℚ :=
  (513975130475 : ℚ) / 54034227456074304

def SurrogateDiagonalTailChunk000Sub000Block092Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3849
    = surrogateDiagTailX0RatChunk000Sub000Block092Part009

theorem surrogateDiagonalTailChunk000Sub000Block092Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part009] using hcert

def TailChunk000Sub000Block092Part010SupportExplicit : Finset ℕ :=
  ([3851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part010 : ℚ :=
  (74136174799 : ℚ) / 21975044755125000

def SurrogateDiagonalTailChunk000Sub000Block092Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3851
    = surrogateDiagTailX0RatChunk000Sub000Block092Part010

theorem surrogateDiagonalTailChunk000Sub000Block092Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part010] using hcert

def TailChunk000Sub000Block092Part011SupportExplicit : Finset ℕ :=
  ([3853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part011 : ℚ :=
  (1855329984775 : ℚ) / 550518569480596608

def SurrogateDiagonalTailChunk000Sub000Block092Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3853
    = surrogateDiagTailX0RatChunk000Sub000Block092Part011

theorem surrogateDiagonalTailChunk000Sub000Block092Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part011] using hcert

def TailChunk000Sub000Block092Part012SupportExplicit : Finset ℕ :=
  ([3854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part012 : ℚ :=
  (4788003 : ℚ) / 207691663360

def SurrogateDiagonalTailChunk000Sub000Block092Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3854
    = surrogateDiagTailX0RatChunk000Sub000Block092Part012

theorem surrogateDiagonalTailChunk000Sub000Block092Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part012] using hcert

def TailChunk000Sub000Block092Part013SupportExplicit : Finset ℕ :=
  ([3855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part013 : ℚ :=
  (174262611075 : ℚ) / 14663087068020736

def SurrogateDiagonalTailChunk000Sub000Block092Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3855
    = surrogateDiagTailX0RatChunk000Sub000Block092Part013

theorem surrogateDiagonalTailChunk000Sub000Block092Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part013] using hcert

def TailChunk000Sub000Block092Part014SupportExplicit : Finset ℕ :=
  ([3857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part014 : ℚ :=
  (194624078275 : ℚ) / 52274996796137472

def SurrogateDiagonalTailChunk000Sub000Block092Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3857
    = surrogateDiagTailX0RatChunk000Sub000Block092Part014

theorem surrogateDiagonalTailChunk000Sub000Block092Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part014] using hcert

def TailChunk000Sub000Block092Part015SupportExplicit : Finset ℕ :=
  ([3858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part015 : ℚ :=
  (90329832775 : ℚ) / 1699131387285792

def SurrogateDiagonalTailChunk000Sub000Block092Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3858
    = surrogateDiagTailX0RatChunk000Sub000Block092Part015

theorem surrogateDiagonalTailChunk000Sub000Block092Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part015] using hcert

def TailChunk000Sub000Block092Part016SupportExplicit : Finset ℕ :=
  ([3859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part016 : ℚ :=
  (889395954025 : ℚ) / 427504357794643968

def SurrogateDiagonalTailChunk000Sub000Block092Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3859
    = surrogateDiagTailX0RatChunk000Sub000Block092Part016

theorem surrogateDiagonalTailChunk000Sub000Block092Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part016] using hcert

def TailChunk000Sub000Block092Part017SupportExplicit : Finset ℕ :=
  ([3862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part017 : ℚ :=
  (9318173739 : ℚ) / 462588499533400

def SurrogateDiagonalTailChunk000Sub000Block092Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3862
    = surrogateDiagTailX0RatChunk000Sub000Block092Part017

theorem surrogateDiagonalTailChunk000Sub000Block092Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part017] using hcert

def TailChunk000Sub000Block092Part018SupportExplicit : Finset ℕ :=
  ([3863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part018 : ℚ :=
  (233168265625 : ℚ) / 139064393268400242

def SurrogateDiagonalTailChunk000Sub000Block092Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3863
    = surrogateDiagTailX0RatChunk000Sub000Block092Part018

theorem surrogateDiagonalTailChunk000Sub000Block092Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part018] using hcert

def TailChunk000Sub000Block092Part019SupportExplicit : Finset ℕ :=
  ([3865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part019 : ℚ :=
  (820861739275 : ℚ) / 227371499290656768

def SurrogateDiagonalTailChunk000Sub000Block092Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3865
    = surrogateDiagTailX0RatChunk000Sub000Block092Part019

theorem surrogateDiagonalTailChunk000Sub000Block092Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part019] using hcert

def TailChunk000Sub000Block092Part020SupportExplicit : Finset ℕ :=
  ([3866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part020 : ℚ :=
  (1588007825 : ℚ) / 78998120304768

def SurrogateDiagonalTailChunk000Sub000Block092Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3866
    = surrogateDiagTailX0RatChunk000Sub000Block092Part020

theorem surrogateDiagonalTailChunk000Sub000Block092Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part020] using hcert

def TailChunk000Sub000Block092Part021SupportExplicit : Finset ℕ :=
  ([3867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part021 : ℚ :=
  (726537201025 : ℚ) / 110105824567001088

def SurrogateDiagonalTailChunk000Sub000Block092Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3867
    = surrogateDiagTailX0RatChunk000Sub000Block092Part021

theorem surrogateDiagonalTailChunk000Sub000Block092Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part021] using hcert

def TailChunk000Sub000Block092Part022SupportExplicit : Finset ℕ :=
  ([3869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part022 : ℚ :=
  (914159302975 : ℚ) / 491326534435995648

def SurrogateDiagonalTailChunk000Sub000Block092Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3869
    = surrogateDiagTailX0RatChunk000Sub000Block092Part022

theorem surrogateDiagonalTailChunk000Sub000Block092Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part022] using hcert

def TailChunk000Sub000Block092Part023SupportExplicit : Finset ℕ :=
  ([3873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part023 : ℚ :=
  (29151733507 : ℚ) / 4431652249219200

def SurrogateDiagonalTailChunk000Sub000Block092Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3873
    = surrogateDiagTailX0RatChunk000Sub000Block092Part023

theorem surrogateDiagonalTailChunk000Sub000Block092Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part023] using hcert

def TailChunk000Sub000Block092Part024SupportExplicit : Finset ℕ :=
  ([3874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block092Part024 : ℚ :=
  (110470995625 : ℚ) / 6219260002639872

def SurrogateDiagonalTailChunk000Sub000Block092Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3874
    = surrogateDiagTailX0RatChunk000Sub000Block092Part024

theorem surrogateDiagonalTailChunk000Sub000Block092Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block092Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block092Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block092Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block092Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block092Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block092Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block092HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block092Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block092Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block092Part000
    + surrogateDiagTailX0RatChunk000Sub000Block092Part001
    + surrogateDiagTailX0RatChunk000Sub000Block092Part002
    + surrogateDiagTailX0RatChunk000Sub000Block092Part003
    + surrogateDiagTailX0RatChunk000Sub000Block092Part004
    + surrogateDiagTailX0RatChunk000Sub000Block092Part005
    + surrogateDiagTailX0RatChunk000Sub000Block092Part006
    + surrogateDiagTailX0RatChunk000Sub000Block092Part007
    + surrogateDiagTailX0RatChunk000Sub000Block092Part008
    + surrogateDiagTailX0RatChunk000Sub000Block092Part009

def surrogateDiagonalTailChunk000Sub000Block092MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block092Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block092Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block092Part010
    + surrogateDiagTailX0RatChunk000Sub000Block092Part011
    + surrogateDiagTailX0RatChunk000Sub000Block092Part012
    + surrogateDiagTailX0RatChunk000Sub000Block092Part013
    + surrogateDiagTailX0RatChunk000Sub000Block092Part014
    + surrogateDiagTailX0RatChunk000Sub000Block092Part015
    + surrogateDiagTailX0RatChunk000Sub000Block092Part016
    + surrogateDiagTailX0RatChunk000Sub000Block092Part017
    + surrogateDiagTailX0RatChunk000Sub000Block092Part018
    + surrogateDiagTailX0RatChunk000Sub000Block092Part019

def surrogateDiagonalTailChunk000Sub000Block092TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block092Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block092Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block092Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block092Part020
    + surrogateDiagTailX0RatChunk000Sub000Block092Part021
    + surrogateDiagTailX0RatChunk000Sub000Block092Part022
    + surrogateDiagTailX0RatChunk000Sub000Block092Part023
    + surrogateDiagTailX0RatChunk000Sub000Block092Part024

def surrogateDiagonalTailChunk000Sub000Block092Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block092HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block092MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block092TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block092 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block092Part000
    + surrogateDiagTailX0RatChunk000Sub000Block092Part001
    + surrogateDiagTailX0RatChunk000Sub000Block092Part002
    + surrogateDiagTailX0RatChunk000Sub000Block092Part003
    + surrogateDiagTailX0RatChunk000Sub000Block092Part004
    + surrogateDiagTailX0RatChunk000Sub000Block092Part005
    + surrogateDiagTailX0RatChunk000Sub000Block092Part006
    + surrogateDiagTailX0RatChunk000Sub000Block092Part007
    + surrogateDiagTailX0RatChunk000Sub000Block092Part008
    + surrogateDiagTailX0RatChunk000Sub000Block092Part009
    + surrogateDiagTailX0RatChunk000Sub000Block092Part010
    + surrogateDiagTailX0RatChunk000Sub000Block092Part011
    + surrogateDiagTailX0RatChunk000Sub000Block092Part012
    + surrogateDiagTailX0RatChunk000Sub000Block092Part013
    + surrogateDiagTailX0RatChunk000Sub000Block092Part014
    + surrogateDiagTailX0RatChunk000Sub000Block092Part015
    + surrogateDiagTailX0RatChunk000Sub000Block092Part016
    + surrogateDiagTailX0RatChunk000Sub000Block092Part017
    + surrogateDiagTailX0RatChunk000Sub000Block092Part018
    + surrogateDiagTailX0RatChunk000Sub000Block092Part019
    + surrogateDiagTailX0RatChunk000Sub000Block092Part020
    + surrogateDiagTailX0RatChunk000Sub000Block092Part021
    + surrogateDiagTailX0RatChunk000Sub000Block092Part022
    + surrogateDiagTailX0RatChunk000Sub000Block092Part023
    + surrogateDiagTailX0RatChunk000Sub000Block092Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block092_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block092Head + surrogateDiagTailX0RatChunk000Sub000Block092Mid + surrogateDiagTailX0RatChunk000Sub000Block092Tail =
      surrogateDiagTailX0RatChunk000Sub000Block092 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block092Head surrogateDiagTailX0RatChunk000Sub000Block092Mid surrogateDiagTailX0RatChunk000Sub000Block092Tail surrogateDiagTailX0RatChunk000Sub000Block092
  ring

def SurrogateDiagonalTailChunk000Sub000Block092HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block092HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block092Head

def SurrogateDiagonalTailChunk000Sub000Block092MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block092MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block092Mid

def SurrogateDiagonalTailChunk000Sub000Block092TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block092TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block092Tail

theorem surrogateDiagonalTailChunk000Sub000Block092_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block092HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block092MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block092TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block092Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block092 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block092HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block092MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block092TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block092Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block092_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
