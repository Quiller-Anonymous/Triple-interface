import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [180,190). -/

/-- Block 180 covers tail-support indices [9500,9525) and q from 15674 to 15711. -/

def TailChunk000Sub001Block180Part000SupportExplicit : Finset ℕ :=
  ([15674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part000 : ℚ :=
  (2936200239 : ℚ) / 6114442569318400

def SurrogateDiagonalTailChunk000Sub001Block180Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15674
    = surrogateDiagTailX0RatChunk000Sub001Block180Part000

theorem surrogateDiagonalTailChunk000Sub001Block180Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part000] using hcert

def TailChunk000Sub001Block180Part001SupportExplicit : Finset ℕ :=
  ([15677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part001 : ℚ :=
  (11871496619 : ℚ) / 111347817422782464

def SurrogateDiagonalTailChunk000Sub001Block180Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15677
    = surrogateDiagTailX0RatChunk000Sub001Block180Part001

theorem surrogateDiagonalTailChunk000Sub001Block180Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part001] using hcert

def TailChunk000Sub001Block180Part002SupportExplicit : Finset ℕ :=
  ([15679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part002 : ℚ :=
  (3841110015625 : ℚ) / 37768480094644222482

def SurrogateDiagonalTailChunk000Sub001Block180Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15679
    = surrogateDiagTailX0RatChunk000Sub001Block180Part002

theorem surrogateDiagonalTailChunk000Sub001Block180Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part002] using hcert

def TailChunk000Sub001Block180Part003SupportExplicit : Finset ℕ :=
  ([15681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part003 : ℚ :=
  (6828393477325 : ℚ) / 29841762050089262208

def SurrogateDiagonalTailChunk000Sub001Block180Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15681
    = surrogateDiagTailX0RatChunk000Sub001Block180Part003

theorem surrogateDiagonalTailChunk000Sub001Block180Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part003] using hcert

def TailChunk000Sub001Block180Part004SupportExplicit : Finset ℕ :=
  ([15682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part004 : ℚ :=
  (1537032025 : ℚ) / 3778775587356672

def SurrogateDiagonalTailChunk000Sub001Block180Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15682
    = surrogateDiagTailX0RatChunk000Sub001Block180Part004

theorem surrogateDiagonalTailChunk000Sub001Block180Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part004] using hcert

def TailChunk000Sub001Block180Part005SupportExplicit : Finset ℕ :=
  ([15683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part005 : ℚ :=
  (3843070140625 : ℚ) / 37807039029836411922

def SurrogateDiagonalTailChunk000Sub001Block180Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15683
    = surrogateDiagTailX0RatChunk000Sub001Block180Part005

theorem surrogateDiagonalTailChunk000Sub001Block180Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part005] using hcert

def TailChunk000Sub001Block180Part006SupportExplicit : Finset ℕ :=
  ([15685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part006 : ℚ :=
  (614734140625 : ℚ) / 3869466201453232128

def SurrogateDiagonalTailChunk000Sub001Block180Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15685
    = surrogateDiagTailX0RatChunk000Sub001Block180Part006

theorem surrogateDiagonalTailChunk000Sub001Block180Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part006] using hcert

def TailChunk000Sub001Block180Part007SupportExplicit : Finset ℕ :=
  ([15686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part007 : ℚ :=
  (30335533117 : ℚ) / 47446327368000000

def SurrogateDiagonalTailChunk000Sub001Block180Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15686
    = surrogateDiagTailX0RatChunk000Sub001Block180Part007

theorem surrogateDiagonalTailChunk000Sub001Block180Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part007] using hcert

def TailChunk000Sub001Block180Part008SupportExplicit : Finset ℕ :=
  ([15689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part008 : ℚ :=
  (10699482937 : ℚ) / 96805549622476800

def SurrogateDiagonalTailChunk000Sub001Block180Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15689
    = surrogateDiagTailX0RatChunk000Sub001Block180Part008

theorem surrogateDiagonalTailChunk000Sub001Block180Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part008] using hcert

def TailChunk000Sub001Block180Part009SupportExplicit : Finset ℕ :=
  ([15690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part009 : ℚ :=
  (1377203725 : ℚ) / 660110042329344

def SurrogateDiagonalTailChunk000Sub001Block180Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15690
    = surrogateDiagTailX0RatChunk000Sub001Block180Part009

theorem surrogateDiagonalTailChunk000Sub001Block180Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part009] using hcert

def TailChunk000Sub001Block180Part010SupportExplicit : Finset ℕ :=
  ([15691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part010 : ℚ :=
  (236469968303 : ℚ) / 1631751157422489600

def SurrogateDiagonalTailChunk000Sub001Block180Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15691
    = surrogateDiagTailX0RatChunk000Sub001Block180Part010

theorem surrogateDiagonalTailChunk000Sub001Block180Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part010] using hcert

def TailChunk000Sub001Block180Part011SupportExplicit : Finset ℕ :=
  ([15693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part011 : ℚ :=
  (273553979077 : ℚ) / 1197329239420291200

def SurrogateDiagonalTailChunk000Sub001Block180Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15693
    = surrogateDiagTailX0RatChunk000Sub001Block180Part011

theorem surrogateDiagonalTailChunk000Sub001Block180Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part011] using hcert

def TailChunk000Sub001Block180Part012SupportExplicit : Finset ℕ :=
  ([15694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part012 : ℚ :=
  (929202646775 : ℚ) / 1283253922288244736

def SurrogateDiagonalTailChunk000Sub001Block180Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15694
    = surrogateDiagTailX0RatChunk000Sub001Block180Part012

theorem surrogateDiagonalTailChunk000Sub001Block180Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part012] using hcert

def TailChunk000Sub001Block180Part013SupportExplicit : Finset ℕ :=
  ([15695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part013 : ℚ :=
  (4639872046625 : ℚ) / 26764798359622385664

def SurrogateDiagonalTailChunk000Sub001Block180Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15695
    = surrogateDiagTailX0RatChunk000Sub001Block180Part013

theorem surrogateDiagonalTailChunk000Sub001Block180Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part013] using hcert

def TailChunk000Sub001Block180Part014SupportExplicit : Finset ℕ :=
  ([15697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part014 : ℚ :=
  (10806246987 : ℚ) / 86163575989677400

def SurrogateDiagonalTailChunk000Sub001Block180Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15697
    = surrogateDiagTailX0RatChunk000Sub001Block180Part014

theorem surrogateDiagonalTailChunk000Sub001Block180Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part014] using hcert

def TailChunk000Sub001Block180Part015SupportExplicit : Finset ℕ :=
  ([15698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part015 : ℚ :=
  (3707321393575 : ℚ) / 8501401704807931008

def SurrogateDiagonalTailChunk000Sub001Block180Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15698
    = surrogateDiagTailX0RatChunk000Sub001Block180Part015

theorem surrogateDiagonalTailChunk000Sub001Block180Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part015] using hcert

def TailChunk000Sub001Block180Part016SupportExplicit : Finset ℕ :=
  ([15699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part016 : ℚ :=
  (6844080476725 : ℚ) / 29979044225242103808

def SurrogateDiagonalTailChunk000Sub001Block180Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15699
    = surrogateDiagTailX0RatChunk000Sub001Block180Part016

theorem surrogateDiagonalTailChunk000Sub001Block180Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part016] using hcert

def TailChunk000Sub001Block180Part017SupportExplicit : Finset ℕ :=
  ([15701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part017 : ℚ :=
  (93291739625 : ℚ) / 639682285041638361

def SurrogateDiagonalTailChunk000Sub001Block180Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15701
    = surrogateDiagTailX0RatChunk000Sub001Block180Part017

theorem surrogateDiagonalTailChunk000Sub001Block180Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part017] using hcert

def TailChunk000Sub001Block180Part018SupportExplicit : Finset ℕ :=
  ([15702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part018 : ℚ :=
  (1711488738325 : ℚ) / 1873690264077631488

def SurrogateDiagonalTailChunk000Sub001Block180Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15702
    = surrogateDiagTailX0RatChunk000Sub001Block180Part018

theorem surrogateDiagonalTailChunk000Sub001Block180Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part018] using hcert

def TailChunk000Sub001Block180Part019SupportExplicit : Finset ℕ :=
  ([15703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part019 : ℚ :=
  (588630110113 : ℚ) / 5452306569921331200

def SurrogateDiagonalTailChunk000Sub001Block180Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15703
    = surrogateDiagTailX0RatChunk000Sub001Block180Part019

theorem surrogateDiagonalTailChunk000Sub001Block180Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part019] using hcert

def TailChunk000Sub001Block180Part020SupportExplicit : Finset ℕ :=
  ([15706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part020 : ℚ :=
  (963587640625 : ℚ) / 2376227574510565152

def SurrogateDiagonalTailChunk000Sub001Block180Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15706
    = surrogateDiagTailX0RatChunk000Sub001Block180Part020

theorem surrogateDiagonalTailChunk000Sub001Block180Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part020] using hcert

def TailChunk000Sub001Block180Part021SupportExplicit : Finset ℕ :=
  ([15707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part021 : ℚ :=
  (1072039297475 : ℚ) / 10192653474202386432

def SurrogateDiagonalTailChunk000Sub001Block180Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15707
    = surrogateDiagTailX0RatChunk000Sub001Block180Part021

theorem surrogateDiagonalTailChunk000Sub001Block180Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part021] using hcert

def TailChunk000Sub001Block180Part022SupportExplicit : Finset ℕ :=
  ([15709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part022 : ℚ :=
  (4750869959325 : ℚ) / 42240964506800853376

def SurrogateDiagonalTailChunk000Sub001Block180Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15709
    = surrogateDiagTailX0RatChunk000Sub001Block180Part022

theorem surrogateDiagonalTailChunk000Sub001Block180Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part022] using hcert

def TailChunk000Sub001Block180Part023SupportExplicit : Finset ℕ :=
  ([15710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part023 : ℚ :=
  (36995921859 : ℚ) / 51856615734630400

def SurrogateDiagonalTailChunk000Sub001Block180Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15710
    = surrogateDiagTailX0RatChunk000Sub001Block180Part023

theorem surrogateDiagonalTailChunk000Sub001Block180Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part023] using hcert

def TailChunk000Sub001Block180Part024SupportExplicit : Finset ℕ :=
  ([15711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block180Part024 : ℚ :=
  (623140770575 : ℚ) / 2733711677243086848

def SurrogateDiagonalTailChunk000Sub001Block180Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15711
    = surrogateDiagTailX0RatChunk000Sub001Block180Part024

theorem surrogateDiagonalTailChunk000Sub001Block180Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block180Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block180Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block180Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block180Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block180Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block180Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block180HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block180Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block180Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block180Part000
    + surrogateDiagTailX0RatChunk000Sub001Block180Part001
    + surrogateDiagTailX0RatChunk000Sub001Block180Part002
    + surrogateDiagTailX0RatChunk000Sub001Block180Part003
    + surrogateDiagTailX0RatChunk000Sub001Block180Part004
    + surrogateDiagTailX0RatChunk000Sub001Block180Part005
    + surrogateDiagTailX0RatChunk000Sub001Block180Part006
    + surrogateDiagTailX0RatChunk000Sub001Block180Part007
    + surrogateDiagTailX0RatChunk000Sub001Block180Part008
    + surrogateDiagTailX0RatChunk000Sub001Block180Part009

def surrogateDiagonalTailChunk000Sub001Block180MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block180Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block180Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block180Part010
    + surrogateDiagTailX0RatChunk000Sub001Block180Part011
    + surrogateDiagTailX0RatChunk000Sub001Block180Part012
    + surrogateDiagTailX0RatChunk000Sub001Block180Part013
    + surrogateDiagTailX0RatChunk000Sub001Block180Part014
    + surrogateDiagTailX0RatChunk000Sub001Block180Part015
    + surrogateDiagTailX0RatChunk000Sub001Block180Part016
    + surrogateDiagTailX0RatChunk000Sub001Block180Part017
    + surrogateDiagTailX0RatChunk000Sub001Block180Part018
    + surrogateDiagTailX0RatChunk000Sub001Block180Part019

def surrogateDiagonalTailChunk000Sub001Block180TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block180Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block180Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block180Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block180Part020
    + surrogateDiagTailX0RatChunk000Sub001Block180Part021
    + surrogateDiagTailX0RatChunk000Sub001Block180Part022
    + surrogateDiagTailX0RatChunk000Sub001Block180Part023
    + surrogateDiagTailX0RatChunk000Sub001Block180Part024

def surrogateDiagonalTailChunk000Sub001Block180Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block180HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block180MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block180TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block180 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block180Part000
    + surrogateDiagTailX0RatChunk000Sub001Block180Part001
    + surrogateDiagTailX0RatChunk000Sub001Block180Part002
    + surrogateDiagTailX0RatChunk000Sub001Block180Part003
    + surrogateDiagTailX0RatChunk000Sub001Block180Part004
    + surrogateDiagTailX0RatChunk000Sub001Block180Part005
    + surrogateDiagTailX0RatChunk000Sub001Block180Part006
    + surrogateDiagTailX0RatChunk000Sub001Block180Part007
    + surrogateDiagTailX0RatChunk000Sub001Block180Part008
    + surrogateDiagTailX0RatChunk000Sub001Block180Part009
    + surrogateDiagTailX0RatChunk000Sub001Block180Part010
    + surrogateDiagTailX0RatChunk000Sub001Block180Part011
    + surrogateDiagTailX0RatChunk000Sub001Block180Part012
    + surrogateDiagTailX0RatChunk000Sub001Block180Part013
    + surrogateDiagTailX0RatChunk000Sub001Block180Part014
    + surrogateDiagTailX0RatChunk000Sub001Block180Part015
    + surrogateDiagTailX0RatChunk000Sub001Block180Part016
    + surrogateDiagTailX0RatChunk000Sub001Block180Part017
    + surrogateDiagTailX0RatChunk000Sub001Block180Part018
    + surrogateDiagTailX0RatChunk000Sub001Block180Part019
    + surrogateDiagTailX0RatChunk000Sub001Block180Part020
    + surrogateDiagTailX0RatChunk000Sub001Block180Part021
    + surrogateDiagTailX0RatChunk000Sub001Block180Part022
    + surrogateDiagTailX0RatChunk000Sub001Block180Part023
    + surrogateDiagTailX0RatChunk000Sub001Block180Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block180_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block180Head + surrogateDiagTailX0RatChunk000Sub001Block180Mid + surrogateDiagTailX0RatChunk000Sub001Block180Tail =
      surrogateDiagTailX0RatChunk000Sub001Block180 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block180Head surrogateDiagTailX0RatChunk000Sub001Block180Mid surrogateDiagTailX0RatChunk000Sub001Block180Tail surrogateDiagTailX0RatChunk000Sub001Block180
  ring

def SurrogateDiagonalTailChunk000Sub001Block180HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block180HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block180Head

def SurrogateDiagonalTailChunk000Sub001Block180MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block180MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block180Mid

def SurrogateDiagonalTailChunk000Sub001Block180TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block180TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block180Tail

theorem surrogateDiagonalTailChunk000Sub001Block180_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block180HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block180MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block180TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block180Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block180 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block180HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block180MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block180TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block180Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block180_eq_head_add_mid_add_tail

/-- Block 181 covers tail-support indices [9525,9550) and q from 15713 to 15755. -/

def TailChunk000Sub001Block181Part000SupportExplicit : Finset ℕ :=
  ([15713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part000 : ℚ :=
  (1169688555625 : ℚ) / 10182532913011849824

def SurrogateDiagonalTailChunk000Sub001Block181Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15713
    = surrogateDiagTailX0RatChunk000Sub001Block181Part000

theorem surrogateDiagonalTailChunk000Sub001Block181Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part000] using hcert

def TailChunk000Sub001Block181Part001SupportExplicit : Finset ℕ :=
  ([15715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part001 : ℚ :=
  (3772901214125 : ℚ) / 16709131852006293504

def SurrogateDiagonalTailChunk000Sub001Block181Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15715
    = surrogateDiagTailX0RatChunk000Sub001Block181Part001

theorem surrogateDiagonalTailChunk000Sub001Block181Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part001] using hcert

def TailChunk000Sub001Block181Part002SupportExplicit : Finset ℕ :=
  ([15718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part002 : ℚ :=
  (180684227 : ℚ) / 403356456760320

def SurrogateDiagonalTailChunk000Sub001Block181Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15718
    = surrogateDiagTailX0RatChunk000Sub001Block181Part002

theorem surrogateDiagonalTailChunk000Sub001Block181Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part002] using hcert

def TailChunk000Sub001Block181Part003SupportExplicit : Finset ℕ :=
  ([15719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part003 : ℚ :=
  (175089930149 : ℚ) / 1386367680044390400

def SurrogateDiagonalTailChunk000Sub001Block181Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15719
    = surrogateDiagTailX0RatChunk000Sub001Block181Part003

theorem surrogateDiagonalTailChunk000Sub001Block181Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part003] using hcert

def TailChunk000Sub001Block181Part004SupportExplicit : Finset ℕ :=
  ([15721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part004 : ℚ :=
  (1665728635075 : ℚ) / 15806056180687673472

def SurrogateDiagonalTailChunk000Sub001Block181Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15721
    = surrogateDiagTailX0RatChunk000Sub001Block181Part004

theorem surrogateDiagonalTailChunk000Sub001Block181Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part004] using hcert

def TailChunk000Sub001Block181Part005SupportExplicit : Finset ℕ :=
  ([15722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part005 : ℚ :=
  (170604094475 : ℚ) / 285319058983396416

def SurrogateDiagonalTailChunk000Sub001Block181Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15722
    = surrogateDiagTailX0RatChunk000Sub001Block181Part005

theorem surrogateDiagonalTailChunk000Sub001Block181Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part005] using hcert

def TailChunk000Sub001Block181Part006SupportExplicit : Finset ℕ :=
  ([15726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part006 : ℚ :=
  (42921861839 : ℚ) / 37703529085977600

def SurrogateDiagonalTailChunk000Sub001Block181Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15726
    = surrogateDiagTailX0RatChunk000Sub001Block181Part006

theorem surrogateDiagonalTailChunk000Sub001Block181Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part006] using hcert

def TailChunk000Sub001Block181Part007SupportExplicit : Finset ℕ :=
  ([15727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part007 : ℚ :=
  (3864664515625 : ℚ) / 38233138748523568722

def SurrogateDiagonalTailChunk000Sub001Block181Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15727
    = surrogateDiagTailX0RatChunk000Sub001Block181Part007

theorem surrogateDiagonalTailChunk000Sub001Block181Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part007] using hcert

def TailChunk000Sub001Block181Part008SupportExplicit : Finset ℕ :=
  ([15731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part008 : ℚ :=
  (6186609025 : ℚ) / 61235284610410482

def SurrogateDiagonalTailChunk000Sub001Block181Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15731
    = surrogateDiagTailX0RatChunk000Sub001Block181Part008

theorem surrogateDiagonalTailChunk000Sub001Block181Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part008] using hcert

def TailChunk000Sub001Block181Part009SupportExplicit : Finset ℕ :=
  ([15733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part009 : ℚ :=
  (3867613890625 : ℚ) / 38291521083761539872

def SurrogateDiagonalTailChunk000Sub001Block181Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15733
    = surrogateDiagTailX0RatChunk000Sub001Block181Part009

theorem surrogateDiagonalTailChunk000Sub001Block181Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part009] using hcert

def TailChunk000Sub001Block181Part010SupportExplicit : Finset ℕ :=
  ([15734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part010 : ℚ :=
  (967026390625 : ℚ) / 2393220067735096242

def SurrogateDiagonalTailChunk000Sub001Block181Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15734
    = surrogateDiagTailX0RatChunk000Sub001Block181Part010

theorem surrogateDiagonalTailChunk000Sub001Block181Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part010] using hcert

def TailChunk000Sub001Block181Part011SupportExplicit : Finset ℕ :=
  ([15735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part011 : ℚ :=
  (4876078413925 : ℚ) / 12354692410893139968

def SurrogateDiagonalTailChunk000Sub001Block181Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15735
    = surrogateDiagTailX0RatChunk000Sub001Block181Part011

theorem surrogateDiagonalTailChunk000Sub001Block181Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part011] using hcert

def TailChunk000Sub001Block181Part012SupportExplicit : Finset ℕ :=
  ([15737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part012 : ℚ :=
  (3869580765625 : ℚ) / 38330479769238999552

def SurrogateDiagonalTailChunk000Sub001Block181Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15737
    = surrogateDiagTailX0RatChunk000Sub001Block181Part012

theorem surrogateDiagonalTailChunk000Sub001Block181Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part012] using hcert

def TailChunk000Sub001Block181Part013SupportExplicit : Finset ℕ :=
  ([15738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part013 : ℚ :=
  (16369736051 : ℚ) / 12907406616330240

def SurrogateDiagonalTailChunk000Sub001Block181Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15738
    = surrogateDiagTailX0RatChunk000Sub001Block181Part013

theorem surrogateDiagonalTailChunk000Sub001Block181Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part013] using hcert

def TailChunk000Sub001Block181Part014SupportExplicit : Finset ℕ :=
  ([15739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part014 : ℚ :=
  (3870564390625 : ℚ) / 38349970256238385842

def SurrogateDiagonalTailChunk000Sub001Block181Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15739
    = surrogateDiagTailX0RatChunk000Sub001Block181Part014

theorem surrogateDiagonalTailChunk000Sub001Block181Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part014] using hcert

def TailChunk000Sub001Block181Part015SupportExplicit : Finset ℕ :=
  ([15742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part015 : ℚ :=
  (3365626975 : ℚ) / 7069859344171008

def SurrogateDiagonalTailChunk000Sub001Block181Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15742
    = surrogateDiagTailX0RatChunk000Sub001Block181Part015

theorem surrogateDiagonalTailChunk000Sub001Block181Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part015] using hcert

def TailChunk000Sub001Block181Part016SupportExplicit : Finset ℕ :=
  ([15743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part016 : ℚ :=
  (10183166591125 : ℚ) / 58812634265477971968

def SurrogateDiagonalTailChunk000Sub001Block181Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15743
    = surrogateDiagTailX0RatChunk000Sub001Block181Part016

theorem surrogateDiagonalTailChunk000Sub001Block181Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part016] using hcert

def TailChunk000Sub001Block181Part017SupportExplicit : Finset ℕ :=
  ([15745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part017 : ℚ :=
  (91906639925 : ℚ) / 503558739322822656

def SurrogateDiagonalTailChunk000Sub001Block181Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15745
    = surrogateDiagTailX0RatChunk000Sub001Block181Part017

theorem surrogateDiagonalTailChunk000Sub001Block181Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part017] using hcert

def TailChunk000Sub001Block181Part018SupportExplicit : Finset ℕ :=
  ([15746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part018 : ℚ :=
  (968502015625 : ℚ) / 2400530394809106432

def SurrogateDiagonalTailChunk000Sub001Block181Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15746
    = surrogateDiagTailX0RatChunk000Sub001Block181Part018

theorem surrogateDiagonalTailChunk000Sub001Block181Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part018] using hcert

def TailChunk000Sub001Block181Part019SupportExplicit : Finset ℕ :=
  ([15747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part019 : ℚ :=
  (129539302289 : ℚ) / 516296264653209600

def SurrogateDiagonalTailChunk000Sub001Block181Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15747
    = surrogateDiagTailX0RatChunk000Sub001Block181Part019

theorem surrogateDiagonalTailChunk000Sub001Block181Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part019] using hcert

def TailChunk000Sub001Block181Part020SupportExplicit : Finset ℕ :=
  ([15749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part020 : ℚ :=
  (3875484390625 : ℚ) / 38447534209401790752

def SurrogateDiagonalTailChunk000Sub001Block181Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15749
    = surrogateDiagTailX0RatChunk000Sub001Block181Part020

theorem surrogateDiagonalTailChunk000Sub001Block181Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part020] using hcert

def TailChunk000Sub001Block181Part021SupportExplicit : Finset ℕ :=
  ([15751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part021 : ℚ :=
  (7052145011225 : ℚ) / 61689071098118513664

def SurrogateDiagonalTailChunk000Sub001Block181Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15751
    = surrogateDiagTailX0RatChunk000Sub001Block181Part021

theorem surrogateDiagonalTailChunk000Sub001Block181Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part021] using hcert

def TailChunk000Sub001Block181Part022SupportExplicit : Finset ℕ :=
  ([15753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part022 : ℚ :=
  (1650461507875 : ℚ) / 6787807432687091712

def SurrogateDiagonalTailChunk000Sub001Block181Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15753
    = surrogateDiagTailX0RatChunk000Sub001Block181Part022

theorem surrogateDiagonalTailChunk000Sub001Block181Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part022] using hcert

def TailChunk000Sub001Block181Part023SupportExplicit : Finset ℕ :=
  ([15754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part023 : ℚ :=
  (969486390625 : ℚ) / 2405413241734416672

def SurrogateDiagonalTailChunk000Sub001Block181Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15754
    = surrogateDiagTailX0RatChunk000Sub001Block181Part023

theorem surrogateDiagonalTailChunk000Sub001Block181Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part023] using hcert

def TailChunk000Sub001Block181Part024SupportExplicit : Finset ℕ :=
  ([15755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block181Part024 : ℚ :=
  (9701543227975 : ℚ) / 51299505760043532288

def SurrogateDiagonalTailChunk000Sub001Block181Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15755
    = surrogateDiagTailX0RatChunk000Sub001Block181Part024

theorem surrogateDiagonalTailChunk000Sub001Block181Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block181Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block181Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block181Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block181Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block181Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block181Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block181HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block181Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block181Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block181Part000
    + surrogateDiagTailX0RatChunk000Sub001Block181Part001
    + surrogateDiagTailX0RatChunk000Sub001Block181Part002
    + surrogateDiagTailX0RatChunk000Sub001Block181Part003
    + surrogateDiagTailX0RatChunk000Sub001Block181Part004
    + surrogateDiagTailX0RatChunk000Sub001Block181Part005
    + surrogateDiagTailX0RatChunk000Sub001Block181Part006
    + surrogateDiagTailX0RatChunk000Sub001Block181Part007
    + surrogateDiagTailX0RatChunk000Sub001Block181Part008
    + surrogateDiagTailX0RatChunk000Sub001Block181Part009

def surrogateDiagonalTailChunk000Sub001Block181MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block181Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block181Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block181Part010
    + surrogateDiagTailX0RatChunk000Sub001Block181Part011
    + surrogateDiagTailX0RatChunk000Sub001Block181Part012
    + surrogateDiagTailX0RatChunk000Sub001Block181Part013
    + surrogateDiagTailX0RatChunk000Sub001Block181Part014
    + surrogateDiagTailX0RatChunk000Sub001Block181Part015
    + surrogateDiagTailX0RatChunk000Sub001Block181Part016
    + surrogateDiagTailX0RatChunk000Sub001Block181Part017
    + surrogateDiagTailX0RatChunk000Sub001Block181Part018
    + surrogateDiagTailX0RatChunk000Sub001Block181Part019

def surrogateDiagonalTailChunk000Sub001Block181TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block181Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block181Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block181Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block181Part020
    + surrogateDiagTailX0RatChunk000Sub001Block181Part021
    + surrogateDiagTailX0RatChunk000Sub001Block181Part022
    + surrogateDiagTailX0RatChunk000Sub001Block181Part023
    + surrogateDiagTailX0RatChunk000Sub001Block181Part024

def surrogateDiagonalTailChunk000Sub001Block181Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block181HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block181MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block181TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block181 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block181Part000
    + surrogateDiagTailX0RatChunk000Sub001Block181Part001
    + surrogateDiagTailX0RatChunk000Sub001Block181Part002
    + surrogateDiagTailX0RatChunk000Sub001Block181Part003
    + surrogateDiagTailX0RatChunk000Sub001Block181Part004
    + surrogateDiagTailX0RatChunk000Sub001Block181Part005
    + surrogateDiagTailX0RatChunk000Sub001Block181Part006
    + surrogateDiagTailX0RatChunk000Sub001Block181Part007
    + surrogateDiagTailX0RatChunk000Sub001Block181Part008
    + surrogateDiagTailX0RatChunk000Sub001Block181Part009
    + surrogateDiagTailX0RatChunk000Sub001Block181Part010
    + surrogateDiagTailX0RatChunk000Sub001Block181Part011
    + surrogateDiagTailX0RatChunk000Sub001Block181Part012
    + surrogateDiagTailX0RatChunk000Sub001Block181Part013
    + surrogateDiagTailX0RatChunk000Sub001Block181Part014
    + surrogateDiagTailX0RatChunk000Sub001Block181Part015
    + surrogateDiagTailX0RatChunk000Sub001Block181Part016
    + surrogateDiagTailX0RatChunk000Sub001Block181Part017
    + surrogateDiagTailX0RatChunk000Sub001Block181Part018
    + surrogateDiagTailX0RatChunk000Sub001Block181Part019
    + surrogateDiagTailX0RatChunk000Sub001Block181Part020
    + surrogateDiagTailX0RatChunk000Sub001Block181Part021
    + surrogateDiagTailX0RatChunk000Sub001Block181Part022
    + surrogateDiagTailX0RatChunk000Sub001Block181Part023
    + surrogateDiagTailX0RatChunk000Sub001Block181Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block181_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block181Head + surrogateDiagTailX0RatChunk000Sub001Block181Mid + surrogateDiagTailX0RatChunk000Sub001Block181Tail =
      surrogateDiagTailX0RatChunk000Sub001Block181 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block181Head surrogateDiagTailX0RatChunk000Sub001Block181Mid surrogateDiagTailX0RatChunk000Sub001Block181Tail surrogateDiagTailX0RatChunk000Sub001Block181
  ring

def SurrogateDiagonalTailChunk000Sub001Block181HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block181HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block181Head

def SurrogateDiagonalTailChunk000Sub001Block181MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block181MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block181Mid

def SurrogateDiagonalTailChunk000Sub001Block181TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block181TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block181Tail

theorem surrogateDiagonalTailChunk000Sub001Block181_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block181HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block181MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block181TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block181Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block181 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block181HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block181MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block181TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block181Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block181_eq_head_add_mid_add_tail

/-- Block 182 covers tail-support indices [9550,9575) and q from 15757 to 15797. -/

def TailChunk000Sub001Block182Part000SupportExplicit : Finset ℕ :=
  ([15757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part000 : ℚ :=
  (93677286989 : ℚ) / 664434110250000000

def SurrogateDiagonalTailChunk000Sub001Block182Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15757
    = surrogateDiagTailX0RatChunk000Sub001Block182Part000

theorem surrogateDiagonalTailChunk000Sub001Block182Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part000] using hcert

def TailChunk000Sub001Block182Part001SupportExplicit : Finset ℕ :=
  ([15758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part001 : ℚ :=
  (969978765625 : ℚ) / 2407857456694709682

def SurrogateDiagonalTailChunk000Sub001Block182Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15758
    = surrogateDiagTailX0RatChunk000Sub001Block182Part001

theorem surrogateDiagonalTailChunk000Sub001Block182Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part001] using hcert

def TailChunk000Sub001Block182Part002SupportExplicit : Finset ℕ :=
  ([15761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part002 : ℚ :=
  (6210228025 : ℚ) / 61703770468196352

def SurrogateDiagonalTailChunk000Sub001Block182Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15761
    = surrogateDiagTailX0RatChunk000Sub001Block182Part002

theorem surrogateDiagonalTailChunk000Sub001Block182Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part002] using hcert

def TailChunk000Sub001Block182Part003SupportExplicit : Finset ℕ :=
  ([15762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part003 : ℚ :=
  (81916836217 : ℚ) / 64537033081651200

def SurrogateDiagonalTailChunk000Sub001Block182Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15762
    = surrogateDiagTailX0RatChunk000Sub001Block182Part003

theorem surrogateDiagonalTailChunk000Sub001Block182Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part003] using hcert

def TailChunk000Sub001Block182Part004SupportExplicit : Finset ℕ :=
  ([15763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part004 : ℚ :=
  (528215899243 : ℚ) / 4205899801133875200

def SurrogateDiagonalTailChunk000Sub001Block182Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15763
    = surrogateDiagTailX0RatChunk000Sub001Block182Part004

theorem surrogateDiagonalTailChunk000Sub001Block182Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part004] using hcert

def TailChunk000Sub001Block182Part005SupportExplicit : Finset ℕ :=
  ([15765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part005 : ℚ :=
  (39157581047 : ℚ) / 99594186854400000

def SurrogateDiagonalTailChunk000Sub001Block182Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15765
    = surrogateDiagTailX0RatChunk000Sub001Block182Part005

theorem surrogateDiagonalTailChunk000Sub001Block182Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part005] using hcert

def TailChunk000Sub001Block182Part006SupportExplicit : Finset ℕ :=
  ([15766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part006 : ℚ :=
  (970963890625 : ℚ) / 2412751474337716722

def SurrogateDiagonalTailChunk000Sub001Block182Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15766
    = surrogateDiagTailX0RatChunk000Sub001Block182Part006

theorem surrogateDiagonalTailChunk000Sub001Block182Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part006] using hcert

def TailChunk000Sub001Block182Part007SupportExplicit : Finset ℕ :=
  ([15767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part007 : ℚ :=
  (3884348265625 : ℚ) / 38623618296750755442

def SurrogateDiagonalTailChunk000Sub001Block182Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15767
    = surrogateDiagTailX0RatChunk000Sub001Block182Part007

theorem surrogateDiagonalTailChunk000Sub001Block182Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part007] using hcert

def TailChunk000Sub001Block182Part008SupportExplicit : Finset ℕ :=
  ([15769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part008 : ℚ :=
  (6750439288175 : ℚ) / 55941270652452225024

def SurrogateDiagonalTailChunk000Sub001Block182Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15769
    = surrogateDiagTailX0RatChunk000Sub001Block182Part008

theorem surrogateDiagonalTailChunk000Sub001Block182Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part008] using hcert

def TailChunk000Sub001Block182Part009SupportExplicit : Finset ℕ :=
  ([15770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part009 : ℚ :=
  (2566505709025 : ℚ) / 3038171280930275328

def SurrogateDiagonalTailChunk000Sub001Block182Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15770
    = surrogateDiagTailX0RatChunk000Sub001Block182Part009

theorem surrogateDiagonalTailChunk000Sub001Block182Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part009] using hcert

def TailChunk000Sub001Block182Part010SupportExplicit : Finset ℕ :=
  ([15771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part010 : ℚ :=
  (24391984649 : ℚ) / 72914580000000000

def SurrogateDiagonalTailChunk000Sub001Block182Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15771
    = surrogateDiagTailX0RatChunk000Sub001Block182Part010

theorem surrogateDiagonalTailChunk000Sub001Block182Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part010] using hcert

def TailChunk000Sub001Block182Part011SupportExplicit : Finset ℕ :=
  ([15773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part011 : ℚ :=
  (3887305140625 : ℚ) / 38682447177327136032

def SurrogateDiagonalTailChunk000Sub001Block182Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15773
    = surrogateDiagTailX0RatChunk000Sub001Block182Part011

theorem surrogateDiagonalTailChunk000Sub001Block182Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part011] using hcert

def TailChunk000Sub001Block182Part012SupportExplicit : Finset ℕ :=
  ([15774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part012 : ℚ :=
  (25388166033 : ℚ) / 17115650370918400

def SurrogateDiagonalTailChunk000Sub001Block182Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15774
    = surrogateDiagTailX0RatChunk000Sub001Block182Part012

theorem surrogateDiagonalTailChunk000Sub001Block182Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part012] using hcert

def TailChunk000Sub001Block182Part013SupportExplicit : Finset ℕ :=
  ([15779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part013 : ℚ :=
  (586882647703 : ℚ) / 5395438147631155200

def SurrogateDiagonalTailChunk000Sub001Block182Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15779
    = surrogateDiagTailX0RatChunk000Sub001Block182Part013

theorem surrogateDiagonalTailChunk000Sub001Block182Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part013] using hcert

def TailChunk000Sub001Block182Part014SupportExplicit : Finset ℕ :=
  ([15781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part014 : ℚ :=
  (14892151856725 : ℚ) / 139620234165669145728

def SurrogateDiagonalTailChunk000Sub001Block182Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15781
    = surrogateDiagTailX0RatChunk000Sub001Block182Part014

theorem surrogateDiagonalTailChunk000Sub001Block182Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part014] using hcert

def TailChunk000Sub001Block182Part015SupportExplicit : Finset ℕ :=
  ([15782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part015 : ℚ :=
  (433132475 : ℚ) / 16186710258232704

def SurrogateDiagonalTailChunk000Sub001Block182Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15782
    = surrogateDiagTailX0RatChunk000Sub001Block182Part015

theorem surrogateDiagonalTailChunk000Sub001Block182Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part015] using hcert

def TailChunk000Sub001Block182Part016SupportExplicit : Finset ℕ :=
  ([15783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part016 : ℚ :=
  (5001 : ℚ) / 244958748723200

def SurrogateDiagonalTailChunk000Sub001Block182Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15783
    = surrogateDiagTailX0RatChunk000Sub001Block182Part016

theorem surrogateDiagonalTailChunk000Sub001Block182Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part016] using hcert

def TailChunk000Sub001Block182Part017SupportExplicit : Finset ℕ :=
  ([15785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part017 : ℚ :=
  (1213548737 : ℚ) / 23597678592000000

def SurrogateDiagonalTailChunk000Sub001Block182Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15785
    = surrogateDiagTailX0RatChunk000Sub001Block182Part017

theorem surrogateDiagonalTailChunk000Sub001Block182Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part017] using hcert

def TailChunk000Sub001Block182Part018SupportExplicit : Finset ℕ :=
  ([15787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block182Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15787
    = surrogateDiagTailX0RatChunk000Sub001Block182Part018

theorem surrogateDiagonalTailChunk000Sub001Block182Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part018] using hcert

def TailChunk000Sub001Block182Part019SupportExplicit : Finset ℕ :=
  ([15789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part019 : ℚ :=
  (182694214525 : ℚ) / 24370991051108548608

def SurrogateDiagonalTailChunk000Sub001Block182Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15789
    = surrogateDiagTailX0RatChunk000Sub001Block182Part019

theorem surrogateDiagonalTailChunk000Sub001Block182Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part019] using hcert

def TailChunk000Sub001Block182Part020SupportExplicit : Finset ℕ :=
  ([15790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part020 : ℚ :=
  (116988556825 : ℚ) / 992281348915425792

def SurrogateDiagonalTailChunk000Sub001Block182Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15790
    = surrogateDiagTailX0RatChunk000Sub001Block182Part020

theorem surrogateDiagonalTailChunk000Sub001Block182Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part020] using hcert

def TailChunk000Sub001Block182Part021SupportExplicit : Finset ℕ :=
  ([15791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block182Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15791
    = surrogateDiagTailX0RatChunk000Sub001Block182Part021

theorem surrogateDiagonalTailChunk000Sub001Block182Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part021] using hcert

def TailChunk000Sub001Block182Part022SupportExplicit : Finset ℕ :=
  ([15793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part022 : ℚ :=
  (273903346525 : ℚ) / 121534252553399697408

def SurrogateDiagonalTailChunk000Sub001Block182Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15793
    = surrogateDiagTailX0RatChunk000Sub001Block182Part022

theorem surrogateDiagonalTailChunk000Sub001Block182Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part022] using hcert

def TailChunk000Sub001Block182Part023SupportExplicit : Finset ℕ :=
  ([15794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part023 : ℚ :=
  (5216079675 : ℚ) / 730980596441964544

def SurrogateDiagonalTailChunk000Sub001Block182Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15794
    = surrogateDiagTailX0RatChunk000Sub001Block182Part023

theorem surrogateDiagonalTailChunk000Sub001Block182Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part023] using hcert

def TailChunk000Sub001Block182Part024SupportExplicit : Finset ℕ :=
  ([15797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block182Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block182Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15797
    = surrogateDiagTailX0RatChunk000Sub001Block182Part024

theorem surrogateDiagonalTailChunk000Sub001Block182Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block182Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block182Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block182Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block182Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block182Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block182Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block182HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block182Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block182Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block182Part000
    + surrogateDiagTailX0RatChunk000Sub001Block182Part001
    + surrogateDiagTailX0RatChunk000Sub001Block182Part002
    + surrogateDiagTailX0RatChunk000Sub001Block182Part003
    + surrogateDiagTailX0RatChunk000Sub001Block182Part004
    + surrogateDiagTailX0RatChunk000Sub001Block182Part005
    + surrogateDiagTailX0RatChunk000Sub001Block182Part006
    + surrogateDiagTailX0RatChunk000Sub001Block182Part007
    + surrogateDiagTailX0RatChunk000Sub001Block182Part008
    + surrogateDiagTailX0RatChunk000Sub001Block182Part009

def surrogateDiagonalTailChunk000Sub001Block182MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block182Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block182Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block182Part010
    + surrogateDiagTailX0RatChunk000Sub001Block182Part011
    + surrogateDiagTailX0RatChunk000Sub001Block182Part012
    + surrogateDiagTailX0RatChunk000Sub001Block182Part013
    + surrogateDiagTailX0RatChunk000Sub001Block182Part014
    + surrogateDiagTailX0RatChunk000Sub001Block182Part015
    + surrogateDiagTailX0RatChunk000Sub001Block182Part016
    + surrogateDiagTailX0RatChunk000Sub001Block182Part017
    + surrogateDiagTailX0RatChunk000Sub001Block182Part018
    + surrogateDiagTailX0RatChunk000Sub001Block182Part019

def surrogateDiagonalTailChunk000Sub001Block182TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block182Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block182Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block182Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block182Part020
    + surrogateDiagTailX0RatChunk000Sub001Block182Part021
    + surrogateDiagTailX0RatChunk000Sub001Block182Part022
    + surrogateDiagTailX0RatChunk000Sub001Block182Part023
    + surrogateDiagTailX0RatChunk000Sub001Block182Part024

def surrogateDiagonalTailChunk000Sub001Block182Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block182HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block182MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block182TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block182 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block182Part000
    + surrogateDiagTailX0RatChunk000Sub001Block182Part001
    + surrogateDiagTailX0RatChunk000Sub001Block182Part002
    + surrogateDiagTailX0RatChunk000Sub001Block182Part003
    + surrogateDiagTailX0RatChunk000Sub001Block182Part004
    + surrogateDiagTailX0RatChunk000Sub001Block182Part005
    + surrogateDiagTailX0RatChunk000Sub001Block182Part006
    + surrogateDiagTailX0RatChunk000Sub001Block182Part007
    + surrogateDiagTailX0RatChunk000Sub001Block182Part008
    + surrogateDiagTailX0RatChunk000Sub001Block182Part009
    + surrogateDiagTailX0RatChunk000Sub001Block182Part010
    + surrogateDiagTailX0RatChunk000Sub001Block182Part011
    + surrogateDiagTailX0RatChunk000Sub001Block182Part012
    + surrogateDiagTailX0RatChunk000Sub001Block182Part013
    + surrogateDiagTailX0RatChunk000Sub001Block182Part014
    + surrogateDiagTailX0RatChunk000Sub001Block182Part015
    + surrogateDiagTailX0RatChunk000Sub001Block182Part016
    + surrogateDiagTailX0RatChunk000Sub001Block182Part017
    + surrogateDiagTailX0RatChunk000Sub001Block182Part018
    + surrogateDiagTailX0RatChunk000Sub001Block182Part019
    + surrogateDiagTailX0RatChunk000Sub001Block182Part020
    + surrogateDiagTailX0RatChunk000Sub001Block182Part021
    + surrogateDiagTailX0RatChunk000Sub001Block182Part022
    + surrogateDiagTailX0RatChunk000Sub001Block182Part023
    + surrogateDiagTailX0RatChunk000Sub001Block182Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block182_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block182Head + surrogateDiagTailX0RatChunk000Sub001Block182Mid + surrogateDiagTailX0RatChunk000Sub001Block182Tail =
      surrogateDiagTailX0RatChunk000Sub001Block182 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block182Head surrogateDiagTailX0RatChunk000Sub001Block182Mid surrogateDiagTailX0RatChunk000Sub001Block182Tail surrogateDiagTailX0RatChunk000Sub001Block182
  ring

def SurrogateDiagonalTailChunk000Sub001Block182HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block182HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block182Head

def SurrogateDiagonalTailChunk000Sub001Block182MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block182MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block182Mid

def SurrogateDiagonalTailChunk000Sub001Block182TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block182TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block182Tail

theorem surrogateDiagonalTailChunk000Sub001Block182_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block182HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block182MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block182TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block182Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block182 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block182HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block182MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block182TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block182Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block182_eq_head_add_mid_add_tail

/-- Block 183 covers tail-support indices [9575,9600) and q from 15798 to 15837. -/

def TailChunk000Sub001Block183Part000SupportExplicit : Finset ℕ :=
  ([15798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part000 : ℚ :=
  (433189838075 : ℚ) / 959976022328623104

def SurrogateDiagonalTailChunk000Sub001Block183Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15798
    = surrogateDiagTailX0RatChunk000Sub001Block183Part000

theorem surrogateDiagonalTailChunk000Sub001Block183Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part000] using hcert

def TailChunk000Sub001Block183Part001SupportExplicit : Finset ℕ :=
  ([15799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part001 : ℚ :=
  (30480924937 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk000Sub001Block183Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15799
    = surrogateDiagTailX0RatChunk000Sub001Block183Part001

theorem surrogateDiagonalTailChunk000Sub001Block183Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part001] using hcert

def TailChunk000Sub001Block183Part002SupportExplicit : Finset ℕ :=
  ([15801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part002 : ℚ :=
  (1230343975 : ℚ) / 17987644593236736

def SurrogateDiagonalTailChunk000Sub001Block183Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15801
    = surrogateDiagTailX0RatChunk000Sub001Block183Part002

theorem surrogateDiagonalTailChunk000Sub001Block183Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part002] using hcert

def TailChunk000Sub001Block183Part003SupportExplicit : Finset ℕ :=
  ([15802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block183Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15802
    = surrogateDiagTailX0RatChunk000Sub001Block183Part003

theorem surrogateDiagonalTailChunk000Sub001Block183Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part003] using hcert

def TailChunk000Sub001Block183Part004SupportExplicit : Finset ℕ :=
  ([15803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block183Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15803
    = surrogateDiagTailX0RatChunk000Sub001Block183Part004

theorem surrogateDiagonalTailChunk000Sub001Block183Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part004] using hcert

def TailChunk000Sub001Block183Part005SupportExplicit : Finset ℕ :=
  ([15805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part005 : ℚ :=
  (105336834025 : ℚ) / 7647085245606395904

def SurrogateDiagonalTailChunk000Sub001Block183Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15805
    = surrogateDiagTailX0RatChunk000Sub001Block183Part005

theorem surrogateDiagonalTailChunk000Sub001Block183Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part005] using hcert

def TailChunk000Sub001Block183Part006SupportExplicit : Finset ℕ :=
  ([15806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part006 : ℚ :=
  (399176121775 : ℚ) / 5246482867553599488

def SurrogateDiagonalTailChunk000Sub001Block183Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15806
    = surrogateDiagTailX0RatChunk000Sub001Block183Part006

theorem surrogateDiagonalTailChunk000Sub001Block183Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part006] using hcert

def TailChunk000Sub001Block183Part007SupportExplicit : Finset ℕ :=
  ([15807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part007 : ℚ :=
  (34967598509 : ℚ) / 417723033949209600

def SurrogateDiagonalTailChunk000Sub001Block183Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15807
    = surrogateDiagTailX0RatChunk000Sub001Block183Part007

theorem surrogateDiagonalTailChunk000Sub001Block183Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part007] using hcert

def TailChunk000Sub001Block183Part008SupportExplicit : Finset ℕ :=
  ([15809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block183Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15809
    = surrogateDiagTailX0RatChunk000Sub001Block183Part008

theorem surrogateDiagonalTailChunk000Sub001Block183Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part008] using hcert

def TailChunk000Sub001Block183Part009SupportExplicit : Finset ℕ :=
  ([15810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part009 : ℚ :=
  (3264124813 : ℚ) / 2174762059038720

def SurrogateDiagonalTailChunk000Sub001Block183Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15810
    = surrogateDiagTailX0RatChunk000Sub001Block183Part009

theorem surrogateDiagonalTailChunk000Sub001Block183Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part009] using hcert

def TailChunk000Sub001Block183Part010SupportExplicit : Finset ℕ :=
  ([15811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part010 : ℚ :=
  (80798731225 : ℚ) / 146275586870039543808

def SurrogateDiagonalTailChunk000Sub001Block183Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15811
    = surrogateDiagTailX0RatChunk000Sub001Block183Part010

theorem surrogateDiagonalTailChunk000Sub001Block183Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part010] using hcert

def TailChunk000Sub001Block183Part011SupportExplicit : Finset ℕ :=
  ([15814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block183Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15814
    = surrogateDiagTailX0RatChunk000Sub001Block183Part011

theorem surrogateDiagonalTailChunk000Sub001Block183Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part011] using hcert

def TailChunk000Sub001Block183Part012SupportExplicit : Finset ℕ :=
  ([15815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part012 : ℚ :=
  (626141042125 : ℚ) / 63990320678497732608

def SurrogateDiagonalTailChunk000Sub001Block183Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15815
    = surrogateDiagTailX0RatChunk000Sub001Block183Part012

theorem surrogateDiagonalTailChunk000Sub001Block183Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part012] using hcert

def TailChunk000Sub001Block183Part013SupportExplicit : Finset ℕ :=
  ([15817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block183Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15817
    = surrogateDiagTailX0RatChunk000Sub001Block183Part013

theorem surrogateDiagonalTailChunk000Sub001Block183Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part013] using hcert

def TailChunk000Sub001Block183Part014SupportExplicit : Finset ℕ :=
  ([15818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part014 : ℚ :=
  (3045303723 : ℚ) / 88606049191638400

def SurrogateDiagonalTailChunk000Sub001Block183Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15818
    = surrogateDiagTailX0RatChunk000Sub001Block183Part014

theorem surrogateDiagonalTailChunk000Sub001Block183Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part014] using hcert

def TailChunk000Sub001Block183Part015SupportExplicit : Finset ℕ :=
  ([15819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part015 : ℚ :=
  (434437263925 : ℚ) / 7726600477015744512

def SurrogateDiagonalTailChunk000Sub001Block183Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15819
    = surrogateDiagTailX0RatChunk000Sub001Block183Part015

theorem surrogateDiagonalTailChunk000Sub001Block183Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part015] using hcert

def TailChunk000Sub001Block183Part016SupportExplicit : Finset ℕ :=
  ([15821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part016 : ℚ :=
  (62199204775 : ℚ) / 18894477753065668608

def SurrogateDiagonalTailChunk000Sub001Block183Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15821
    = surrogateDiagTailX0RatChunk000Sub001Block183Part016

theorem surrogateDiagonalTailChunk000Sub001Block183Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part016] using hcert

def TailChunk000Sub001Block183Part017SupportExplicit : Finset ℕ :=
  ([15823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block183Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15823
    = surrogateDiagTailX0RatChunk000Sub001Block183Part017

theorem surrogateDiagonalTailChunk000Sub001Block183Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part017] using hcert

def TailChunk000Sub001Block183Part018SupportExplicit : Finset ℕ :=
  ([15826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part018 : ℚ :=
  (480712763 : ℚ) / 57993654907699200

def SurrogateDiagonalTailChunk000Sub001Block183Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15826
    = surrogateDiagTailX0RatChunk000Sub001Block183Part018

theorem surrogateDiagonalTailChunk000Sub001Block183Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part018] using hcert

def TailChunk000Sub001Block183Part019SupportExplicit : Finset ℕ :=
  ([15829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part019 : ℚ :=
  (15627728767 : ℚ) / 4276834004097667200

def SurrogateDiagonalTailChunk000Sub001Block183Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15829
    = surrogateDiagTailX0RatChunk000Sub001Block183Part019

theorem surrogateDiagonalTailChunk000Sub001Block183Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part019] using hcert

def TailChunk000Sub001Block183Part020SupportExplicit : Finset ℕ :=
  ([15830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part020 : ℚ :=
  (104425887525 : ℚ) / 668253882203737088

def SurrogateDiagonalTailChunk000Sub001Block183Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15830
    = surrogateDiagTailX0RatChunk000Sub001Block183Part020

theorem surrogateDiagonalTailChunk000Sub001Block183Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part020] using hcert

def TailChunk000Sub001Block183Part021SupportExplicit : Finset ℕ :=
  ([15833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part021 : ℚ :=
  (594870961 : ℚ) / 972164275152235200

def SurrogateDiagonalTailChunk000Sub001Block183Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15833
    = surrogateDiagTailX0RatChunk000Sub001Block183Part021

theorem surrogateDiagonalTailChunk000Sub001Block183Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part021] using hcert

def TailChunk000Sub001Block183Part022SupportExplicit : Finset ℕ :=
  ([15834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part022 : ℚ :=
  (115486044025 : ℚ) / 94408459822301184

def SurrogateDiagonalTailChunk000Sub001Block183Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15834
    = surrogateDiagTailX0RatChunk000Sub001Block183Part022

theorem surrogateDiagonalTailChunk000Sub001Block183Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part022] using hcert

def TailChunk000Sub001Block183Part023SupportExplicit : Finset ℕ :=
  ([15835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part023 : ℚ :=
  (1253944086025 : ℚ) / 64314732300872337408

def SurrogateDiagonalTailChunk000Sub001Block183Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15835
    = surrogateDiagTailX0RatChunk000Sub001Block183Part023

theorem surrogateDiagonalTailChunk000Sub001Block183Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part023] using hcert

def TailChunk000Sub001Block183Part024SupportExplicit : Finset ℕ :=
  ([15837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block183Part024 : ℚ :=
  (124407521825 : ℚ) / 2217667078602935232

def SurrogateDiagonalTailChunk000Sub001Block183Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15837
    = surrogateDiagTailX0RatChunk000Sub001Block183Part024

theorem surrogateDiagonalTailChunk000Sub001Block183Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block183Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block183Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block183Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block183Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block183Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block183Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block183HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block183Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block183Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block183Part000
    + surrogateDiagTailX0RatChunk000Sub001Block183Part001
    + surrogateDiagTailX0RatChunk000Sub001Block183Part002
    + surrogateDiagTailX0RatChunk000Sub001Block183Part003
    + surrogateDiagTailX0RatChunk000Sub001Block183Part004
    + surrogateDiagTailX0RatChunk000Sub001Block183Part005
    + surrogateDiagTailX0RatChunk000Sub001Block183Part006
    + surrogateDiagTailX0RatChunk000Sub001Block183Part007
    + surrogateDiagTailX0RatChunk000Sub001Block183Part008
    + surrogateDiagTailX0RatChunk000Sub001Block183Part009

def surrogateDiagonalTailChunk000Sub001Block183MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block183Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block183Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block183Part010
    + surrogateDiagTailX0RatChunk000Sub001Block183Part011
    + surrogateDiagTailX0RatChunk000Sub001Block183Part012
    + surrogateDiagTailX0RatChunk000Sub001Block183Part013
    + surrogateDiagTailX0RatChunk000Sub001Block183Part014
    + surrogateDiagTailX0RatChunk000Sub001Block183Part015
    + surrogateDiagTailX0RatChunk000Sub001Block183Part016
    + surrogateDiagTailX0RatChunk000Sub001Block183Part017
    + surrogateDiagTailX0RatChunk000Sub001Block183Part018
    + surrogateDiagTailX0RatChunk000Sub001Block183Part019

def surrogateDiagonalTailChunk000Sub001Block183TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block183Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block183Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block183Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block183Part020
    + surrogateDiagTailX0RatChunk000Sub001Block183Part021
    + surrogateDiagTailX0RatChunk000Sub001Block183Part022
    + surrogateDiagTailX0RatChunk000Sub001Block183Part023
    + surrogateDiagTailX0RatChunk000Sub001Block183Part024

def surrogateDiagonalTailChunk000Sub001Block183Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block183HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block183MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block183TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block183 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block183Part000
    + surrogateDiagTailX0RatChunk000Sub001Block183Part001
    + surrogateDiagTailX0RatChunk000Sub001Block183Part002
    + surrogateDiagTailX0RatChunk000Sub001Block183Part003
    + surrogateDiagTailX0RatChunk000Sub001Block183Part004
    + surrogateDiagTailX0RatChunk000Sub001Block183Part005
    + surrogateDiagTailX0RatChunk000Sub001Block183Part006
    + surrogateDiagTailX0RatChunk000Sub001Block183Part007
    + surrogateDiagTailX0RatChunk000Sub001Block183Part008
    + surrogateDiagTailX0RatChunk000Sub001Block183Part009
    + surrogateDiagTailX0RatChunk000Sub001Block183Part010
    + surrogateDiagTailX0RatChunk000Sub001Block183Part011
    + surrogateDiagTailX0RatChunk000Sub001Block183Part012
    + surrogateDiagTailX0RatChunk000Sub001Block183Part013
    + surrogateDiagTailX0RatChunk000Sub001Block183Part014
    + surrogateDiagTailX0RatChunk000Sub001Block183Part015
    + surrogateDiagTailX0RatChunk000Sub001Block183Part016
    + surrogateDiagTailX0RatChunk000Sub001Block183Part017
    + surrogateDiagTailX0RatChunk000Sub001Block183Part018
    + surrogateDiagTailX0RatChunk000Sub001Block183Part019
    + surrogateDiagTailX0RatChunk000Sub001Block183Part020
    + surrogateDiagTailX0RatChunk000Sub001Block183Part021
    + surrogateDiagTailX0RatChunk000Sub001Block183Part022
    + surrogateDiagTailX0RatChunk000Sub001Block183Part023
    + surrogateDiagTailX0RatChunk000Sub001Block183Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block183_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block183Head + surrogateDiagTailX0RatChunk000Sub001Block183Mid + surrogateDiagTailX0RatChunk000Sub001Block183Tail =
      surrogateDiagTailX0RatChunk000Sub001Block183 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block183Head surrogateDiagTailX0RatChunk000Sub001Block183Mid surrogateDiagTailX0RatChunk000Sub001Block183Tail surrogateDiagTailX0RatChunk000Sub001Block183
  ring

def SurrogateDiagonalTailChunk000Sub001Block183HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block183HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block183Head

def SurrogateDiagonalTailChunk000Sub001Block183MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block183MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block183Mid

def SurrogateDiagonalTailChunk000Sub001Block183TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block183TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block183Tail

theorem surrogateDiagonalTailChunk000Sub001Block183_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block183HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block183MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block183TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block183Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block183 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block183HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block183MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block183TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block183Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block183_eq_head_add_mid_add_tail

/-- Block 184 covers tail-support indices [9600,9625) and q from 15838 to 15881. -/

def TailChunk000Sub001Block184Part000SupportExplicit : Finset ℕ :=
  ([15838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block184Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15838
    = surrogateDiagTailX0RatChunk000Sub001Block184Part000

theorem surrogateDiagonalTailChunk000Sub001Block184Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part000] using hcert

def TailChunk000Sub001Block184Part001SupportExplicit : Finset ℕ :=
  ([15839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part001 : ℚ :=
  (4281089875 : ℚ) / 5096326737101193216

def SurrogateDiagonalTailChunk000Sub001Block184Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15839
    = surrogateDiagTailX0RatChunk000Sub001Block184Part001

theorem surrogateDiagonalTailChunk000Sub001Block184Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part001] using hcert

def TailChunk000Sub001Block184Part002SupportExplicit : Finset ℕ :=
  ([15841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part002 : ℚ :=
  (42593128813 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk000Sub001Block184Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15841
    = surrogateDiagTailX0RatChunk000Sub001Block184Part002

theorem surrogateDiagonalTailChunk000Sub001Block184Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part002] using hcert

def TailChunk000Sub001Block184Part003SupportExplicit : Finset ℕ :=
  ([15843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part003 : ℚ :=
  (3486050111 : ℚ) / 62188850207784960

def SurrogateDiagonalTailChunk000Sub001Block184Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15843
    = surrogateDiagTailX0RatChunk000Sub001Block184Part003

theorem surrogateDiagonalTailChunk000Sub001Block184Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part003] using hcert

def TailChunk000Sub001Block184Part004SupportExplicit : Finset ℕ :=
  ([15845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part004 : ℚ :=
  (418509089575 : ℚ) / 21492466631810482176

def SurrogateDiagonalTailChunk000Sub001Block184Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15845
    = surrogateDiagTailX0RatChunk000Sub001Block184Part004

theorem surrogateDiagonalTailChunk000Sub001Block184Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part004] using hcert

def TailChunk000Sub001Block184Part005SupportExplicit : Finset ℕ :=
  ([15846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part005 : ℚ :=
  (8015189525 : ℚ) / 14103582784206336

def SurrogateDiagonalTailChunk000Sub001Block184Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15846
    = surrogateDiagTailX0RatChunk000Sub001Block184Part005

theorem surrogateDiagonalTailChunk000Sub001Block184Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part005] using hcert

def TailChunk000Sub001Block184Part006SupportExplicit : Finset ℕ :=
  ([15847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part006 : ℚ :=
  (590786255575 : ℚ) / 88808787539227312128

def SurrogateDiagonalTailChunk000Sub001Block184Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15847
    = surrogateDiagTailX0RatChunk000Sub001Block184Part006

theorem surrogateDiagonalTailChunk000Sub001Block184Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part006] using hcert

def TailChunk000Sub001Block184Part007SupportExplicit : Finset ℕ :=
  ([15853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part007 : ℚ :=
  (671166893 : ℚ) / 1178654881538739840

def SurrogateDiagonalTailChunk000Sub001Block184Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15853
    = surrogateDiagTailX0RatChunk000Sub001Block184Part007

theorem surrogateDiagonalTailChunk000Sub001Block184Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part007] using hcert

def TailChunk000Sub001Block184Part008SupportExplicit : Finset ℕ :=
  ([15854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block184Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15854
    = surrogateDiagTailX0RatChunk000Sub001Block184Part008

theorem surrogateDiagonalTailChunk000Sub001Block184Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part008] using hcert

def TailChunk000Sub001Block184Part009SupportExplicit : Finset ℕ :=
  ([15855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part009 : ℚ :=
  (1272802289 : ℚ) / 5375846154240000

def SurrogateDiagonalTailChunk000Sub001Block184Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15855
    = surrogateDiagTailX0RatChunk000Sub001Block184Part009

theorem surrogateDiagonalTailChunk000Sub001Block184Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part009] using hcert

def TailChunk000Sub001Block184Part010SupportExplicit : Finset ℕ :=
  ([15857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part010 : ℚ :=
  (1065650557 : ℚ) / 1974531147264000000

def SurrogateDiagonalTailChunk000Sub001Block184Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15857
    = surrogateDiagTailX0RatChunk000Sub001Block184Part010

theorem surrogateDiagonalTailChunk000Sub001Block184Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part010] using hcert

def TailChunk000Sub001Block184Part011SupportExplicit : Finset ℕ :=
  ([15859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block184Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15859
    = surrogateDiagTailX0RatChunk000Sub001Block184Part011

theorem surrogateDiagonalTailChunk000Sub001Block184Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part011] using hcert

def TailChunk000Sub001Block184Part012SupportExplicit : Finset ℕ :=
  ([15861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part012 : ℚ :=
  (17456972659 : ℚ) / 242143908121804800

def SurrogateDiagonalTailChunk000Sub001Block184Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15861
    = surrogateDiagTailX0RatChunk000Sub001Block184Part012

theorem surrogateDiagonalTailChunk000Sub001Block184Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part012] using hcert

def TailChunk000Sub001Block184Part013SupportExplicit : Finset ℕ :=
  ([15862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part013 : ℚ :=
  (3110466407 : ℚ) / 23385210762931200

def SurrogateDiagonalTailChunk000Sub001Block184Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15862
    = surrogateDiagTailX0RatChunk000Sub001Block184Part013

theorem surrogateDiagonalTailChunk000Sub001Block184Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part013] using hcert

def TailChunk000Sub001Block184Part014SupportExplicit : Finset ℕ :=
  ([15863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part014 : ℚ :=
  (6775132025 : ℚ) / 5253590368743994368

def SurrogateDiagonalTailChunk000Sub001Block184Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15863
    = surrogateDiagTailX0RatChunk000Sub001Block184Part014

theorem surrogateDiagonalTailChunk000Sub001Block184Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part014] using hcert

def TailChunk000Sub001Block184Part015SupportExplicit : Finset ℕ :=
  ([15865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part015 : ℚ :=
  (167440950275 : ℚ) / 6378215810863435776

def SurrogateDiagonalTailChunk000Sub001Block184Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15865
    = surrogateDiagTailX0RatChunk000Sub001Block184Part015

theorem surrogateDiagonalTailChunk000Sub001Block184Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part015] using hcert

def TailChunk000Sub001Block184Part016SupportExplicit : Finset ℕ :=
  ([15866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block184Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15866
    = surrogateDiagTailX0RatChunk000Sub001Block184Part016

theorem surrogateDiagonalTailChunk000Sub001Block184Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part016] using hcert

def TailChunk000Sub001Block184Part017SupportExplicit : Finset ℕ :=
  ([15869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part017 : ℚ :=
  (321795465875 : ℚ) / 42721007563862489664

def SurrogateDiagonalTailChunk000Sub001Block184Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15869
    = surrogateDiagTailX0RatChunk000Sub001Block184Part017

theorem surrogateDiagonalTailChunk000Sub001Block184Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part017] using hcert

def TailChunk000Sub001Block184Part018SupportExplicit : Finset ℕ :=
  ([15871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part018 : ℚ :=
  (51580342925 : ℚ) / 72987420226577409024

def SurrogateDiagonalTailChunk000Sub001Block184Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15871
    = surrogateDiagTailX0RatChunk000Sub001Block184Part018

theorem surrogateDiagonalTailChunk000Sub001Block184Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part018] using hcert

def TailChunk000Sub001Block184Part019SupportExplicit : Finset ℕ :=
  ([15873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part019 : ℚ :=
  (3311761667 : ℚ) / 27868386463580160

def SurrogateDiagonalTailChunk000Sub001Block184Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15873
    = surrogateDiagTailX0RatChunk000Sub001Block184Part019

theorem surrogateDiagonalTailChunk000Sub001Block184Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part019] using hcert

def TailChunk000Sub001Block184Part020SupportExplicit : Finset ℕ :=
  ([15874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part020 : ℚ :=
  (984312015625 : ℚ) / 2479553619167281152

def SurrogateDiagonalTailChunk000Sub001Block184Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15874
    = surrogateDiagTailX0RatChunk000Sub001Block184Part020

theorem surrogateDiagonalTailChunk000Sub001Block184Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part020] using hcert

def TailChunk000Sub001Block184Part021SupportExplicit : Finset ℕ :=
  ([15877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block184Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15877
    = surrogateDiagTailX0RatChunk000Sub001Block184Part021

theorem surrogateDiagonalTailChunk000Sub001Block184Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part021] using hcert

def TailChunk000Sub001Block184Part022SupportExplicit : Finset ℕ :=
  ([15878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part022 : ℚ :=
  (150659364675 : ℚ) / 321987650093514752

def SurrogateDiagonalTailChunk000Sub001Block184Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15878
    = surrogateDiagTailX0RatChunk000Sub001Block184Part022

theorem surrogateDiagonalTailChunk000Sub001Block184Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part022] using hcert

def TailChunk000Sub001Block184Part023SupportExplicit : Finset ℕ :=
  ([15879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part023 : ℚ :=
  (1745072254075 : ℚ) / 28099655432333641728

def SurrogateDiagonalTailChunk000Sub001Block184Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15879
    = surrogateDiagTailX0RatChunk000Sub001Block184Part023

theorem surrogateDiagonalTailChunk000Sub001Block184Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part023] using hcert

def TailChunk000Sub001Block184Part024SupportExplicit : Finset ℕ :=
  ([15881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block184Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block184Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15881
    = surrogateDiagTailX0RatChunk000Sub001Block184Part024

theorem surrogateDiagonalTailChunk000Sub001Block184Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block184Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block184Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block184Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block184Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block184Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block184Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block184HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block184Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block184Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block184Part000
    + surrogateDiagTailX0RatChunk000Sub001Block184Part001
    + surrogateDiagTailX0RatChunk000Sub001Block184Part002
    + surrogateDiagTailX0RatChunk000Sub001Block184Part003
    + surrogateDiagTailX0RatChunk000Sub001Block184Part004
    + surrogateDiagTailX0RatChunk000Sub001Block184Part005
    + surrogateDiagTailX0RatChunk000Sub001Block184Part006
    + surrogateDiagTailX0RatChunk000Sub001Block184Part007
    + surrogateDiagTailX0RatChunk000Sub001Block184Part008
    + surrogateDiagTailX0RatChunk000Sub001Block184Part009

def surrogateDiagonalTailChunk000Sub001Block184MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block184Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block184Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block184Part010
    + surrogateDiagTailX0RatChunk000Sub001Block184Part011
    + surrogateDiagTailX0RatChunk000Sub001Block184Part012
    + surrogateDiagTailX0RatChunk000Sub001Block184Part013
    + surrogateDiagTailX0RatChunk000Sub001Block184Part014
    + surrogateDiagTailX0RatChunk000Sub001Block184Part015
    + surrogateDiagTailX0RatChunk000Sub001Block184Part016
    + surrogateDiagTailX0RatChunk000Sub001Block184Part017
    + surrogateDiagTailX0RatChunk000Sub001Block184Part018
    + surrogateDiagTailX0RatChunk000Sub001Block184Part019

def surrogateDiagonalTailChunk000Sub001Block184TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block184Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block184Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block184Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block184Part020
    + surrogateDiagTailX0RatChunk000Sub001Block184Part021
    + surrogateDiagTailX0RatChunk000Sub001Block184Part022
    + surrogateDiagTailX0RatChunk000Sub001Block184Part023
    + surrogateDiagTailX0RatChunk000Sub001Block184Part024

def surrogateDiagonalTailChunk000Sub001Block184Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block184HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block184MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block184TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block184 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block184Part000
    + surrogateDiagTailX0RatChunk000Sub001Block184Part001
    + surrogateDiagTailX0RatChunk000Sub001Block184Part002
    + surrogateDiagTailX0RatChunk000Sub001Block184Part003
    + surrogateDiagTailX0RatChunk000Sub001Block184Part004
    + surrogateDiagTailX0RatChunk000Sub001Block184Part005
    + surrogateDiagTailX0RatChunk000Sub001Block184Part006
    + surrogateDiagTailX0RatChunk000Sub001Block184Part007
    + surrogateDiagTailX0RatChunk000Sub001Block184Part008
    + surrogateDiagTailX0RatChunk000Sub001Block184Part009
    + surrogateDiagTailX0RatChunk000Sub001Block184Part010
    + surrogateDiagTailX0RatChunk000Sub001Block184Part011
    + surrogateDiagTailX0RatChunk000Sub001Block184Part012
    + surrogateDiagTailX0RatChunk000Sub001Block184Part013
    + surrogateDiagTailX0RatChunk000Sub001Block184Part014
    + surrogateDiagTailX0RatChunk000Sub001Block184Part015
    + surrogateDiagTailX0RatChunk000Sub001Block184Part016
    + surrogateDiagTailX0RatChunk000Sub001Block184Part017
    + surrogateDiagTailX0RatChunk000Sub001Block184Part018
    + surrogateDiagTailX0RatChunk000Sub001Block184Part019
    + surrogateDiagTailX0RatChunk000Sub001Block184Part020
    + surrogateDiagTailX0RatChunk000Sub001Block184Part021
    + surrogateDiagTailX0RatChunk000Sub001Block184Part022
    + surrogateDiagTailX0RatChunk000Sub001Block184Part023
    + surrogateDiagTailX0RatChunk000Sub001Block184Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block184_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block184Head + surrogateDiagTailX0RatChunk000Sub001Block184Mid + surrogateDiagTailX0RatChunk000Sub001Block184Tail =
      surrogateDiagTailX0RatChunk000Sub001Block184 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block184Head surrogateDiagTailX0RatChunk000Sub001Block184Mid surrogateDiagTailX0RatChunk000Sub001Block184Tail surrogateDiagTailX0RatChunk000Sub001Block184
  ring

def SurrogateDiagonalTailChunk000Sub001Block184HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block184HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block184Head

def SurrogateDiagonalTailChunk000Sub001Block184MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block184MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block184Mid

def SurrogateDiagonalTailChunk000Sub001Block184TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block184TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block184Tail

theorem surrogateDiagonalTailChunk000Sub001Block184_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block184HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block184MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block184TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block184Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block184 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block184HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block184MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block184TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block184Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block184_eq_head_add_mid_add_tail

/-- Block 185 covers tail-support indices [9625,9650) and q from 15882 to 15922. -/

def TailChunk000Sub001Block185Part000SupportExplicit : Finset ℕ :=
  ([15882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part000 : ℚ :=
  (547221546775 : ℚ) / 490282294170023712

def SurrogateDiagonalTailChunk000Sub001Block185Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15882
    = surrogateDiagTailX0RatChunk000Sub001Block185Part000

theorem surrogateDiagonalTailChunk000Sub001Block185Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part000] using hcert

def TailChunk000Sub001Block185Part001SupportExplicit : Finset ℕ :=
  ([15883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part001 : ℚ :=
  (322362102575 : ℚ) / 42872031747432244224

def SurrogateDiagonalTailChunk000Sub001Block185Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15883
    = surrogateDiagTailX0RatChunk000Sub001Block185Part001

theorem surrogateDiagonalTailChunk000Sub001Block185Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part001] using hcert

def TailChunk000Sub001Block185Part002SupportExplicit : Finset ℕ :=
  ([15887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block185Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15887
    = surrogateDiagTailX0RatChunk000Sub001Block185Part002

theorem surrogateDiagonalTailChunk000Sub001Block185Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part002] using hcert

def TailChunk000Sub001Block185Part003SupportExplicit : Finset ℕ :=
  ([15889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block185Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15889
    = surrogateDiagTailX0RatChunk000Sub001Block185Part003

theorem surrogateDiagonalTailChunk000Sub001Block185Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part003] using hcert

def TailChunk000Sub001Block185Part004SupportExplicit : Finset ℕ :=
  ([15890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part004 : ℚ :=
  (570158502625 : ℚ) / 541060202833846272

def SurrogateDiagonalTailChunk000Sub001Block185Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15890
    = surrogateDiagTailX0RatChunk000Sub001Block185Part004

theorem surrogateDiagonalTailChunk000Sub001Block185Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part004] using hcert

def TailChunk000Sub001Block185Part005SupportExplicit : Finset ℕ :=
  ([15891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part005 : ℚ :=
  (438400263775 : ℚ) / 7868260970361126912

def SurrogateDiagonalTailChunk000Sub001Block185Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15891
    = surrogateDiagTailX0RatChunk000Sub001Block185Part005

theorem surrogateDiagonalTailChunk000Sub001Block185Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part005] using hcert

def TailChunk000Sub001Block185Part006SupportExplicit : Finset ℕ :=
  ([15893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part006 : ℚ :=
  (716361149 : ℚ) / 442580923232949600

def SurrogateDiagonalTailChunk000Sub001Block185Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15893
    = surrogateDiagTailX0RatChunk000Sub001Block185Part006

theorem surrogateDiagonalTailChunk000Sub001Block185Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part006] using hcert

def TailChunk000Sub001Block185Part007SupportExplicit : Finset ℕ :=
  ([15897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part007 : ℚ :=
  (190937741525 : ℚ) / 1881899884660948992

def SurrogateDiagonalTailChunk000Sub001Block185Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15897
    = surrogateDiagTailX0RatChunk000Sub001Block185Part007

theorem surrogateDiagonalTailChunk000Sub001Block185Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part007] using hcert

def TailChunk000Sub001Block185Part008SupportExplicit : Finset ℕ :=
  ([15898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part008 : ℚ :=
  (987290640625 : ℚ) / 2494584969640241952

def SurrogateDiagonalTailChunk000Sub001Block185Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15898
    = surrogateDiagTailX0RatChunk000Sub001Block185Part008

theorem surrogateDiagonalTailChunk000Sub001Block185Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part008] using hcert

def TailChunk000Sub001Block185Part009SupportExplicit : Finset ℕ :=
  ([15899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part009 : ℚ :=
  (62808338275 : ℚ) / 19270164246424685568

def SurrogateDiagonalTailChunk000Sub001Block185Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15899
    = surrogateDiagTailX0RatChunk000Sub001Block185Part009

theorem surrogateDiagonalTailChunk000Sub001Block185Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part009] using hcert

def TailChunk000Sub001Block185Part010SupportExplicit : Finset ℕ :=
  ([15901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block185Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15901
    = surrogateDiagTailX0RatChunk000Sub001Block185Part010

theorem surrogateDiagonalTailChunk000Sub001Block185Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part010] using hcert

def TailChunk000Sub001Block185Part011SupportExplicit : Finset ℕ :=
  ([15902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part011 : ℚ :=
  (63218401 : ℚ) / 159814196698050

def SurrogateDiagonalTailChunk000Sub001Block185Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15902
    = surrogateDiagTailX0RatChunk000Sub001Block185Part011

theorem surrogateDiagonalTailChunk000Sub001Block185Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part011] using hcert

def TailChunk000Sub001Block185Part012SupportExplicit : Finset ℕ :=
  ([15905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part012 : ℚ :=
  (5066206319 : ℚ) / 523679159740170240

def SurrogateDiagonalTailChunk000Sub001Block185Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15905
    = surrogateDiagTailX0RatChunk000Sub001Block185Part012

theorem surrogateDiagonalTailChunk000Sub001Block185Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part012] using hcert

def TailChunk000Sub001Block185Part013SupportExplicit : Finset ℕ :=
  ([15906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part013 : ℚ :=
  (2873672801 : ℚ) / 1966473216000000

def SurrogateDiagonalTailChunk000Sub001Block185Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15906
    = surrogateDiagTailX0RatChunk000Sub001Block185Part013

theorem surrogateDiagonalTailChunk000Sub001Block185Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part013] using hcert

def TailChunk000Sub001Block185Part014SupportExplicit : Finset ℕ :=
  ([15907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block185Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15907
    = surrogateDiagTailX0RatChunk000Sub001Block185Part014

theorem surrogateDiagonalTailChunk000Sub001Block185Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part014] using hcert

def TailChunk000Sub001Block185Part015SupportExplicit : Finset ℕ :=
  ([15909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part015 : ℚ :=
  (878787652475 : ℚ) / 15807956765753638464

def SurrogateDiagonalTailChunk000Sub001Block185Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15909
    = surrogateDiagTailX0RatChunk000Sub001Block185Part015

theorem surrogateDiagonalTailChunk000Sub001Block185Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part015] using hcert

def TailChunk000Sub001Block185Part016SupportExplicit : Finset ℕ :=
  ([15910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part016 : ℚ :=
  (95169055075 : ℚ) / 119485706962599936

def SurrogateDiagonalTailChunk000Sub001Block185Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15910
    = surrogateDiagTailX0RatChunk000Sub001Block185Part016

theorem surrogateDiagonalTailChunk000Sub001Block185Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part016] using hcert

def TailChunk000Sub001Block185Part017SupportExplicit : Finset ℕ :=
  ([15911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part017 : ℚ :=
  (53853304225 : ℚ) / 4797253445763465216

def SurrogateDiagonalTailChunk000Sub001Block185Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15911
    = surrogateDiagTailX0RatChunk000Sub001Block185Part017

theorem surrogateDiagonalTailChunk000Sub001Block185Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part017] using hcert

def TailChunk000Sub001Block185Part018SupportExplicit : Finset ℕ :=
  ([15913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block185Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15913
    = surrogateDiagTailX0RatChunk000Sub001Block185Part018

theorem surrogateDiagonalTailChunk000Sub001Block185Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part018] using hcert

def TailChunk000Sub001Block185Part019SupportExplicit : Finset ℕ :=
  ([15914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part019 : ℚ :=
  (958652571475 : ℚ) / 2285556044844367872

def SurrogateDiagonalTailChunk000Sub001Block185Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15914
    = surrogateDiagTailX0RatChunk000Sub001Block185Part019

theorem surrogateDiagonalTailChunk000Sub001Block185Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part019] using hcert

def TailChunk000Sub001Block185Part020SupportExplicit : Finset ℕ :=
  ([15915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part020 : ℚ :=
  (15475341553 : ℚ) / 129303496232140800

def SurrogateDiagonalTailChunk000Sub001Block185Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15915
    = surrogateDiagTailX0RatChunk000Sub001Block185Part020

theorem surrogateDiagonalTailChunk000Sub001Block185Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part020] using hcert

def TailChunk000Sub001Block185Part021SupportExplicit : Finset ℕ :=
  ([15917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part021 : ℚ :=
  (15800699383 : ℚ) / 4372804104999811200

def SurrogateDiagonalTailChunk000Sub001Block185Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15917
    = surrogateDiagTailX0RatChunk000Sub001Block185Part021

theorem surrogateDiagonalTailChunk000Sub001Block185Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part021] using hcert

def TailChunk000Sub001Block185Part022SupportExplicit : Finset ℕ :=
  ([15918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part022 : ℚ :=
  (259556480725 : ℚ) / 151224097874540544

def SurrogateDiagonalTailChunk000Sub001Block185Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15918
    = surrogateDiagTailX0RatChunk000Sub001Block185Part022

theorem surrogateDiagonalTailChunk000Sub001Block185Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part022] using hcert

def TailChunk000Sub001Block185Part023SupportExplicit : Finset ℕ :=
  ([15919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block185Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15919
    = surrogateDiagTailX0RatChunk000Sub001Block185Part023

theorem surrogateDiagonalTailChunk000Sub001Block185Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part023] using hcert

def TailChunk000Sub001Block185Part024SupportExplicit : Finset ℕ :=
  ([15922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block185Part024 : ℚ :=
  (1221503213275 : ℚ) / 2671165222095655296

def SurrogateDiagonalTailChunk000Sub001Block185Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15922
    = surrogateDiagTailX0RatChunk000Sub001Block185Part024

theorem surrogateDiagonalTailChunk000Sub001Block185Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block185Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block185Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block185Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block185Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block185Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block185Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block185HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block185Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block185Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block185Part000
    + surrogateDiagTailX0RatChunk000Sub001Block185Part001
    + surrogateDiagTailX0RatChunk000Sub001Block185Part002
    + surrogateDiagTailX0RatChunk000Sub001Block185Part003
    + surrogateDiagTailX0RatChunk000Sub001Block185Part004
    + surrogateDiagTailX0RatChunk000Sub001Block185Part005
    + surrogateDiagTailX0RatChunk000Sub001Block185Part006
    + surrogateDiagTailX0RatChunk000Sub001Block185Part007
    + surrogateDiagTailX0RatChunk000Sub001Block185Part008
    + surrogateDiagTailX0RatChunk000Sub001Block185Part009

def surrogateDiagonalTailChunk000Sub001Block185MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block185Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block185Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block185Part010
    + surrogateDiagTailX0RatChunk000Sub001Block185Part011
    + surrogateDiagTailX0RatChunk000Sub001Block185Part012
    + surrogateDiagTailX0RatChunk000Sub001Block185Part013
    + surrogateDiagTailX0RatChunk000Sub001Block185Part014
    + surrogateDiagTailX0RatChunk000Sub001Block185Part015
    + surrogateDiagTailX0RatChunk000Sub001Block185Part016
    + surrogateDiagTailX0RatChunk000Sub001Block185Part017
    + surrogateDiagTailX0RatChunk000Sub001Block185Part018
    + surrogateDiagTailX0RatChunk000Sub001Block185Part019

def surrogateDiagonalTailChunk000Sub001Block185TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block185Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block185Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block185Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block185Part020
    + surrogateDiagTailX0RatChunk000Sub001Block185Part021
    + surrogateDiagTailX0RatChunk000Sub001Block185Part022
    + surrogateDiagTailX0RatChunk000Sub001Block185Part023
    + surrogateDiagTailX0RatChunk000Sub001Block185Part024

def surrogateDiagonalTailChunk000Sub001Block185Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block185HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block185MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block185TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block185 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block185Part000
    + surrogateDiagTailX0RatChunk000Sub001Block185Part001
    + surrogateDiagTailX0RatChunk000Sub001Block185Part002
    + surrogateDiagTailX0RatChunk000Sub001Block185Part003
    + surrogateDiagTailX0RatChunk000Sub001Block185Part004
    + surrogateDiagTailX0RatChunk000Sub001Block185Part005
    + surrogateDiagTailX0RatChunk000Sub001Block185Part006
    + surrogateDiagTailX0RatChunk000Sub001Block185Part007
    + surrogateDiagTailX0RatChunk000Sub001Block185Part008
    + surrogateDiagTailX0RatChunk000Sub001Block185Part009
    + surrogateDiagTailX0RatChunk000Sub001Block185Part010
    + surrogateDiagTailX0RatChunk000Sub001Block185Part011
    + surrogateDiagTailX0RatChunk000Sub001Block185Part012
    + surrogateDiagTailX0RatChunk000Sub001Block185Part013
    + surrogateDiagTailX0RatChunk000Sub001Block185Part014
    + surrogateDiagTailX0RatChunk000Sub001Block185Part015
    + surrogateDiagTailX0RatChunk000Sub001Block185Part016
    + surrogateDiagTailX0RatChunk000Sub001Block185Part017
    + surrogateDiagTailX0RatChunk000Sub001Block185Part018
    + surrogateDiagTailX0RatChunk000Sub001Block185Part019
    + surrogateDiagTailX0RatChunk000Sub001Block185Part020
    + surrogateDiagTailX0RatChunk000Sub001Block185Part021
    + surrogateDiagTailX0RatChunk000Sub001Block185Part022
    + surrogateDiagTailX0RatChunk000Sub001Block185Part023
    + surrogateDiagTailX0RatChunk000Sub001Block185Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block185_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block185Head + surrogateDiagTailX0RatChunk000Sub001Block185Mid + surrogateDiagTailX0RatChunk000Sub001Block185Tail =
      surrogateDiagTailX0RatChunk000Sub001Block185 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block185Head surrogateDiagTailX0RatChunk000Sub001Block185Mid surrogateDiagTailX0RatChunk000Sub001Block185Tail surrogateDiagTailX0RatChunk000Sub001Block185
  ring

def SurrogateDiagonalTailChunk000Sub001Block185HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block185HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block185Head

def SurrogateDiagonalTailChunk000Sub001Block185MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block185MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block185Mid

def SurrogateDiagonalTailChunk000Sub001Block185TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block185TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block185Tail

theorem surrogateDiagonalTailChunk000Sub001Block185_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block185HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block185MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block185TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block185Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block185 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block185HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block185MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block185TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block185Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block185_eq_head_add_mid_add_tail

/-- Block 186 covers tail-support indices [9650,9675) and q from 15923 to 15962. -/

def TailChunk000Sub001Block186Part000SupportExplicit : Finset ℕ :=
  ([15923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block186Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15923
    = surrogateDiagTailX0RatChunk000Sub001Block186Part000

theorem surrogateDiagonalTailChunk000Sub001Block186Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part000] using hcert

def TailChunk000Sub001Block186Part001SupportExplicit : Finset ℕ :=
  ([15926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part001 : ℚ :=
  (990771390625 : ℚ) / 2512207804955982642

def SurrogateDiagonalTailChunk000Sub001Block186Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15926
    = surrogateDiagTailX0RatChunk000Sub001Block186Part001

theorem surrogateDiagonalTailChunk000Sub001Block186Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part001] using hcert

def TailChunk000Sub001Block186Part002SupportExplicit : Finset ℕ :=
  ([15927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part002 : ℚ :=
  (110097128425 : ℚ) / 1984954315026949248

def SurrogateDiagonalTailChunk000Sub001Block186Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15927
    = surrogateDiagTailX0RatChunk000Sub001Block186Part002

theorem surrogateDiagonalTailChunk000Sub001Block186Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part002] using hcert

def TailChunk000Sub001Block186Part003SupportExplicit : Finset ℕ :=
  ([15929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part003 : ℚ :=
  (278559616525 : ℚ) / 125779592815614885888

def SurrogateDiagonalTailChunk000Sub001Block186Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15929
    = surrogateDiagTailX0RatChunk000Sub001Block186Part003

theorem surrogateDiagonalTailChunk000Sub001Block186Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part003] using hcert

def TailChunk000Sub001Block186Part004SupportExplicit : Finset ℕ :=
  ([15931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part004 : ℚ :=
  (41517915125 : ℚ) / 75267512099725000704

def SurrogateDiagonalTailChunk000Sub001Block186Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15931
    = surrogateDiagTailX0RatChunk000Sub001Block186Part004

theorem surrogateDiagonalTailChunk000Sub001Block186Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part004] using hcert

def TailChunk000Sub001Block186Part005SupportExplicit : Finset ℕ :=
  ([15933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part005 : ℚ :=
  (251014846225 : ℚ) / 4026727298450325504

def SurrogateDiagonalTailChunk000Sub001Block186Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15933
    = surrogateDiagTailX0RatChunk000Sub001Block186Part005

theorem surrogateDiagonalTailChunk000Sub001Block186Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part005] using hcert

def TailChunk000Sub001Block186Part006SupportExplicit : Finset ℕ :=
  ([15934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part006 : ℚ :=
  (150802544017 : ℚ) / 347961929446195200

def SurrogateDiagonalTailChunk000Sub001Block186Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15934
    = surrogateDiagTailX0RatChunk000Sub001Block186Part006

theorem surrogateDiagonalTailChunk000Sub001Block186Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part006] using hcert

def TailChunk000Sub001Block186Part007SupportExplicit : Finset ℕ :=
  ([15935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part007 : ℚ :=
  (423273634675 : ℚ) / 21985110629343369216

def SurrogateDiagonalTailChunk000Sub001Block186Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15935
    = surrogateDiagTailX0RatChunk000Sub001Block186Part007

theorem surrogateDiagonalTailChunk000Sub001Block186Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part007] using hcert

def TailChunk000Sub001Block186Part008SupportExplicit : Finset ℕ :=
  ([15937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block186Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15937
    = surrogateDiagTailX0RatChunk000Sub001Block186Part008

theorem surrogateDiagonalTailChunk000Sub001Block186Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part008] using hcert

def TailChunk000Sub001Block186Part009SupportExplicit : Finset ℕ :=
  ([15938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part009 : ℚ :=
  (27649169075 : ℚ) / 56826062153922816

def SurrogateDiagonalTailChunk000Sub001Block186Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15938
    = surrogateDiagTailX0RatChunk000Sub001Block186Part009

theorem surrogateDiagonalTailChunk000Sub001Block186Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part009] using hcert

def TailChunk000Sub001Block186Part010SupportExplicit : Finset ℕ :=
  ([15941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part010 : ℚ :=
  (134350265675 : ℚ) / 64723643655336926784

def SurrogateDiagonalTailChunk000Sub001Block186Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15941
    = surrogateDiagTailX0RatChunk000Sub001Block186Part010

theorem surrogateDiagonalTailChunk000Sub001Block186Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part010] using hcert

def TailChunk000Sub001Block186Part011SupportExplicit : Finset ℕ :=
  ([15942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part011 : ℚ :=
  (1102728793925 : ℚ) / 995472182643523584

def SurrogateDiagonalTailChunk000Sub001Block186Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15942
    = surrogateDiagTailX0RatChunk000Sub001Block186Part011

theorem surrogateDiagonalTailChunk000Sub001Block186Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part011] using hcert

def TailChunk000Sub001Block186Part012SupportExplicit : Finset ℕ :=
  ([15943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part012 : ℚ :=
  (3314619225 : ℚ) / 6310822130258469632

def SurrogateDiagonalTailChunk000Sub001Block186Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15943
    = surrogateDiagTailX0RatChunk000Sub001Block186Part012

theorem surrogateDiagonalTailChunk000Sub001Block186Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part012] using hcert

def TailChunk000Sub001Block186Part013SupportExplicit : Finset ℕ :=
  ([15945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part013 : ℚ :=
  (229388144525 : ℚ) / 1628526713284694016

def SurrogateDiagonalTailChunk000Sub001Block186Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15945
    = surrogateDiagTailX0RatChunk000Sub001Block186Part013

theorem surrogateDiagonalTailChunk000Sub001Block186Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part013] using hcert

def TailChunk000Sub001Block186Part014SupportExplicit : Finset ℕ :=
  ([15946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part014 : ℚ :=
  (974159873275 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk000Sub001Block186Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15946
    = surrogateDiagTailX0RatChunk000Sub001Block186Part014

theorem surrogateDiagonalTailChunk000Sub001Block186Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part014] using hcert

def TailChunk000Sub001Block186Part015SupportExplicit : Finset ℕ :=
  ([15947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part015 : ℚ :=
  (1104836849 : ℚ) / 1148684262997616640

def SurrogateDiagonalTailChunk000Sub001Block186Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15947
    = surrogateDiagTailX0RatChunk000Sub001Block186Part015

theorem surrogateDiagonalTailChunk000Sub001Block186Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part015] using hcert

def TailChunk000Sub001Block186Part016SupportExplicit : Finset ℕ :=
  ([15949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part016 : ℚ :=
  (1793710629 : ℚ) / 1934338443535974400

def SurrogateDiagonalTailChunk000Sub001Block186Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15949
    = surrogateDiagTailX0RatChunk000Sub001Block186Part016

theorem surrogateDiagonalTailChunk000Sub001Block186Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part016] using hcert

def TailChunk000Sub001Block186Part017SupportExplicit : Finset ℕ :=
  ([15951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part017 : ℚ :=
  (64310999725 : ℚ) / 5747149397097971712

def SurrogateDiagonalTailChunk000Sub001Block186Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15951
    = surrogateDiagTailX0RatChunk000Sub001Block186Part017

theorem surrogateDiagonalTailChunk000Sub001Block186Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part017] using hcert

def TailChunk000Sub001Block186Part018SupportExplicit : Finset ℕ :=
  ([15953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part018 : ℚ :=
  (770873944375 : ℚ) / 73729688073801596928

def SurrogateDiagonalTailChunk000Sub001Block186Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15953
    = surrogateDiagTailX0RatChunk000Sub001Block186Part018

theorem surrogateDiagonalTailChunk000Sub001Block186Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part018] using hcert

def TailChunk000Sub001Block186Part019SupportExplicit : Finset ℕ :=
  ([15954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part019 : ℚ :=
  (1766865734125 : ℚ) / 1996947962582410368

def SurrogateDiagonalTailChunk000Sub001Block186Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15954
    = surrogateDiagTailX0RatChunk000Sub001Block186Part019

theorem surrogateDiagonalTailChunk000Sub001Block186Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part019] using hcert

def TailChunk000Sub001Block186Part020SupportExplicit : Finset ℕ :=
  ([15955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part020 : ℚ :=
  (50920330609 : ℚ) / 2651487278393395200

def SurrogateDiagonalTailChunk000Sub001Block186Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15955
    = surrogateDiagTailX0RatChunk000Sub001Block186Part020

theorem surrogateDiagonalTailChunk000Sub001Block186Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part020] using hcert

def TailChunk000Sub001Block186Part021SupportExplicit : Finset ℕ :=
  ([15958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part021 : ℚ :=
  (38576684611 : ℚ) / 92556147528000000

def SurrogateDiagonalTailChunk000Sub001Block186Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15958
    = surrogateDiagTailX0RatChunk000Sub001Block186Part021

theorem surrogateDiagonalTailChunk000Sub001Block186Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part021] using hcert

def TailChunk000Sub001Block186Part022SupportExplicit : Finset ℕ :=
  ([15959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block186Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15959
    = surrogateDiagTailX0RatChunk000Sub001Block186Part022

theorem surrogateDiagonalTailChunk000Sub001Block186Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part022] using hcert

def TailChunk000Sub001Block186Part023SupportExplicit : Finset ℕ :=
  ([15961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part023 : ℚ :=
  (7045822863 : ℚ) / 1473796783750000000

def SurrogateDiagonalTailChunk000Sub001Block186Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15961
    = surrogateDiagTailX0RatChunk000Sub001Block186Part023

theorem surrogateDiagonalTailChunk000Sub001Block186Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part023] using hcert

def TailChunk000Sub001Block186Part024SupportExplicit : Finset ℕ :=
  ([15962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block186Part024 : ℚ :=
  (3733642201075 : ℚ) / 8395024682182435968

def SurrogateDiagonalTailChunk000Sub001Block186Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15962
    = surrogateDiagTailX0RatChunk000Sub001Block186Part024

theorem surrogateDiagonalTailChunk000Sub001Block186Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block186Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block186Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block186Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block186Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block186Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block186Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block186HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block186Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block186Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block186Part000
    + surrogateDiagTailX0RatChunk000Sub001Block186Part001
    + surrogateDiagTailX0RatChunk000Sub001Block186Part002
    + surrogateDiagTailX0RatChunk000Sub001Block186Part003
    + surrogateDiagTailX0RatChunk000Sub001Block186Part004
    + surrogateDiagTailX0RatChunk000Sub001Block186Part005
    + surrogateDiagTailX0RatChunk000Sub001Block186Part006
    + surrogateDiagTailX0RatChunk000Sub001Block186Part007
    + surrogateDiagTailX0RatChunk000Sub001Block186Part008
    + surrogateDiagTailX0RatChunk000Sub001Block186Part009

def surrogateDiagonalTailChunk000Sub001Block186MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block186Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block186Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block186Part010
    + surrogateDiagTailX0RatChunk000Sub001Block186Part011
    + surrogateDiagTailX0RatChunk000Sub001Block186Part012
    + surrogateDiagTailX0RatChunk000Sub001Block186Part013
    + surrogateDiagTailX0RatChunk000Sub001Block186Part014
    + surrogateDiagTailX0RatChunk000Sub001Block186Part015
    + surrogateDiagTailX0RatChunk000Sub001Block186Part016
    + surrogateDiagTailX0RatChunk000Sub001Block186Part017
    + surrogateDiagTailX0RatChunk000Sub001Block186Part018
    + surrogateDiagTailX0RatChunk000Sub001Block186Part019

def surrogateDiagonalTailChunk000Sub001Block186TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block186Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block186Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block186Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block186Part020
    + surrogateDiagTailX0RatChunk000Sub001Block186Part021
    + surrogateDiagTailX0RatChunk000Sub001Block186Part022
    + surrogateDiagTailX0RatChunk000Sub001Block186Part023
    + surrogateDiagTailX0RatChunk000Sub001Block186Part024

def surrogateDiagonalTailChunk000Sub001Block186Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block186HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block186MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block186TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block186 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block186Part000
    + surrogateDiagTailX0RatChunk000Sub001Block186Part001
    + surrogateDiagTailX0RatChunk000Sub001Block186Part002
    + surrogateDiagTailX0RatChunk000Sub001Block186Part003
    + surrogateDiagTailX0RatChunk000Sub001Block186Part004
    + surrogateDiagTailX0RatChunk000Sub001Block186Part005
    + surrogateDiagTailX0RatChunk000Sub001Block186Part006
    + surrogateDiagTailX0RatChunk000Sub001Block186Part007
    + surrogateDiagTailX0RatChunk000Sub001Block186Part008
    + surrogateDiagTailX0RatChunk000Sub001Block186Part009
    + surrogateDiagTailX0RatChunk000Sub001Block186Part010
    + surrogateDiagTailX0RatChunk000Sub001Block186Part011
    + surrogateDiagTailX0RatChunk000Sub001Block186Part012
    + surrogateDiagTailX0RatChunk000Sub001Block186Part013
    + surrogateDiagTailX0RatChunk000Sub001Block186Part014
    + surrogateDiagTailX0RatChunk000Sub001Block186Part015
    + surrogateDiagTailX0RatChunk000Sub001Block186Part016
    + surrogateDiagTailX0RatChunk000Sub001Block186Part017
    + surrogateDiagTailX0RatChunk000Sub001Block186Part018
    + surrogateDiagTailX0RatChunk000Sub001Block186Part019
    + surrogateDiagTailX0RatChunk000Sub001Block186Part020
    + surrogateDiagTailX0RatChunk000Sub001Block186Part021
    + surrogateDiagTailX0RatChunk000Sub001Block186Part022
    + surrogateDiagTailX0RatChunk000Sub001Block186Part023
    + surrogateDiagTailX0RatChunk000Sub001Block186Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block186_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block186Head + surrogateDiagTailX0RatChunk000Sub001Block186Mid + surrogateDiagTailX0RatChunk000Sub001Block186Tail =
      surrogateDiagTailX0RatChunk000Sub001Block186 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block186Head surrogateDiagTailX0RatChunk000Sub001Block186Mid surrogateDiagTailX0RatChunk000Sub001Block186Tail surrogateDiagTailX0RatChunk000Sub001Block186
  ring

def SurrogateDiagonalTailChunk000Sub001Block186HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block186HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block186Head

def SurrogateDiagonalTailChunk000Sub001Block186MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block186MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block186Mid

def SurrogateDiagonalTailChunk000Sub001Block186TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block186TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block186Tail

theorem surrogateDiagonalTailChunk000Sub001Block186_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block186HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block186MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block186TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block186Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block186 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block186HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block186MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block186TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block186Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block186_eq_head_add_mid_add_tail

/-- Block 187 covers tail-support indices [9675,9700) and q from 15963 to 16005. -/

def TailChunk000Sub001Block187Part000SupportExplicit : Finset ℕ :=
  ([15963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part000 : ℚ :=
  (437509749925 : ℚ) / 6211337916820488192

def SurrogateDiagonalTailChunk000Sub001Block187Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15963
    = surrogateDiagTailX0RatChunk000Sub001Block187Part000

theorem surrogateDiagonalTailChunk000Sub001Block187Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part000] using hcert

def TailChunk000Sub001Block187Part001SupportExplicit : Finset ℕ :=
  ([15965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part001 : ℚ :=
  (26711765801 : ℚ) / 1122490116620697600

def SurrogateDiagonalTailChunk000Sub001Block187Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15965
    = surrogateDiagTailX0RatChunk000Sub001Block187Part001

theorem surrogateDiagonalTailChunk000Sub001Block187Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part001] using hcert

def TailChunk000Sub001Block187Part002SupportExplicit : Finset ℕ :=
  ([15967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part002 : ℚ :=
  (13030896827 : ℚ) / 1751464116666777600

def SurrogateDiagonalTailChunk000Sub001Block187Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15967
    = surrogateDiagTailX0RatChunk000Sub001Block187Part002

theorem surrogateDiagonalTailChunk000Sub001Block187Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part002] using hcert

def TailChunk000Sub001Block187Part003SupportExplicit : Finset ℕ :=
  ([15969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part003 : ℚ :=
  (885427652225 : ℚ) / 16047830430938447424

def SurrogateDiagonalTailChunk000Sub001Block187Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15969
    = surrogateDiagTailX0RatChunk000Sub001Block187Part003

theorem surrogateDiagonalTailChunk000Sub001Block187Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part003] using hcert

def TailChunk000Sub001Block187Part004SupportExplicit : Finset ℕ :=
  ([15970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part004 : ℚ :=
  (409616292475 : ℚ) / 593335498288103424

def SurrogateDiagonalTailChunk000Sub001Block187Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15970
    = surrogateDiagTailX0RatChunk000Sub001Block187Part004

theorem surrogateDiagonalTailChunk000Sub001Block187Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part004] using hcert

def TailChunk000Sub001Block187Part005SupportExplicit : Finset ℕ :=
  ([15971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block187Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15971
    = surrogateDiagTailX0RatChunk000Sub001Block187Part005

theorem surrogateDiagonalTailChunk000Sub001Block187Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part005] using hcert

def TailChunk000Sub001Block187Part006SupportExplicit : Finset ℕ :=
  ([15973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block187Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15973
    = surrogateDiagTailX0RatChunk000Sub001Block187Part006

theorem surrogateDiagonalTailChunk000Sub001Block187Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part006] using hcert

def TailChunk000Sub001Block187Part007SupportExplicit : Finset ℕ :=
  ([15977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part007 : ℚ :=
  (63420469975 : ℚ) / 19651425529577914368

def SurrogateDiagonalTailChunk000Sub001Block187Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15977
    = surrogateDiagTailX0RatChunk000Sub001Block187Part007

theorem surrogateDiagonalTailChunk000Sub001Block187Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part007] using hcert

def TailChunk000Sub001Block187Part008SupportExplicit : Finset ℕ :=
  ([15978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part008 : ℚ :=
  (553857608275 : ℚ) / 502248969983415072

def SurrogateDiagonalTailChunk000Sub001Block187Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15978
    = surrogateDiagTailX0RatChunk000Sub001Block187Part008

theorem surrogateDiagonalTailChunk000Sub001Block187Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part008] using hcert

def TailChunk000Sub001Block187Part009SupportExplicit : Finset ℕ :=
  ([15981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part009 : ℚ :=
  (68017252603 : ℚ) / 691936441152307200

def SurrogateDiagonalTailChunk000Sub001Block187Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15981
    = surrogateDiagTailX0RatChunk000Sub001Block187Part009

theorem surrogateDiagonalTailChunk000Sub001Block187Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part009] using hcert

def TailChunk000Sub001Block187Part010SupportExplicit : Finset ℕ :=
  ([15982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part010 : ℚ :=
  (51476933273 : ℚ) / 123408196704000000

def SurrogateDiagonalTailChunk000Sub001Block187Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15982
    = surrogateDiagTailX0RatChunk000Sub001Block187Part010

theorem surrogateDiagonalTailChunk000Sub001Block187Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part010] using hcert

def TailChunk000Sub001Block187Part011SupportExplicit : Finset ℕ :=
  ([15983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part011 : ℚ :=
  (15931057093 : ℚ) / 4445834745567283200

def SurrogateDiagonalTailChunk000Sub001Block187Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15983
    = surrogateDiagTailX0RatChunk000Sub001Block187Part011

theorem surrogateDiagonalTailChunk000Sub001Block187Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part011] using hcert

def TailChunk000Sub001Block187Part012SupportExplicit : Finset ℕ :=
  ([15985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part012 : ℚ :=
  (85603844875 : ℚ) / 6042704871873871872

def SurrogateDiagonalTailChunk000Sub001Block187Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15985
    = surrogateDiagTailX0RatChunk000Sub001Block187Part012

theorem surrogateDiagonalTailChunk000Sub001Block187Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part012] using hcert

def TailChunk000Sub001Block187Part013SupportExplicit : Finset ℕ :=
  ([15986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part013 : ℚ :=
  (998250765625 : ℚ) / 2550285304832512512

def SurrogateDiagonalTailChunk000Sub001Block187Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15986
    = surrogateDiagTailX0RatChunk000Sub001Block187Part013

theorem surrogateDiagonalTailChunk000Sub001Block187Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part013] using hcert

def TailChunk000Sub001Block187Part014SupportExplicit : Finset ℕ :=
  ([15989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part014 : ℚ :=
  (3996430687 : ℚ) / 6015252760726147200

def SurrogateDiagonalTailChunk000Sub001Block187Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15989
    = surrogateDiagTailX0RatChunk000Sub001Block187Part014

theorem surrogateDiagonalTailChunk000Sub001Block187Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part014] using hcert

def TailChunk000Sub001Block187Part015SupportExplicit : Finset ℕ :=
  ([15990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part015 : ℚ :=
  (7275798953 : ℚ) / 2718452573798400

def SurrogateDiagonalTailChunk000Sub001Block187Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15990
    = surrogateDiagTailX0RatChunk000Sub001Block187Part015

theorem surrogateDiagonalTailChunk000Sub001Block187Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part015] using hcert

def TailChunk000Sub001Block187Part016SupportExplicit : Finset ℕ :=
  ([15991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block187Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15991
    = surrogateDiagTailX0RatChunk000Sub001Block187Part016

theorem surrogateDiagonalTailChunk000Sub001Block187Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part016] using hcert

def TailChunk000Sub001Block187Part017SupportExplicit : Finset ℕ :=
  ([15994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part017 : ℚ :=
  (423708283 : ℚ) / 842014156357440

def SurrogateDiagonalTailChunk000Sub001Block187Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15994
    = surrogateDiagTailX0RatChunk000Sub001Block187Part017

theorem surrogateDiagonalTailChunk000Sub001Block187Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part017] using hcert

def TailChunk000Sub001Block187Part018SupportExplicit : Finset ℕ :=
  ([15995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part018 : ℚ :=
  (1190057140825 : ℚ) / 35869985109335605248

def SurrogateDiagonalTailChunk000Sub001Block187Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15995
    = surrogateDiagTailX0RatChunk000Sub001Block187Part018

theorem surrogateDiagonalTailChunk000Sub001Block187Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part018] using hcert

def TailChunk000Sub001Block187Part019SupportExplicit : Finset ℕ :=
  ([15997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part019 : ℚ :=
  (11236109581 : ℚ) / 5117739727532851200

def SurrogateDiagonalTailChunk000Sub001Block187Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15997
    = surrogateDiagTailX0RatChunk000Sub001Block187Part019

theorem surrogateDiagonalTailChunk000Sub001Block187Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part019] using hcert

def TailChunk000Sub001Block187Part020SupportExplicit : Finset ℕ :=
  ([15998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part020 : ℚ :=
  (147984275107 : ℚ) / 326718729975859200

def SurrogateDiagonalTailChunk000Sub001Block187Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15998
    = surrogateDiagTailX0RatChunk000Sub001Block187Part020

theorem surrogateDiagonalTailChunk000Sub001Block187Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part020] using hcert

def TailChunk000Sub001Block187Part021SupportExplicit : Finset ℕ :=
  ([15999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part021 : ℚ :=
  (222189256775 : ℚ) / 4042196461087570176

def SurrogateDiagonalTailChunk000Sub001Block187Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15999
    = surrogateDiagTailX0RatChunk000Sub001Block187Part021

theorem surrogateDiagonalTailChunk000Sub001Block187Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part021] using hcert

def TailChunk000Sub001Block187Part022SupportExplicit : Finset ℕ :=
  ([16001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block187Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16001
    = surrogateDiagTailX0RatChunk000Sub001Block187Part022

theorem surrogateDiagonalTailChunk000Sub001Block187Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part022] using hcert

def TailChunk000Sub001Block187Part023SupportExplicit : Finset ℕ :=
  ([16003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part023 : ℚ :=
  (7635021617 : ℚ) / 2373571313226777600

def SurrogateDiagonalTailChunk000Sub001Block187Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16003
    = surrogateDiagTailX0RatChunk000Sub001Block187Part023

theorem surrogateDiagonalTailChunk000Sub001Block187Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part023] using hcert

def TailChunk000Sub001Block187Part024SupportExplicit : Finset ℕ :=
  ([16005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block187Part024 : ℚ :=
  (63780437161 : ℚ) / 347961929446195200

def SurrogateDiagonalTailChunk000Sub001Block187Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16005
    = surrogateDiagTailX0RatChunk000Sub001Block187Part024

theorem surrogateDiagonalTailChunk000Sub001Block187Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block187Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block187Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block187Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block187Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block187Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block187Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block187HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block187Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block187Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block187Part000
    + surrogateDiagTailX0RatChunk000Sub001Block187Part001
    + surrogateDiagTailX0RatChunk000Sub001Block187Part002
    + surrogateDiagTailX0RatChunk000Sub001Block187Part003
    + surrogateDiagTailX0RatChunk000Sub001Block187Part004
    + surrogateDiagTailX0RatChunk000Sub001Block187Part005
    + surrogateDiagTailX0RatChunk000Sub001Block187Part006
    + surrogateDiagTailX0RatChunk000Sub001Block187Part007
    + surrogateDiagTailX0RatChunk000Sub001Block187Part008
    + surrogateDiagTailX0RatChunk000Sub001Block187Part009

def surrogateDiagonalTailChunk000Sub001Block187MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block187Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block187Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block187Part010
    + surrogateDiagTailX0RatChunk000Sub001Block187Part011
    + surrogateDiagTailX0RatChunk000Sub001Block187Part012
    + surrogateDiagTailX0RatChunk000Sub001Block187Part013
    + surrogateDiagTailX0RatChunk000Sub001Block187Part014
    + surrogateDiagTailX0RatChunk000Sub001Block187Part015
    + surrogateDiagTailX0RatChunk000Sub001Block187Part016
    + surrogateDiagTailX0RatChunk000Sub001Block187Part017
    + surrogateDiagTailX0RatChunk000Sub001Block187Part018
    + surrogateDiagTailX0RatChunk000Sub001Block187Part019

def surrogateDiagonalTailChunk000Sub001Block187TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block187Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block187Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block187Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block187Part020
    + surrogateDiagTailX0RatChunk000Sub001Block187Part021
    + surrogateDiagTailX0RatChunk000Sub001Block187Part022
    + surrogateDiagTailX0RatChunk000Sub001Block187Part023
    + surrogateDiagTailX0RatChunk000Sub001Block187Part024

def surrogateDiagonalTailChunk000Sub001Block187Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block187HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block187MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block187TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block187 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block187Part000
    + surrogateDiagTailX0RatChunk000Sub001Block187Part001
    + surrogateDiagTailX0RatChunk000Sub001Block187Part002
    + surrogateDiagTailX0RatChunk000Sub001Block187Part003
    + surrogateDiagTailX0RatChunk000Sub001Block187Part004
    + surrogateDiagTailX0RatChunk000Sub001Block187Part005
    + surrogateDiagTailX0RatChunk000Sub001Block187Part006
    + surrogateDiagTailX0RatChunk000Sub001Block187Part007
    + surrogateDiagTailX0RatChunk000Sub001Block187Part008
    + surrogateDiagTailX0RatChunk000Sub001Block187Part009
    + surrogateDiagTailX0RatChunk000Sub001Block187Part010
    + surrogateDiagTailX0RatChunk000Sub001Block187Part011
    + surrogateDiagTailX0RatChunk000Sub001Block187Part012
    + surrogateDiagTailX0RatChunk000Sub001Block187Part013
    + surrogateDiagTailX0RatChunk000Sub001Block187Part014
    + surrogateDiagTailX0RatChunk000Sub001Block187Part015
    + surrogateDiagTailX0RatChunk000Sub001Block187Part016
    + surrogateDiagTailX0RatChunk000Sub001Block187Part017
    + surrogateDiagTailX0RatChunk000Sub001Block187Part018
    + surrogateDiagTailX0RatChunk000Sub001Block187Part019
    + surrogateDiagTailX0RatChunk000Sub001Block187Part020
    + surrogateDiagTailX0RatChunk000Sub001Block187Part021
    + surrogateDiagTailX0RatChunk000Sub001Block187Part022
    + surrogateDiagTailX0RatChunk000Sub001Block187Part023
    + surrogateDiagTailX0RatChunk000Sub001Block187Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block187_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block187Head + surrogateDiagTailX0RatChunk000Sub001Block187Mid + surrogateDiagTailX0RatChunk000Sub001Block187Tail =
      surrogateDiagTailX0RatChunk000Sub001Block187 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block187Head surrogateDiagTailX0RatChunk000Sub001Block187Mid surrogateDiagTailX0RatChunk000Sub001Block187Tail surrogateDiagTailX0RatChunk000Sub001Block187
  ring

def SurrogateDiagonalTailChunk000Sub001Block187HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block187HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block187Head

def SurrogateDiagonalTailChunk000Sub001Block187MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block187MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block187Mid

def SurrogateDiagonalTailChunk000Sub001Block187TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block187TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block187Tail

theorem surrogateDiagonalTailChunk000Sub001Block187_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block187HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block187MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block187TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block187Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block187 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block187HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block187MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block187TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block187Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block187_eq_head_add_mid_add_tail

/-- Block 188 covers tail-support indices [9700,9725) and q from 16006 to 16045. -/

def TailChunk000Sub001Block188Part000SupportExplicit : Finset ℕ :=
  ([16006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part000 : ℚ :=
  (154574076427 : ℚ) / 370224590112000000

def SurrogateDiagonalTailChunk000Sub001Block188Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16006
    = surrogateDiagTailX0RatChunk000Sub001Block188Part000

theorem surrogateDiagonalTailChunk000Sub001Block188Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part000] using hcert

def TailChunk000Sub001Block188Part001SupportExplicit : Finset ℕ :=
  ([16007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block188Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16007
    = surrogateDiagTailX0RatChunk000Sub001Block188Part001

theorem surrogateDiagonalTailChunk000Sub001Block188Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part001] using hcert

def TailChunk000Sub001Block188Part002SupportExplicit : Finset ℕ :=
  ([16009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part002 : ℚ :=
  (327484328375 : ℚ) / 44249337108260011584

def SurrogateDiagonalTailChunk000Sub001Block188Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16009
    = surrogateDiagTailX0RatChunk000Sub001Block188Part002

theorem surrogateDiagonalTailChunk000Sub001Block188Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part002] using hcert

def TailChunk000Sub001Block188Part003SupportExplicit : Finset ℕ :=
  ([16010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part003 : ℚ :=
  (38422643799 : ℚ) / 55935238144000000

def SurrogateDiagonalTailChunk000Sub001Block188Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16010
    = surrogateDiagTailX0RatChunk000Sub001Block188Part003

theorem surrogateDiagonalTailChunk000Sub001Block188Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part003] using hcert

def TailChunk000Sub001Block188Part004SupportExplicit : Finset ℕ :=
  ([16013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part004 : ℚ :=
  (91260200875 : ℚ) / 152233569026474398848

def SurrogateDiagonalTailChunk000Sub001Block188Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16013
    = surrogateDiagTailX0RatChunk000Sub001Block188Part004

theorem surrogateDiagonalTailChunk000Sub001Block188Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part004] using hcert

def TailChunk000Sub001Block188Part005SupportExplicit : Finset ℕ :=
  ([16014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part005 : ℚ :=
  (2048383358725 : ℚ) / 1552834479205122048

def SurrogateDiagonalTailChunk000Sub001Block188Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16014
    = surrogateDiagTailX0RatChunk000Sub001Block188Part005

theorem surrogateDiagonalTailChunk000Sub001Block188Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part005] using hcert

def TailChunk000Sub001Block188Part006SupportExplicit : Finset ℕ :=
  ([16015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part006 : ℚ :=
  (214017012375 : ℚ) / 22430082956882876416

def SurrogateDiagonalTailChunk000Sub001Block188Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16015
    = surrogateDiagTailX0RatChunk000Sub001Block188Part006

theorem surrogateDiagonalTailChunk000Sub001Block188Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part006] using hcert

def TailChunk000Sub001Block188Part007SupportExplicit : Finset ℕ :=
  ([16017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part007 : ℚ :=
  (472089791 : ℚ) / 6883950195376128

def SurrogateDiagonalTailChunk000Sub001Block188Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16017
    = surrogateDiagTailX0RatChunk000Sub001Block188Part007

theorem surrogateDiagonalTailChunk000Sub001Block188Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part007] using hcert

def TailChunk000Sub001Block188Part008SupportExplicit : Finset ℕ :=
  ([16018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part008 : ℚ :=
  (1002251265625 : ℚ) / 2570769421316608512

def SurrogateDiagonalTailChunk000Sub001Block188Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16018
    = surrogateDiagTailX0RatChunk000Sub001Block188Part008

theorem surrogateDiagonalTailChunk000Sub001Block188Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part008] using hcert

def TailChunk000Sub001Block188Part009SupportExplicit : Finset ℕ :=
  ([16019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part009 : ℚ :=
  (85131147625 : ℚ) / 153633945267782811648

def SurrogateDiagonalTailChunk000Sub001Block188Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16019
    = surrogateDiagTailX0RatChunk000Sub001Block188Part009

theorem surrogateDiagonalTailChunk000Sub001Block188Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part009] using hcert

def TailChunk000Sub001Block188Part010SupportExplicit : Finset ℕ :=
  ([16021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part010 : ℚ :=
  (16766657225 : ℚ) / 16252842985559949312

def SurrogateDiagonalTailChunk000Sub001Block188Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16021
    = surrogateDiagTailX0RatChunk000Sub001Block188Part010

theorem surrogateDiagonalTailChunk000Sub001Block188Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part010] using hcert

def TailChunk000Sub001Block188Part011SupportExplicit : Finset ℕ :=
  ([16022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part011 : ℚ :=
  (1604403025 : ℚ) / 4117341735696402

def SurrogateDiagonalTailChunk000Sub001Block188Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16022
    = surrogateDiagTailX0RatChunk000Sub001Block188Part011

theorem surrogateDiagonalTailChunk000Sub001Block188Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part011] using hcert

def TailChunk000Sub001Block188Part012SupportExplicit : Finset ℕ :=
  ([16026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part012 : ℚ :=
  (22287625657 : ℚ) / 20332551781216800

def SurrogateDiagonalTailChunk000Sub001Block188Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16026
    = surrogateDiagTailX0RatChunk000Sub001Block188Part012

theorem surrogateDiagonalTailChunk000Sub001Block188Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part012] using hcert

def TailChunk000Sub001Block188Part013SupportExplicit : Finset ℕ :=
  ([16027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part013 : ℚ :=
  (5782837321 : ℚ) / 906866176968000000

def SurrogateDiagonalTailChunk000Sub001Block188Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16027
    = surrogateDiagTailX0RatChunk000Sub001Block188Part013

theorem surrogateDiagonalTailChunk000Sub001Block188Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part013] using hcert

def TailChunk000Sub001Block188Part014SupportExplicit : Finset ℕ :=
  ([16030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part014 : ℚ :=
  (2483681656975 : ℚ) / 2241874069333475328

def SurrogateDiagonalTailChunk000Sub001Block188Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16030
    = surrogateDiagTailX0RatChunk000Sub001Block188Part014

theorem surrogateDiagonalTailChunk000Sub001Block188Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part014] using hcert

def TailChunk000Sub001Block188Part015SupportExplicit : Finset ℕ :=
  ([16031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part015 : ℚ :=
  (10867688459 : ℚ) / 1965474771999129600

def SurrogateDiagonalTailChunk000Sub001Block188Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16031
    = surrogateDiagTailX0RatChunk000Sub001Block188Part015

theorem surrogateDiagonalTailChunk000Sub001Block188Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part015] using hcert

def TailChunk000Sub001Block188Part016SupportExplicit : Finset ℕ :=
  ([16033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block188Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16033
    = surrogateDiagTailX0RatChunk000Sub001Block188Part016

theorem surrogateDiagonalTailChunk000Sub001Block188Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part016] using hcert

def TailChunk000Sub001Block188Part017SupportExplicit : Finset ℕ :=
  ([16034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block188Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16034
    = surrogateDiagTailX0RatChunk000Sub001Block188Part017

theorem surrogateDiagonalTailChunk000Sub001Block188Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part017] using hcert

def TailChunk000Sub001Block188Part018SupportExplicit : Finset ℕ :=
  ([16035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part018 : ℚ :=
  (463967765575 : ℚ) / 3331285283834560512

def SurrogateDiagonalTailChunk000Sub001Block188Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16035
    = surrogateDiagTailX0RatChunk000Sub001Block188Part018

theorem surrogateDiagonalTailChunk000Sub001Block188Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part018] using hcert

def TailChunk000Sub001Block188Part019SupportExplicit : Finset ℕ :=
  ([16037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part019 : ℚ :=
  (790392134725 : ℚ) / 73729688073801596928

def SurrogateDiagonalTailChunk000Sub001Block188Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16037
    = surrogateDiagTailX0RatChunk000Sub001Block188Part019

theorem surrogateDiagonalTailChunk000Sub001Block188Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part019] using hcert

def TailChunk000Sub001Block188Part020SupportExplicit : Finset ℕ :=
  ([16039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part020 : ℚ :=
  (125368257625 : ℚ) / 149003263321498994688

def SurrogateDiagonalTailChunk000Sub001Block188Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16039
    = surrogateDiagTailX0RatChunk000Sub001Block188Part020

theorem surrogateDiagonalTailChunk000Sub001Block188Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part020] using hcert

def TailChunk000Sub001Block188Part021SupportExplicit : Finset ℕ :=
  ([16041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part021 : ℚ :=
  (893428651925 : ℚ) / 16339270533479682624

def SurrogateDiagonalTailChunk000Sub001Block188Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16041
    = surrogateDiagTailX0RatChunk000Sub001Block188Part021

theorem surrogateDiagonalTailChunk000Sub001Block188Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part021] using hcert

def TailChunk000Sub001Block188Part022SupportExplicit : Finset ℕ :=
  ([16042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part022 : ℚ :=
  (3018978925 : ℚ) / 116652679178821632

def SurrogateDiagonalTailChunk000Sub001Block188Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16042
    = surrogateDiagTailX0RatChunk000Sub001Block188Part022

theorem surrogateDiagonalTailChunk000Sub001Block188Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part022] using hcert

def TailChunk000Sub001Block188Part023SupportExplicit : Finset ℕ :=
  ([16043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part023 : ℚ :=
  (666525361 : ℚ) / 1017995285321395200

def SurrogateDiagonalTailChunk000Sub001Block188Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16043
    = surrogateDiagTailX0RatChunk000Sub001Block188Part023

theorem surrogateDiagonalTailChunk000Sub001Block188Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part023] using hcert

def TailChunk000Sub001Block188Part024SupportExplicit : Finset ℕ :=
  ([16045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block188Part024 : ℚ :=
  (1287400880725 : ℚ) / 67796029914009305088

def SurrogateDiagonalTailChunk000Sub001Block188Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16045
    = surrogateDiagTailX0RatChunk000Sub001Block188Part024

theorem surrogateDiagonalTailChunk000Sub001Block188Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block188Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block188Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block188Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block188Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block188Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block188Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block188HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block188Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block188Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block188Part000
    + surrogateDiagTailX0RatChunk000Sub001Block188Part001
    + surrogateDiagTailX0RatChunk000Sub001Block188Part002
    + surrogateDiagTailX0RatChunk000Sub001Block188Part003
    + surrogateDiagTailX0RatChunk000Sub001Block188Part004
    + surrogateDiagTailX0RatChunk000Sub001Block188Part005
    + surrogateDiagTailX0RatChunk000Sub001Block188Part006
    + surrogateDiagTailX0RatChunk000Sub001Block188Part007
    + surrogateDiagTailX0RatChunk000Sub001Block188Part008
    + surrogateDiagTailX0RatChunk000Sub001Block188Part009

def surrogateDiagonalTailChunk000Sub001Block188MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block188Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block188Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block188Part010
    + surrogateDiagTailX0RatChunk000Sub001Block188Part011
    + surrogateDiagTailX0RatChunk000Sub001Block188Part012
    + surrogateDiagTailX0RatChunk000Sub001Block188Part013
    + surrogateDiagTailX0RatChunk000Sub001Block188Part014
    + surrogateDiagTailX0RatChunk000Sub001Block188Part015
    + surrogateDiagTailX0RatChunk000Sub001Block188Part016
    + surrogateDiagTailX0RatChunk000Sub001Block188Part017
    + surrogateDiagTailX0RatChunk000Sub001Block188Part018
    + surrogateDiagTailX0RatChunk000Sub001Block188Part019

def surrogateDiagonalTailChunk000Sub001Block188TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block188Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block188Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block188Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block188Part020
    + surrogateDiagTailX0RatChunk000Sub001Block188Part021
    + surrogateDiagTailX0RatChunk000Sub001Block188Part022
    + surrogateDiagTailX0RatChunk000Sub001Block188Part023
    + surrogateDiagTailX0RatChunk000Sub001Block188Part024

def surrogateDiagonalTailChunk000Sub001Block188Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block188HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block188MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block188TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block188 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block188Part000
    + surrogateDiagTailX0RatChunk000Sub001Block188Part001
    + surrogateDiagTailX0RatChunk000Sub001Block188Part002
    + surrogateDiagTailX0RatChunk000Sub001Block188Part003
    + surrogateDiagTailX0RatChunk000Sub001Block188Part004
    + surrogateDiagTailX0RatChunk000Sub001Block188Part005
    + surrogateDiagTailX0RatChunk000Sub001Block188Part006
    + surrogateDiagTailX0RatChunk000Sub001Block188Part007
    + surrogateDiagTailX0RatChunk000Sub001Block188Part008
    + surrogateDiagTailX0RatChunk000Sub001Block188Part009
    + surrogateDiagTailX0RatChunk000Sub001Block188Part010
    + surrogateDiagTailX0RatChunk000Sub001Block188Part011
    + surrogateDiagTailX0RatChunk000Sub001Block188Part012
    + surrogateDiagTailX0RatChunk000Sub001Block188Part013
    + surrogateDiagTailX0RatChunk000Sub001Block188Part014
    + surrogateDiagTailX0RatChunk000Sub001Block188Part015
    + surrogateDiagTailX0RatChunk000Sub001Block188Part016
    + surrogateDiagTailX0RatChunk000Sub001Block188Part017
    + surrogateDiagTailX0RatChunk000Sub001Block188Part018
    + surrogateDiagTailX0RatChunk000Sub001Block188Part019
    + surrogateDiagTailX0RatChunk000Sub001Block188Part020
    + surrogateDiagTailX0RatChunk000Sub001Block188Part021
    + surrogateDiagTailX0RatChunk000Sub001Block188Part022
    + surrogateDiagTailX0RatChunk000Sub001Block188Part023
    + surrogateDiagTailX0RatChunk000Sub001Block188Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block188_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block188Head + surrogateDiagTailX0RatChunk000Sub001Block188Mid + surrogateDiagTailX0RatChunk000Sub001Block188Tail =
      surrogateDiagTailX0RatChunk000Sub001Block188 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block188Head surrogateDiagTailX0RatChunk000Sub001Block188Mid surrogateDiagTailX0RatChunk000Sub001Block188Tail surrogateDiagTailX0RatChunk000Sub001Block188
  ring

def SurrogateDiagonalTailChunk000Sub001Block188HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block188HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block188Head

def SurrogateDiagonalTailChunk000Sub001Block188MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block188MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block188Mid

def SurrogateDiagonalTailChunk000Sub001Block188TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block188TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block188Tail

theorem surrogateDiagonalTailChunk000Sub001Block188_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block188HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block188MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block188TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block188Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block188 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block188HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block188MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block188TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block188Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block188_eq_head_add_mid_add_tail

/-- Block 189 covers tail-support indices [9725,9750) and q from 16046 to 16087. -/

def TailChunk000Sub001Block189Part000SupportExplicit : Finset ℕ :=
  ([16046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part000 : ℚ :=
  (12963427 : ℚ) / 2159300335632384

def SurrogateDiagonalTailChunk000Sub001Block189Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16046
    = surrogateDiagTailX0RatChunk000Sub001Block189Part000

theorem surrogateDiagonalTailChunk000Sub001Block189Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part000] using hcert

def TailChunk000Sub001Block189Part001SupportExplicit : Finset ℕ :=
  ([16049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part001 : ℚ :=
  (21369968749 : ℚ) / 4519776358212739200

def SurrogateDiagonalTailChunk000Sub001Block189Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16049
    = surrogateDiagTailX0RatChunk000Sub001Block189Part001

theorem surrogateDiagonalTailChunk000Sub001Block189Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part001] using hcert

def TailChunk000Sub001Block189Part002SupportExplicit : Finset ℕ :=
  ([16051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part002 : ℚ :=
  (329200735175 : ℚ) / 44715729256567317504

def SurrogateDiagonalTailChunk000Sub001Block189Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16051
    = surrogateDiagTailX0RatChunk000Sub001Block189Part002

theorem surrogateDiagonalTailChunk000Sub001Block189Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part002] using hcert

def TailChunk000Sub001Block189Part003SupportExplicit : Finset ℕ :=
  ([16053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part003 : ℚ :=
  (1431625043 : ℚ) / 26221163384040000

def SurrogateDiagonalTailChunk000Sub001Block189Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16053
    = surrogateDiagTailX0RatChunk000Sub001Block189Part003

theorem surrogateDiagonalTailChunk000Sub001Block189Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part003] using hcert

def TailChunk000Sub001Block189Part004SupportExplicit : Finset ℕ :=
  ([16054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part004 : ℚ :=
  (112553748475 : ℚ) / 8590818781994600448

def SurrogateDiagonalTailChunk000Sub001Block189Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16054
    = surrogateDiagTailX0RatChunk000Sub001Block189Part004

theorem surrogateDiagonalTailChunk000Sub001Block189Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part004] using hcert

def TailChunk000Sub001Block189Part005SupportExplicit : Finset ℕ :=
  ([16057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block189Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16057
    = surrogateDiagTailX0RatChunk000Sub001Block189Part005

theorem surrogateDiagonalTailChunk000Sub001Block189Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part005] using hcert

def TailChunk000Sub001Block189Part006SupportExplicit : Finset ℕ :=
  ([16058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part006 : ℚ :=
  (717646751 : ℚ) / 6531653077401600

def SurrogateDiagonalTailChunk000Sub001Block189Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16058
    = surrogateDiagTailX0RatChunk000Sub001Block189Part006

theorem surrogateDiagonalTailChunk000Sub001Block189Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part006] using hcert

def TailChunk000Sub001Block189Part007SupportExplicit : Finset ℕ :=
  ([16059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part007 : ℚ :=
  (71334410929 : ℚ) / 1170092531712000000

def SurrogateDiagonalTailChunk000Sub001Block189Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16059
    = surrogateDiagTailX0RatChunk000Sub001Block189Part007

theorem surrogateDiagonalTailChunk000Sub001Block189Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part007] using hcert

def TailChunk000Sub001Block189Part008SupportExplicit : Finset ℕ :=
  ([16061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block189Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16061
    = surrogateDiagTailX0RatChunk000Sub001Block189Part008

theorem surrogateDiagonalTailChunk000Sub001Block189Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part008] using hcert

def TailChunk000Sub001Block189Part009SupportExplicit : Finset ℕ :=
  ([16062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part009 : ℚ :=
  (447783916475 : ℚ) / 1025796663760610304

def SurrogateDiagonalTailChunk000Sub001Block189Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16062
    = surrogateDiagTailX0RatChunk000Sub001Block189Part009

theorem surrogateDiagonalTailChunk000Sub001Block189Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part009] using hcert

def TailChunk000Sub001Block189Part010SupportExplicit : Finset ℕ :=
  ([16063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block189Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16063
    = surrogateDiagTailX0RatChunk000Sub001Block189Part010

theorem surrogateDiagonalTailChunk000Sub001Block189Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part010] using hcert

def TailChunk000Sub001Block189Part011SupportExplicit : Finset ℕ :=
  ([16066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part011 : ℚ :=
  (13448062675 : ℚ) / 1274081684275298304

def SurrogateDiagonalTailChunk000Sub001Block189Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16066
    = surrogateDiagTailX0RatChunk000Sub001Block189Part011

theorem surrogateDiagonalTailChunk000Sub001Block189Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part011] using hcert

def TailChunk000Sub001Block189Part012SupportExplicit : Finset ℕ :=
  ([16067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block189Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16067
    = surrogateDiagTailX0RatChunk000Sub001Block189Part012

theorem surrogateDiagonalTailChunk000Sub001Block189Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part012] using hcert

def TailChunk000Sub001Block189Part013SupportExplicit : Finset ℕ :=
  ([16069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block189Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16069
    = surrogateDiagTailX0RatChunk000Sub001Block189Part013

theorem surrogateDiagonalTailChunk000Sub001Block189Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part013] using hcert

def TailChunk000Sub001Block189Part014SupportExplicit : Finset ℕ :=
  ([16070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part014 : ℚ :=
  (60582940775 : ℚ) / 532303106829179136

def SurrogateDiagonalTailChunk000Sub001Block189Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16070
    = surrogateDiagTailX0RatChunk000Sub001Block189Part014

theorem surrogateDiagonalTailChunk000Sub001Block189Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part014] using hcert

def TailChunk000Sub001Block189Part015SupportExplicit : Finset ℕ :=
  ([16071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part015 : ℚ :=
  (1165501267 : ℚ) / 14879922166955520

def SurrogateDiagonalTailChunk000Sub001Block189Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16071
    = surrogateDiagTailX0RatChunk000Sub001Block189Part015

theorem surrogateDiagonalTailChunk000Sub001Block189Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part015] using hcert

def TailChunk000Sub001Block189Part016SupportExplicit : Finset ℕ :=
  ([16073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block189Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16073
    = surrogateDiagTailX0RatChunk000Sub001Block189Part016

theorem surrogateDiagonalTailChunk000Sub001Block189Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part016] using hcert

def TailChunk000Sub001Block189Part017SupportExplicit : Finset ℕ :=
  ([16077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part017 : ℚ :=
  (594386185125 : ℚ) / 9050409910249455616

def SurrogateDiagonalTailChunk000Sub001Block189Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16077
    = surrogateDiagTailX0RatChunk000Sub001Block189Part017

theorem surrogateDiagonalTailChunk000Sub001Block189Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part017] using hcert

def TailChunk000Sub001Block189Part018SupportExplicit : Finset ℕ :=
  ([16078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block189Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16078
    = surrogateDiagTailX0RatChunk000Sub001Block189Part018

theorem surrogateDiagonalTailChunk000Sub001Block189Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part018] using hcert

def TailChunk000Sub001Block189Part019SupportExplicit : Finset ℕ :=
  ([16079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part019 : ℚ :=
  (330347505875 : ℚ) / 45028699046380191744

def SurrogateDiagonalTailChunk000Sub001Block189Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16079
    = surrogateDiagTailX0RatChunk000Sub001Block189Part019

theorem surrogateDiagonalTailChunk000Sub001Block189Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part019] using hcert

def TailChunk000Sub001Block189Part020SupportExplicit : Finset ℕ :=
  ([16081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part020 : ℚ :=
  (192723928325 : ℚ) / 60505622078017388544

def SurrogateDiagonalTailChunk000Sub001Block189Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16081
    = surrogateDiagTailX0RatChunk000Sub001Block189Part020

theorem surrogateDiagonalTailChunk000Sub001Block189Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part020] using hcert

def TailChunk000Sub001Block189Part021SupportExplicit : Finset ℕ :=
  ([16082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part021 : ℚ :=
  (234193583 : ℚ) / 3237601502822400

def SurrogateDiagonalTailChunk000Sub001Block189Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16082
    = surrogateDiagTailX0RatChunk000Sub001Block189Part021

theorem surrogateDiagonalTailChunk000Sub001Block189Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part021] using hcert

def TailChunk000Sub001Block189Part022SupportExplicit : Finset ℕ :=
  ([16085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part022 : ℚ :=
  (647666785375 : ℚ) / 68474833434216235008

def SurrogateDiagonalTailChunk000Sub001Block189Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16085
    = surrogateDiagTailX0RatChunk000Sub001Block189Part022

theorem surrogateDiagonalTailChunk000Sub001Block189Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part022] using hcert

def TailChunk000Sub001Block189Part023SupportExplicit : Finset ℕ :=
  ([16086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part023 : ℚ :=
  (870030840325 : ℚ) / 1104092080409069568

def SurrogateDiagonalTailChunk000Sub001Block189Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16086
    = surrogateDiagTailX0RatChunk000Sub001Block189Part023

theorem surrogateDiagonalTailChunk000Sub001Block189Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part023] using hcert

def TailChunk000Sub001Block189Part024SupportExplicit : Finset ℕ :=
  ([16087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block189Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block189Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16087
    = surrogateDiagTailX0RatChunk000Sub001Block189Part024

theorem surrogateDiagonalTailChunk000Sub001Block189Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block189Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block189Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block189Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block189Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block189Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block189Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block189HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block189Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block189Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block189Part000
    + surrogateDiagTailX0RatChunk000Sub001Block189Part001
    + surrogateDiagTailX0RatChunk000Sub001Block189Part002
    + surrogateDiagTailX0RatChunk000Sub001Block189Part003
    + surrogateDiagTailX0RatChunk000Sub001Block189Part004
    + surrogateDiagTailX0RatChunk000Sub001Block189Part005
    + surrogateDiagTailX0RatChunk000Sub001Block189Part006
    + surrogateDiagTailX0RatChunk000Sub001Block189Part007
    + surrogateDiagTailX0RatChunk000Sub001Block189Part008
    + surrogateDiagTailX0RatChunk000Sub001Block189Part009

def surrogateDiagonalTailChunk000Sub001Block189MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block189Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block189Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block189Part010
    + surrogateDiagTailX0RatChunk000Sub001Block189Part011
    + surrogateDiagTailX0RatChunk000Sub001Block189Part012
    + surrogateDiagTailX0RatChunk000Sub001Block189Part013
    + surrogateDiagTailX0RatChunk000Sub001Block189Part014
    + surrogateDiagTailX0RatChunk000Sub001Block189Part015
    + surrogateDiagTailX0RatChunk000Sub001Block189Part016
    + surrogateDiagTailX0RatChunk000Sub001Block189Part017
    + surrogateDiagTailX0RatChunk000Sub001Block189Part018
    + surrogateDiagTailX0RatChunk000Sub001Block189Part019

def surrogateDiagonalTailChunk000Sub001Block189TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block189Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block189Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block189Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block189Part020
    + surrogateDiagTailX0RatChunk000Sub001Block189Part021
    + surrogateDiagTailX0RatChunk000Sub001Block189Part022
    + surrogateDiagTailX0RatChunk000Sub001Block189Part023
    + surrogateDiagTailX0RatChunk000Sub001Block189Part024

def surrogateDiagonalTailChunk000Sub001Block189Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block189HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block189MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block189TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block189 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block189Part000
    + surrogateDiagTailX0RatChunk000Sub001Block189Part001
    + surrogateDiagTailX0RatChunk000Sub001Block189Part002
    + surrogateDiagTailX0RatChunk000Sub001Block189Part003
    + surrogateDiagTailX0RatChunk000Sub001Block189Part004
    + surrogateDiagTailX0RatChunk000Sub001Block189Part005
    + surrogateDiagTailX0RatChunk000Sub001Block189Part006
    + surrogateDiagTailX0RatChunk000Sub001Block189Part007
    + surrogateDiagTailX0RatChunk000Sub001Block189Part008
    + surrogateDiagTailX0RatChunk000Sub001Block189Part009
    + surrogateDiagTailX0RatChunk000Sub001Block189Part010
    + surrogateDiagTailX0RatChunk000Sub001Block189Part011
    + surrogateDiagTailX0RatChunk000Sub001Block189Part012
    + surrogateDiagTailX0RatChunk000Sub001Block189Part013
    + surrogateDiagTailX0RatChunk000Sub001Block189Part014
    + surrogateDiagTailX0RatChunk000Sub001Block189Part015
    + surrogateDiagTailX0RatChunk000Sub001Block189Part016
    + surrogateDiagTailX0RatChunk000Sub001Block189Part017
    + surrogateDiagTailX0RatChunk000Sub001Block189Part018
    + surrogateDiagTailX0RatChunk000Sub001Block189Part019
    + surrogateDiagTailX0RatChunk000Sub001Block189Part020
    + surrogateDiagTailX0RatChunk000Sub001Block189Part021
    + surrogateDiagTailX0RatChunk000Sub001Block189Part022
    + surrogateDiagTailX0RatChunk000Sub001Block189Part023
    + surrogateDiagTailX0RatChunk000Sub001Block189Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block189_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block189Head + surrogateDiagTailX0RatChunk000Sub001Block189Mid + surrogateDiagTailX0RatChunk000Sub001Block189Tail =
      surrogateDiagTailX0RatChunk000Sub001Block189 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block189Head surrogateDiagTailX0RatChunk000Sub001Block189Mid surrogateDiagTailX0RatChunk000Sub001Block189Tail surrogateDiagTailX0RatChunk000Sub001Block189
  ring

def SurrogateDiagonalTailChunk000Sub001Block189HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block189HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block189Head

def SurrogateDiagonalTailChunk000Sub001Block189MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block189MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block189Mid

def SurrogateDiagonalTailChunk000Sub001Block189TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block189TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block189Tail

theorem surrogateDiagonalTailChunk000Sub001Block189_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block189HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block189MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block189TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block189Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block189 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block189HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block189MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block189TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block189Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block189_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
