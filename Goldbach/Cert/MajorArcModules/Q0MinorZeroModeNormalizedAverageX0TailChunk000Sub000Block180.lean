import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [180,181). -/

/-- Block 180 covers tail-support indices [4500,4525) and q from 7454 to 7491. -/

def TailChunk000Sub000Block180Part000SupportExplicit : Finset ℕ :=
  ([7454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part000 : ℚ :=
  (217039515625 : ℚ) / 120486466988512722

def SurrogateDiagonalTailChunk000Sub000Block180Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7454
    = surrogateDiagTailX0RatChunk000Sub000Block180Part000

theorem surrogateDiagonalTailChunk000Sub000Block180Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part000] using hcert

def TailChunk000Sub000Block180Part001SupportExplicit : Finset ℕ :=
  ([7455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part001 : ℚ :=
  (176726393 : ℚ) / 78691703193600

def SurrogateDiagonalTailChunk000Sub000Block180Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7455
    = surrogateDiagTailX0RatChunk000Sub000Block180Part001

theorem surrogateDiagonalTailChunk000Sub000Block180Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part001] using hcert

def TailChunk000Sub000Block180Part002SupportExplicit : Finset ℕ :=
  ([7457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block180Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7457
    = surrogateDiagTailX0RatChunk000Sub000Block180Part002

theorem surrogateDiagonalTailChunk000Sub000Block180Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part002] using hcert

def TailChunk000Sub000Block180Part003SupportExplicit : Finset ℕ :=
  ([7458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part003 : ℚ :=
  (4134595737 : ℚ) / 419689083699200

def SurrogateDiagonalTailChunk000Sub000Block180Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7458
    = surrogateDiagTailX0RatChunk000Sub000Block180Part003

theorem surrogateDiagonalTailChunk000Sub000Block180Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part003] using hcert

def TailChunk000Sub000Block180Part004SupportExplicit : Finset ℕ :=
  ([7459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block180Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7459
    = surrogateDiagTailX0RatChunk000Sub000Block180Part004

theorem surrogateDiagonalTailChunk000Sub000Block180Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part004] using hcert

def TailChunk000Sub000Block180Part005SupportExplicit : Finset ℕ :=
  ([7462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part005 : ℚ :=
  (14462308199 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block180Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7462
    = surrogateDiagTailX0RatChunk000Sub000Block180Part005

theorem surrogateDiagonalTailChunk000Sub000Block180Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part005] using hcert

def TailChunk000Sub000Block180Part006SupportExplicit : Finset ℕ :=
  ([7463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part006 : ℚ :=
  (200434945975 : ℚ) / 376949567079088128

def SurrogateDiagonalTailChunk000Sub000Block180Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7463
    = surrogateDiagTailX0RatChunk000Sub000Block180Part006

theorem surrogateDiagonalTailChunk000Sub000Block180Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part006] using hcert

def TailChunk000Sub000Block180Part007SupportExplicit : Finset ℕ :=
  ([7465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part007 : ℚ :=
  (1322601019325 : ℚ) / 1586032641370374144

def SurrogateDiagonalTailChunk000Sub000Block180Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7465
    = surrogateDiagTailX0RatChunk000Sub000Block180Part007

theorem surrogateDiagonalTailChunk000Sub000Block180Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part007] using hcert

def TailChunk000Sub000Block180Part008SupportExplicit : Finset ℕ :=
  ([7466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part008 : ℚ :=
  (1741562742775 : ℚ) / 485057695578127488

def SurrogateDiagonalTailChunk000Sub000Block180Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7466
    = surrogateDiagTailX0RatChunk000Sub000Block180Part008

theorem surrogateDiagonalTailChunk000Sub000Block180Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part008] using hcert

def TailChunk000Sub000Block180Part009SupportExplicit : Finset ℕ :=
  ([7467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part009 : ℚ :=
  (14363442881 : ℚ) / 9596221375703040

def SurrogateDiagonalTailChunk000Sub000Block180Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7467
    = surrogateDiagTailX0RatChunk000Sub000Block180Part009

theorem surrogateDiagonalTailChunk000Sub000Block180Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part009] using hcert

def TailChunk000Sub000Block180Part010SupportExplicit : Finset ℕ :=
  ([7469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part010 : ℚ :=
  (386086411 : ℚ) / 430067692339200

def SurrogateDiagonalTailChunk000Sub000Block180Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7469
    = surrogateDiagTailX0RatChunk000Sub000Block180Part010

theorem surrogateDiagonalTailChunk000Sub000Block180Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part010] using hcert

def TailChunk000Sub000Block180Part011SupportExplicit : Finset ℕ :=
  ([7471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part011 : ℚ :=
  (13287569221 : ℚ) / 26879230771200000

def SurrogateDiagonalTailChunk000Sub000Block180Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7471
    = surrogateDiagTailX0RatChunk000Sub000Block180Part011

theorem surrogateDiagonalTailChunk000Sub000Block180Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part011] using hcert

def TailChunk000Sub000Block180Part012SupportExplicit : Finset ℕ :=
  ([7473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part012 : ℚ :=
  (923795040875 : ℚ) / 654879728333635584

def SurrogateDiagonalTailChunk000Sub000Block180Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7473
    = surrogateDiagTailX0RatChunk000Sub000Block180Part012

theorem surrogateDiagonalTailChunk000Sub000Block180Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part012] using hcert

def TailChunk000Sub000Block180Part013SupportExplicit : Finset ℕ :=
  ([7474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part013 : ℚ :=
  (7383700127 : ℚ) / 1866613248000000

def SurrogateDiagonalTailChunk000Sub000Block180Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7474
    = surrogateDiagTailX0RatChunk000Sub000Block180Part013

theorem surrogateDiagonalTailChunk000Sub000Block180Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part013] using hcert

def TailChunk000Sub000Block180Part014SupportExplicit : Finset ℕ :=
  ([7477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part014 : ℚ :=
  (873523890625 : ℚ) / 1952738273068061472

def SurrogateDiagonalTailChunk000Sub000Block180Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7477
    = surrogateDiagTailX0RatChunk000Sub000Block180Part014

theorem surrogateDiagonalTailChunk000Sub000Block180Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part014] using hcert

def TailChunk000Sub000Block180Part015SupportExplicit : Finset ℕ :=
  ([7478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part015 : ℚ :=
  (1747165621975 : ℚ) / 488184568267015368

def SurrogateDiagonalTailChunk000Sub000Block180Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7478
    = surrogateDiagTailX0RatChunk000Sub000Block180Part015

theorem surrogateDiagonalTailChunk000Sub000Block180Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part015] using hcert

def TailChunk000Sub000Block180Part016SupportExplicit : Finset ℕ :=
  ([7481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part016 : ℚ :=
  (1399134025 : ℚ) / 3131073349612032

def SurrogateDiagonalTailChunk000Sub000Block180Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7481
    = surrogateDiagTailX0RatChunk000Sub000Block180Part016

theorem surrogateDiagonalTailChunk000Sub000Block180Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part016] using hcert

def TailChunk000Sub000Block180Part017SupportExplicit : Finset ℕ :=
  ([7482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part017 : ℚ :=
  (4494743975 : ℚ) / 531390316972032

def SurrogateDiagonalTailChunk000Sub000Block180Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7482
    = surrogateDiagTailX0RatChunk000Sub000Block180Part017

theorem surrogateDiagonalTailChunk000Sub000Block180Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part017] using hcert

def TailChunk000Sub000Block180Part018SupportExplicit : Finset ℕ :=
  ([7483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part018 : ℚ :=
  (2853945325375 : ℚ) / 4216157937353115648

def SurrogateDiagonalTailChunk000Sub000Block180Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7483
    = surrogateDiagTailX0RatChunk000Sub000Block180Part018

theorem surrogateDiagonalTailChunk000Sub000Block180Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part018] using hcert

def TailChunk000Sub000Block180Part019SupportExplicit : Finset ℕ :=
  ([7485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part019 : ℚ :=
  (729848426675 : ℚ) / 314973620289552384

def SurrogateDiagonalTailChunk000Sub000Block180Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7485
    = surrogateDiagTailX0RatChunk000Sub000Block180Part019

theorem surrogateDiagonalTailChunk000Sub000Block180Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part019] using hcert

def TailChunk000Sub000Block180Part020SupportExplicit : Finset ℕ :=
  ([7486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part020 : ℚ :=
  (841299008575 : ℚ) / 387383541072611328

def SurrogateDiagonalTailChunk000Sub000Block180Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7486
    = surrogateDiagTailX0RatChunk000Sub000Block180Part020

theorem surrogateDiagonalTailChunk000Sub000Block180Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part020] using hcert

def TailChunk000Sub000Block180Part021SupportExplicit : Finset ℕ :=
  ([7487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part021 : ℚ :=
  (875862015625 : ℚ) / 1963207292769974802

def SurrogateDiagonalTailChunk000Sub000Block180Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7487
    = surrogateDiagTailX0RatChunk000Sub000Block180Part021

theorem surrogateDiagonalTailChunk000Sub000Block180Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part021] using hcert

def TailChunk000Sub000Block180Part022SupportExplicit : Finset ℕ :=
  ([7489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part022 : ℚ :=
  (876330015625 : ℚ) / 1965306137743982592

def SurrogateDiagonalTailChunk000Sub000Block180Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7489
    = surrogateDiagTailX0RatChunk000Sub000Block180Part022

theorem surrogateDiagonalTailChunk000Sub000Block180Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part022] using hcert

def TailChunk000Sub000Block180Part023SupportExplicit : Finset ℕ :=
  ([7490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part023 : ℚ :=
  (9390306325 : ℚ) / 1454664332611584

def SurrogateDiagonalTailChunk000Sub000Block180Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7490
    = surrogateDiagTailX0RatChunk000Sub000Block180Part023

theorem surrogateDiagonalTailChunk000Sub000Block180Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part023] using hcert

def TailChunk000Sub000Block180Part024SupportExplicit : Finset ℕ :=
  ([7491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block180Part024 : ℚ :=
  (34478230793 : ℚ) / 20874236220441600

def SurrogateDiagonalTailChunk000Sub000Block180Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7491
    = surrogateDiagTailX0RatChunk000Sub000Block180Part024

theorem surrogateDiagonalTailChunk000Sub000Block180Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block180Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block180Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block180Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block180Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block180Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block180Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block180HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block180Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block180Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block180Part000
    + surrogateDiagTailX0RatChunk000Sub000Block180Part001
    + surrogateDiagTailX0RatChunk000Sub000Block180Part002
    + surrogateDiagTailX0RatChunk000Sub000Block180Part003
    + surrogateDiagTailX0RatChunk000Sub000Block180Part004
    + surrogateDiagTailX0RatChunk000Sub000Block180Part005
    + surrogateDiagTailX0RatChunk000Sub000Block180Part006
    + surrogateDiagTailX0RatChunk000Sub000Block180Part007
    + surrogateDiagTailX0RatChunk000Sub000Block180Part008
    + surrogateDiagTailX0RatChunk000Sub000Block180Part009

def surrogateDiagonalTailChunk000Sub000Block180MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block180Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block180Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block180Part010
    + surrogateDiagTailX0RatChunk000Sub000Block180Part011
    + surrogateDiagTailX0RatChunk000Sub000Block180Part012
    + surrogateDiagTailX0RatChunk000Sub000Block180Part013
    + surrogateDiagTailX0RatChunk000Sub000Block180Part014
    + surrogateDiagTailX0RatChunk000Sub000Block180Part015
    + surrogateDiagTailX0RatChunk000Sub000Block180Part016
    + surrogateDiagTailX0RatChunk000Sub000Block180Part017
    + surrogateDiagTailX0RatChunk000Sub000Block180Part018
    + surrogateDiagTailX0RatChunk000Sub000Block180Part019

def surrogateDiagonalTailChunk000Sub000Block180TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block180Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block180Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block180Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block180Part020
    + surrogateDiagTailX0RatChunk000Sub000Block180Part021
    + surrogateDiagTailX0RatChunk000Sub000Block180Part022
    + surrogateDiagTailX0RatChunk000Sub000Block180Part023
    + surrogateDiagTailX0RatChunk000Sub000Block180Part024

def surrogateDiagonalTailChunk000Sub000Block180Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block180HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block180MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block180TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block180 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block180Part000
    + surrogateDiagTailX0RatChunk000Sub000Block180Part001
    + surrogateDiagTailX0RatChunk000Sub000Block180Part002
    + surrogateDiagTailX0RatChunk000Sub000Block180Part003
    + surrogateDiagTailX0RatChunk000Sub000Block180Part004
    + surrogateDiagTailX0RatChunk000Sub000Block180Part005
    + surrogateDiagTailX0RatChunk000Sub000Block180Part006
    + surrogateDiagTailX0RatChunk000Sub000Block180Part007
    + surrogateDiagTailX0RatChunk000Sub000Block180Part008
    + surrogateDiagTailX0RatChunk000Sub000Block180Part009
    + surrogateDiagTailX0RatChunk000Sub000Block180Part010
    + surrogateDiagTailX0RatChunk000Sub000Block180Part011
    + surrogateDiagTailX0RatChunk000Sub000Block180Part012
    + surrogateDiagTailX0RatChunk000Sub000Block180Part013
    + surrogateDiagTailX0RatChunk000Sub000Block180Part014
    + surrogateDiagTailX0RatChunk000Sub000Block180Part015
    + surrogateDiagTailX0RatChunk000Sub000Block180Part016
    + surrogateDiagTailX0RatChunk000Sub000Block180Part017
    + surrogateDiagTailX0RatChunk000Sub000Block180Part018
    + surrogateDiagTailX0RatChunk000Sub000Block180Part019
    + surrogateDiagTailX0RatChunk000Sub000Block180Part020
    + surrogateDiagTailX0RatChunk000Sub000Block180Part021
    + surrogateDiagTailX0RatChunk000Sub000Block180Part022
    + surrogateDiagTailX0RatChunk000Sub000Block180Part023
    + surrogateDiagTailX0RatChunk000Sub000Block180Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block180_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block180Head + surrogateDiagTailX0RatChunk000Sub000Block180Mid + surrogateDiagTailX0RatChunk000Sub000Block180Tail =
      surrogateDiagTailX0RatChunk000Sub000Block180 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block180Head surrogateDiagTailX0RatChunk000Sub000Block180Mid surrogateDiagTailX0RatChunk000Sub000Block180Tail surrogateDiagTailX0RatChunk000Sub000Block180
  ring

def SurrogateDiagonalTailChunk000Sub000Block180HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block180HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block180Head

def SurrogateDiagonalTailChunk000Sub000Block180MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block180MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block180Mid

def SurrogateDiagonalTailChunk000Sub000Block180TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block180TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block180Tail

theorem surrogateDiagonalTailChunk000Sub000Block180_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block180HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block180MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block180TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block180Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block180 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block180HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block180MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block180TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block180Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block180_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
