import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [180,190). -/

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

/-- Block 181 covers tail-support indices [4525,4550) and q from 7493 to 7534. -/

def TailChunk000Sub000Block181Part000SupportExplicit : Finset ℕ :=
  ([7493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part000 : ℚ :=
  (377133259625 : ℚ) / 792462105816377472

def SurrogateDiagonalTailChunk000Sub000Block181Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7493
    = surrogateDiagTailX0RatChunk000Sub000Block181Part000

theorem surrogateDiagonalTailChunk000Sub000Block181Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part000] using hcert

def TailChunk000Sub000Block181Part001SupportExplicit : Finset ℕ :=
  ([7494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part001 : ℚ :=
  (682149594025 : ℚ) / 97052154950320128

def SurrogateDiagonalTailChunk000Sub000Block181Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7494
    = surrogateDiagTailX0RatChunk000Sub000Block181Part001

theorem surrogateDiagonalTailChunk000Sub000Block181Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part001] using hcert

def TailChunk000Sub000Block181Part002SupportExplicit : Finset ℕ :=
  ([7495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part002 : ℚ :=
  (120292736925 : ℚ) / 153495194295052288

def SurrogateDiagonalTailChunk000Sub000Block181Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7495
    = surrogateDiagTailX0RatChunk000Sub000Block181Part002

theorem surrogateDiagonalTailChunk000Sub000Block181Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part002] using hcert

def TailChunk000Sub000Block181Part003SupportExplicit : Finset ℕ :=
  ([7498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part003 : ℚ :=
  (850068678475 : ℚ) / 403438778604436608

def SurrogateDiagonalTailChunk000Sub000Block181Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7498
    = surrogateDiagTailX0RatChunk000Sub000Block181Part003

theorem surrogateDiagonalTailChunk000Sub000Block181Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part003] using hcert

def TailChunk000Sub000Block181Part004SupportExplicit : Finset ℕ :=
  ([7499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part004 : ℚ :=
  (878671890625 : ℚ) / 1975825617206230002

def SurrogateDiagonalTailChunk000Sub000Block181Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7499
    = surrogateDiagTailX0RatChunk000Sub000Block181Part004

theorem surrogateDiagonalTailChunk000Sub000Block181Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part004] using hcert

def TailChunk000Sub000Block181Part005SupportExplicit : Finset ℕ :=
  ([7501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part005 : ℚ :=
  (456623375 : ℚ) / 825729969291264

def SurrogateDiagonalTailChunk000Sub000Block181Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7501
    = surrogateDiagTailX0RatChunk000Sub000Block181Part005

theorem surrogateDiagonalTailChunk000Sub000Block181Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part005] using hcert

def TailChunk000Sub000Block181Part006SupportExplicit : Finset ℕ :=
  ([7503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part006 : ℚ :=
  (74405388433 : ℚ) / 53094776832000000

def SurrogateDiagonalTailChunk000Sub000Block181Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7503
    = surrogateDiagTailX0RatChunk000Sub000Block181Part006

theorem surrogateDiagonalTailChunk000Sub000Block181Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part006] using hcert

def TailChunk000Sub000Block181Part007SupportExplicit : Finset ℕ :=
  ([7505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part007 : ℚ :=
  (582791433925 : ℚ) / 621835145145556992

def SurrogateDiagonalTailChunk000Sub000Block181Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7505
    = surrogateDiagTailX0RatChunk000Sub000Block181Part007

theorem surrogateDiagonalTailChunk000Sub000Block181Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part007] using hcert

def TailChunk000Sub000Block181Part008SupportExplicit : Finset ℕ :=
  ([7507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part008 : ℚ :=
  (880547640625 : ℚ) / 1984271560257870162

def SurrogateDiagonalTailChunk000Sub000Block181Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7507
    = surrogateDiagTailX0RatChunk000Sub000Block181Part008

theorem surrogateDiagonalTailChunk000Sub000Block181Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part008] using hcert

def TailChunk000Sub000Block181Part009SupportExplicit : Finset ℕ :=
  ([7509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part009 : ℚ :=
  (489297281275 : ℚ) / 391954876100320032

def SurrogateDiagonalTailChunk000Sub000Block181Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7509
    = surrogateDiagTailX0RatChunk000Sub000Block181Part009

theorem surrogateDiagonalTailChunk000Sub000Block181Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part009] using hcert

def TailChunk000Sub000Block181Part010SupportExplicit : Finset ℕ :=
  ([7510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part010 : ℚ :=
  (10330849493 : ℚ) / 2700540000000000

def SurrogateDiagonalTailChunk000Sub000Block181Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7510
    = surrogateDiagTailX0RatChunk000Sub000Block181Part010

theorem surrogateDiagonalTailChunk000Sub000Block181Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part010] using hcert

def TailChunk000Sub000Block181Part011SupportExplicit : Finset ℕ :=
  ([7511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part011 : ℚ :=
  (7730536075 : ℚ) / 9753935262253056

def SurrogateDiagonalTailChunk000Sub000Block181Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7511
    = surrogateDiagTailX0RatChunk000Sub000Block181Part011

theorem surrogateDiagonalTailChunk000Sub000Block181Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part011] using hcert

def TailChunk000Sub000Block181Part012SupportExplicit : Finset ℕ :=
  ([7513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part012 : ℚ :=
  (224370301 : ℚ) / 393424733532864

def SurrogateDiagonalTailChunk000Sub000Block181Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7513
    = surrogateDiagTailX0RatChunk000Sub000Block181Part012

theorem surrogateDiagonalTailChunk000Sub000Block181Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part012] using hcert

def TailChunk000Sub000Block181Part013SupportExplicit : Finset ℕ :=
  ([7517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part013 : ℚ :=
  (882895140625 : ℚ) / 1994867032968828192

def SurrogateDiagonalTailChunk000Sub000Block181Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7517
    = surrogateDiagTailX0RatChunk000Sub000Block181Part013

theorem surrogateDiagonalTailChunk000Sub000Block181Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part013] using hcert

def TailChunk000Sub000Block181Part014SupportExplicit : Finset ℕ :=
  ([7518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part014 : ℚ :=
  (22144824725 : ℚ) / 1927827131848704

def SurrogateDiagonalTailChunk000Sub000Block181Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7518
    = surrogateDiagTailX0RatChunk000Sub000Block181Part014

theorem surrogateDiagonalTailChunk000Sub000Block181Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part014] using hcert

def TailChunk000Sub000Block181Part015SupportExplicit : Finset ℕ :=
  ([7519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part015 : ℚ :=
  (3424070537425 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk000Sub000Block181Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7519
    = surrogateDiagTailX0RatChunk000Sub000Block181Part015

theorem surrogateDiagonalTailChunk000Sub000Block181Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part015] using hcert

def TailChunk000Sub000Block181Part016SupportExplicit : Finset ℕ :=
  ([7521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part016 : ℚ :=
  (1840694716225 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk000Sub000Block181Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7521
    = surrogateDiagTailX0RatChunk000Sub000Block181Part016

theorem surrogateDiagonalTailChunk000Sub000Block181Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part016] using hcert

def TailChunk000Sub000Block181Part017SupportExplicit : Finset ℕ :=
  ([7522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part017 : ℚ :=
  (70711459879 : ℚ) / 19991170810675200

def SurrogateDiagonalTailChunk000Sub000Block181Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7522
    = surrogateDiagTailX0RatChunk000Sub000Block181Part017

theorem surrogateDiagonalTailChunk000Sub000Block181Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part017] using hcert

def TailChunk000Sub000Block181Part018SupportExplicit : Finset ℕ :=
  ([7523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part018 : ℚ :=
  (884305140625 : ℚ) / 2001244649942619282

def SurrogateDiagonalTailChunk000Sub000Block181Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7523
    = surrogateDiagTailX0RatChunk000Sub000Block181Part018

theorem surrogateDiagonalTailChunk000Sub000Block181Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part018] using hcert

def TailChunk000Sub000Block181Part019SupportExplicit : Finset ℕ :=
  ([7526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part019 : ℚ :=
  (67732139113 : ℚ) / 17558701054003200

def SurrogateDiagonalTailChunk000Sub000Block181Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7526
    = surrogateDiagTailX0RatChunk000Sub000Block181Part019

theorem surrogateDiagonalTailChunk000Sub000Block181Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part019] using hcert

def TailChunk000Sub000Block181Part020SupportExplicit : Finset ℕ :=
  ([7527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part020 : ℚ :=
  (444302410975 : ℚ) / 281849162851418112

def SurrogateDiagonalTailChunk000Sub000Block181Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7527
    = surrogateDiagTailX0RatChunk000Sub000Block181Part020

theorem surrogateDiagonalTailChunk000Sub000Block181Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part020] using hcert

def TailChunk000Sub000Block181Part021SupportExplicit : Finset ℕ :=
  ([7529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part021 : ℚ :=
  (885716265625 : ℚ) / 2007637546704056832

def SurrogateDiagonalTailChunk000Sub000Block181Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7529
    = surrogateDiagTailX0RatChunk000Sub000Block181Part021

theorem surrogateDiagonalTailChunk000Sub000Block181Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part021] using hcert

def TailChunk000Sub000Block181Part022SupportExplicit : Finset ℕ :=
  ([7530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part022 : ℚ :=
  (29320311937 : ℚ) / 1600320000000000

def SurrogateDiagonalTailChunk000Sub000Block181Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7530
    = surrogateDiagTailX0RatChunk000Sub000Block181Part022

theorem surrogateDiagonalTailChunk000Sub000Block181Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part022] using hcert

def TailChunk000Sub000Block181Part023SupportExplicit : Finset ℕ :=
  ([7531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part023 : ℚ :=
  (135561255525 : ℚ) / 260606128909647872

def SurrogateDiagonalTailChunk000Sub000Block181Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7531
    = surrogateDiagTailX0RatChunk000Sub000Block181Part023

theorem surrogateDiagonalTailChunk000Sub000Block181Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part023] using hcert

def TailChunk000Sub000Block181Part024SupportExplicit : Finset ℕ :=
  ([7534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part024 : ℚ :=
  (1773431367775 : ℚ) / 502976994672717768

def SurrogateDiagonalTailChunk000Sub000Block181Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7534
    = surrogateDiagTailX0RatChunk000Sub000Block181Part024

theorem surrogateDiagonalTailChunk000Sub000Block181Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block181HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block181Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block181Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block181Part000
    + surrogateDiagTailX0RatChunk000Sub000Block181Part001
    + surrogateDiagTailX0RatChunk000Sub000Block181Part002
    + surrogateDiagTailX0RatChunk000Sub000Block181Part003
    + surrogateDiagTailX0RatChunk000Sub000Block181Part004
    + surrogateDiagTailX0RatChunk000Sub000Block181Part005
    + surrogateDiagTailX0RatChunk000Sub000Block181Part006
    + surrogateDiagTailX0RatChunk000Sub000Block181Part007
    + surrogateDiagTailX0RatChunk000Sub000Block181Part008
    + surrogateDiagTailX0RatChunk000Sub000Block181Part009

def surrogateDiagonalTailChunk000Sub000Block181MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block181Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block181Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block181Part010
    + surrogateDiagTailX0RatChunk000Sub000Block181Part011
    + surrogateDiagTailX0RatChunk000Sub000Block181Part012
    + surrogateDiagTailX0RatChunk000Sub000Block181Part013
    + surrogateDiagTailX0RatChunk000Sub000Block181Part014
    + surrogateDiagTailX0RatChunk000Sub000Block181Part015
    + surrogateDiagTailX0RatChunk000Sub000Block181Part016
    + surrogateDiagTailX0RatChunk000Sub000Block181Part017
    + surrogateDiagTailX0RatChunk000Sub000Block181Part018
    + surrogateDiagTailX0RatChunk000Sub000Block181Part019

def surrogateDiagonalTailChunk000Sub000Block181TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block181Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block181Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block181Part020
    + surrogateDiagTailX0RatChunk000Sub000Block181Part021
    + surrogateDiagTailX0RatChunk000Sub000Block181Part022
    + surrogateDiagTailX0RatChunk000Sub000Block181Part023
    + surrogateDiagTailX0RatChunk000Sub000Block181Part024

def surrogateDiagonalTailChunk000Sub000Block181Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block181HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block181MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block181TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block181 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block181Part000
    + surrogateDiagTailX0RatChunk000Sub000Block181Part001
    + surrogateDiagTailX0RatChunk000Sub000Block181Part002
    + surrogateDiagTailX0RatChunk000Sub000Block181Part003
    + surrogateDiagTailX0RatChunk000Sub000Block181Part004
    + surrogateDiagTailX0RatChunk000Sub000Block181Part005
    + surrogateDiagTailX0RatChunk000Sub000Block181Part006
    + surrogateDiagTailX0RatChunk000Sub000Block181Part007
    + surrogateDiagTailX0RatChunk000Sub000Block181Part008
    + surrogateDiagTailX0RatChunk000Sub000Block181Part009
    + surrogateDiagTailX0RatChunk000Sub000Block181Part010
    + surrogateDiagTailX0RatChunk000Sub000Block181Part011
    + surrogateDiagTailX0RatChunk000Sub000Block181Part012
    + surrogateDiagTailX0RatChunk000Sub000Block181Part013
    + surrogateDiagTailX0RatChunk000Sub000Block181Part014
    + surrogateDiagTailX0RatChunk000Sub000Block181Part015
    + surrogateDiagTailX0RatChunk000Sub000Block181Part016
    + surrogateDiagTailX0RatChunk000Sub000Block181Part017
    + surrogateDiagTailX0RatChunk000Sub000Block181Part018
    + surrogateDiagTailX0RatChunk000Sub000Block181Part019
    + surrogateDiagTailX0RatChunk000Sub000Block181Part020
    + surrogateDiagTailX0RatChunk000Sub000Block181Part021
    + surrogateDiagTailX0RatChunk000Sub000Block181Part022
    + surrogateDiagTailX0RatChunk000Sub000Block181Part023
    + surrogateDiagTailX0RatChunk000Sub000Block181Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block181_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block181Head + surrogateDiagTailX0RatChunk000Sub000Block181Mid + surrogateDiagTailX0RatChunk000Sub000Block181Tail =
      surrogateDiagTailX0RatChunk000Sub000Block181 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block181Head surrogateDiagTailX0RatChunk000Sub000Block181Mid surrogateDiagTailX0RatChunk000Sub000Block181Tail surrogateDiagTailX0RatChunk000Sub000Block181
  ring

def SurrogateDiagonalTailChunk000Sub000Block181HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block181HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block181Head

def SurrogateDiagonalTailChunk000Sub000Block181MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block181MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block181Mid

def SurrogateDiagonalTailChunk000Sub000Block181TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block181TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block181Tail

theorem surrogateDiagonalTailChunk000Sub000Block181_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block181HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block181MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block181TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block181Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block181 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block181HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block181MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block181TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block181Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block181_eq_head_add_mid_add_tail

/-- Block 182 covers tail-support indices [4550,4575) and q from 7535 to 7574. -/

def TailChunk000Sub000Block182Part000SupportExplicit : Finset ℕ :=
  ([7535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part000 : ℚ :=
  (94750856503 : ℚ) / 87595631719219200

def SurrogateDiagonalTailChunk000Sub000Block182Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7535
    = surrogateDiagTailX0RatChunk000Sub000Block182Part000

theorem surrogateDiagonalTailChunk000Sub000Block182Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part000] using hcert

def TailChunk000Sub000Block182Part001SupportExplicit : Finset ℕ :=
  ([7537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part001 : ℚ :=
  (887599515625 : ℚ) / 2016185219762429952

def SurrogateDiagonalTailChunk000Sub000Block182Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7537
    = surrogateDiagTailX0RatChunk000Sub000Block182Part001

theorem surrogateDiagonalTailChunk000Sub000Block182Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part001] using hcert

def TailChunk000Sub000Block182Part002SupportExplicit : Finset ℕ :=
  ([7538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part002 : ℚ :=
  (221958765625 : ℚ) / 126011576235151872

def SurrogateDiagonalTailChunk000Sub000Block182Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7538
    = surrogateDiagTailX0RatChunk000Sub000Block182Part002

theorem surrogateDiagonalTailChunk000Sub000Block182Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part002] using hcert

def TailChunk000Sub000Block182Part003SupportExplicit : Finset ℕ :=
  ([7539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part003 : ℚ :=
  (28616645725 : ℚ) / 31544248508504064

def SurrogateDiagonalTailChunk000Sub000Block182Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7539
    = surrogateDiagTailX0RatChunk000Sub000Block182Part003

theorem surrogateDiagonalTailChunk000Sub000Block182Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part003] using hcert

def TailChunk000Sub000Block182Part004SupportExplicit : Finset ℕ :=
  ([7541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7541
    = surrogateDiagTailX0RatChunk000Sub000Block182Part004

theorem surrogateDiagonalTailChunk000Sub000Block182Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part004] using hcert

def TailChunk000Sub000Block182Part005SupportExplicit : Finset ℕ :=
  ([7543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part005 : ℚ :=
  (204827525 : ℚ) / 9961451323566336

def SurrogateDiagonalTailChunk000Sub000Block182Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7543
    = surrogateDiagTailX0RatChunk000Sub000Block182Part005

theorem surrogateDiagonalTailChunk000Sub000Block182Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part005] using hcert

def TailChunk000Sub000Block182Part006SupportExplicit : Finset ℕ :=
  ([7545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part006 : ℚ :=
  (758345821825 : ℚ) / 650431664324640768

def SurrogateDiagonalTailChunk000Sub000Block182Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7545
    = surrogateDiagTailX0RatChunk000Sub000Block182Part006

theorem surrogateDiagonalTailChunk000Sub000Block182Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part006] using hcert

def TailChunk000Sub000Block182Part007SupportExplicit : Finset ℕ :=
  ([7547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7547
    = surrogateDiagTailX0RatChunk000Sub000Block182Part007

theorem surrogateDiagonalTailChunk000Sub000Block182Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part007] using hcert

def TailChunk000Sub000Block182Part008SupportExplicit : Finset ℕ :=
  ([7549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7549
    = surrogateDiagTailX0RatChunk000Sub000Block182Part008

theorem surrogateDiagonalTailChunk000Sub000Block182Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part008] using hcert

def TailChunk000Sub000Block182Part009SupportExplicit : Finset ℕ :=
  ([7553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part009 : ℚ :=
  (480221934775 : ℚ) / 3038171280930275328

def SurrogateDiagonalTailChunk000Sub000Block182Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7553
    = surrogateDiagTailX0RatChunk000Sub000Block182Part009

theorem surrogateDiagonalTailChunk000Sub000Block182Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part009] using hcert

def TailChunk000Sub000Block182Part010SupportExplicit : Finset ℕ :=
  ([7554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part010 : ℚ :=
  (693115223275 : ℚ) / 100200388634352768

def SurrogateDiagonalTailChunk000Sub000Block182Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7554
    = surrogateDiagTailX0RatChunk000Sub000Block182Part010

theorem surrogateDiagonalTailChunk000Sub000Block182Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part010] using hcert

def TailChunk000Sub000Block182Part011SupportExplicit : Finset ℕ :=
  ([7555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part011 : ℚ :=
  (3806218509 : ℚ) / 22186221999795200

def SurrogateDiagonalTailChunk000Sub000Block182Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7555
    = surrogateDiagTailX0RatChunk000Sub000Block182Part011

theorem surrogateDiagonalTailChunk000Sub000Block182Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part011] using hcert

def TailChunk000Sub000Block182Part012SupportExplicit : Finset ℕ :=
  ([7557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part012 : ℚ :=
  (1681649263 : ℚ) / 2276106714316800

def SurrogateDiagonalTailChunk000Sub000Block182Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7557
    = surrogateDiagTailX0RatChunk000Sub000Block182Part012

theorem surrogateDiagonalTailChunk000Sub000Block182Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part012] using hcert

def TailChunk000Sub000Block182Part013SupportExplicit : Finset ℕ :=
  ([7558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part013 : ℚ :=
  (223138140625 : ℚ) / 127354613419928082

def SurrogateDiagonalTailChunk000Sub000Block182Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7558
    = surrogateDiagTailX0RatChunk000Sub000Block182Part013

theorem surrogateDiagonalTailChunk000Sub000Block182Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part013] using hcert

def TailChunk000Sub000Block182Part014SupportExplicit : Finset ℕ :=
  ([7559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7559
    = surrogateDiagTailX0RatChunk000Sub000Block182Part014

theorem surrogateDiagonalTailChunk000Sub000Block182Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part014] using hcert

def TailChunk000Sub000Block182Part015SupportExplicit : Finset ℕ :=
  ([7561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7561
    = surrogateDiagTailX0RatChunk000Sub000Block182Part015

theorem surrogateDiagonalTailChunk000Sub000Block182Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part015] using hcert

def TailChunk000Sub000Block182Part016SupportExplicit : Finset ℕ :=
  ([7562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part016 : ℚ :=
  (858441081175 : ℚ) / 403438778604436608

def SurrogateDiagonalTailChunk000Sub000Block182Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7562
    = surrogateDiagTailX0RatChunk000Sub000Block182Part016

theorem surrogateDiagonalTailChunk000Sub000Block182Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part016] using hcert

def TailChunk000Sub000Block182Part017SupportExplicit : Finset ℕ :=
  ([7563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part017 : ℚ :=
  (15885322259 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub000Block182Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7563
    = surrogateDiagTailX0RatChunk000Sub000Block182Part017

theorem surrogateDiagonalTailChunk000Sub000Block182Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part017] using hcert

def TailChunk000Sub000Block182Part018SupportExplicit : Finset ℕ :=
  ([7565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part018 : ℚ :=
  (165849338025 : ℚ) / 838602569386295296

def SurrogateDiagonalTailChunk000Sub000Block182Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7565
    = surrogateDiagTailX0RatChunk000Sub000Block182Part018

theorem surrogateDiagonalTailChunk000Sub000Block182Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part018] using hcert

def TailChunk000Sub000Block182Part019SupportExplicit : Finset ℕ :=
  ([7566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part019 : ℚ :=
  (160861292275 : ℚ) / 17615572678213632

def SurrogateDiagonalTailChunk000Sub000Block182Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7566
    = surrogateDiagTailX0RatChunk000Sub000Block182Part019

theorem surrogateDiagonalTailChunk000Sub000Block182Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part019] using hcert

def TailChunk000Sub000Block182Part020SupportExplicit : Finset ℕ :=
  ([7567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part020 : ℚ :=
  (49283466425 : ℚ) / 377669054492116992

def SurrogateDiagonalTailChunk000Sub000Block182Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7567
    = surrogateDiagTailX0RatChunk000Sub000Block182Part020

theorem surrogateDiagonalTailChunk000Sub000Block182Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part020] using hcert

def TailChunk000Sub000Block182Part021SupportExplicit : Finset ℕ :=
  ([7570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part021 : ℚ :=
  (262413414425 : ℚ) / 69699995728183296

def SurrogateDiagonalTailChunk000Sub000Block182Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7570
    = surrogateDiagTailX0RatChunk000Sub000Block182Part021

theorem surrogateDiagonalTailChunk000Sub000Block182Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part021] using hcert

def TailChunk000Sub000Block182Part022SupportExplicit : Finset ℕ :=
  ([7571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part022 : ℚ :=
  (441974125 : ℚ) / 59252154503528448

def SurrogateDiagonalTailChunk000Sub000Block182Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7571
    = surrogateDiagTailX0RatChunk000Sub000Block182Part022

theorem surrogateDiagonalTailChunk000Sub000Block182Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part022] using hcert

def TailChunk000Sub000Block182Part023SupportExplicit : Finset ℕ :=
  ([7573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7573
    = surrogateDiagTailX0RatChunk000Sub000Block182Part023

theorem surrogateDiagonalTailChunk000Sub000Block182Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part023] using hcert

def TailChunk000Sub000Block182Part024SupportExplicit : Finset ℕ :=
  ([7574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part024 : ℚ :=
  (32156715553 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk000Sub000Block182Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7574
    = surrogateDiagTailX0RatChunk000Sub000Block182Part024

theorem surrogateDiagonalTailChunk000Sub000Block182Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block182HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block182Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block182Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block182Part000
    + surrogateDiagTailX0RatChunk000Sub000Block182Part001
    + surrogateDiagTailX0RatChunk000Sub000Block182Part002
    + surrogateDiagTailX0RatChunk000Sub000Block182Part003
    + surrogateDiagTailX0RatChunk000Sub000Block182Part004
    + surrogateDiagTailX0RatChunk000Sub000Block182Part005
    + surrogateDiagTailX0RatChunk000Sub000Block182Part006
    + surrogateDiagTailX0RatChunk000Sub000Block182Part007
    + surrogateDiagTailX0RatChunk000Sub000Block182Part008
    + surrogateDiagTailX0RatChunk000Sub000Block182Part009

def surrogateDiagonalTailChunk000Sub000Block182MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block182Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block182Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block182Part010
    + surrogateDiagTailX0RatChunk000Sub000Block182Part011
    + surrogateDiagTailX0RatChunk000Sub000Block182Part012
    + surrogateDiagTailX0RatChunk000Sub000Block182Part013
    + surrogateDiagTailX0RatChunk000Sub000Block182Part014
    + surrogateDiagTailX0RatChunk000Sub000Block182Part015
    + surrogateDiagTailX0RatChunk000Sub000Block182Part016
    + surrogateDiagTailX0RatChunk000Sub000Block182Part017
    + surrogateDiagTailX0RatChunk000Sub000Block182Part018
    + surrogateDiagTailX0RatChunk000Sub000Block182Part019

def surrogateDiagonalTailChunk000Sub000Block182TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block182Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block182Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block182Part020
    + surrogateDiagTailX0RatChunk000Sub000Block182Part021
    + surrogateDiagTailX0RatChunk000Sub000Block182Part022
    + surrogateDiagTailX0RatChunk000Sub000Block182Part023
    + surrogateDiagTailX0RatChunk000Sub000Block182Part024

def surrogateDiagonalTailChunk000Sub000Block182Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block182HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block182MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block182TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block182 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block182Part000
    + surrogateDiagTailX0RatChunk000Sub000Block182Part001
    + surrogateDiagTailX0RatChunk000Sub000Block182Part002
    + surrogateDiagTailX0RatChunk000Sub000Block182Part003
    + surrogateDiagTailX0RatChunk000Sub000Block182Part004
    + surrogateDiagTailX0RatChunk000Sub000Block182Part005
    + surrogateDiagTailX0RatChunk000Sub000Block182Part006
    + surrogateDiagTailX0RatChunk000Sub000Block182Part007
    + surrogateDiagTailX0RatChunk000Sub000Block182Part008
    + surrogateDiagTailX0RatChunk000Sub000Block182Part009
    + surrogateDiagTailX0RatChunk000Sub000Block182Part010
    + surrogateDiagTailX0RatChunk000Sub000Block182Part011
    + surrogateDiagTailX0RatChunk000Sub000Block182Part012
    + surrogateDiagTailX0RatChunk000Sub000Block182Part013
    + surrogateDiagTailX0RatChunk000Sub000Block182Part014
    + surrogateDiagTailX0RatChunk000Sub000Block182Part015
    + surrogateDiagTailX0RatChunk000Sub000Block182Part016
    + surrogateDiagTailX0RatChunk000Sub000Block182Part017
    + surrogateDiagTailX0RatChunk000Sub000Block182Part018
    + surrogateDiagTailX0RatChunk000Sub000Block182Part019
    + surrogateDiagTailX0RatChunk000Sub000Block182Part020
    + surrogateDiagTailX0RatChunk000Sub000Block182Part021
    + surrogateDiagTailX0RatChunk000Sub000Block182Part022
    + surrogateDiagTailX0RatChunk000Sub000Block182Part023
    + surrogateDiagTailX0RatChunk000Sub000Block182Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block182_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block182Head + surrogateDiagTailX0RatChunk000Sub000Block182Mid + surrogateDiagTailX0RatChunk000Sub000Block182Tail =
      surrogateDiagTailX0RatChunk000Sub000Block182 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block182Head surrogateDiagTailX0RatChunk000Sub000Block182Mid surrogateDiagTailX0RatChunk000Sub000Block182Tail surrogateDiagTailX0RatChunk000Sub000Block182
  ring

def SurrogateDiagonalTailChunk000Sub000Block182HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block182HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block182Head

def SurrogateDiagonalTailChunk000Sub000Block182MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block182MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block182Mid

def SurrogateDiagonalTailChunk000Sub000Block182TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block182TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block182Tail

theorem surrogateDiagonalTailChunk000Sub000Block182_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block182HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block182MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block182TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block182Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block182 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block182HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block182MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block182TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block182Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block182_eq_head_add_mid_add_tail

/-- Block 183 covers tail-support indices [4575,4600) and q from 7577 to 7617. -/

def TailChunk000Sub000Block183Part000SupportExplicit : Finset ℕ :=
  ([7577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part000 : ℚ :=
  (897045765625 : ℚ) / 2059333723539190272

def SurrogateDiagonalTailChunk000Sub000Block183Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7577
    = surrogateDiagTailX0RatChunk000Sub000Block183Part000

theorem surrogateDiagonalTailChunk000Sub000Block183Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part000] using hcert

def TailChunk000Sub000Block183Part001SupportExplicit : Finset ℕ :=
  ([7579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part001 : ℚ :=
  (55306721381 : ℚ) / 75821996054937600

def SurrogateDiagonalTailChunk000Sub000Block183Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7579
    = surrogateDiagTailX0RatChunk000Sub000Block183Part001

theorem surrogateDiagonalTailChunk000Sub000Block183Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part001] using hcert

def TailChunk000Sub000Block183Part002SupportExplicit : Finset ℕ :=
  ([7582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part002 : ℚ :=
  (547965652025 : ℚ) / 132677546722983936

def SurrogateDiagonalTailChunk000Sub000Block183Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7582
    = surrogateDiagTailX0RatChunk000Sub000Block183Part002

theorem surrogateDiagonalTailChunk000Sub000Block183Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part002] using hcert

def TailChunk000Sub000Block183Part003SupportExplicit : Finset ℕ :=
  ([7583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part003 : ℚ :=
  (898467015625 : ℚ) / 2065865238087141522

def SurrogateDiagonalTailChunk000Sub000Block183Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7583
    = surrogateDiagTailX0RatChunk000Sub000Block183Part003

theorem surrogateDiagonalTailChunk000Sub000Block183Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part003] using hcert

def TailChunk000Sub000Block183Part004SupportExplicit : Finset ℕ :=
  ([7585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part004 : ℚ :=
  (5384518009 : ℚ) / 6116518291046400

def SurrogateDiagonalTailChunk000Sub000Block183Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7585
    = surrogateDiagTailX0RatChunk000Sub000Block183Part004

theorem surrogateDiagonalTailChunk000Sub000Block183Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part004] using hcert

def TailChunk000Sub000Block183Part005SupportExplicit : Finset ℕ :=
  ([7586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part005 : ℚ :=
  (1797996453775 : ℚ) / 517011464570830848

def SurrogateDiagonalTailChunk000Sub000Block183Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7586
    = surrogateDiagTailX0RatChunk000Sub000Block183Part005

theorem surrogateDiagonalTailChunk000Sub000Block183Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part005] using hcert

def TailChunk000Sub000Block183Part006SupportExplicit : Finset ℕ :=
  ([7589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part006 : ℚ :=
  (899889390625 : ℚ) / 2072412277156476192

def SurrogateDiagonalTailChunk000Sub000Block183Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7589
    = surrogateDiagTailX0RatChunk000Sub000Block183Part006

theorem surrogateDiagonalTailChunk000Sub000Block183Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part006] using hcert

def TailChunk000Sub000Block183Part007SupportExplicit : Finset ℕ :=
  ([7590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part007 : ℚ :=
  (6478134079 : ℚ) / 239926119628800

def SurrogateDiagonalTailChunk000Sub000Block183Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7590
    = surrogateDiagTailX0RatChunk000Sub000Block183Part007

theorem surrogateDiagonalTailChunk000Sub000Block183Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part007] using hcert

def TailChunk000Sub000Block183Part008SupportExplicit : Finset ℕ :=
  ([7591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part008 : ℚ :=
  (1440582025 : ℚ) / 3319356924247122

def SurrogateDiagonalTailChunk000Sub000Block183Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7591
    = surrogateDiagTailX0RatChunk000Sub000Block183Part008

theorem surrogateDiagonalTailChunk000Sub000Block183Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part008] using hcert

def TailChunk000Sub000Block183Part009SupportExplicit : Finset ℕ :=
  ([7593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part009 : ℚ :=
  (5003065423 : ℚ) / 4097971511416200

def SurrogateDiagonalTailChunk000Sub000Block183Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7593
    = surrogateDiagTailX0RatChunk000Sub000Block183Part009

theorem surrogateDiagonalTailChunk000Sub000Block183Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part009] using hcert

def TailChunk000Sub000Block183Part010SupportExplicit : Finset ℕ :=
  ([7594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part010 : ℚ :=
  (225268890625 : ℚ) / 129799100421318432

def SurrogateDiagonalTailChunk000Sub000Block183Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7594
    = surrogateDiagTailX0RatChunk000Sub000Block183Part010

theorem surrogateDiagonalTailChunk000Sub000Block183Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part010] using hcert

def TailChunk000Sub000Block183Part011SupportExplicit : Finset ℕ :=
  ([7597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part011 : ℚ :=
  (6990759161 : ℚ) / 15159067111980960

def SurrogateDiagonalTailChunk000Sub000Block183Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7597
    = surrogateDiagTailX0RatChunk000Sub000Block183Part011

theorem surrogateDiagonalTailChunk000Sub000Block183Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part011] using hcert

def TailChunk000Sub000Block183Part012SupportExplicit : Finset ℕ :=
  ([7598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part012 : ℚ :=
  (350407171 : ℚ) / 175587010540032

def SurrogateDiagonalTailChunk000Sub000Block183Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7598
    = surrogateDiagTailX0RatChunk000Sub000Block183Part012

theorem surrogateDiagonalTailChunk000Sub000Block183Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part012] using hcert

def TailChunk000Sub000Block183Part013SupportExplicit : Finset ℕ :=
  ([7599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part013 : ℚ :=
  (307898334675 : ℚ) / 209663283710394368

def SurrogateDiagonalTailChunk000Sub000Block183Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7599
    = surrogateDiagTailX0RatChunk000Sub000Block183Part013

theorem surrogateDiagonalTailChunk000Sub000Block183Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part013] using hcert

def TailChunk000Sub000Block183Part014SupportExplicit : Finset ℕ :=
  ([7601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part014 : ℚ :=
  (4210426649 : ℚ) / 7557218141400000

def SurrogateDiagonalTailChunk000Sub000Block183Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7601
    = surrogateDiagTailX0RatChunk000Sub000Block183Part014

theorem surrogateDiagonalTailChunk000Sub000Block183Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part014] using hcert

def TailChunk000Sub000Block183Part015SupportExplicit : Finset ℕ :=
  ([7602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part015 : ℚ :=
  (914659597 : ℚ) / 80637692313600

def SurrogateDiagonalTailChunk000Sub000Block183Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7602
    = surrogateDiagTailX0RatChunk000Sub000Block183Part015

theorem surrogateDiagonalTailChunk000Sub000Block183Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part015] using hcert

def TailChunk000Sub000Block183Part016SupportExplicit : Finset ℕ :=
  ([7603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part016 : ℚ :=
  (903212640625 : ℚ) / 2087749212901320402

def SurrogateDiagonalTailChunk000Sub000Block183Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7603
    = surrogateDiagTailX0RatChunk000Sub000Block183Part016

theorem surrogateDiagonalTailChunk000Sub000Block183Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part016] using hcert

def TailChunk000Sub000Block183Part017SupportExplicit : Finset ℕ :=
  ([7606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part017 : ℚ :=
  (225981390625 : ℚ) / 130621695791345202

def SurrogateDiagonalTailChunk000Sub000Block183Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7606
    = surrogateDiagTailX0RatChunk000Sub000Block183Part017

theorem surrogateDiagonalTailChunk000Sub000Block183Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part017] using hcert

def TailChunk000Sub000Block183Part018SupportExplicit : Finset ℕ :=
  ([7607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part018 : ℚ :=
  (904163265625 : ℚ) / 2092146787393150962

def SurrogateDiagonalTailChunk000Sub000Block183Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7607
    = surrogateDiagTailX0RatChunk000Sub000Block183Part018

theorem surrogateDiagonalTailChunk000Sub000Block183Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part018] using hcert

def TailChunk000Sub000Block183Part019SupportExplicit : Finset ℕ :=
  ([7609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part019 : ℚ :=
  (2950892768275 : ℚ) / 4507660108155120768

def SurrogateDiagonalTailChunk000Sub000Block183Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7609
    = surrogateDiagTailX0RatChunk000Sub000Block183Part019

theorem surrogateDiagonalTailChunk000Sub000Block183Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part019] using hcert

def TailChunk000Sub000Block183Part020SupportExplicit : Finset ℕ :=
  ([7610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part020 : ℚ :=
  (2025317979 : ℚ) / 569495013294080

def SurrogateDiagonalTailChunk000Sub000Block183Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7610
    = surrogateDiagTailX0RatChunk000Sub000Block183Part020

theorem surrogateDiagonalTailChunk000Sub000Block183Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part020] using hcert

def TailChunk000Sub000Block183Part021SupportExplicit : Finset ℕ :=
  ([7611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part021 : ℚ :=
  (119729624425 : ℚ) / 88051345090708608

def SurrogateDiagonalTailChunk000Sub000Block183Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7611
    = surrogateDiagTailX0RatChunk000Sub000Block183Part021

theorem surrogateDiagonalTailChunk000Sub000Block183Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part021] using hcert

def TailChunk000Sub000Block183Part022SupportExplicit : Finset ℕ :=
  ([7613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part022 : ℚ :=
  (54899969 : ℚ) / 112268554180992

def SurrogateDiagonalTailChunk000Sub000Block183Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7613
    = surrogateDiagTailX0RatChunk000Sub000Block183Part022

theorem surrogateDiagonalTailChunk000Sub000Block183Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part022] using hcert

def TailChunk000Sub000Block183Part023SupportExplicit : Finset ℕ :=
  ([7615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part023 : ℚ :=
  (869233387275 : ℚ) / 1144996552934496256

def SurrogateDiagonalTailChunk000Sub000Block183Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7615
    = surrogateDiagTailX0RatChunk000Sub000Block183Part023

theorem surrogateDiagonalTailChunk000Sub000Block183Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part023] using hcert

def TailChunk000Sub000Block183Part024SupportExplicit : Finset ℕ :=
  ([7617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block183Part024 : ℚ :=
  (251737274525 : ℚ) / 207502496226485136

def SurrogateDiagonalTailChunk000Sub000Block183Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7617
    = surrogateDiagTailX0RatChunk000Sub000Block183Part024

theorem surrogateDiagonalTailChunk000Sub000Block183Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block183Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block183Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block183Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block183Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block183Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block183Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block183HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block183Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block183Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block183Part000
    + surrogateDiagTailX0RatChunk000Sub000Block183Part001
    + surrogateDiagTailX0RatChunk000Sub000Block183Part002
    + surrogateDiagTailX0RatChunk000Sub000Block183Part003
    + surrogateDiagTailX0RatChunk000Sub000Block183Part004
    + surrogateDiagTailX0RatChunk000Sub000Block183Part005
    + surrogateDiagTailX0RatChunk000Sub000Block183Part006
    + surrogateDiagTailX0RatChunk000Sub000Block183Part007
    + surrogateDiagTailX0RatChunk000Sub000Block183Part008
    + surrogateDiagTailX0RatChunk000Sub000Block183Part009

def surrogateDiagonalTailChunk000Sub000Block183MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block183Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block183Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block183Part010
    + surrogateDiagTailX0RatChunk000Sub000Block183Part011
    + surrogateDiagTailX0RatChunk000Sub000Block183Part012
    + surrogateDiagTailX0RatChunk000Sub000Block183Part013
    + surrogateDiagTailX0RatChunk000Sub000Block183Part014
    + surrogateDiagTailX0RatChunk000Sub000Block183Part015
    + surrogateDiagTailX0RatChunk000Sub000Block183Part016
    + surrogateDiagTailX0RatChunk000Sub000Block183Part017
    + surrogateDiagTailX0RatChunk000Sub000Block183Part018
    + surrogateDiagTailX0RatChunk000Sub000Block183Part019

def surrogateDiagonalTailChunk000Sub000Block183TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block183Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block183Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block183Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block183Part020
    + surrogateDiagTailX0RatChunk000Sub000Block183Part021
    + surrogateDiagTailX0RatChunk000Sub000Block183Part022
    + surrogateDiagTailX0RatChunk000Sub000Block183Part023
    + surrogateDiagTailX0RatChunk000Sub000Block183Part024

def surrogateDiagonalTailChunk000Sub000Block183Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block183HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block183MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block183TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block183 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block183Part000
    + surrogateDiagTailX0RatChunk000Sub000Block183Part001
    + surrogateDiagTailX0RatChunk000Sub000Block183Part002
    + surrogateDiagTailX0RatChunk000Sub000Block183Part003
    + surrogateDiagTailX0RatChunk000Sub000Block183Part004
    + surrogateDiagTailX0RatChunk000Sub000Block183Part005
    + surrogateDiagTailX0RatChunk000Sub000Block183Part006
    + surrogateDiagTailX0RatChunk000Sub000Block183Part007
    + surrogateDiagTailX0RatChunk000Sub000Block183Part008
    + surrogateDiagTailX0RatChunk000Sub000Block183Part009
    + surrogateDiagTailX0RatChunk000Sub000Block183Part010
    + surrogateDiagTailX0RatChunk000Sub000Block183Part011
    + surrogateDiagTailX0RatChunk000Sub000Block183Part012
    + surrogateDiagTailX0RatChunk000Sub000Block183Part013
    + surrogateDiagTailX0RatChunk000Sub000Block183Part014
    + surrogateDiagTailX0RatChunk000Sub000Block183Part015
    + surrogateDiagTailX0RatChunk000Sub000Block183Part016
    + surrogateDiagTailX0RatChunk000Sub000Block183Part017
    + surrogateDiagTailX0RatChunk000Sub000Block183Part018
    + surrogateDiagTailX0RatChunk000Sub000Block183Part019
    + surrogateDiagTailX0RatChunk000Sub000Block183Part020
    + surrogateDiagTailX0RatChunk000Sub000Block183Part021
    + surrogateDiagTailX0RatChunk000Sub000Block183Part022
    + surrogateDiagTailX0RatChunk000Sub000Block183Part023
    + surrogateDiagTailX0RatChunk000Sub000Block183Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block183_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block183Head + surrogateDiagTailX0RatChunk000Sub000Block183Mid + surrogateDiagTailX0RatChunk000Sub000Block183Tail =
      surrogateDiagTailX0RatChunk000Sub000Block183 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block183Head surrogateDiagTailX0RatChunk000Sub000Block183Mid surrogateDiagTailX0RatChunk000Sub000Block183Tail surrogateDiagTailX0RatChunk000Sub000Block183
  ring

def SurrogateDiagonalTailChunk000Sub000Block183HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block183HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block183Head

def SurrogateDiagonalTailChunk000Sub000Block183MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block183MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block183Mid

def SurrogateDiagonalTailChunk000Sub000Block183TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block183TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block183Tail

theorem surrogateDiagonalTailChunk000Sub000Block183_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block183HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block183MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block183TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block183Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block183 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block183HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block183MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block183TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block183Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block183_eq_head_add_mid_add_tail

/-- Block 184 covers tail-support indices [4600,4625) and q from 7618 to 7655. -/

def TailChunk000Sub000Block184Part000SupportExplicit : Finset ℕ :=
  ([7618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part000 : ℚ :=
  (71378124125 : ℚ) / 31412463923257344

def SurrogateDiagonalTailChunk000Sub000Block184Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7618
    = surrogateDiagTailX0RatChunk000Sub000Block184Part000

theorem surrogateDiagonalTailChunk000Sub000Block184Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part000] using hcert

def TailChunk000Sub000Block184Part001SupportExplicit : Finset ℕ :=
  ([7619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part001 : ℚ :=
  (134648055757 : ℚ) / 268792307712000000

def SurrogateDiagonalTailChunk000Sub000Block184Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7619
    = surrogateDiagTailX0RatChunk000Sub000Block184Part001

theorem surrogateDiagonalTailChunk000Sub000Block184Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part001] using hcert

def TailChunk000Sub000Block184Part002SupportExplicit : Finset ℕ :=
  ([7621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part002 : ℚ :=
  (1451991025 : ℚ) / 3372148842269472

def SurrogateDiagonalTailChunk000Sub000Block184Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7621
    = surrogateDiagTailX0RatChunk000Sub000Block184Part002

theorem surrogateDiagonalTailChunk000Sub000Block184Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part002] using hcert

def TailChunk000Sub000Block184Part003SupportExplicit : Finset ℕ :=
  ([7622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part003 : ℚ :=
  (884601949075 : ℚ) / 454608497231382528

def SurrogateDiagonalTailChunk000Sub000Block184Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7622
    = surrogateDiagTailX0RatChunk000Sub000Block184Part003

theorem surrogateDiagonalTailChunk000Sub000Block184Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part003] using hcert

def TailChunk000Sub000Block184Part004SupportExplicit : Finset ℕ :=
  ([7626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part004 : ℚ :=
  (13439620361 : ℚ) / 1659211776000000

def SurrogateDiagonalTailChunk000Sub000Block184Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7626
    = surrogateDiagTailX0RatChunk000Sub000Block184Part004

theorem surrogateDiagonalTailChunk000Sub000Block184Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part004] using hcert

def TailChunk000Sub000Block184Part005SupportExplicit : Finset ℕ :=
  ([7627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part005 : ℚ :=
  (164288702925 : ℚ) / 344861612706408448

def SurrogateDiagonalTailChunk000Sub000Block184Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7627
    = surrogateDiagTailX0RatChunk000Sub000Block184Part005

theorem surrogateDiagonalTailChunk000Sub000Block184Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part005] using hcert

def TailChunk000Sub000Block184Part006SupportExplicit : Finset ℕ :=
  ([7629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part006 : ℚ :=
  (505062303025 : ℚ) / 417627448704943392

def SurrogateDiagonalTailChunk000Sub000Block184Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7629
    = surrogateDiagTailX0RatChunk000Sub000Block184Part006

theorem surrogateDiagonalTailChunk000Sub000Block184Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part006] using hcert

def TailChunk000Sub000Block184Part007SupportExplicit : Finset ℕ :=
  ([7630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part007 : ℚ :=
  (112556909875 : ℚ) / 18811160862916608

def SurrogateDiagonalTailChunk000Sub000Block184Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7630
    = surrogateDiagTailX0RatChunk000Sub000Block184Part007

theorem surrogateDiagonalTailChunk000Sub000Block184Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part007] using hcert

def TailChunk000Sub000Block184Part008SupportExplicit : Finset ℕ :=
  ([7631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part008 : ℚ :=
  (204161907625 : ℚ) / 382139846210544768

def SurrogateDiagonalTailChunk000Sub000Block184Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7631
    = surrogateDiagTailX0RatChunk000Sub000Block184Part008

theorem surrogateDiagonalTailChunk000Sub000Block184Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part008] using hcert

def TailChunk000Sub000Block184Part009SupportExplicit : Finset ℕ :=
  ([7633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part009 : ℚ :=
  (139260957375 : ℚ) / 275047437893107712

def SurrogateDiagonalTailChunk000Sub000Block184Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7633
    = surrogateDiagTailX0RatChunk000Sub000Block184Part009

theorem surrogateDiagonalTailChunk000Sub000Block184Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part009] using hcert

def TailChunk000Sub000Block184Part010SupportExplicit : Finset ℕ :=
  ([7634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part010 : ℚ :=
  (31941593429 : ℚ) / 7167393520065600

def SurrogateDiagonalTailChunk000Sub000Block184Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7634
    = surrogateDiagTailX0RatChunk000Sub000Block184Part010

theorem surrogateDiagonalTailChunk000Sub000Block184Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part010] using hcert

def TailChunk000Sub000Block184Part011SupportExplicit : Finset ℕ :=
  ([7635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part011 : ℚ :=
  (759403311425 : ℚ) / 341044979208290304

def SurrogateDiagonalTailChunk000Sub000Block184Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7635
    = surrogateDiagTailX0RatChunk000Sub000Block184Part011

theorem surrogateDiagonalTailChunk000Sub000Block184Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part011] using hcert

def TailChunk000Sub000Block184Part012SupportExplicit : Finset ℕ :=
  ([7637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part012 : ℚ :=
  (6440691491 : ℚ) / 10165420269518400

def SurrogateDiagonalTailChunk000Sub000Block184Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7637
    = surrogateDiagTailX0RatChunk000Sub000Block184Part012

theorem surrogateDiagonalTailChunk000Sub000Block184Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part012] using hcert

def TailChunk000Sub000Block184Part013SupportExplicit : Finset ℕ :=
  ([7638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part013 : ℚ :=
  (931364117425 : ℚ) / 79691610588530688

def SurrogateDiagonalTailChunk000Sub000Block184Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7638
    = surrogateDiagTailX0RatChunk000Sub000Block184Part013

theorem surrogateDiagonalTailChunk000Sub000Block184Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part013] using hcert

def TailChunk000Sub000Block184Part014SupportExplicit : Finset ℕ :=
  ([7639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part014 : ℚ :=
  (911786265625 : ℚ) / 2127577964778064242

def SurrogateDiagonalTailChunk000Sub000Block184Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7639
    = surrogateDiagTailX0RatChunk000Sub000Block184Part014

theorem surrogateDiagonalTailChunk000Sub000Block184Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part014] using hcert

def TailChunk000Sub000Block184Part015SupportExplicit : Finset ℕ :=
  ([7642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part015 : ℚ :=
  (72985604959 : ℚ) / 21298072538755200

def SurrogateDiagonalTailChunk000Sub000Block184Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7642
    = surrogateDiagTailX0RatChunk000Sub000Block184Part015

theorem surrogateDiagonalTailChunk000Sub000Block184Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part015] using hcert

def TailChunk000Sub000Block184Part016SupportExplicit : Finset ℕ :=
  ([7643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part016 : ℚ :=
  (912741390625 : ℚ) / 2132038294411213362

def SurrogateDiagonalTailChunk000Sub000Block184Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7643
    = surrogateDiagTailX0RatChunk000Sub000Block184Part016

theorem surrogateDiagonalTailChunk000Sub000Block184Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part016] using hcert

def TailChunk000Sub000Block184Part017SupportExplicit : Finset ℕ :=
  ([7645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part017 : ℚ :=
  (5114611069 : ℚ) / 5159060917862400

def SurrogateDiagonalTailChunk000Sub000Block184Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7645
    = surrogateDiagTailX0RatChunk000Sub000Block184Part017

theorem surrogateDiagonalTailChunk000Sub000Block184Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part017] using hcert

def TailChunk000Sub000Block184Part018SupportExplicit : Finset ℕ :=
  ([7646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part018 : ℚ :=
  (1826550741775 : ℚ) / 533567771825561928

def SurrogateDiagonalTailChunk000Sub000Block184Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7646
    = surrogateDiagTailX0RatChunk000Sub000Block184Part018

theorem surrogateDiagonalTailChunk000Sub000Block184Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part018] using hcert

def TailChunk000Sub000Block184Part019SupportExplicit : Finset ℕ :=
  ([7647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part019 : ℚ :=
  (1014897244475 : ℚ) / 843168824613233664

def SurrogateDiagonalTailChunk000Sub000Block184Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7647
    = surrogateDiagTailX0RatChunk000Sub000Block184Part019

theorem surrogateDiagonalTailChunk000Sub000Block184Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part019] using hcert

def TailChunk000Sub000Block184Part020SupportExplicit : Finset ℕ :=
  ([7649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part020 : ℚ :=
  (914175015625 : ℚ) / 2138741933819953152

def SurrogateDiagonalTailChunk000Sub000Block184Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7649
    = surrogateDiagTailX0RatChunk000Sub000Block184Part020

theorem surrogateDiagonalTailChunk000Sub000Block184Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part020] using hcert

def TailChunk000Sub000Block184Part021SupportExplicit : Finset ℕ :=
  ([7651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part021 : ℚ :=
  (2983568647375 : ℚ) / 4608105504612599808

def SurrogateDiagonalTailChunk000Sub000Block184Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7651
    = surrogateDiagTailX0RatChunk000Sub000Block184Part021

theorem surrogateDiagonalTailChunk000Sub000Block184Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part021] using hcert

def TailChunk000Sub000Block184Part022SupportExplicit : Finset ℕ :=
  ([7653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part022 : ℚ :=
  (325625099 : ℚ) / 1353310808040000

def SurrogateDiagonalTailChunk000Sub000Block184Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7653
    = surrogateDiagTailX0RatChunk000Sub000Block184Part022

theorem surrogateDiagonalTailChunk000Sub000Block184Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part022] using hcert

def TailChunk000Sub000Block184Part023SupportExplicit : Finset ℕ :=
  ([7654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part023 : ℚ :=
  (447064595975 : ℚ) / 233305358357643264

def SurrogateDiagonalTailChunk000Sub000Block184Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7654
    = surrogateDiagTailX0RatChunk000Sub000Block184Part023

theorem surrogateDiagonalTailChunk000Sub000Block184Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part023] using hcert

def TailChunk000Sub000Block184Part024SupportExplicit : Finset ℕ :=
  ([7655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block184Part024 : ℚ :=
  (4399934413 : ℚ) / 35077816144396800

def SurrogateDiagonalTailChunk000Sub000Block184Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7655
    = surrogateDiagTailX0RatChunk000Sub000Block184Part024

theorem surrogateDiagonalTailChunk000Sub000Block184Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block184Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block184Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block184Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block184Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block184Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block184Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block184HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block184Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block184Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block184Part000
    + surrogateDiagTailX0RatChunk000Sub000Block184Part001
    + surrogateDiagTailX0RatChunk000Sub000Block184Part002
    + surrogateDiagTailX0RatChunk000Sub000Block184Part003
    + surrogateDiagTailX0RatChunk000Sub000Block184Part004
    + surrogateDiagTailX0RatChunk000Sub000Block184Part005
    + surrogateDiagTailX0RatChunk000Sub000Block184Part006
    + surrogateDiagTailX0RatChunk000Sub000Block184Part007
    + surrogateDiagTailX0RatChunk000Sub000Block184Part008
    + surrogateDiagTailX0RatChunk000Sub000Block184Part009

def surrogateDiagonalTailChunk000Sub000Block184MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block184Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block184Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block184Part010
    + surrogateDiagTailX0RatChunk000Sub000Block184Part011
    + surrogateDiagTailX0RatChunk000Sub000Block184Part012
    + surrogateDiagTailX0RatChunk000Sub000Block184Part013
    + surrogateDiagTailX0RatChunk000Sub000Block184Part014
    + surrogateDiagTailX0RatChunk000Sub000Block184Part015
    + surrogateDiagTailX0RatChunk000Sub000Block184Part016
    + surrogateDiagTailX0RatChunk000Sub000Block184Part017
    + surrogateDiagTailX0RatChunk000Sub000Block184Part018
    + surrogateDiagTailX0RatChunk000Sub000Block184Part019

def surrogateDiagonalTailChunk000Sub000Block184TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block184Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block184Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block184Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block184Part020
    + surrogateDiagTailX0RatChunk000Sub000Block184Part021
    + surrogateDiagTailX0RatChunk000Sub000Block184Part022
    + surrogateDiagTailX0RatChunk000Sub000Block184Part023
    + surrogateDiagTailX0RatChunk000Sub000Block184Part024

def surrogateDiagonalTailChunk000Sub000Block184Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block184HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block184MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block184TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block184 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block184Part000
    + surrogateDiagTailX0RatChunk000Sub000Block184Part001
    + surrogateDiagTailX0RatChunk000Sub000Block184Part002
    + surrogateDiagTailX0RatChunk000Sub000Block184Part003
    + surrogateDiagTailX0RatChunk000Sub000Block184Part004
    + surrogateDiagTailX0RatChunk000Sub000Block184Part005
    + surrogateDiagTailX0RatChunk000Sub000Block184Part006
    + surrogateDiagTailX0RatChunk000Sub000Block184Part007
    + surrogateDiagTailX0RatChunk000Sub000Block184Part008
    + surrogateDiagTailX0RatChunk000Sub000Block184Part009
    + surrogateDiagTailX0RatChunk000Sub000Block184Part010
    + surrogateDiagTailX0RatChunk000Sub000Block184Part011
    + surrogateDiagTailX0RatChunk000Sub000Block184Part012
    + surrogateDiagTailX0RatChunk000Sub000Block184Part013
    + surrogateDiagTailX0RatChunk000Sub000Block184Part014
    + surrogateDiagTailX0RatChunk000Sub000Block184Part015
    + surrogateDiagTailX0RatChunk000Sub000Block184Part016
    + surrogateDiagTailX0RatChunk000Sub000Block184Part017
    + surrogateDiagTailX0RatChunk000Sub000Block184Part018
    + surrogateDiagTailX0RatChunk000Sub000Block184Part019
    + surrogateDiagTailX0RatChunk000Sub000Block184Part020
    + surrogateDiagTailX0RatChunk000Sub000Block184Part021
    + surrogateDiagTailX0RatChunk000Sub000Block184Part022
    + surrogateDiagTailX0RatChunk000Sub000Block184Part023
    + surrogateDiagTailX0RatChunk000Sub000Block184Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block184_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block184Head + surrogateDiagTailX0RatChunk000Sub000Block184Mid + surrogateDiagTailX0RatChunk000Sub000Block184Tail =
      surrogateDiagTailX0RatChunk000Sub000Block184 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block184Head surrogateDiagTailX0RatChunk000Sub000Block184Mid surrogateDiagTailX0RatChunk000Sub000Block184Tail surrogateDiagTailX0RatChunk000Sub000Block184
  ring

def SurrogateDiagonalTailChunk000Sub000Block184HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block184HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block184Head

def SurrogateDiagonalTailChunk000Sub000Block184MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block184MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block184Mid

def SurrogateDiagonalTailChunk000Sub000Block184TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block184TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block184Tail

theorem surrogateDiagonalTailChunk000Sub000Block184_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block184HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block184MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block184TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block184Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block184 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block184HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block184MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block184TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block184Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block184_eq_head_add_mid_add_tail

/-- Block 185 covers tail-support indices [4625,4650) and q from 7657 to 7697. -/

def TailChunk000Sub000Block185Part000SupportExplicit : Finset ℕ :=
  ([7657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part000 : ℚ :=
  (13733085007 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub000Block185Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7657
    = surrogateDiagTailX0RatChunk000Sub000Block185Part000

theorem surrogateDiagonalTailChunk000Sub000Block185Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part000] using hcert

def TailChunk000Sub000Block185Part001SupportExplicit : Finset ℕ :=
  ([7658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part001 : ℚ :=
  (821840147125 : ℚ) / 288006594038287488

def SurrogateDiagonalTailChunk000Sub000Block185Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7658
    = surrogateDiagTailX0RatChunk000Sub000Block185Part001

theorem surrogateDiagonalTailChunk000Sub000Block185Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part001] using hcert

def TailChunk000Sub000Block185Part002SupportExplicit : Finset ℕ :=
  ([7661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part002 : ℚ :=
  (1351385825 : ℚ) / 160648622651350296

def SurrogateDiagonalTailChunk000Sub000Block185Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7661
    = surrogateDiagTailX0RatChunk000Sub000Block185Part002

theorem surrogateDiagonalTailChunk000Sub000Block185Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part002] using hcert

def TailChunk000Sub000Block185Part003SupportExplicit : Finset ℕ :=
  ([7662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part003 : ℚ :=
  (713073893725 : ℚ) / 106059491135735808

def SurrogateDiagonalTailChunk000Sub000Block185Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7662
    = surrogateDiagTailX0RatChunk000Sub000Block185Part003

theorem surrogateDiagonalTailChunk000Sub000Block185Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part003] using hcert

def TailChunk000Sub000Block185Part004SupportExplicit : Finset ℕ :=
  ([7663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part004 : ℚ :=
  (53908962625 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk000Sub000Block185Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7663
    = surrogateDiagTailX0RatChunk000Sub000Block185Part004

theorem surrogateDiagonalTailChunk000Sub000Block185Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part004] using hcert

def TailChunk000Sub000Block185Part005SupportExplicit : Finset ℕ :=
  ([7665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part005 : ℚ :=
  (377366560025 : ℚ) / 178357673366913024

def SurrogateDiagonalTailChunk000Sub000Block185Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7665
    = surrogateDiagTailX0RatChunk000Sub000Block185Part005

theorem surrogateDiagonalTailChunk000Sub000Block185Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part005] using hcert

def TailChunk000Sub000Block185Part006SupportExplicit : Finset ℕ :=
  ([7666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part006 : ℚ :=
  (229560765625 : ℚ) / 134793474855670272

def SurrogateDiagonalTailChunk000Sub000Block185Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7666
    = surrogateDiagTailX0RatChunk000Sub000Block185Part006

theorem surrogateDiagonalTailChunk000Sub000Block185Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part006] using hcert

def TailChunk000Sub000Block185Part007SupportExplicit : Finset ℕ :=
  ([7667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part007 : ℚ :=
  (2796790901 : ℚ) / 33561142886400000

def SurrogateDiagonalTailChunk000Sub000Block185Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7667
    = surrogateDiagTailX0RatChunk000Sub000Block185Part007

theorem surrogateDiagonalTailChunk000Sub000Block185Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part007] using hcert

def TailChunk000Sub000Block185Part008SupportExplicit : Finset ℕ :=
  ([7669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7669
    = surrogateDiagTailX0RatChunk000Sub000Block185Part008

theorem surrogateDiagonalTailChunk000Sub000Block185Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part008] using hcert

def TailChunk000Sub000Block185Part009SupportExplicit : Finset ℕ :=
  ([7670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part009 : ℚ :=
  (249282886475 : ℚ) / 50070569136685056

def SurrogateDiagonalTailChunk000Sub000Block185Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7670
    = surrogateDiagTailX0RatChunk000Sub000Block185Part009

theorem surrogateDiagonalTailChunk000Sub000Block185Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part009] using hcert

def TailChunk000Sub000Block185Part010SupportExplicit : Finset ℕ :=
  ([7671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part010 : ℚ :=
  (408551770475 : ℚ) / 853808047353897984

def SurrogateDiagonalTailChunk000Sub000Block185Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7671
    = surrogateDiagTailX0RatChunk000Sub000Block185Part010

theorem surrogateDiagonalTailChunk000Sub000Block185Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part010] using hcert

def TailChunk000Sub000Block185Part011SupportExplicit : Finset ℕ :=
  ([7673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7673
    = surrogateDiagTailX0RatChunk000Sub000Block185Part011

theorem surrogateDiagonalTailChunk000Sub000Block185Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part011] using hcert

def TailChunk000Sub000Block185Part012SupportExplicit : Finset ℕ :=
  ([7674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part012 : ℚ :=
  (10074775025 : ℚ) / 1503183181961088

def SurrogateDiagonalTailChunk000Sub000Block185Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7674
    = surrogateDiagTailX0RatChunk000Sub000Block185Part012

theorem surrogateDiagonalTailChunk000Sub000Block185Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part012] using hcert

def TailChunk000Sub000Block185Part013SupportExplicit : Finset ℕ :=
  ([7678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part013 : ℚ :=
  (17171513771 : ℚ) / 7334556025881600

def SurrogateDiagonalTailChunk000Sub000Block185Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7678
    = surrogateDiagTailX0RatChunk000Sub000Block185Part013

theorem surrogateDiagonalTailChunk000Sub000Block185Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part013] using hcert

def TailChunk000Sub000Block185Part014SupportExplicit : Finset ℕ :=
  ([7679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part014 : ℚ :=
  (376953921775 : ℚ) / 4675995418926809088

def SurrogateDiagonalTailChunk000Sub000Block185Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7679
    = surrogateDiagTailX0RatChunk000Sub000Block185Part014

theorem surrogateDiagonalTailChunk000Sub000Block185Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part014] using hcert

def TailChunk000Sub000Block185Part015SupportExplicit : Finset ℕ :=
  ([7681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7681
    = surrogateDiagTailX0RatChunk000Sub000Block185Part015

theorem surrogateDiagonalTailChunk000Sub000Block185Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part015] using hcert

def TailChunk000Sub000Block185Part016SupportExplicit : Finset ℕ :=
  ([7682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part016 : ℚ :=
  (40399485175 : ℚ) / 20217490769936064

def SurrogateDiagonalTailChunk000Sub000Block185Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7682
    = surrogateDiagTailX0RatChunk000Sub000Block185Part016

theorem surrogateDiagonalTailChunk000Sub000Block185Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part016] using hcert

def TailChunk000Sub000Block185Part017SupportExplicit : Finset ℕ :=
  ([7683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part017 : ℚ :=
  (811672890625 : ℚ) / 1224323290303561728

def SurrogateDiagonalTailChunk000Sub000Block185Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7683
    = surrogateDiagTailX0RatChunk000Sub000Block185Part017

theorem surrogateDiagonalTailChunk000Sub000Block185Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part017] using hcert

def TailChunk000Sub000Block185Part018SupportExplicit : Finset ℕ :=
  ([7685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part018 : ℚ :=
  (247748638175 : ℚ) / 1438408790343942144

def SurrogateDiagonalTailChunk000Sub000Block185Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7685
    = surrogateDiagTailX0RatChunk000Sub000Block185Part018

theorem surrogateDiagonalTailChunk000Sub000Block185Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part018] using hcert

def TailChunk000Sub000Block185Part019SupportExplicit : Finset ℕ :=
  ([7687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7687
    = surrogateDiagTailX0RatChunk000Sub000Block185Part019

theorem surrogateDiagonalTailChunk000Sub000Block185Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part019] using hcert

def TailChunk000Sub000Block185Part020SupportExplicit : Finset ℕ :=
  ([7689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part020 : ℚ :=
  (32673346159 : ℚ) / 46361638089523200

def SurrogateDiagonalTailChunk000Sub000Block185Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7689
    = surrogateDiagTailX0RatChunk000Sub000Block185Part020

theorem surrogateDiagonalTailChunk000Sub000Block185Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part020] using hcert

def TailChunk000Sub000Block185Part021SupportExplicit : Finset ℕ :=
  ([7690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part021 : ℚ :=
  (775541297125 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk000Sub000Block185Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7690
    = surrogateDiagTailX0RatChunk000Sub000Block185Part021

theorem surrogateDiagonalTailChunk000Sub000Block185Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part021] using hcert

def TailChunk000Sub000Block185Part022SupportExplicit : Finset ℕ :=
  ([7691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block185Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7691
    = surrogateDiagTailX0RatChunk000Sub000Block185Part022

theorem surrogateDiagonalTailChunk000Sub000Block185Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part022] using hcert

def TailChunk000Sub000Block185Part023SupportExplicit : Finset ℕ :=
  ([7694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part023 : ℚ :=
  (1849556139775 : ℚ) / 547096552992752328

def SurrogateDiagonalTailChunk000Sub000Block185Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7694
    = surrogateDiagTailX0RatChunk000Sub000Block185Part023

theorem surrogateDiagonalTailChunk000Sub000Block185Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part023] using hcert

def TailChunk000Sub000Block185Part024SupportExplicit : Finset ℕ :=
  ([7697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block185Part024 : ℚ :=
  (197796896875 : ℚ) / 433941838459569216

def SurrogateDiagonalTailChunk000Sub000Block185Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7697
    = surrogateDiagTailX0RatChunk000Sub000Block185Part024

theorem surrogateDiagonalTailChunk000Sub000Block185Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block185Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block185Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block185Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block185Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block185Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block185Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block185HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block185Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block185Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block185Part000
    + surrogateDiagTailX0RatChunk000Sub000Block185Part001
    + surrogateDiagTailX0RatChunk000Sub000Block185Part002
    + surrogateDiagTailX0RatChunk000Sub000Block185Part003
    + surrogateDiagTailX0RatChunk000Sub000Block185Part004
    + surrogateDiagTailX0RatChunk000Sub000Block185Part005
    + surrogateDiagTailX0RatChunk000Sub000Block185Part006
    + surrogateDiagTailX0RatChunk000Sub000Block185Part007
    + surrogateDiagTailX0RatChunk000Sub000Block185Part008
    + surrogateDiagTailX0RatChunk000Sub000Block185Part009

def surrogateDiagonalTailChunk000Sub000Block185MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block185Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block185Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block185Part010
    + surrogateDiagTailX0RatChunk000Sub000Block185Part011
    + surrogateDiagTailX0RatChunk000Sub000Block185Part012
    + surrogateDiagTailX0RatChunk000Sub000Block185Part013
    + surrogateDiagTailX0RatChunk000Sub000Block185Part014
    + surrogateDiagTailX0RatChunk000Sub000Block185Part015
    + surrogateDiagTailX0RatChunk000Sub000Block185Part016
    + surrogateDiagTailX0RatChunk000Sub000Block185Part017
    + surrogateDiagTailX0RatChunk000Sub000Block185Part018
    + surrogateDiagTailX0RatChunk000Sub000Block185Part019

def surrogateDiagonalTailChunk000Sub000Block185TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block185Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block185Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block185Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block185Part020
    + surrogateDiagTailX0RatChunk000Sub000Block185Part021
    + surrogateDiagTailX0RatChunk000Sub000Block185Part022
    + surrogateDiagTailX0RatChunk000Sub000Block185Part023
    + surrogateDiagTailX0RatChunk000Sub000Block185Part024

def surrogateDiagonalTailChunk000Sub000Block185Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block185HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block185MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block185TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block185 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block185Part000
    + surrogateDiagTailX0RatChunk000Sub000Block185Part001
    + surrogateDiagTailX0RatChunk000Sub000Block185Part002
    + surrogateDiagTailX0RatChunk000Sub000Block185Part003
    + surrogateDiagTailX0RatChunk000Sub000Block185Part004
    + surrogateDiagTailX0RatChunk000Sub000Block185Part005
    + surrogateDiagTailX0RatChunk000Sub000Block185Part006
    + surrogateDiagTailX0RatChunk000Sub000Block185Part007
    + surrogateDiagTailX0RatChunk000Sub000Block185Part008
    + surrogateDiagTailX0RatChunk000Sub000Block185Part009
    + surrogateDiagTailX0RatChunk000Sub000Block185Part010
    + surrogateDiagTailX0RatChunk000Sub000Block185Part011
    + surrogateDiagTailX0RatChunk000Sub000Block185Part012
    + surrogateDiagTailX0RatChunk000Sub000Block185Part013
    + surrogateDiagTailX0RatChunk000Sub000Block185Part014
    + surrogateDiagTailX0RatChunk000Sub000Block185Part015
    + surrogateDiagTailX0RatChunk000Sub000Block185Part016
    + surrogateDiagTailX0RatChunk000Sub000Block185Part017
    + surrogateDiagTailX0RatChunk000Sub000Block185Part018
    + surrogateDiagTailX0RatChunk000Sub000Block185Part019
    + surrogateDiagTailX0RatChunk000Sub000Block185Part020
    + surrogateDiagTailX0RatChunk000Sub000Block185Part021
    + surrogateDiagTailX0RatChunk000Sub000Block185Part022
    + surrogateDiagTailX0RatChunk000Sub000Block185Part023
    + surrogateDiagTailX0RatChunk000Sub000Block185Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block185_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block185Head + surrogateDiagTailX0RatChunk000Sub000Block185Mid + surrogateDiagTailX0RatChunk000Sub000Block185Tail =
      surrogateDiagTailX0RatChunk000Sub000Block185 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block185Head surrogateDiagTailX0RatChunk000Sub000Block185Mid surrogateDiagTailX0RatChunk000Sub000Block185Tail surrogateDiagTailX0RatChunk000Sub000Block185
  ring

def SurrogateDiagonalTailChunk000Sub000Block185HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block185HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block185Head

def SurrogateDiagonalTailChunk000Sub000Block185MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block185MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block185Mid

def SurrogateDiagonalTailChunk000Sub000Block185TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block185TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block185Tail

theorem surrogateDiagonalTailChunk000Sub000Block185_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block185HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block185MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block185TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block185Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block185 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block185HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block185MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block185TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block185Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block185_eq_head_add_mid_add_tail

/-- Block 186 covers tail-support indices [4650,4675) and q from 7698 to 7735. -/

def TailChunk000Sub000Block186Part000SupportExplicit : Finset ℕ :=
  ([7698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part000 : ℚ :=
  (513975130475 : ℚ) / 54034227456074304

def SurrogateDiagonalTailChunk000Sub000Block186Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7698
    = surrogateDiagTailX0RatChunk000Sub000Block186Part000

theorem surrogateDiagonalTailChunk000Sub000Block186Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part000] using hcert

def TailChunk000Sub000Block186Part001SupportExplicit : Finset ℕ :=
  ([7699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part001 : ℚ :=
  (926165640625 : ℚ) / 2195222243353349202

def SurrogateDiagonalTailChunk000Sub000Block186Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7699
    = surrogateDiagTailX0RatChunk000Sub000Block186Part001

theorem surrogateDiagonalTailChunk000Sub000Block186Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part001] using hcert

def TailChunk000Sub000Block186Part002SupportExplicit : Finset ℕ :=
  ([7701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part002 : ℚ :=
  (37919811653 : ℚ) / 26547388416000000

def SurrogateDiagonalTailChunk000Sub000Block186Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7701
    = surrogateDiagTailX0RatChunk000Sub000Block186Part002

theorem surrogateDiagonalTailChunk000Sub000Block186Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part002] using hcert

def TailChunk000Sub000Block186Part003SupportExplicit : Finset ℕ :=
  ([7702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part003 : ℚ :=
  (74136174799 : ℚ) / 21975044755125000

def SurrogateDiagonalTailChunk000Sub000Block186Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7702
    = surrogateDiagTailX0RatChunk000Sub000Block186Part003

theorem surrogateDiagonalTailChunk000Sub000Block186Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part003] using hcert

def TailChunk000Sub000Block186Part004SupportExplicit : Finset ℕ :=
  ([7703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part004 : ℚ :=
  (927128265625 : ℚ) / 2199788486727410802

def SurrogateDiagonalTailChunk000Sub000Block186Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7703
    = surrogateDiagTailX0RatChunk000Sub000Block186Part004

theorem surrogateDiagonalTailChunk000Sub000Block186Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part004] using hcert

def TailChunk000Sub000Block186Part005SupportExplicit : Finset ℕ :=
  ([7705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part005 : ℚ :=
  (1238080594925 : ℚ) / 1422667118581530624

def SurrogateDiagonalTailChunk000Sub000Block186Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7705
    = surrogateDiagTailX0RatChunk000Sub000Block186Part005

theorem surrogateDiagonalTailChunk000Sub000Block186Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part005] using hcert

def TailChunk000Sub000Block186Part006SupportExplicit : Finset ℕ :=
  ([7706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part006 : ℚ :=
  (1855329984775 : ℚ) / 550518569480596608

def SurrogateDiagonalTailChunk000Sub000Block186Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7706
    = surrogateDiagTailX0RatChunk000Sub000Block186Part006

theorem surrogateDiagonalTailChunk000Sub000Block186Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part006] using hcert

def TailChunk000Sub000Block186Part007SupportExplicit : Finset ℕ :=
  ([7707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part007 : ℚ :=
  (5856803825 : ℚ) / 3230603780037696

def SurrogateDiagonalTailChunk000Sub000Block186Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7707
    = surrogateDiagTailX0RatChunk000Sub000Block186Part007

theorem surrogateDiagonalTailChunk000Sub000Block186Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part007] using hcert

def TailChunk000Sub000Block186Part008SupportExplicit : Finset ℕ :=
  ([7709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part008 : ℚ :=
  (275983393175 : ℚ) / 530710186891935744

def SurrogateDiagonalTailChunk000Sub000Block186Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7709
    = surrogateDiagTailX0RatChunk000Sub000Block186Part008

theorem surrogateDiagonalTailChunk000Sub000Block186Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part008] using hcert

def TailChunk000Sub000Block186Part009SupportExplicit : Finset ℕ :=
  ([7710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part009 : ℚ :=
  (174262611075 : ℚ) / 14663087068020736

def SurrogateDiagonalTailChunk000Sub000Block186Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7710
    = surrogateDiagTailX0RatChunk000Sub000Block186Part009

theorem surrogateDiagonalTailChunk000Sub000Block186Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part009] using hcert

def TailChunk000Sub000Block186Part010SupportExplicit : Finset ℕ :=
  ([7711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part010 : ℚ :=
  (12999692497 : ℚ) / 24014802000000000

def SurrogateDiagonalTailChunk000Sub000Block186Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7711
    = surrogateDiagTailX0RatChunk000Sub000Block186Part010

theorem surrogateDiagonalTailChunk000Sub000Block186Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part010] using hcert

def TailChunk000Sub000Block186Part011SupportExplicit : Finset ℕ :=
  ([7714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part011 : ℚ :=
  (194624078275 : ℚ) / 52274996796137472

def SurrogateDiagonalTailChunk000Sub000Block186Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7714
    = surrogateDiagTailX0RatChunk000Sub000Block186Part011

theorem surrogateDiagonalTailChunk000Sub000Block186Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part011] using hcert

def TailChunk000Sub000Block186Part012SupportExplicit : Finset ℕ :=
  ([7715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part012 : ℚ :=
  (2676650887825 : ℚ) / 3619131130895321088

def SurrogateDiagonalTailChunk000Sub000Block186Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7715
    = surrogateDiagTailX0RatChunk000Sub000Block186Part012

theorem surrogateDiagonalTailChunk000Sub000Block186Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part012] using hcert

def TailChunk000Sub000Block186Part013SupportExplicit : Finset ℕ :=
  ([7717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part013 : ℚ :=
  (930501390625 : ℚ) / 2215826456464917792

def SurrogateDiagonalTailChunk000Sub000Block186Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7717
    = surrogateDiagTailX0RatChunk000Sub000Block186Part013

theorem surrogateDiagonalTailChunk000Sub000Block186Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part013] using hcert

def TailChunk000Sub000Block186Part014SupportExplicit : Finset ℕ :=
  ([7718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part014 : ℚ :=
  (889395954025 : ℚ) / 427504357794643968

def SurrogateDiagonalTailChunk000Sub000Block186Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7718
    = surrogateDiagTailX0RatChunk000Sub000Block186Part014

theorem surrogateDiagonalTailChunk000Sub000Block186Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part014] using hcert

def TailChunk000Sub000Block186Part015SupportExplicit : Finset ℕ :=
  ([7719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part015 : ℚ :=
  (7832999263 : ℚ) / 5860669909201920

def SurrogateDiagonalTailChunk000Sub000Block186Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7719
    = surrogateDiagTailX0RatChunk000Sub000Block186Part015

theorem surrogateDiagonalTailChunk000Sub000Block186Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part015] using hcert

def TailChunk000Sub000Block186Part016SupportExplicit : Finset ℕ :=
  ([7721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part016 : ℚ :=
  (164579834975 : ℚ) / 265512965513587776

def SurrogateDiagonalTailChunk000Sub000Block186Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7721
    = surrogateDiagTailX0RatChunk000Sub000Block186Part016

theorem surrogateDiagonalTailChunk000Sub000Block186Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part016] using hcert

def TailChunk000Sub000Block186Part017SupportExplicit : Finset ℕ :=
  ([7723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part017 : ℚ :=
  (931948890625 : ℚ) / 2222726650409204082

def SurrogateDiagonalTailChunk000Sub000Block186Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7723
    = surrogateDiagTailX0RatChunk000Sub000Block186Part017

theorem surrogateDiagonalTailChunk000Sub000Block186Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part017] using hcert

def TailChunk000Sub000Block186Part018SupportExplicit : Finset ℕ :=
  ([7726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part018 : ℚ :=
  (233168265625 : ℚ) / 139064393268400242

def SurrogateDiagonalTailChunk000Sub000Block186Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7726
    = surrogateDiagTailX0RatChunk000Sub000Block186Part018

theorem surrogateDiagonalTailChunk000Sub000Block186Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part018] using hcert

def TailChunk000Sub000Block186Part019SupportExplicit : Finset ℕ :=
  ([7727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part019 : ℚ :=
  (932914515625 : ℚ) / 2227335724342864722

def SurrogateDiagonalTailChunk000Sub000Block186Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7727
    = surrogateDiagTailX0RatChunk000Sub000Block186Part019

theorem surrogateDiagonalTailChunk000Sub000Block186Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part019] using hcert

def TailChunk000Sub000Block186Part020SupportExplicit : Finset ℕ :=
  ([7729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part020 : ℚ :=
  (144436024093 : ℚ) / 323275084344451200

def SurrogateDiagonalTailChunk000Sub000Block186Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7729
    = surrogateDiagTailX0RatChunk000Sub000Block186Part020

theorem surrogateDiagonalTailChunk000Sub000Block186Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part020] using hcert

def TailChunk000Sub000Block186Part021SupportExplicit : Finset ℕ :=
  ([7730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part021 : ℚ :=
  (820861739275 : ℚ) / 227371499290656768

def SurrogateDiagonalTailChunk000Sub000Block186Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7730
    = surrogateDiagTailX0RatChunk000Sub000Block186Part021

theorem surrogateDiagonalTailChunk000Sub000Block186Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part021] using hcert

def TailChunk000Sub000Block186Part022SupportExplicit : Finset ℕ :=
  ([7733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part022 : ℚ :=
  (117404093737 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub000Block186Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7733
    = surrogateDiagTailX0RatChunk000Sub000Block186Part022

theorem surrogateDiagonalTailChunk000Sub000Block186Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part022] using hcert

def TailChunk000Sub000Block186Part023SupportExplicit : Finset ℕ :=
  ([7734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part023 : ℚ :=
  (726537201025 : ℚ) / 110105824567001088

def SurrogateDiagonalTailChunk000Sub000Block186Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7734
    = surrogateDiagTailX0RatChunk000Sub000Block186Part023

theorem surrogateDiagonalTailChunk000Sub000Block186Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part023] using hcert

def TailChunk000Sub000Block186Part024SupportExplicit : Finset ℕ :=
  ([7735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block186Part024 : ℚ :=
  (103259268275 : ℚ) / 62633147300315136

def SurrogateDiagonalTailChunk000Sub000Block186Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7735
    = surrogateDiagTailX0RatChunk000Sub000Block186Part024

theorem surrogateDiagonalTailChunk000Sub000Block186Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block186Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block186Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block186Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block186Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block186Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block186Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block186HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block186Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block186Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block186Part000
    + surrogateDiagTailX0RatChunk000Sub000Block186Part001
    + surrogateDiagTailX0RatChunk000Sub000Block186Part002
    + surrogateDiagTailX0RatChunk000Sub000Block186Part003
    + surrogateDiagTailX0RatChunk000Sub000Block186Part004
    + surrogateDiagTailX0RatChunk000Sub000Block186Part005
    + surrogateDiagTailX0RatChunk000Sub000Block186Part006
    + surrogateDiagTailX0RatChunk000Sub000Block186Part007
    + surrogateDiagTailX0RatChunk000Sub000Block186Part008
    + surrogateDiagTailX0RatChunk000Sub000Block186Part009

def surrogateDiagonalTailChunk000Sub000Block186MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block186Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block186Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block186Part010
    + surrogateDiagTailX0RatChunk000Sub000Block186Part011
    + surrogateDiagTailX0RatChunk000Sub000Block186Part012
    + surrogateDiagTailX0RatChunk000Sub000Block186Part013
    + surrogateDiagTailX0RatChunk000Sub000Block186Part014
    + surrogateDiagTailX0RatChunk000Sub000Block186Part015
    + surrogateDiagTailX0RatChunk000Sub000Block186Part016
    + surrogateDiagTailX0RatChunk000Sub000Block186Part017
    + surrogateDiagTailX0RatChunk000Sub000Block186Part018
    + surrogateDiagTailX0RatChunk000Sub000Block186Part019

def surrogateDiagonalTailChunk000Sub000Block186TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block186Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block186Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block186Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block186Part020
    + surrogateDiagTailX0RatChunk000Sub000Block186Part021
    + surrogateDiagTailX0RatChunk000Sub000Block186Part022
    + surrogateDiagTailX0RatChunk000Sub000Block186Part023
    + surrogateDiagTailX0RatChunk000Sub000Block186Part024

def surrogateDiagonalTailChunk000Sub000Block186Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block186HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block186MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block186TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block186 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block186Part000
    + surrogateDiagTailX0RatChunk000Sub000Block186Part001
    + surrogateDiagTailX0RatChunk000Sub000Block186Part002
    + surrogateDiagTailX0RatChunk000Sub000Block186Part003
    + surrogateDiagTailX0RatChunk000Sub000Block186Part004
    + surrogateDiagTailX0RatChunk000Sub000Block186Part005
    + surrogateDiagTailX0RatChunk000Sub000Block186Part006
    + surrogateDiagTailX0RatChunk000Sub000Block186Part007
    + surrogateDiagTailX0RatChunk000Sub000Block186Part008
    + surrogateDiagTailX0RatChunk000Sub000Block186Part009
    + surrogateDiagTailX0RatChunk000Sub000Block186Part010
    + surrogateDiagTailX0RatChunk000Sub000Block186Part011
    + surrogateDiagTailX0RatChunk000Sub000Block186Part012
    + surrogateDiagTailX0RatChunk000Sub000Block186Part013
    + surrogateDiagTailX0RatChunk000Sub000Block186Part014
    + surrogateDiagTailX0RatChunk000Sub000Block186Part015
    + surrogateDiagTailX0RatChunk000Sub000Block186Part016
    + surrogateDiagTailX0RatChunk000Sub000Block186Part017
    + surrogateDiagTailX0RatChunk000Sub000Block186Part018
    + surrogateDiagTailX0RatChunk000Sub000Block186Part019
    + surrogateDiagTailX0RatChunk000Sub000Block186Part020
    + surrogateDiagTailX0RatChunk000Sub000Block186Part021
    + surrogateDiagTailX0RatChunk000Sub000Block186Part022
    + surrogateDiagTailX0RatChunk000Sub000Block186Part023
    + surrogateDiagTailX0RatChunk000Sub000Block186Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block186_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block186Head + surrogateDiagTailX0RatChunk000Sub000Block186Mid + surrogateDiagTailX0RatChunk000Sub000Block186Tail =
      surrogateDiagTailX0RatChunk000Sub000Block186 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block186Head surrogateDiagTailX0RatChunk000Sub000Block186Mid surrogateDiagTailX0RatChunk000Sub000Block186Tail surrogateDiagTailX0RatChunk000Sub000Block186
  ring

def SurrogateDiagonalTailChunk000Sub000Block186HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block186HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block186Head

def SurrogateDiagonalTailChunk000Sub000Block186MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block186MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block186Mid

def SurrogateDiagonalTailChunk000Sub000Block186TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block186TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block186Tail

theorem surrogateDiagonalTailChunk000Sub000Block186_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block186HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block186MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block186TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block186Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block186 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block186HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block186MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block186TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block186Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block186_eq_head_add_mid_add_tail

/-- Block 187 covers tail-support indices [4675,4700) and q from 7737 to 7778. -/

def TailChunk000Sub000Block187Part000SupportExplicit : Finset ℕ :=
  ([7737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part000 : ℚ :=
  (32466537925 : ℚ) / 27612041638476882

def SurrogateDiagonalTailChunk000Sub000Block187Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7737
    = surrogateDiagTailX0RatChunk000Sub000Block187Part000

theorem surrogateDiagonalTailChunk000Sub000Block187Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part000] using hcert

def TailChunk000Sub000Block187Part001SupportExplicit : Finset ℕ :=
  ([7738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part001 : ℚ :=
  (914159302975 : ℚ) / 491326534435995648

def SurrogateDiagonalTailChunk000Sub000Block187Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7738
    = surrogateDiagTailX0RatChunk000Sub000Block187Part001

theorem surrogateDiagonalTailChunk000Sub000Block187Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part001] using hcert

def TailChunk000Sub000Block187Part002SupportExplicit : Finset ℕ :=
  ([7739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part002 : ℚ :=
  (4145110799 : ℚ) / 9334820856453120

def SurrogateDiagonalTailChunk000Sub000Block187Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7739
    = surrogateDiagTailX0RatChunk000Sub000Block187Part002

theorem surrogateDiagonalTailChunk000Sub000Block187Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part002] using hcert

def TailChunk000Sub000Block187Part003SupportExplicit : Finset ℕ :=
  ([7741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part003 : ℚ :=
  (1498077025 : ℚ) / 3589638321867552

def SurrogateDiagonalTailChunk000Sub000Block187Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7741
    = surrogateDiagTailX0RatChunk000Sub000Block187Part003

theorem surrogateDiagonalTailChunk000Sub000Block187Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part003] using hcert

def TailChunk000Sub000Block187Part004SupportExplicit : Finset ℕ :=
  ([7743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part004 : ℚ :=
  (655834387575 : ℚ) / 491573429955198976

def SurrogateDiagonalTailChunk000Sub000Block187Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7743
    = surrogateDiagTailX0RatChunk000Sub000Block187Part004

theorem surrogateDiagonalTailChunk000Sub000Block187Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part004] using hcert

def TailChunk000Sub000Block187Part005SupportExplicit : Finset ℕ :=
  ([7745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part005 : ℚ :=
  (474566724475 : ℚ) / 612631606932062208

def SurrogateDiagonalTailChunk000Sub000Block187Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7745
    = surrogateDiagTailX0RatChunk000Sub000Block187Part005

theorem surrogateDiagonalTailChunk000Sub000Block187Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part005] using hcert

def TailChunk000Sub000Block187Part006SupportExplicit : Finset ℕ :=
  ([7746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part006 : ℚ :=
  (29151733507 : ℚ) / 4431652249219200

def SurrogateDiagonalTailChunk000Sub000Block187Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7746
    = surrogateDiagTailX0RatChunk000Sub000Block187Part006

theorem surrogateDiagonalTailChunk000Sub000Block187Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part006] using hcert

def TailChunk000Sub000Block187Part007SupportExplicit : Finset ℕ :=
  ([7747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part007 : ℚ :=
  (403218191 : ℚ) / 907552027710720

def SurrogateDiagonalTailChunk000Sub000Block187Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7747
    = surrogateDiagTailX0RatChunk000Sub000Block187Part007

theorem surrogateDiagonalTailChunk000Sub000Block187Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part007] using hcert

def TailChunk000Sub000Block187Part008SupportExplicit : Finset ℕ :=
  ([7751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part008 : ℚ :=
  (391259193175 : ℚ) / 829530163049398272

def SurrogateDiagonalTailChunk000Sub000Block187Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7751
    = surrogateDiagTailX0RatChunk000Sub000Block187Part008

theorem surrogateDiagonalTailChunk000Sub000Block187Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part008] using hcert

def TailChunk000Sub000Block187Part009SupportExplicit : Finset ℕ :=
  ([7753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part009 : ℚ :=
  (939203265625 : ℚ) / 2257469668026634752

def SurrogateDiagonalTailChunk000Sub000Block187Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7753
    = surrogateDiagTailX0RatChunk000Sub000Block187Part009

theorem surrogateDiagonalTailChunk000Sub000Block187Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part009] using hcert

def TailChunk000Sub000Block187Part010SupportExplicit : Finset ℕ :=
  ([7754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part010 : ℚ :=
  (1878515346775 : ℚ) / 564367417006658688

def SurrogateDiagonalTailChunk000Sub000Block187Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7754
    = surrogateDiagTailX0RatChunk000Sub000Block187Part010

theorem surrogateDiagonalTailChunk000Sub000Block187Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part010] using hcert

def TailChunk000Sub000Block187Part011SupportExplicit : Finset ℕ :=
  ([7755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part011 : ℚ :=
  (5413370083 : ℚ) / 1834332770795520

def SurrogateDiagonalTailChunk000Sub000Block187Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7755
    = surrogateDiagTailX0RatChunk000Sub000Block187Part011

theorem surrogateDiagonalTailChunk000Sub000Block187Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part011] using hcert

def TailChunk000Sub000Block187Part012SupportExplicit : Finset ℕ :=
  ([7757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part012 : ℚ :=
  (940172640625 : ℚ) / 2262132655718490912

def SurrogateDiagonalTailChunk000Sub000Block187Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7757
    = surrogateDiagTailX0RatChunk000Sub000Block187Part012

theorem surrogateDiagonalTailChunk000Sub000Block187Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part012] using hcert

def TailChunk000Sub000Block187Part013SupportExplicit : Finset ℕ :=
  ([7759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part013 : ℚ :=
  (940657515625 : ℚ) / 2264466856639575762

def SurrogateDiagonalTailChunk000Sub000Block187Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7759
    = surrogateDiagTailX0RatChunk000Sub000Block187Part013

theorem surrogateDiagonalTailChunk000Sub000Block187Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part013] using hcert

def TailChunk000Sub000Block187Part014SupportExplicit : Finset ℕ :=
  ([7761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part014 : ℚ :=
  (3867735125 : ℚ) / 2623592118140928

def SurrogateDiagonalTailChunk000Sub000Block187Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7761
    = surrogateDiagTailX0RatChunk000Sub000Block187Part014

theorem surrogateDiagonalTailChunk000Sub000Block187Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part014] using hcert

def TailChunk000Sub000Block187Part015SupportExplicit : Finset ℕ :=
  ([7762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part015 : ℚ :=
  (75295742839 : ℚ) / 22668028635187200

def SurrogateDiagonalTailChunk000Sub000Block187Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7762
    = surrogateDiagTailX0RatChunk000Sub000Block187Part015

theorem surrogateDiagonalTailChunk000Sub000Block187Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part015] using hcert

def TailChunk000Sub000Block187Part016SupportExplicit : Finset ℕ :=
  ([7763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part016 : ℚ :=
  (3071584483375 : ℚ) / 4884171464908228608

def SurrogateDiagonalTailChunk000Sub000Block187Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7763
    = surrogateDiagTailX0RatChunk000Sub000Block187Part016

theorem surrogateDiagonalTailChunk000Sub000Block187Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part016] using hcert

def TailChunk000Sub000Block187Part017SupportExplicit : Finset ℕ :=
  ([7765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part017 : ℚ :=
  (1431064068575 : ℚ) / 1856964905794535424

def SurrogateDiagonalTailChunk000Sub000Block187Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7765
    = surrogateDiagTailX0RatChunk000Sub000Block187Part017

theorem surrogateDiagonalTailChunk000Sub000Block187Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part017] using hcert

def TailChunk000Sub000Block187Part018SupportExplicit : Finset ℕ :=
  ([7766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part018 : ℚ :=
  (21934295847 : ℚ) / 5118423885414400

def SurrogateDiagonalTailChunk000Sub000Block187Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7766
    = surrogateDiagTailX0RatChunk000Sub000Block187Part018

theorem surrogateDiagonalTailChunk000Sub000Block187Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part018] using hcert

def TailChunk000Sub000Block187Part019SupportExplicit : Finset ℕ :=
  ([7769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part019 : ℚ :=
  (144271489925 : ℚ) / 295226214891651072

def SurrogateDiagonalTailChunk000Sub000Block187Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7769
    = surrogateDiagTailX0RatChunk000Sub000Block187Part019

theorem surrogateDiagonalTailChunk000Sub000Block187Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part019] using hcert

def TailChunk000Sub000Block187Part020SupportExplicit : Finset ℕ :=
  ([7770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part020 : ℚ :=
  (115578155425 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk000Sub000Block187Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7770
    = surrogateDiagTailX0RatChunk000Sub000Block187Part020

theorem surrogateDiagonalTailChunk000Sub000Block187Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part020] using hcert

def TailChunk000Sub000Block187Part021SupportExplicit : Finset ℕ :=
  ([7771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part021 : ℚ :=
  (130194603625 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk000Sub000Block187Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7771
    = surrogateDiagTailX0RatChunk000Sub000Block187Part021

theorem surrogateDiagonalTailChunk000Sub000Block187Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part021] using hcert

def TailChunk000Sub000Block187Part022SupportExplicit : Finset ℕ :=
  ([7773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part022 : ℚ :=
  (16779393269 : ℚ) / 36006084264897600

def SurrogateDiagonalTailChunk000Sub000Block187Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7773
    = surrogateDiagTailX0RatChunk000Sub000Block187Part022

theorem surrogateDiagonalTailChunk000Sub000Block187Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part022] using hcert

def TailChunk000Sub000Block187Part023SupportExplicit : Finset ℕ :=
  ([7777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part023 : ℚ :=
  (18018085927 : ℚ) / 129625920000000000

def SurrogateDiagonalTailChunk000Sub000Block187Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7777
    = surrogateDiagTailX0RatChunk000Sub000Block187Part023

theorem surrogateDiagonalTailChunk000Sub000Block187Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part023] using hcert

def TailChunk000Sub000Block187Part024SupportExplicit : Finset ℕ :=
  ([7778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block187Part024 : ℚ :=
  (236317515625 : ℚ) / 142847252802772992

def SurrogateDiagonalTailChunk000Sub000Block187Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7778
    = surrogateDiagTailX0RatChunk000Sub000Block187Part024

theorem surrogateDiagonalTailChunk000Sub000Block187Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block187Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block187Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block187Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block187Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block187Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block187Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block187HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block187Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block187Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block187Part000
    + surrogateDiagTailX0RatChunk000Sub000Block187Part001
    + surrogateDiagTailX0RatChunk000Sub000Block187Part002
    + surrogateDiagTailX0RatChunk000Sub000Block187Part003
    + surrogateDiagTailX0RatChunk000Sub000Block187Part004
    + surrogateDiagTailX0RatChunk000Sub000Block187Part005
    + surrogateDiagTailX0RatChunk000Sub000Block187Part006
    + surrogateDiagTailX0RatChunk000Sub000Block187Part007
    + surrogateDiagTailX0RatChunk000Sub000Block187Part008
    + surrogateDiagTailX0RatChunk000Sub000Block187Part009

def surrogateDiagonalTailChunk000Sub000Block187MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block187Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block187Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block187Part010
    + surrogateDiagTailX0RatChunk000Sub000Block187Part011
    + surrogateDiagTailX0RatChunk000Sub000Block187Part012
    + surrogateDiagTailX0RatChunk000Sub000Block187Part013
    + surrogateDiagTailX0RatChunk000Sub000Block187Part014
    + surrogateDiagTailX0RatChunk000Sub000Block187Part015
    + surrogateDiagTailX0RatChunk000Sub000Block187Part016
    + surrogateDiagTailX0RatChunk000Sub000Block187Part017
    + surrogateDiagTailX0RatChunk000Sub000Block187Part018
    + surrogateDiagTailX0RatChunk000Sub000Block187Part019

def surrogateDiagonalTailChunk000Sub000Block187TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block187Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block187Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block187Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block187Part020
    + surrogateDiagTailX0RatChunk000Sub000Block187Part021
    + surrogateDiagTailX0RatChunk000Sub000Block187Part022
    + surrogateDiagTailX0RatChunk000Sub000Block187Part023
    + surrogateDiagTailX0RatChunk000Sub000Block187Part024

def surrogateDiagonalTailChunk000Sub000Block187Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block187HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block187MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block187TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block187 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block187Part000
    + surrogateDiagTailX0RatChunk000Sub000Block187Part001
    + surrogateDiagTailX0RatChunk000Sub000Block187Part002
    + surrogateDiagTailX0RatChunk000Sub000Block187Part003
    + surrogateDiagTailX0RatChunk000Sub000Block187Part004
    + surrogateDiagTailX0RatChunk000Sub000Block187Part005
    + surrogateDiagTailX0RatChunk000Sub000Block187Part006
    + surrogateDiagTailX0RatChunk000Sub000Block187Part007
    + surrogateDiagTailX0RatChunk000Sub000Block187Part008
    + surrogateDiagTailX0RatChunk000Sub000Block187Part009
    + surrogateDiagTailX0RatChunk000Sub000Block187Part010
    + surrogateDiagTailX0RatChunk000Sub000Block187Part011
    + surrogateDiagTailX0RatChunk000Sub000Block187Part012
    + surrogateDiagTailX0RatChunk000Sub000Block187Part013
    + surrogateDiagTailX0RatChunk000Sub000Block187Part014
    + surrogateDiagTailX0RatChunk000Sub000Block187Part015
    + surrogateDiagTailX0RatChunk000Sub000Block187Part016
    + surrogateDiagTailX0RatChunk000Sub000Block187Part017
    + surrogateDiagTailX0RatChunk000Sub000Block187Part018
    + surrogateDiagTailX0RatChunk000Sub000Block187Part019
    + surrogateDiagTailX0RatChunk000Sub000Block187Part020
    + surrogateDiagTailX0RatChunk000Sub000Block187Part021
    + surrogateDiagTailX0RatChunk000Sub000Block187Part022
    + surrogateDiagTailX0RatChunk000Sub000Block187Part023
    + surrogateDiagTailX0RatChunk000Sub000Block187Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block187_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block187Head + surrogateDiagTailX0RatChunk000Sub000Block187Mid + surrogateDiagTailX0RatChunk000Sub000Block187Tail =
      surrogateDiagTailX0RatChunk000Sub000Block187 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block187Head surrogateDiagTailX0RatChunk000Sub000Block187Mid surrogateDiagTailX0RatChunk000Sub000Block187Tail surrogateDiagTailX0RatChunk000Sub000Block187
  ring

def SurrogateDiagonalTailChunk000Sub000Block187HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block187HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block187Head

def SurrogateDiagonalTailChunk000Sub000Block187MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block187MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block187Mid

def SurrogateDiagonalTailChunk000Sub000Block187TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block187TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block187Tail

theorem surrogateDiagonalTailChunk000Sub000Block187_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block187HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block187MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block187TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block187Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block187 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block187HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block187MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block187TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block187Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block187_eq_head_add_mid_add_tail

/-- Block 188 covers tail-support indices [4700,4725) and q from 7779 to 7817. -/

def TailChunk000Sub000Block188Part000SupportExplicit : Finset ℕ :=
  ([7779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part000 : ℚ :=
  (420132452075 : ℚ) / 902935721419997184

def SurrogateDiagonalTailChunk000Sub000Block188Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7779
    = surrogateDiagTailX0RatChunk000Sub000Block188Part000

theorem surrogateDiagonalTailChunk000Sub000Block188Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part000] using hcert

def TailChunk000Sub000Block188Part001SupportExplicit : Finset ℕ :=
  ([7781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part001 : ℚ :=
  (333239707 : ℚ) / 31646953125000000

def SurrogateDiagonalTailChunk000Sub000Block188Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7781
    = surrogateDiagTailX0RatChunk000Sub000Block188Part001

theorem surrogateDiagonalTailChunk000Sub000Block188Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part001] using hcert

def TailChunk000Sub000Block188Part002SupportExplicit : Finset ℕ :=
  ([7782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part002 : ℚ :=
  (735582751225 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block188Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7782
    = surrogateDiagTailX0RatChunk000Sub000Block188Part002

theorem surrogateDiagonalTailChunk000Sub000Block188Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part002] using hcert

def TailChunk000Sub000Block188Part003SupportExplicit : Finset ℕ :=
  ([7783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part003 : ℚ :=
  (139183721 : ℚ) / 16335936498792960

def SurrogateDiagonalTailChunk000Sub000Block188Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7783
    = surrogateDiagTailX0RatChunk000Sub000Block188Part003

theorem surrogateDiagonalTailChunk000Sub000Block188Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part003] using hcert

def TailChunk000Sub000Block188Part004SupportExplicit : Finset ℕ :=
  ([7786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part004 : ℚ :=
  (905118563725 : ℚ) / 442839322337476608

def SurrogateDiagonalTailChunk000Sub000Block188Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7786
    = surrogateDiagTailX0RatChunk000Sub000Block188Part004

theorem surrogateDiagonalTailChunk000Sub000Block188Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part004] using hcert

def TailChunk000Sub000Block188Part005SupportExplicit : Finset ℕ :=
  ([7787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part005 : ℚ :=
  (15737103325 : ℚ) / 510050557644466176

def SurrogateDiagonalTailChunk000Sub000Block188Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7787
    = surrogateDiagTailX0RatChunk000Sub000Block188Part005

theorem surrogateDiagonalTailChunk000Sub000Block188Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part005] using hcert

def TailChunk000Sub000Block188Part006SupportExplicit : Finset ℕ :=
  ([7789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block188Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7789
    = surrogateDiagTailX0RatChunk000Sub000Block188Part006

theorem surrogateDiagonalTailChunk000Sub000Block188Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part006] using hcert

def TailChunk000Sub000Block188Part007SupportExplicit : Finset ℕ :=
  ([7790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part007 : ℚ :=
  (15615268223 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block188Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7790
    = surrogateDiagTailX0RatChunk000Sub000Block188Part007

theorem surrogateDiagonalTailChunk000Sub000Block188Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part007] using hcert

def TailChunk000Sub000Block188Part008SupportExplicit : Finset ℕ :=
  ([7793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block188Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7793
    = surrogateDiagTailX0RatChunk000Sub000Block188Part008

theorem surrogateDiagonalTailChunk000Sub000Block188Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part008] using hcert

def TailChunk000Sub000Block188Part009SupportExplicit : Finset ℕ :=
  ([7795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part009 : ℚ :=
  (57024867725 : ℚ) / 471461952615495936

def SurrogateDiagonalTailChunk000Sub000Block188Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7795
    = surrogateDiagTailX0RatChunk000Sub000Block188Part009

theorem surrogateDiagonalTailChunk000Sub000Block188Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part009] using hcert

def TailChunk000Sub000Block188Part010SupportExplicit : Finset ℕ :=
  ([7797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part010 : ℚ :=
  (140227976925 : ℚ) / 245786714977599488

def SurrogateDiagonalTailChunk000Sub000Block188Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7797
    = surrogateDiagTailX0RatChunk000Sub000Block188Part010

theorem surrogateDiagonalTailChunk000Sub000Block188Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part010] using hcert

def TailChunk000Sub000Block188Part011SupportExplicit : Finset ℕ :=
  ([7798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part011 : ℚ :=
  (852150657625 : ℚ) / 309692741610129408

def SurrogateDiagonalTailChunk000Sub000Block188Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7798
    = surrogateDiagTailX0RatChunk000Sub000Block188Part011

theorem surrogateDiagonalTailChunk000Sub000Block188Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part011] using hcert

def TailChunk000Sub000Block188Part012SupportExplicit : Finset ℕ :=
  ([7799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part012 : ℚ :=
  (8886661399 : ℚ) / 251315850815539200

def SurrogateDiagonalTailChunk000Sub000Block188Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7799
    = surrogateDiagTailX0RatChunk000Sub000Block188Part012

theorem surrogateDiagonalTailChunk000Sub000Block188Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part012] using hcert

def TailChunk000Sub000Block188Part013SupportExplicit : Finset ℕ :=
  ([7801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part013 : ℚ :=
  (93713558875 : ℚ) / 7928630163751600128

def SurrogateDiagonalTailChunk000Sub000Block188Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7801
    = surrogateDiagTailX0RatChunk000Sub000Block188Part013

theorem surrogateDiagonalTailChunk000Sub000Block188Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part013] using hcert

def TailChunk000Sub000Block188Part014SupportExplicit : Finset ℕ :=
  ([7802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part014 : ℚ :=
  (464201925725 : ℚ) / 253095019762496064

def SurrogateDiagonalTailChunk000Sub000Block188Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7802
    = surrogateDiagTailX0RatChunk000Sub000Block188Part014

theorem surrogateDiagonalTailChunk000Sub000Block188Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part014] using hcert

def TailChunk000Sub000Block188Part015SupportExplicit : Finset ℕ :=
  ([7805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part015 : ℚ :=
  (583392105025 : ℚ) / 2015040240855318528

def SurrogateDiagonalTailChunk000Sub000Block188Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7805
    = surrogateDiagTailX0RatChunk000Sub000Block188Part015

theorem surrogateDiagonalTailChunk000Sub000Block188Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part015] using hcert

def TailChunk000Sub000Block188Part016SupportExplicit : Finset ℕ :=
  ([7806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part016 : ℚ :=
  (29605061197 : ℚ) / 4570673952000000

def SurrogateDiagonalTailChunk000Sub000Block188Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7806
    = surrogateDiagTailX0RatChunk000Sub000Block188Part016

theorem surrogateDiagonalTailChunk000Sub000Block188Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part016] using hcert

def TailChunk000Sub000Block188Part017SupportExplicit : Finset ℕ :=
  ([7807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part017 : ℚ :=
  (114197497 : ℚ) / 12100693702809600

def SurrogateDiagonalTailChunk000Sub000Block188Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7807
    = surrogateDiagTailX0RatChunk000Sub000Block188Part017

theorem surrogateDiagonalTailChunk000Sub000Block188Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part017] using hcert

def TailChunk000Sub000Block188Part018SupportExplicit : Finset ℕ :=
  ([7809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part018 : ℚ :=
  (35092828325 : ℚ) / 59866139553103872

def SurrogateDiagonalTailChunk000Sub000Block188Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7809
    = surrogateDiagTailX0RatChunk000Sub000Block188Part018

theorem surrogateDiagonalTailChunk000Sub000Block188Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part018] using hcert

def TailChunk000Sub000Block188Part019SupportExplicit : Finset ℕ :=
  ([7810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part019 : ℚ :=
  (76557081 : ℚ) / 16009868000000

def SurrogateDiagonalTailChunk000Sub000Block188Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7810
    = surrogateDiagTailX0RatChunk000Sub000Block188Part019

theorem surrogateDiagonalTailChunk000Sub000Block188Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part019] using hcert

def TailChunk000Sub000Block188Part020SupportExplicit : Finset ℕ :=
  ([7811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part020 : ℚ :=
  (18347564275 : ℚ) / 2827867462596919296

def SurrogateDiagonalTailChunk000Sub000Block188Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7811
    = surrogateDiagTailX0RatChunk000Sub000Block188Part020

theorem surrogateDiagonalTailChunk000Sub000Block188Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part020] using hcert

def TailChunk000Sub000Block188Part021SupportExplicit : Finset ℕ :=
  ([7813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part021 : ℚ :=
  (29725319 : ℚ) / 58331664000000

def SurrogateDiagonalTailChunk000Sub000Block188Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7813
    = surrogateDiagTailX0RatChunk000Sub000Block188Part021

theorem surrogateDiagonalTailChunk000Sub000Block188Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part021] using hcert

def TailChunk000Sub000Block188Part022SupportExplicit : Finset ℕ :=
  ([7814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part022 : ℚ :=
  (1907699508775 : ℚ) / 582043997349605448

def SurrogateDiagonalTailChunk000Sub000Block188Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7814
    = surrogateDiagTailX0RatChunk000Sub000Block188Part022

theorem surrogateDiagonalTailChunk000Sub000Block188Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part022] using hcert

def TailChunk000Sub000Block188Part023SupportExplicit : Finset ℕ :=
  ([7815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part023 : ℚ :=
  (8210457461 : ℚ) / 3744296101478400

def SurrogateDiagonalTailChunk000Sub000Block188Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7815
    = surrogateDiagTailX0RatChunk000Sub000Block188Part023

theorem surrogateDiagonalTailChunk000Sub000Block188Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part023] using hcert

def TailChunk000Sub000Block188Part024SupportExplicit : Finset ℕ :=
  ([7817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part024 : ℚ :=
  (954773265625 : ℚ) / 2332948062626222592

def SurrogateDiagonalTailChunk000Sub000Block188Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7817
    = surrogateDiagTailX0RatChunk000Sub000Block188Part024

theorem surrogateDiagonalTailChunk000Sub000Block188Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block188HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block188Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block188Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block188Part000
    + surrogateDiagTailX0RatChunk000Sub000Block188Part001
    + surrogateDiagTailX0RatChunk000Sub000Block188Part002
    + surrogateDiagTailX0RatChunk000Sub000Block188Part003
    + surrogateDiagTailX0RatChunk000Sub000Block188Part004
    + surrogateDiagTailX0RatChunk000Sub000Block188Part005
    + surrogateDiagTailX0RatChunk000Sub000Block188Part006
    + surrogateDiagTailX0RatChunk000Sub000Block188Part007
    + surrogateDiagTailX0RatChunk000Sub000Block188Part008
    + surrogateDiagTailX0RatChunk000Sub000Block188Part009

def surrogateDiagonalTailChunk000Sub000Block188MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block188Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block188Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block188Part010
    + surrogateDiagTailX0RatChunk000Sub000Block188Part011
    + surrogateDiagTailX0RatChunk000Sub000Block188Part012
    + surrogateDiagTailX0RatChunk000Sub000Block188Part013
    + surrogateDiagTailX0RatChunk000Sub000Block188Part014
    + surrogateDiagTailX0RatChunk000Sub000Block188Part015
    + surrogateDiagTailX0RatChunk000Sub000Block188Part016
    + surrogateDiagTailX0RatChunk000Sub000Block188Part017
    + surrogateDiagTailX0RatChunk000Sub000Block188Part018
    + surrogateDiagTailX0RatChunk000Sub000Block188Part019

def surrogateDiagonalTailChunk000Sub000Block188TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block188Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block188Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block188Part020
    + surrogateDiagTailX0RatChunk000Sub000Block188Part021
    + surrogateDiagTailX0RatChunk000Sub000Block188Part022
    + surrogateDiagTailX0RatChunk000Sub000Block188Part023
    + surrogateDiagTailX0RatChunk000Sub000Block188Part024

def surrogateDiagonalTailChunk000Sub000Block188Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block188HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block188MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block188TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block188 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block188Part000
    + surrogateDiagTailX0RatChunk000Sub000Block188Part001
    + surrogateDiagTailX0RatChunk000Sub000Block188Part002
    + surrogateDiagTailX0RatChunk000Sub000Block188Part003
    + surrogateDiagTailX0RatChunk000Sub000Block188Part004
    + surrogateDiagTailX0RatChunk000Sub000Block188Part005
    + surrogateDiagTailX0RatChunk000Sub000Block188Part006
    + surrogateDiagTailX0RatChunk000Sub000Block188Part007
    + surrogateDiagTailX0RatChunk000Sub000Block188Part008
    + surrogateDiagTailX0RatChunk000Sub000Block188Part009
    + surrogateDiagTailX0RatChunk000Sub000Block188Part010
    + surrogateDiagTailX0RatChunk000Sub000Block188Part011
    + surrogateDiagTailX0RatChunk000Sub000Block188Part012
    + surrogateDiagTailX0RatChunk000Sub000Block188Part013
    + surrogateDiagTailX0RatChunk000Sub000Block188Part014
    + surrogateDiagTailX0RatChunk000Sub000Block188Part015
    + surrogateDiagTailX0RatChunk000Sub000Block188Part016
    + surrogateDiagTailX0RatChunk000Sub000Block188Part017
    + surrogateDiagTailX0RatChunk000Sub000Block188Part018
    + surrogateDiagTailX0RatChunk000Sub000Block188Part019
    + surrogateDiagTailX0RatChunk000Sub000Block188Part020
    + surrogateDiagTailX0RatChunk000Sub000Block188Part021
    + surrogateDiagTailX0RatChunk000Sub000Block188Part022
    + surrogateDiagTailX0RatChunk000Sub000Block188Part023
    + surrogateDiagTailX0RatChunk000Sub000Block188Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block188_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block188Head + surrogateDiagTailX0RatChunk000Sub000Block188Mid + surrogateDiagTailX0RatChunk000Sub000Block188Tail =
      surrogateDiagTailX0RatChunk000Sub000Block188 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block188Head surrogateDiagTailX0RatChunk000Sub000Block188Mid surrogateDiagTailX0RatChunk000Sub000Block188Tail surrogateDiagTailX0RatChunk000Sub000Block188
  ring

def SurrogateDiagonalTailChunk000Sub000Block188HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block188HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block188Head

def SurrogateDiagonalTailChunk000Sub000Block188MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block188MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block188Mid

def SurrogateDiagonalTailChunk000Sub000Block188TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block188TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block188Tail

theorem surrogateDiagonalTailChunk000Sub000Block188_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block188HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block188MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block188TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block188Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block188 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block188HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block188MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block188TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block188Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block188_eq_head_add_mid_add_tail

/-- Block 189 covers tail-support indices [4725,4750) and q from 7818 to 7858. -/

def TailChunk000Sub000Block189Part000SupportExplicit : Finset ℕ :=
  ([7818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part000 : ℚ :=
  (530127067475 : ℚ) / 57485826898726464

def SurrogateDiagonalTailChunk000Sub000Block189Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7818
    = surrogateDiagTailX0RatChunk000Sub000Block189Part000

theorem surrogateDiagonalTailChunk000Sub000Block189Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part000] using hcert

def TailChunk000Sub000Block189Part001SupportExplicit : Finset ℕ :=
  ([7819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part001 : ℚ :=
  (3116072487775 : ℚ) / 5026765651412502528

def SurrogateDiagonalTailChunk000Sub000Block189Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7819
    = surrogateDiagTailX0RatChunk000Sub000Block189Part001

theorem surrogateDiagonalTailChunk000Sub000Block189Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part001] using hcert

def TailChunk000Sub000Block189Part002SupportExplicit : Finset ℕ :=
  ([7822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part002 : ℚ :=
  (76464309079 : ℚ) / 23377274681032200

def SurrogateDiagonalTailChunk000Sub000Block189Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7822
    = surrogateDiagTailX0RatChunk000Sub000Block189Part002

theorem surrogateDiagonalTailChunk000Sub000Block189Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part002] using hcert

def TailChunk000Sub000Block189Part003SupportExplicit : Finset ℕ :=
  ([7823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part003 : ℚ :=
  (956239515625 : ℚ) / 2340119922780886482

def SurrogateDiagonalTailChunk000Sub000Block189Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7823
    = surrogateDiagTailX0RatChunk000Sub000Block189Part003

theorem surrogateDiagonalTailChunk000Sub000Block189Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part003] using hcert

def TailChunk000Sub000Block189Part004SupportExplicit : Finset ℕ :=
  ([7826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part004 : ℚ :=
  (1342060542925 : ℚ) / 209099987184549888

def SurrogateDiagonalTailChunk000Sub000Block189Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7826
    = surrogateDiagTailX0RatChunk000Sub000Block189Part004

theorem surrogateDiagonalTailChunk000Sub000Block189Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part004] using hcert

def TailChunk000Sub000Block189Part005SupportExplicit : Finset ℕ :=
  ([7827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part005 : ℚ :=
  (1063242477725 : ℚ) / 925437713910595584

def SurrogateDiagonalTailChunk000Sub000Block189Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7827
    = surrogateDiagTailX0RatChunk000Sub000Block189Part005

theorem surrogateDiagonalTailChunk000Sub000Block189Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part005] using hcert

def TailChunk000Sub000Block189Part006SupportExplicit : Finset ℕ :=
  ([7829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part006 : ℚ :=
  (957706890625 : ℚ) / 2347308305835769632

def SurrogateDiagonalTailChunk000Sub000Block189Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7829
    = surrogateDiagTailX0RatChunk000Sub000Block189Part006

theorem surrogateDiagonalTailChunk000Sub000Block189Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part006] using hcert

def TailChunk000Sub000Block189Part007SupportExplicit : Finset ℕ :=
  ([7831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part007 : ℚ :=
  (147177714229 : ℚ) / 333688484352000000

def SurrogateDiagonalTailChunk000Sub000Block189Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7831
    = surrogateDiagTailX0RatChunk000Sub000Block189Part007

theorem surrogateDiagonalTailChunk000Sub000Block189Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part007] using hcert

def TailChunk000Sub000Block189Part008SupportExplicit : Finset ℕ :=
  ([7833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part008 : ℚ :=
  (1759791606325 : ℚ) / 992941363241975808

def SurrogateDiagonalTailChunk000Sub000Block189Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7833
    = surrogateDiagTailX0RatChunk000Sub000Block189Part008

theorem surrogateDiagonalTailChunk000Sub000Block189Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part008] using hcert

def TailChunk000Sub000Block189Part009SupportExplicit : Finset ℕ :=
  ([7834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part009 : ℚ :=
  (239732640625 : ℚ) / 147006859569775392

def SurrogateDiagonalTailChunk000Sub000Block189Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7834
    = surrogateDiagTailX0RatChunk000Sub000Block189Part009

theorem surrogateDiagonalTailChunk000Sub000Block189Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part009] using hcert

def TailChunk000Sub000Block189Part010SupportExplicit : Finset ℕ :=
  ([7835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part010 : ℚ :=
  (2760579943825 : ℚ) / 3849761766864734208

def SurrogateDiagonalTailChunk000Sub000Block189Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7835
    = surrogateDiagTailX0RatChunk000Sub000Block189Part010

theorem surrogateDiagonalTailChunk000Sub000Block189Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part010] using hcert

def TailChunk000Sub000Block189Part011SupportExplicit : Finset ℕ :=
  ([7837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part011 : ℚ :=
  (2936200239 : ℚ) / 6114442569318400

def SurrogateDiagonalTailChunk000Sub000Block189Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7837
    = surrogateDiagTailX0RatChunk000Sub000Block189Part011

theorem surrogateDiagonalTailChunk000Sub000Block189Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part011] using hcert

def TailChunk000Sub000Block189Part012SupportExplicit : Finset ℕ :=
  ([7838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part012 : ℚ :=
  (239977515625 : ℚ) / 147307410168525522

def SurrogateDiagonalTailChunk000Sub000Block189Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7838
    = surrogateDiagTailX0RatChunk000Sub000Block189Part012

theorem surrogateDiagonalTailChunk000Sub000Block189Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part012] using hcert

def TailChunk000Sub000Block189Part013SupportExplicit : Finset ℕ :=
  ([7841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part013 : ℚ :=
  (1537032025 : ℚ) / 3778775587356672

def SurrogateDiagonalTailChunk000Sub000Block189Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7841
    = surrogateDiagTailX0RatChunk000Sub000Block189Part013

theorem surrogateDiagonalTailChunk000Sub000Block189Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part013] using hcert

def TailChunk000Sub000Block189Part014SupportExplicit : Finset ℕ :=
  ([7842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part014 : ℚ :=
  (746968452475 : ℚ) / 116391040133155968

def SurrogateDiagonalTailChunk000Sub000Block189Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7842
    = surrogateDiagTailX0RatChunk000Sub000Block189Part014

theorem surrogateDiagonalTailChunk000Sub000Block189Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part014] using hcert

def TailChunk000Sub000Block189Part015SupportExplicit : Finset ℕ :=
  ([7843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part015 : ℚ :=
  (30335533117 : ℚ) / 47446327368000000

def SurrogateDiagonalTailChunk000Sub000Block189Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7843
    = surrogateDiagTailX0RatChunk000Sub000Block189Part015

theorem surrogateDiagonalTailChunk000Sub000Block189Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part015] using hcert

def TailChunk000Sub000Block189Part016SupportExplicit : Finset ℕ :=
  ([7845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part016 : ℚ :=
  (1377203725 : ℚ) / 660110042329344

def SurrogateDiagonalTailChunk000Sub000Block189Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7845
    = surrogateDiagTailX0RatChunk000Sub000Block189Part016

theorem surrogateDiagonalTailChunk000Sub000Block189Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part016] using hcert

def TailChunk000Sub000Block189Part017SupportExplicit : Finset ℕ :=
  ([7846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part017 : ℚ :=
  (240467640625 : ℚ) / 147909893677932882

def SurrogateDiagonalTailChunk000Sub000Block189Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7846
    = surrogateDiagTailX0RatChunk000Sub000Block189Part017

theorem surrogateDiagonalTailChunk000Sub000Block189Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part017] using hcert

def TailChunk000Sub000Block189Part018SupportExplicit : Finset ℕ :=
  ([7847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part018 : ℚ :=
  (929202646775 : ℚ) / 1283253922288244736

def SurrogateDiagonalTailChunk000Sub000Block189Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7847
    = surrogateDiagTailX0RatChunk000Sub000Block189Part018

theorem surrogateDiagonalTailChunk000Sub000Block189Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part018] using hcert

def TailChunk000Sub000Block189Part019SupportExplicit : Finset ℕ :=
  ([7849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part019 : ℚ :=
  (3707321393575 : ℚ) / 8501401704807931008

def SurrogateDiagonalTailChunk000Sub000Block189Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7849
    = surrogateDiagTailX0RatChunk000Sub000Block189Part019

theorem surrogateDiagonalTailChunk000Sub000Block189Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part019] using hcert

def TailChunk000Sub000Block189Part020SupportExplicit : Finset ℕ :=
  ([7851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part020 : ℚ :=
  (1711488738325 : ℚ) / 1873690264077631488

def SurrogateDiagonalTailChunk000Sub000Block189Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7851
    = surrogateDiagTailX0RatChunk000Sub000Block189Part020

theorem surrogateDiagonalTailChunk000Sub000Block189Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part020] using hcert

def TailChunk000Sub000Block189Part021SupportExplicit : Finset ℕ :=
  ([7853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part021 : ℚ :=
  (963587640625 : ℚ) / 2376227574510565152

def SurrogateDiagonalTailChunk000Sub000Block189Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7853
    = surrogateDiagTailX0RatChunk000Sub000Block189Part021

theorem surrogateDiagonalTailChunk000Sub000Block189Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part021] using hcert

def TailChunk000Sub000Block189Part022SupportExplicit : Finset ℕ :=
  ([7854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part022 : ℚ :=
  (11316766589 : ℚ) / 679613143449600

def SurrogateDiagonalTailChunk000Sub000Block189Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7854
    = surrogateDiagTailX0RatChunk000Sub000Block189Part022

theorem surrogateDiagonalTailChunk000Sub000Block189Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part022] using hcert

def TailChunk000Sub000Block189Part023SupportExplicit : Finset ℕ :=
  ([7855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part023 : ℚ :=
  (36995921859 : ℚ) / 51856615734630400

def SurrogateDiagonalTailChunk000Sub000Block189Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7855
    = surrogateDiagTailX0RatChunk000Sub000Block189Part023

theorem surrogateDiagonalTailChunk000Sub000Block189Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part023] using hcert

def TailChunk000Sub000Block189Part024SupportExplicit : Finset ℕ :=
  ([7858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block189Part024 : ℚ :=
  (241203765625 : ℚ) / 148817081781023232

def SurrogateDiagonalTailChunk000Sub000Block189Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7858
    = surrogateDiagTailX0RatChunk000Sub000Block189Part024

theorem surrogateDiagonalTailChunk000Sub000Block189Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block189Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block189Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block189Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block189Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block189Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block189Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block189HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block189Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block189Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block189Part000
    + surrogateDiagTailX0RatChunk000Sub000Block189Part001
    + surrogateDiagTailX0RatChunk000Sub000Block189Part002
    + surrogateDiagTailX0RatChunk000Sub000Block189Part003
    + surrogateDiagTailX0RatChunk000Sub000Block189Part004
    + surrogateDiagTailX0RatChunk000Sub000Block189Part005
    + surrogateDiagTailX0RatChunk000Sub000Block189Part006
    + surrogateDiagTailX0RatChunk000Sub000Block189Part007
    + surrogateDiagTailX0RatChunk000Sub000Block189Part008
    + surrogateDiagTailX0RatChunk000Sub000Block189Part009

def surrogateDiagonalTailChunk000Sub000Block189MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block189Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block189Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block189Part010
    + surrogateDiagTailX0RatChunk000Sub000Block189Part011
    + surrogateDiagTailX0RatChunk000Sub000Block189Part012
    + surrogateDiagTailX0RatChunk000Sub000Block189Part013
    + surrogateDiagTailX0RatChunk000Sub000Block189Part014
    + surrogateDiagTailX0RatChunk000Sub000Block189Part015
    + surrogateDiagTailX0RatChunk000Sub000Block189Part016
    + surrogateDiagTailX0RatChunk000Sub000Block189Part017
    + surrogateDiagTailX0RatChunk000Sub000Block189Part018
    + surrogateDiagTailX0RatChunk000Sub000Block189Part019

def surrogateDiagonalTailChunk000Sub000Block189TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block189Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block189Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block189Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block189Part020
    + surrogateDiagTailX0RatChunk000Sub000Block189Part021
    + surrogateDiagTailX0RatChunk000Sub000Block189Part022
    + surrogateDiagTailX0RatChunk000Sub000Block189Part023
    + surrogateDiagTailX0RatChunk000Sub000Block189Part024

def surrogateDiagonalTailChunk000Sub000Block189Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block189HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block189MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block189TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block189 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block189Part000
    + surrogateDiagTailX0RatChunk000Sub000Block189Part001
    + surrogateDiagTailX0RatChunk000Sub000Block189Part002
    + surrogateDiagTailX0RatChunk000Sub000Block189Part003
    + surrogateDiagTailX0RatChunk000Sub000Block189Part004
    + surrogateDiagTailX0RatChunk000Sub000Block189Part005
    + surrogateDiagTailX0RatChunk000Sub000Block189Part006
    + surrogateDiagTailX0RatChunk000Sub000Block189Part007
    + surrogateDiagTailX0RatChunk000Sub000Block189Part008
    + surrogateDiagTailX0RatChunk000Sub000Block189Part009
    + surrogateDiagTailX0RatChunk000Sub000Block189Part010
    + surrogateDiagTailX0RatChunk000Sub000Block189Part011
    + surrogateDiagTailX0RatChunk000Sub000Block189Part012
    + surrogateDiagTailX0RatChunk000Sub000Block189Part013
    + surrogateDiagTailX0RatChunk000Sub000Block189Part014
    + surrogateDiagTailX0RatChunk000Sub000Block189Part015
    + surrogateDiagTailX0RatChunk000Sub000Block189Part016
    + surrogateDiagTailX0RatChunk000Sub000Block189Part017
    + surrogateDiagTailX0RatChunk000Sub000Block189Part018
    + surrogateDiagTailX0RatChunk000Sub000Block189Part019
    + surrogateDiagTailX0RatChunk000Sub000Block189Part020
    + surrogateDiagTailX0RatChunk000Sub000Block189Part021
    + surrogateDiagTailX0RatChunk000Sub000Block189Part022
    + surrogateDiagTailX0RatChunk000Sub000Block189Part023
    + surrogateDiagTailX0RatChunk000Sub000Block189Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block189_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block189Head + surrogateDiagTailX0RatChunk000Sub000Block189Mid + surrogateDiagTailX0RatChunk000Sub000Block189Tail =
      surrogateDiagTailX0RatChunk000Sub000Block189 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block189Head surrogateDiagTailX0RatChunk000Sub000Block189Mid surrogateDiagTailX0RatChunk000Sub000Block189Tail surrogateDiagTailX0RatChunk000Sub000Block189
  ring

def SurrogateDiagonalTailChunk000Sub000Block189HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block189HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block189Head

def SurrogateDiagonalTailChunk000Sub000Block189MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block189MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block189Mid

def SurrogateDiagonalTailChunk000Sub000Block189TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block189TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block189Tail

theorem surrogateDiagonalTailChunk000Sub000Block189_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block189HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block189MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block189TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block189Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block189 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block189HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block189MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block189TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block189Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block189_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
