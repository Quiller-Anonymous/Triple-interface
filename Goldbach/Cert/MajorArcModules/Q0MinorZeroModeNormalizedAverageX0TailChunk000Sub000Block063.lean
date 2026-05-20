import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [63,64). -/

/- Block 063 covers tail-support indices [1575,1600) and q from 2639 to 2681. -/

def TailChunk000Sub000Block063Part000SupportExplicit : Finset ℕ :=
  ([2639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part000 : ℚ :=
  (326505787775 : ℚ) / 20651850586128384

def SurrogateDiagonalTailChunk000Sub000Block063Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2639
    = surrogateDiagTailX0RatChunk000Sub000Block063Part000

theorem surrogateDiagonalTailChunk000Sub000Block063Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part000] using hcert

def TailChunk000Sub000Block063Part001SupportExplicit : Finset ℕ :=
  ([2641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part001 : ℚ :=
  (7569372425 : ℚ) / 881473924012896

def SurrogateDiagonalTailChunk000Sub000Block063Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2641
    = surrogateDiagTailX0RatChunk000Sub000Block063Part001

theorem surrogateDiagonalTailChunk000Sub000Block063Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part001] using hcert

def TailChunk000Sub000Block063Part002SupportExplicit : Finset ℕ :=
  ([2642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part002 : ℚ :=
  (8719969877 : ℚ) / 151828247577600

def SurrogateDiagonalTailChunk000Sub000Block063Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2642
    = surrogateDiagTailX0RatChunk000Sub000Block063Part002

theorem surrogateDiagonalTailChunk000Sub000Block063Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part002] using hcert

def TailChunk000Sub000Block063Part003SupportExplicit : Finset ℕ :=
  ([2643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part003 : ℚ :=
  (930279 : ℚ) / 38380503040

def SurrogateDiagonalTailChunk000Sub000Block063Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2643
    = surrogateDiagTailX0RatChunk000Sub000Block063Part003

theorem surrogateDiagonalTailChunk000Sub000Block063Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part003] using hcert

def TailChunk000Sub000Block063Part004SupportExplicit : Finset ℕ :=
  ([2647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part004 : ℚ :=
  (875650959775 : ℚ) / 122570573542505928

def SurrogateDiagonalTailChunk000Sub000Block063Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2647
    = surrogateDiagTailX0RatChunk000Sub000Block063Part004

theorem surrogateDiagonalTailChunk000Sub000Block063Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part004] using hcert

def TailChunk000Sub000Block063Part005SupportExplicit : Finset ℕ :=
  ([2649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part005 : ℚ :=
  (535544530825 : ℚ) / 24211471317038208

def SurrogateDiagonalTailChunk000Sub000Block063Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2649
    = surrogateDiagTailX0RatChunk000Sub000Block063Part005

theorem surrogateDiagonalTailChunk000Sub000Block063Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part005] using hcert

def TailChunk000Sub000Block063Part006SupportExplicit : Finset ℕ :=
  ([2651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part006 : ℚ :=
  (3518541281 : ℚ) / 368713728000000

def SurrogateDiagonalTailChunk000Sub000Block063Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2651
    = surrogateDiagTailX0RatChunk000Sub000Block063Part006

theorem surrogateDiagonalTailChunk000Sub000Block063Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part006] using hcert

def TailChunk000Sub000Block063Part007SupportExplicit : Finset ℕ :=
  ([2653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part007 : ℚ :=
  (371613395975 : ℚ) / 33080271410055744

def SurrogateDiagonalTailChunk000Sub000Block063Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2653
    = surrogateDiagTailX0RatChunk000Sub000Block063Part007

theorem surrogateDiagonalTailChunk000Sub000Block063Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part007] using hcert

def TailChunk000Sub000Block063Part008SupportExplicit : Finset ℕ :=
  ([2654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part008 : ℚ :=
  (219984055325 : ℚ) / 3865190998843044

def SurrogateDiagonalTailChunk000Sub000Block063Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2654
    = surrogateDiagTailX0RatChunk000Sub000Block063Part008

theorem surrogateDiagonalTailChunk000Sub000Block063Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part008] using hcert

def TailChunk000Sub000Block063Part009SupportExplicit : Finset ℕ :=
  ([2657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part009 : ℚ :=
  (882279633775 : ℚ) / 124434022830440448

def SurrogateDiagonalTailChunk000Sub000Block063Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2657
    = surrogateDiagTailX0RatChunk000Sub000Block063Part009

theorem surrogateDiagonalTailChunk000Sub000Block063Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part009] using hcert

def TailChunk000Sub000Block063Part010SupportExplicit : Finset ℕ :=
  ([2658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part010 : ℚ :=
  (244868028325 : ℚ) / 1526989036579968

def SurrogateDiagonalTailChunk000Sub000Block063Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2658
    = surrogateDiagTailX0RatChunk000Sub000Block063Part010

theorem surrogateDiagonalTailChunk000Sub000Block063Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part010] using hcert

def TailChunk000Sub000Block063Part011SupportExplicit : Finset ℕ :=
  ([2659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part011 : ℚ :=
  (110473140625 : ℚ) / 31202311915350162

def SurrogateDiagonalTailChunk000Sub000Block063Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2659
    = surrogateDiagTailX0RatChunk000Sub000Block063Part011

theorem surrogateDiagonalTailChunk000Sub000Block063Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part011] using hcert

def TailChunk000Sub000Block063Part012SupportExplicit : Finset ℕ :=
  ([2661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part012 : ℚ :=
  (117874275 : ℚ) / 4929749760128

def SurrogateDiagonalTailChunk000Sub000Block063Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2661
    = surrogateDiagTailX0RatChunk000Sub000Block063Part012

theorem surrogateDiagonalTailChunk000Sub000Block063Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part012] using hcert

def TailChunk000Sub000Block063Part013SupportExplicit : Finset ℕ :=
  ([2663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part013 : ℚ :=
  (886268835775 : ℚ) / 125562242495853768

def SurrogateDiagonalTailChunk000Sub000Block063Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2663
    = surrogateDiagTailX0RatChunk000Sub000Block063Part013

theorem surrogateDiagonalTailChunk000Sub000Block063Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part013] using hcert

def TailChunk000Sub000Block063Part014SupportExplicit : Finset ℕ :=
  ([2665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part014 : ℚ :=
  (3103276901 : ℚ) / 169903285862400

def SurrogateDiagonalTailChunk000Sub000Block063Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2665
    = surrogateDiagTailX0RatChunk000Sub000Block063Part014

theorem surrogateDiagonalTailChunk000Sub000Block063Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part014] using hcert

def TailChunk000Sub000Block063Part015SupportExplicit : Finset ℕ :=
  ([2666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part015 : ℚ :=
  (12779088169 : ℚ) / 252097785475200

def SurrogateDiagonalTailChunk000Sub000Block063Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2666
    = surrogateDiagTailX0RatChunk000Sub000Block063Part015

theorem surrogateDiagonalTailChunk000Sub000Block063Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part015] using hcert

def TailChunk000Sub000Block063Part016SupportExplicit : Finset ℕ :=
  ([2667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part016 : ℚ :=
  (16595275 : ℚ) / 435537865728

def SurrogateDiagonalTailChunk000Sub000Block063Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2667
    = surrogateDiagTailX0RatChunk000Sub000Block063Part016

theorem surrogateDiagonalTailChunk000Sub000Block063Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part016] using hcert

def TailChunk000Sub000Block063Part017SupportExplicit : Finset ℕ :=
  ([2669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part017 : ℚ :=
  (414755462825 : ℚ) / 48526077475160064

def SurrogateDiagonalTailChunk000Sub000Block063Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2669
    = surrogateDiagTailX0RatChunk000Sub000Block063Part017

theorem surrogateDiagonalTailChunk000Sub000Block063Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part017] using hcert

def TailChunk000Sub000Block063Part018SupportExplicit : Finset ℕ :=
  ([2670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part018 : ℚ :=
  (224669775175 : ℚ) / 614210866249728

def SurrogateDiagonalTailChunk000Sub000Block063Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2670
    = surrogateDiagTailX0RatChunk000Sub000Block063Part018

theorem surrogateDiagonalTailChunk000Sub000Block063Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part018] using hcert

def TailChunk000Sub000Block063Part019SupportExplicit : Finset ℕ :=
  ([2671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part019 : ℚ :=
  (35664070759 : ℚ) / 5083137945304200

def SurrogateDiagonalTailChunk000Sub000Block063Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2671
    = surrogateDiagTailX0RatChunk000Sub000Block063Part019

theorem surrogateDiagonalTailChunk000Sub000Block063Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part019] using hcert

def TailChunk000Sub000Block063Part020SupportExplicit : Finset ℕ :=
  ([2674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part020 : ℚ :=
  (37647499 : ℚ) / 422324488008

def SurrogateDiagonalTailChunk000Sub000Block063Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2674
    = surrogateDiagTailX0RatChunk000Sub000Block063Part020

theorem surrogateDiagonalTailChunk000Sub000Block063Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part020] using hcert

def TailChunk000Sub000Block063Part021SupportExplicit : Finset ℕ :=
  ([2677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part021 : ℚ :=
  (895611966775 : ℚ) / 128224582970076288

def SurrogateDiagonalTailChunk000Sub000Block063Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2677
    = surrogateDiagTailX0RatChunk000Sub000Block063Part021

theorem surrogateDiagonalTailChunk000Sub000Block063Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part021] using hcert

def TailChunk000Sub000Block063Part022SupportExplicit : Finset ℕ :=
  ([2678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part022 : ℚ :=
  (22608280175 : ℚ) / 311802810172416

def SurrogateDiagonalTailChunk000Sub000Block063Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2678
    = surrogateDiagTailX0RatChunk000Sub000Block063Part022

theorem surrogateDiagonalTailChunk000Sub000Block063Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part022] using hcert

def TailChunk000Sub000Block063Part023SupportExplicit : Finset ℕ :=
  ([2679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part023 : ℚ :=
  (275812271525 : ℚ) / 9402388522804224

def SurrogateDiagonalTailChunk000Sub000Block063Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2679
    = surrogateDiagTailX0RatChunk000Sub000Block063Part023

theorem surrogateDiagonalTailChunk000Sub000Block063Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part023] using hcert

def TailChunk000Sub000Block063Part024SupportExplicit : Finset ℕ :=
  ([2681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block063Part024 : ℚ :=
  (379499953775 : ℚ) / 34502877512783424

def SurrogateDiagonalTailChunk000Sub000Block063Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2681
    = surrogateDiagTailX0RatChunk000Sub000Block063Part024

theorem surrogateDiagonalTailChunk000Sub000Block063Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block063Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block063Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block063Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block063Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block063Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block063Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block063HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block063Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block063Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block063Part000
    + surrogateDiagTailX0RatChunk000Sub000Block063Part001
    + surrogateDiagTailX0RatChunk000Sub000Block063Part002
    + surrogateDiagTailX0RatChunk000Sub000Block063Part003
    + surrogateDiagTailX0RatChunk000Sub000Block063Part004
    + surrogateDiagTailX0RatChunk000Sub000Block063Part005
    + surrogateDiagTailX0RatChunk000Sub000Block063Part006
    + surrogateDiagTailX0RatChunk000Sub000Block063Part007
    + surrogateDiagTailX0RatChunk000Sub000Block063Part008
    + surrogateDiagTailX0RatChunk000Sub000Block063Part009

def surrogateDiagonalTailChunk000Sub000Block063MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block063Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block063Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block063Part010
    + surrogateDiagTailX0RatChunk000Sub000Block063Part011
    + surrogateDiagTailX0RatChunk000Sub000Block063Part012
    + surrogateDiagTailX0RatChunk000Sub000Block063Part013
    + surrogateDiagTailX0RatChunk000Sub000Block063Part014
    + surrogateDiagTailX0RatChunk000Sub000Block063Part015
    + surrogateDiagTailX0RatChunk000Sub000Block063Part016
    + surrogateDiagTailX0RatChunk000Sub000Block063Part017
    + surrogateDiagTailX0RatChunk000Sub000Block063Part018
    + surrogateDiagTailX0RatChunk000Sub000Block063Part019

def surrogateDiagonalTailChunk000Sub000Block063TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block063Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block063Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block063Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block063Part020
    + surrogateDiagTailX0RatChunk000Sub000Block063Part021
    + surrogateDiagTailX0RatChunk000Sub000Block063Part022
    + surrogateDiagTailX0RatChunk000Sub000Block063Part023
    + surrogateDiagTailX0RatChunk000Sub000Block063Part024

def surrogateDiagonalTailChunk000Sub000Block063Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block063HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block063MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block063TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block063 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block063Part000
    + surrogateDiagTailX0RatChunk000Sub000Block063Part001
    + surrogateDiagTailX0RatChunk000Sub000Block063Part002
    + surrogateDiagTailX0RatChunk000Sub000Block063Part003
    + surrogateDiagTailX0RatChunk000Sub000Block063Part004
    + surrogateDiagTailX0RatChunk000Sub000Block063Part005
    + surrogateDiagTailX0RatChunk000Sub000Block063Part006
    + surrogateDiagTailX0RatChunk000Sub000Block063Part007
    + surrogateDiagTailX0RatChunk000Sub000Block063Part008
    + surrogateDiagTailX0RatChunk000Sub000Block063Part009
    + surrogateDiagTailX0RatChunk000Sub000Block063Part010
    + surrogateDiagTailX0RatChunk000Sub000Block063Part011
    + surrogateDiagTailX0RatChunk000Sub000Block063Part012
    + surrogateDiagTailX0RatChunk000Sub000Block063Part013
    + surrogateDiagTailX0RatChunk000Sub000Block063Part014
    + surrogateDiagTailX0RatChunk000Sub000Block063Part015
    + surrogateDiagTailX0RatChunk000Sub000Block063Part016
    + surrogateDiagTailX0RatChunk000Sub000Block063Part017
    + surrogateDiagTailX0RatChunk000Sub000Block063Part018
    + surrogateDiagTailX0RatChunk000Sub000Block063Part019
    + surrogateDiagTailX0RatChunk000Sub000Block063Part020
    + surrogateDiagTailX0RatChunk000Sub000Block063Part021
    + surrogateDiagTailX0RatChunk000Sub000Block063Part022
    + surrogateDiagTailX0RatChunk000Sub000Block063Part023
    + surrogateDiagTailX0RatChunk000Sub000Block063Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block063_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block063Head + surrogateDiagTailX0RatChunk000Sub000Block063Mid + surrogateDiagTailX0RatChunk000Sub000Block063Tail =
      surrogateDiagTailX0RatChunk000Sub000Block063 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block063Head surrogateDiagTailX0RatChunk000Sub000Block063Mid surrogateDiagTailX0RatChunk000Sub000Block063Tail surrogateDiagTailX0RatChunk000Sub000Block063
  ring

def SurrogateDiagonalTailChunk000Sub000Block063HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block063HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block063Head

def SurrogateDiagonalTailChunk000Sub000Block063MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block063MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block063Mid

def SurrogateDiagonalTailChunk000Sub000Block063TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block063TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block063Tail

theorem surrogateDiagonalTailChunk000Sub000Block063_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block063HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block063MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block063TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block063Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block063 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block063HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block063MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block063TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block063Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block063_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
