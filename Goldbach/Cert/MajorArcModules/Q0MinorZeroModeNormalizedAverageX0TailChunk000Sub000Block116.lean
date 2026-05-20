import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [116,117). -/

/- Block 116 covers tail-support indices [2900,2925) and q from 4819 to 4858. -/

def TailChunk000Sub000Block116Part000SupportExplicit : Finset ℕ :=
  ([4819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part000 : ℚ :=
  (58077611 : ℚ) / 49363278681600

def SurrogateDiagonalTailChunk000Sub000Block116Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4819
    = surrogateDiagTailX0RatChunk000Sub000Block116Part000

theorem surrogateDiagonalTailChunk000Sub000Block116Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part000] using hcert

def TailChunk000Sub000Block116Part001SupportExplicit : Finset ℕ :=
  ([4821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part001 : ℚ :=
  (96783825 : ℚ) / 26609833374784

def SurrogateDiagonalTailChunk000Sub000Block116Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4821
    = surrogateDiagTailX0RatChunk000Sub000Block116Part001

theorem surrogateDiagonalTailChunk000Sub000Block116Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part001] using hcert

def TailChunk000Sub000Block116Part002SupportExplicit : Finset ℕ :=
  ([4822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part002 : ℚ :=
  (29058792079 : ℚ) / 3374077241512200

def SurrogateDiagonalTailChunk000Sub000Block116Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4822
    = surrogateDiagTailX0RatChunk000Sub000Block116Part002

theorem surrogateDiagonalTailChunk000Sub000Block116Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part002] using hcert

def TailChunk000Sub000Block116Part003SupportExplicit : Finset ℕ :=
  ([4823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part003 : ℚ :=
  (126245999375 : ℚ) / 54591837159555072

def SurrogateDiagonalTailChunk000Sub000Block116Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4823
    = surrogateDiagTailX0RatChunk000Sub000Block116Part003

theorem surrogateDiagonalTailChunk000Sub000Block116Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part003] using hcert

def TailChunk000Sub000Block116Part004SupportExplicit : Finset ℕ :=
  ([4826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part004 : ℚ :=
  (38078176525 : ℚ) / 3675585712228416

def SurrogateDiagonalTailChunk000Sub000Block116Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4826
    = surrogateDiagTailX0RatChunk000Sub000Block116Part004

theorem surrogateDiagonalTailChunk000Sub000Block116Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part004] using hcert

def TailChunk000Sub000Block116Part005SupportExplicit : Finset ℕ :=
  ([4827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part005 : ℚ :=
  (32341625 : ℚ) / 8914211094528

def SurrogateDiagonalTailChunk000Sub000Block116Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4827
    = surrogateDiagTailX0RatChunk000Sub000Block116Part005

theorem surrogateDiagonalTailChunk000Sub000Block116Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part005] using hcert

def TailChunk000Sub000Block116Part006SupportExplicit : Finset ℕ :=
  ([4829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part006 : ℚ :=
  (10674424337 : ℚ) / 7362296232013440

def SurrogateDiagonalTailChunk000Sub000Block116Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4829
    = surrogateDiagTailX0RatChunk000Sub000Block116Part006

theorem surrogateDiagonalTailChunk000Sub000Block116Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part006] using hcert

def TailChunk000Sub000Block116Part007SupportExplicit : Finset ℕ :=
  ([4830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part007 : ℚ :=
  (321748720525 : ℚ) / 3109442510389248

def SurrogateDiagonalTailChunk000Sub000Block116Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4830
    = surrogateDiagTailX0RatChunk000Sub000Block116Part007

theorem surrogateDiagonalTailChunk000Sub000Block116Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part007] using hcert

def TailChunk000Sub000Block116Part008SupportExplicit : Finset ℕ :=
  ([4831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part008 : ℚ :=
  (583464025 : ℚ) / 544346422725042

def SurrogateDiagonalTailChunk000Sub000Block116Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4831
    = surrogateDiagTailX0RatChunk000Sub000Block116Part008

theorem surrogateDiagonalTailChunk000Sub000Block116Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part008] using hcert

def TailChunk000Sub000Block116Part009SupportExplicit : Finset ℕ :=
  ([4834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part009 : ℚ :=
  (730090077775 : ℚ) / 85195092479213568

def SurrogateDiagonalTailChunk000Sub000Block116Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4834
    = surrogateDiagTailX0RatChunk000Sub000Block116Part009

theorem surrogateDiagonalTailChunk000Sub000Block116Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part009] using hcert

def TailChunk000Sub000Block116Part010SupportExplicit : Finset ℕ :=
  ([4835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part010 : ℚ :=
  (583964144375 : ℚ) / 278705368435221504

def SurrogateDiagonalTailChunk000Sub000Block116Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4835
    = surrogateDiagTailX0RatChunk000Sub000Block116Part010

theorem surrogateDiagonalTailChunk000Sub000Block116Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part010] using hcert

def TailChunk000Sub000Block116Part011SupportExplicit : Finset ℕ :=
  ([4837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part011 : ℚ :=
  (185464391 : ℚ) / 108823941236160

def SurrogateDiagonalTailChunk000Sub000Block116Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4837
    = surrogateDiagTailX0RatChunk000Sub000Block116Part011

theorem surrogateDiagonalTailChunk000Sub000Block116Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part011] using hcert

def TailChunk000Sub000Block116Part012SupportExplicit : Finset ℕ :=
  ([4838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part012 : ℚ :=
  (14053812281 : ℚ) / 1448801190297600

def SurrogateDiagonalTailChunk000Sub000Block116Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4838
    = surrogateDiagTailX0RatChunk000Sub000Block116Part012

theorem surrogateDiagonalTailChunk000Sub000Block116Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part012] using hcert

def TailChunk000Sub000Block116Part013SupportExplicit : Finset ℕ :=
  ([4839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part013 : ℚ :=
  (1137682662925 : ℚ) / 270151256244799488

def SurrogateDiagonalTailChunk000Sub000Block116Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4839
    = surrogateDiagTailX0RatChunk000Sub000Block116Part013

theorem surrogateDiagonalTailChunk000Sub000Block116Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part013] using hcert

def TailChunk000Sub000Block116Part014SupportExplicit : Finset ℕ :=
  ([4841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part014 : ℚ :=
  (19735611775 : ℚ) / 16831637770343184

def SurrogateDiagonalTailChunk000Sub000Block116Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4841
    = surrogateDiagTailX0RatChunk000Sub000Block116Part014

theorem surrogateDiagonalTailChunk000Sub000Block116Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part014] using hcert

def TailChunk000Sub000Block116Part015SupportExplicit : Finset ℕ :=
  ([4843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part015 : ℚ :=
  (21991054525 : ℚ) / 18235234913079072

def SurrogateDiagonalTailChunk000Sub000Block116Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4843
    = surrogateDiagTailX0RatChunk000Sub000Block116Part015

theorem surrogateDiagonalTailChunk000Sub000Block116Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part015] using hcert

def TailChunk000Sub000Block116Part016SupportExplicit : Finset ℕ :=
  ([4845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part016 : ℚ :=
  (30025676825 : ℚ) / 2935928779702272

def SurrogateDiagonalTailChunk000Sub000Block116Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4845
    = surrogateDiagTailX0RatChunk000Sub000Block116Part016

theorem surrogateDiagonalTailChunk000Sub000Block116Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part016] using hcert

def TailChunk000Sub000Block116Part017SupportExplicit : Finset ℕ :=
  ([4846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part017 : ℚ :=
  (733719351775 : ℚ) / 86044559208387528

def SurrogateDiagonalTailChunk000Sub000Block116Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4846
    = surrogateDiagTailX0RatChunk000Sub000Block116Part017

theorem surrogateDiagonalTailChunk000Sub000Block116Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part017] using hcert

def TailChunk000Sub000Block116Part018SupportExplicit : Finset ℕ :=
  ([4847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part018 : ℚ :=
  (7097103473 : ℚ) / 5997638359814400

def SurrogateDiagonalTailChunk000Sub000Block116Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4847
    = surrogateDiagTailX0RatChunk000Sub000Block116Part018

theorem surrogateDiagonalTailChunk000Sub000Block116Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part018] using hcert

def TailChunk000Sub000Block116Part019SupportExplicit : Finset ℕ :=
  ([4849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part019 : ℚ :=
  (676629173675 : ℚ) / 496470681620987904

def SurrogateDiagonalTailChunk000Sub000Block116Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4849
    = surrogateDiagTailX0RatChunk000Sub000Block116Part019

theorem surrogateDiagonalTailChunk000Sub000Block116Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part019] using hcert

def TailChunk000Sub000Block116Part020SupportExplicit : Finset ℕ :=
  ([4853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part020 : ℚ :=
  (3121179239 : ℚ) / 2531525155790400

def SurrogateDiagonalTailChunk000Sub000Block116Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4853
    = surrogateDiagTailX0RatChunk000Sub000Block116Part020

theorem surrogateDiagonalTailChunk000Sub000Block116Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part020] using hcert

def TailChunk000Sub000Block116Part021SupportExplicit : Finset ℕ :=
  ([4854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part021 : ℚ :=
  (98054475 : ℚ) / 3409851219968

def SurrogateDiagonalTailChunk000Sub000Block116Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4854
    = surrogateDiagTailX0RatChunk000Sub000Block116Part021

theorem surrogateDiagonalTailChunk000Sub000Block116Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part021] using hcert

def TailChunk000Sub000Block116Part022SupportExplicit : Finset ℕ :=
  ([4855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part022 : ℚ :=
  (8474036899 : ℚ) / 2266802863518720

def SurrogateDiagonalTailChunk000Sub000Block116Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4855
    = surrogateDiagTailX0RatChunk000Sub000Block116Part022

theorem surrogateDiagonalTailChunk000Sub000Block116Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part022] using hcert

def TailChunk000Sub000Block116Part023SupportExplicit : Finset ℕ :=
  ([4857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part023 : ℚ :=
  (98234625 : ℚ) / 27414104279104

def SurrogateDiagonalTailChunk000Sub000Block116Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4857
    = surrogateDiagTailX0RatChunk000Sub000Block116Part023

theorem surrogateDiagonalTailChunk000Sub000Block116Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part023] using hcert

def TailChunk000Sub000Block116Part024SupportExplicit : Finset ℕ :=
  ([4858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block116Part024 : ℚ :=
  (637986467875 : ℚ) / 46444710010025088

def SurrogateDiagonalTailChunk000Sub000Block116Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4858
    = surrogateDiagTailX0RatChunk000Sub000Block116Part024

theorem surrogateDiagonalTailChunk000Sub000Block116Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block116Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block116Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block116Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block116Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block116Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block116Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block116HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block116Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block116Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block116Part000
    + surrogateDiagTailX0RatChunk000Sub000Block116Part001
    + surrogateDiagTailX0RatChunk000Sub000Block116Part002
    + surrogateDiagTailX0RatChunk000Sub000Block116Part003
    + surrogateDiagTailX0RatChunk000Sub000Block116Part004
    + surrogateDiagTailX0RatChunk000Sub000Block116Part005
    + surrogateDiagTailX0RatChunk000Sub000Block116Part006
    + surrogateDiagTailX0RatChunk000Sub000Block116Part007
    + surrogateDiagTailX0RatChunk000Sub000Block116Part008
    + surrogateDiagTailX0RatChunk000Sub000Block116Part009

def surrogateDiagonalTailChunk000Sub000Block116MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block116Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block116Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block116Part010
    + surrogateDiagTailX0RatChunk000Sub000Block116Part011
    + surrogateDiagTailX0RatChunk000Sub000Block116Part012
    + surrogateDiagTailX0RatChunk000Sub000Block116Part013
    + surrogateDiagTailX0RatChunk000Sub000Block116Part014
    + surrogateDiagTailX0RatChunk000Sub000Block116Part015
    + surrogateDiagTailX0RatChunk000Sub000Block116Part016
    + surrogateDiagTailX0RatChunk000Sub000Block116Part017
    + surrogateDiagTailX0RatChunk000Sub000Block116Part018
    + surrogateDiagTailX0RatChunk000Sub000Block116Part019

def surrogateDiagonalTailChunk000Sub000Block116TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block116Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block116Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block116Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block116Part020
    + surrogateDiagTailX0RatChunk000Sub000Block116Part021
    + surrogateDiagTailX0RatChunk000Sub000Block116Part022
    + surrogateDiagTailX0RatChunk000Sub000Block116Part023
    + surrogateDiagTailX0RatChunk000Sub000Block116Part024

def surrogateDiagonalTailChunk000Sub000Block116Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block116HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block116MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block116TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block116 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block116Part000
    + surrogateDiagTailX0RatChunk000Sub000Block116Part001
    + surrogateDiagTailX0RatChunk000Sub000Block116Part002
    + surrogateDiagTailX0RatChunk000Sub000Block116Part003
    + surrogateDiagTailX0RatChunk000Sub000Block116Part004
    + surrogateDiagTailX0RatChunk000Sub000Block116Part005
    + surrogateDiagTailX0RatChunk000Sub000Block116Part006
    + surrogateDiagTailX0RatChunk000Sub000Block116Part007
    + surrogateDiagTailX0RatChunk000Sub000Block116Part008
    + surrogateDiagTailX0RatChunk000Sub000Block116Part009
    + surrogateDiagTailX0RatChunk000Sub000Block116Part010
    + surrogateDiagTailX0RatChunk000Sub000Block116Part011
    + surrogateDiagTailX0RatChunk000Sub000Block116Part012
    + surrogateDiagTailX0RatChunk000Sub000Block116Part013
    + surrogateDiagTailX0RatChunk000Sub000Block116Part014
    + surrogateDiagTailX0RatChunk000Sub000Block116Part015
    + surrogateDiagTailX0RatChunk000Sub000Block116Part016
    + surrogateDiagTailX0RatChunk000Sub000Block116Part017
    + surrogateDiagTailX0RatChunk000Sub000Block116Part018
    + surrogateDiagTailX0RatChunk000Sub000Block116Part019
    + surrogateDiagTailX0RatChunk000Sub000Block116Part020
    + surrogateDiagTailX0RatChunk000Sub000Block116Part021
    + surrogateDiagTailX0RatChunk000Sub000Block116Part022
    + surrogateDiagTailX0RatChunk000Sub000Block116Part023
    + surrogateDiagTailX0RatChunk000Sub000Block116Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block116_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block116Head + surrogateDiagTailX0RatChunk000Sub000Block116Mid + surrogateDiagTailX0RatChunk000Sub000Block116Tail =
      surrogateDiagTailX0RatChunk000Sub000Block116 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block116Head surrogateDiagTailX0RatChunk000Sub000Block116Mid surrogateDiagTailX0RatChunk000Sub000Block116Tail surrogateDiagTailX0RatChunk000Sub000Block116
  ring

def SurrogateDiagonalTailChunk000Sub000Block116HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block116HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block116Head

def SurrogateDiagonalTailChunk000Sub000Block116MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block116MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block116Mid

def SurrogateDiagonalTailChunk000Sub000Block116TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block116TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block116Tail

theorem surrogateDiagonalTailChunk000Sub000Block116_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block116HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block116MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block116TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block116Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block116 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block116HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block116MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block116TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block116Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block116_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
