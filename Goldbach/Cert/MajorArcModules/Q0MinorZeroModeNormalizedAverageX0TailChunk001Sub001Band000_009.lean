import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [0,10). -/

/-- Block 000 covers tail-support indices [15000,15025) and q from 24727 to 24765. -/

def TailChunk001Sub001Block000Part000SupportExplicit : Finset ℕ :=
  ([24727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part000 : ℚ :=
  (121321193275 : ℚ) / 877048571876654481408

def SurrogateDiagonalTailChunk001Sub001Block000Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24727
    = surrogateDiagTailX0RatChunk001Sub001Block000Part000

theorem surrogateDiagonalTailChunk001Sub001Block000Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part000] using hcert

def TailChunk001Sub001Block000Part001SupportExplicit : Finset ℕ :=
  ([24729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part001 : ℚ :=
  (2123142615725 : ℚ) / 92309688753263352384

def SurrogateDiagonalTailChunk001Sub001Block000Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24729
    = surrogateDiagTailX0RatChunk001Sub001Block000Part001

theorem surrogateDiagonalTailChunk001Sub001Block000Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part001] using hcert

def TailChunk001Sub001Block000Part002SupportExplicit : Finset ℕ :=
  ([24730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part002 : ℚ :=
  (254981871175 : ℚ) / 7967818545253318656

def SurrogateDiagonalTailChunk001Sub001Block000Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24730
    = surrogateDiagTailX0RatChunk001Sub001Block000Part002

theorem surrogateDiagonalTailChunk001Sub001Block000Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part002] using hcert

def TailChunk001Sub001Block000Part003SupportExplicit : Finset ℕ :=
  ([24731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part003 : ℚ :=
  (781563926425 : ℚ) / 504329810906889013248

def SurrogateDiagonalTailChunk001Sub001Block000Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24731
    = surrogateDiagTailX0RatChunk001Sub001Block000Part003

theorem surrogateDiagonalTailChunk001Sub001Block000Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part003] using hcert

def TailChunk001Sub001Block000Part004SupportExplicit : Finset ℕ :=
  ([24733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block000Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24733
    = surrogateDiagTailX0RatChunk001Sub001Block000Part004

theorem surrogateDiagonalTailChunk001Sub001Block000Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part004] using hcert

def TailChunk001Sub001Block000Part005SupportExplicit : Finset ℕ :=
  ([24734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part005 : ℚ :=
  (71763950725 : ℚ) / 54241180136789035008

def SurrogateDiagonalTailChunk001Sub001Block000Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24734
    = surrogateDiagTailX0RatChunk001Sub001Block000Part005

theorem surrogateDiagonalTailChunk001Sub001Block000Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part005] using hcert

def TailChunk001Sub001Block000Part006SupportExplicit : Finset ℕ :=
  ([24735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part006 : ℚ :=
  (1127388865325 : ℚ) / 19003360840154873856

def SurrogateDiagonalTailChunk001Sub001Block000Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24735
    = surrogateDiagTailX0RatChunk001Sub001Block000Part006

theorem surrogateDiagonalTailChunk001Sub001Block000Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part006] using hcert

def TailChunk001Sub001Block000Part007SupportExplicit : Finset ℕ :=
  ([24737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part007 : ℚ :=
  (280673863375 : ℚ) / 809873825855489998848

def SurrogateDiagonalTailChunk001Sub001Block000Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24737
    = surrogateDiagTailX0RatChunk001Sub001Block000Part007

theorem surrogateDiagonalTailChunk001Sub001Block000Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part007] using hcert

def TailChunk001Sub001Block000Part008SupportExplicit : Finset ℕ :=
  ([24738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part008 : ℚ :=
  (1812145165 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk001Sub001Block000Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24738
    = surrogateDiagTailX0RatChunk001Sub001Block000Part008

theorem surrogateDiagonalTailChunk001Sub001Block000Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part008] using hcert

def TailChunk001Sub001Block000Part009SupportExplicit : Finset ℕ :=
  ([24739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part009 : ℚ :=
  (23379692699 : ℚ) / 9076023806400921600

def SurrogateDiagonalTailChunk001Sub001Block000Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24739
    = surrogateDiagTailX0RatChunk001Sub001Block000Part009

theorem surrogateDiagonalTailChunk001Sub001Block000Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part009] using hcert

def TailChunk001Sub001Block000Part010SupportExplicit : Finset ℕ :=
  ([24742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part010 : ℚ :=
  (3913101475 : ℚ) / 3021352435936935936

def SurrogateDiagonalTailChunk001Sub001Block000Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24742
    = surrogateDiagTailX0RatChunk001Sub001Block000Part010

theorem surrogateDiagonalTailChunk001Sub001Block000Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part010] using hcert

def TailChunk001Sub001Block000Part011SupportExplicit : Finset ℕ :=
  ([24743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part011 : ℚ :=
  (17296541875 : ℚ) / 147912332949702724608

def SurrogateDiagonalTailChunk001Sub001Block000Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24743
    = surrogateDiagTailX0RatChunk001Sub001Block000Part011

theorem surrogateDiagonalTailChunk001Sub001Block000Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part011] using hcert

def TailChunk001Sub001Block000Part012SupportExplicit : Finset ℕ :=
  ([24746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block000Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24746
    = surrogateDiagTailX0RatChunk001Sub001Block000Part012

theorem surrogateDiagonalTailChunk001Sub001Block000Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part012] using hcert

def TailChunk001Sub001Block000Part013SupportExplicit : Finset ℕ :=
  ([24747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part013 : ℚ :=
  (1392583333975 : ℚ) / 56393320000521240576

def SurrogateDiagonalTailChunk001Sub001Block000Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24747
    = surrogateDiagTailX0RatChunk001Sub001Block000Part013

theorem surrogateDiagonalTailChunk001Sub001Block000Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part013] using hcert

def TailChunk001Sub001Block000Part014SupportExplicit : Finset ℕ :=
  ([24749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block000Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24749
    = surrogateDiagTailX0RatChunk001Sub001Block000Part014

theorem surrogateDiagonalTailChunk001Sub001Block000Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part014] using hcert

def TailChunk001Sub001Block000Part015SupportExplicit : Finset ℕ :=
  ([24751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part015 : ℚ :=
  (165354578125 : ℚ) / 862152119467582015488

def SurrogateDiagonalTailChunk001Sub001Block000Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24751
    = surrogateDiagTailX0RatChunk001Sub001Block000Part015

theorem surrogateDiagonalTailChunk001Sub001Block000Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part015] using hcert

def TailChunk001Sub001Block000Part016SupportExplicit : Finset ℕ :=
  ([24753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part016 : ℚ :=
  (460421363225 : ℚ) / 18135362167697866752

def SurrogateDiagonalTailChunk001Sub001Block000Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24753
    = surrogateDiagTailX0RatChunk001Sub001Block000Part016

theorem surrogateDiagonalTailChunk001Sub001Block000Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part016] using hcert

def TailChunk001Sub001Block000Part017SupportExplicit : Finset ℕ :=
  ([24754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block000Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24754
    = surrogateDiagTailX0RatChunk001Sub001Block000Part017

theorem surrogateDiagonalTailChunk001Sub001Block000Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part017] using hcert

def TailChunk001Sub001Block000Part018SupportExplicit : Finset ℕ :=
  ([24755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part018 : ℚ :=
  (12261254549 : ℚ) / 3074522013446400000

def SurrogateDiagonalTailChunk001Sub001Block000Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24755
    = surrogateDiagTailX0RatChunk001Sub001Block000Part018

theorem surrogateDiagonalTailChunk001Sub001Block000Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part018] using hcert

def TailChunk001Sub001Block000Part019SupportExplicit : Finset ℕ :=
  ([24757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part019 : ℚ :=
  (47685496525 : ℚ) / 83814335618343184512

def SurrogateDiagonalTailChunk001Sub001Block000Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24757
    = surrogateDiagTailX0RatChunk001Sub001Block000Part019

theorem surrogateDiagonalTailChunk001Sub001Block000Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part019] using hcert

def TailChunk001Sub001Block000Part020SupportExplicit : Finset ℕ :=
  ([24758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block000Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24758
    = surrogateDiagTailX0RatChunk001Sub001Block000Part020

theorem surrogateDiagonalTailChunk001Sub001Block000Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part020] using hcert

def TailChunk001Sub001Block000Part021SupportExplicit : Finset ℕ :=
  ([24761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part021 : ℚ :=
  (264922349 : ℚ) / 267021166992187500

def SurrogateDiagonalTailChunk001Sub001Block000Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24761
    = surrogateDiagTailX0RatChunk001Sub001Block000Part021

theorem surrogateDiagonalTailChunk001Sub001Block000Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part021] using hcert

def TailChunk001Sub001Block000Part022SupportExplicit : Finset ℕ :=
  ([24762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part022 : ℚ :=
  (532308667175 : ℚ) / 5797406330683773504

def SurrogateDiagonalTailChunk001Sub001Block000Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24762
    = surrogateDiagTailX0RatChunk001Sub001Block000Part022

theorem surrogateDiagonalTailChunk001Sub001Block000Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part022] using hcert

def TailChunk001Sub001Block000Part023SupportExplicit : Finset ℕ :=
  ([24763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block000Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24763
    = surrogateDiagTailX0RatChunk001Sub001Block000Part023

theorem surrogateDiagonalTailChunk001Sub001Block000Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part023] using hcert

def TailChunk001Sub001Block000Part024SupportExplicit : Finset ℕ :=
  ([24765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block000Part024 : ℚ :=
  (834847934125 : ℚ) / 13382399179811192832

def SurrogateDiagonalTailChunk001Sub001Block000Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24765
    = surrogateDiagTailX0RatChunk001Sub001Block000Part024

theorem surrogateDiagonalTailChunk001Sub001Block000Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block000Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block000Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block000Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block000Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block000Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block000Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block000HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block000Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block000Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block000Part000
    + surrogateDiagTailX0RatChunk001Sub001Block000Part001
    + surrogateDiagTailX0RatChunk001Sub001Block000Part002
    + surrogateDiagTailX0RatChunk001Sub001Block000Part003
    + surrogateDiagTailX0RatChunk001Sub001Block000Part004
    + surrogateDiagTailX0RatChunk001Sub001Block000Part005
    + surrogateDiagTailX0RatChunk001Sub001Block000Part006
    + surrogateDiagTailX0RatChunk001Sub001Block000Part007
    + surrogateDiagTailX0RatChunk001Sub001Block000Part008
    + surrogateDiagTailX0RatChunk001Sub001Block000Part009

def surrogateDiagonalTailChunk001Sub001Block000MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block000Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block000Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block000Part010
    + surrogateDiagTailX0RatChunk001Sub001Block000Part011
    + surrogateDiagTailX0RatChunk001Sub001Block000Part012
    + surrogateDiagTailX0RatChunk001Sub001Block000Part013
    + surrogateDiagTailX0RatChunk001Sub001Block000Part014
    + surrogateDiagTailX0RatChunk001Sub001Block000Part015
    + surrogateDiagTailX0RatChunk001Sub001Block000Part016
    + surrogateDiagTailX0RatChunk001Sub001Block000Part017
    + surrogateDiagTailX0RatChunk001Sub001Block000Part018
    + surrogateDiagTailX0RatChunk001Sub001Block000Part019

def surrogateDiagonalTailChunk001Sub001Block000TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block000Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block000Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block000Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block000Part020
    + surrogateDiagTailX0RatChunk001Sub001Block000Part021
    + surrogateDiagTailX0RatChunk001Sub001Block000Part022
    + surrogateDiagTailX0RatChunk001Sub001Block000Part023
    + surrogateDiagTailX0RatChunk001Sub001Block000Part024

def surrogateDiagonalTailChunk001Sub001Block000Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block000HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block000MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block000TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block000 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block000Part000
    + surrogateDiagTailX0RatChunk001Sub001Block000Part001
    + surrogateDiagTailX0RatChunk001Sub001Block000Part002
    + surrogateDiagTailX0RatChunk001Sub001Block000Part003
    + surrogateDiagTailX0RatChunk001Sub001Block000Part004
    + surrogateDiagTailX0RatChunk001Sub001Block000Part005
    + surrogateDiagTailX0RatChunk001Sub001Block000Part006
    + surrogateDiagTailX0RatChunk001Sub001Block000Part007
    + surrogateDiagTailX0RatChunk001Sub001Block000Part008
    + surrogateDiagTailX0RatChunk001Sub001Block000Part009
    + surrogateDiagTailX0RatChunk001Sub001Block000Part010
    + surrogateDiagTailX0RatChunk001Sub001Block000Part011
    + surrogateDiagTailX0RatChunk001Sub001Block000Part012
    + surrogateDiagTailX0RatChunk001Sub001Block000Part013
    + surrogateDiagTailX0RatChunk001Sub001Block000Part014
    + surrogateDiagTailX0RatChunk001Sub001Block000Part015
    + surrogateDiagTailX0RatChunk001Sub001Block000Part016
    + surrogateDiagTailX0RatChunk001Sub001Block000Part017
    + surrogateDiagTailX0RatChunk001Sub001Block000Part018
    + surrogateDiagTailX0RatChunk001Sub001Block000Part019
    + surrogateDiagTailX0RatChunk001Sub001Block000Part020
    + surrogateDiagTailX0RatChunk001Sub001Block000Part021
    + surrogateDiagTailX0RatChunk001Sub001Block000Part022
    + surrogateDiagTailX0RatChunk001Sub001Block000Part023
    + surrogateDiagTailX0RatChunk001Sub001Block000Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block000_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block000Head + surrogateDiagTailX0RatChunk001Sub001Block000Mid + surrogateDiagTailX0RatChunk001Sub001Block000Tail =
      surrogateDiagTailX0RatChunk001Sub001Block000 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block000Head surrogateDiagTailX0RatChunk001Sub001Block000Mid surrogateDiagTailX0RatChunk001Sub001Block000Tail surrogateDiagTailX0RatChunk001Sub001Block000
  ring

def SurrogateDiagonalTailChunk001Sub001Block000HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block000HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block000Head

def SurrogateDiagonalTailChunk001Sub001Block000MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block000MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block000Mid

def SurrogateDiagonalTailChunk001Sub001Block000TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block000TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block000Tail

theorem surrogateDiagonalTailChunk001Sub001Block000_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block000HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block000MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block000TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block000Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block000 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block000HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block000MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block000TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block000Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block000_eq_head_add_mid_add_tail

/-- Block 001 covers tail-support indices [15025,15050) and q from 24766 to 24806. -/

def TailChunk001Sub001Block001Part000SupportExplicit : Finset ℕ :=
  ([24766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part000 : ℚ :=
  (230827097 : ℚ) / 8604937744220160

def SurrogateDiagonalTailChunk001Sub001Block001Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24766
    = surrogateDiagTailX0RatChunk001Sub001Block001Part000

theorem surrogateDiagonalTailChunk001Sub001Block001Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part000] using hcert

def TailChunk001Sub001Block001Part001SupportExplicit : Finset ℕ :=
  ([24767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block001Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24767
    = surrogateDiagTailX0RatChunk001Sub001Block001Part001

theorem surrogateDiagonalTailChunk001Sub001Block001Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part001] using hcert

def TailChunk001Sub001Block001Part002SupportExplicit : Finset ℕ :=
  ([24769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part002 : ℚ :=
  (15272102771 : ℚ) / 11886476354754969600

def SurrogateDiagonalTailChunk001Sub001Block001Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24769
    = surrogateDiagTailX0RatChunk001Sub001Block001Part002

theorem surrogateDiagonalTailChunk001Sub001Block001Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part002] using hcert

def TailChunk001Sub001Block001Part003SupportExplicit : Finset ℕ :=
  ([24770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part003 : ℚ :=
  (767419117525 : ℚ) / 24058546485884387328

def SurrogateDiagonalTailChunk001Sub001Block001Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24770
    = surrogateDiagTailX0RatChunk001Sub001Block001Part003

theorem surrogateDiagonalTailChunk001Sub001Block001Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part003] using hcert

def TailChunk001Sub001Block001Part004SupportExplicit : Finset ℕ :=
  ([24771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part004 : ℚ :=
  (2045496899075 : ℚ) / 76973223735501333504

def SurrogateDiagonalTailChunk001Sub001Block001Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24771
    = surrogateDiagTailX0RatChunk001Sub001Block001Part004

theorem surrogateDiagonalTailChunk001Sub001Block001Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part004] using hcert

def TailChunk001Sub001Block001Part005SupportExplicit : Finset ℕ :=
  ([24773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part005 : ℚ :=
  (784215176725 : ℚ) / 507765482699742592128

def SurrogateDiagonalTailChunk001Sub001Block001Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24773
    = surrogateDiagTailX0RatChunk001Sub001Block001Part005

theorem surrogateDiagonalTailChunk001Sub001Block001Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part005] using hcert

def TailChunk001Sub001Block001Part006SupportExplicit : Finset ℕ :=
  ([24774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part006 : ℚ :=
  (266412271075 : ℚ) / 2904327618048294912

def SurrogateDiagonalTailChunk001Sub001Block001Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24774
    = surrogateDiagTailX0RatChunk001Sub001Block001Part006

theorem surrogateDiagonalTailChunk001Sub001Block001Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part006] using hcert

def TailChunk001Sub001Block001Part007SupportExplicit : Finset ℕ :=
  ([24778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part007 : ℚ :=
  (286746290125 : ℚ) / 42589215130963673088

def SurrogateDiagonalTailChunk001Sub001Block001Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24778
    = surrogateDiagTailX0RatChunk001Sub001Block001Part007

theorem surrogateDiagonalTailChunk001Sub001Block001Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part007] using hcert

def TailChunk001Sub001Block001Part008SupportExplicit : Finset ℕ :=
  ([24779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part008 : ℚ :=
  (364119191 : ℚ) / 2515752716877388800

def SurrogateDiagonalTailChunk001Sub001Block001Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24779
    = surrogateDiagTailX0RatChunk001Sub001Block001Part008

theorem surrogateDiagonalTailChunk001Sub001Block001Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part008] using hcert

def TailChunk001Sub001Block001Part009SupportExplicit : Finset ℕ :=
  ([24781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block001Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24781
    = surrogateDiagTailX0RatChunk001Sub001Block001Part009

theorem surrogateDiagonalTailChunk001Sub001Block001Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part009] using hcert

def TailChunk001Sub001Block001Part010SupportExplicit : Finset ℕ :=
  ([24782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block001Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24782
    = surrogateDiagTailX0RatChunk001Sub001Block001Part010

theorem surrogateDiagonalTailChunk001Sub001Block001Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part010] using hcert

def TailChunk001Sub001Block001Part011SupportExplicit : Finset ℕ :=
  ([24783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part011 : ℚ :=
  (215938091 : ℚ) / 6751350000000000

def SurrogateDiagonalTailChunk001Sub001Block001Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24783
    = surrogateDiagTailX0RatChunk001Sub001Block001Part011

theorem surrogateDiagonalTailChunk001Sub001Block001Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part011] using hcert

def TailChunk001Sub001Block001Part012SupportExplicit : Finset ℕ :=
  ([24785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part012 : ℚ :=
  (1536371567875 : ℚ) / 386181988997190156288

def SurrogateDiagonalTailChunk001Sub001Block001Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24785
    = surrogateDiagTailX0RatChunk001Sub001Block001Part012

theorem surrogateDiagonalTailChunk001Sub001Block001Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part012] using hcert

def TailChunk001Sub001Block001Part013SupportExplicit : Finset ℕ :=
  ([24787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part013 : ℚ :=
  (31403997073 : ℚ) / 20356583916058675200

def SurrogateDiagonalTailChunk001Sub001Block001Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24787
    = surrogateDiagTailX0RatChunk001Sub001Block001Part013

theorem surrogateDiagonalTailChunk001Sub001Block001Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part013] using hcert

def TailChunk001Sub001Block001Part014SupportExplicit : Finset ℕ :=
  ([24789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part014 : ℚ :=
  (2133457615475 : ℚ) / 93208948447971898944

def SurrogateDiagonalTailChunk001Sub001Block001Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24789
    = surrogateDiagTailX0RatChunk001Sub001Block001Part014

theorem surrogateDiagonalTailChunk001Sub001Block001Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part014] using hcert

def TailChunk001Sub001Block001Part015SupportExplicit : Finset ℕ :=
  ([24790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part015 : ℚ :=
  (75585333125 : ℚ) / 1854641119151259648

def SurrogateDiagonalTailChunk001Sub001Block001Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24790
    = surrogateDiagTailX0RatChunk001Sub001Block001Part015

theorem surrogateDiagonalTailChunk001Sub001Block001Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part015] using hcert

def TailChunk001Sub001Block001Part016SupportExplicit : Finset ℕ :=
  ([24791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part016 : ℚ :=
  (457767232525 : ℚ) / 684295097019201865728

def SurrogateDiagonalTailChunk001Sub001Block001Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24791
    = surrogateDiagTailX0RatChunk001Sub001Block001Part016

theorem surrogateDiagonalTailChunk001Sub001Block001Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part016] using hcert

def TailChunk001Sub001Block001Part017SupportExplicit : Finset ℕ :=
  ([24793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block001Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24793
    = surrogateDiagTailX0RatChunk001Sub001Block001Part017

theorem surrogateDiagonalTailChunk001Sub001Block001Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part017] using hcert

def TailChunk001Sub001Block001Part018SupportExplicit : Finset ℕ :=
  ([24797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part018 : ℚ :=
  (331569083 : ℚ) / 2993306977655193600

def SurrogateDiagonalTailChunk001Sub001Block001Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24797
    = surrogateDiagTailX0RatChunk001Sub001Block001Part018

theorem surrogateDiagonalTailChunk001Sub001Block001Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part018] using hcert

def TailChunk001Sub001Block001Part019SupportExplicit : Finset ℕ :=
  ([24798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part019 : ℚ :=
  (1067187938075 : ℚ) / 5831202148903855104

def SurrogateDiagonalTailChunk001Sub001Block001Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24798
    = surrogateDiagTailX0RatChunk001Sub001Block001Part019

theorem surrogateDiagonalTailChunk001Sub001Block001Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part019] using hcert

def TailChunk001Sub001Block001Part020SupportExplicit : Finset ℕ :=
  ([24799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block001Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24799
    = surrogateDiagTailX0RatChunk001Sub001Block001Part020

theorem surrogateDiagonalTailChunk001Sub001Block001Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part020] using hcert

def TailChunk001Sub001Block001Part021SupportExplicit : Finset ℕ :=
  ([24801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part021 : ℚ :=
  (338787071 : ℚ) / 9307994474649600

def SurrogateDiagonalTailChunk001Sub001Block001Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24801
    = surrogateDiagTailX0RatChunk001Sub001Block001Part021

theorem surrogateDiagonalTailChunk001Sub001Block001Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part021] using hcert

def TailChunk001Sub001Block001Part022SupportExplicit : Finset ℕ :=
  ([24802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block001Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24802
    = surrogateDiagTailX0RatChunk001Sub001Block001Part022

theorem surrogateDiagonalTailChunk001Sub001Block001Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part022] using hcert

def TailChunk001Sub001Block001Part023SupportExplicit : Finset ℕ :=
  ([24803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part023 : ℚ :=
  (536120926675 : ℚ) / 740520158529575190528

def SurrogateDiagonalTailChunk001Sub001Block001Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24803
    = surrogateDiagTailX0RatChunk001Sub001Block001Part023

theorem surrogateDiagonalTailChunk001Sub001Block001Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part023] using hcert

def TailChunk001Sub001Block001Part024SupportExplicit : Finset ℕ :=
  ([24806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block001Part024 : ℚ :=
  (72636461875 : ℚ) / 54815535742290905088

def SurrogateDiagonalTailChunk001Sub001Block001Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24806
    = surrogateDiagTailX0RatChunk001Sub001Block001Part024

theorem surrogateDiagonalTailChunk001Sub001Block001Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block001Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block001Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block001Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block001Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block001Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block001Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block001HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block001Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block001Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block001Part000
    + surrogateDiagTailX0RatChunk001Sub001Block001Part001
    + surrogateDiagTailX0RatChunk001Sub001Block001Part002
    + surrogateDiagTailX0RatChunk001Sub001Block001Part003
    + surrogateDiagTailX0RatChunk001Sub001Block001Part004
    + surrogateDiagTailX0RatChunk001Sub001Block001Part005
    + surrogateDiagTailX0RatChunk001Sub001Block001Part006
    + surrogateDiagTailX0RatChunk001Sub001Block001Part007
    + surrogateDiagTailX0RatChunk001Sub001Block001Part008
    + surrogateDiagTailX0RatChunk001Sub001Block001Part009

def surrogateDiagonalTailChunk001Sub001Block001MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block001Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block001Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block001Part010
    + surrogateDiagTailX0RatChunk001Sub001Block001Part011
    + surrogateDiagTailX0RatChunk001Sub001Block001Part012
    + surrogateDiagTailX0RatChunk001Sub001Block001Part013
    + surrogateDiagTailX0RatChunk001Sub001Block001Part014
    + surrogateDiagTailX0RatChunk001Sub001Block001Part015
    + surrogateDiagTailX0RatChunk001Sub001Block001Part016
    + surrogateDiagTailX0RatChunk001Sub001Block001Part017
    + surrogateDiagTailX0RatChunk001Sub001Block001Part018
    + surrogateDiagTailX0RatChunk001Sub001Block001Part019

def surrogateDiagonalTailChunk001Sub001Block001TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block001Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block001Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block001Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block001Part020
    + surrogateDiagTailX0RatChunk001Sub001Block001Part021
    + surrogateDiagTailX0RatChunk001Sub001Block001Part022
    + surrogateDiagTailX0RatChunk001Sub001Block001Part023
    + surrogateDiagTailX0RatChunk001Sub001Block001Part024

def surrogateDiagonalTailChunk001Sub001Block001Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block001HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block001MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block001TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block001 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block001Part000
    + surrogateDiagTailX0RatChunk001Sub001Block001Part001
    + surrogateDiagTailX0RatChunk001Sub001Block001Part002
    + surrogateDiagTailX0RatChunk001Sub001Block001Part003
    + surrogateDiagTailX0RatChunk001Sub001Block001Part004
    + surrogateDiagTailX0RatChunk001Sub001Block001Part005
    + surrogateDiagTailX0RatChunk001Sub001Block001Part006
    + surrogateDiagTailX0RatChunk001Sub001Block001Part007
    + surrogateDiagTailX0RatChunk001Sub001Block001Part008
    + surrogateDiagTailX0RatChunk001Sub001Block001Part009
    + surrogateDiagTailX0RatChunk001Sub001Block001Part010
    + surrogateDiagTailX0RatChunk001Sub001Block001Part011
    + surrogateDiagTailX0RatChunk001Sub001Block001Part012
    + surrogateDiagTailX0RatChunk001Sub001Block001Part013
    + surrogateDiagTailX0RatChunk001Sub001Block001Part014
    + surrogateDiagTailX0RatChunk001Sub001Block001Part015
    + surrogateDiagTailX0RatChunk001Sub001Block001Part016
    + surrogateDiagTailX0RatChunk001Sub001Block001Part017
    + surrogateDiagTailX0RatChunk001Sub001Block001Part018
    + surrogateDiagTailX0RatChunk001Sub001Block001Part019
    + surrogateDiagTailX0RatChunk001Sub001Block001Part020
    + surrogateDiagTailX0RatChunk001Sub001Block001Part021
    + surrogateDiagTailX0RatChunk001Sub001Block001Part022
    + surrogateDiagTailX0RatChunk001Sub001Block001Part023
    + surrogateDiagTailX0RatChunk001Sub001Block001Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block001_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block001Head + surrogateDiagTailX0RatChunk001Sub001Block001Mid + surrogateDiagTailX0RatChunk001Sub001Block001Tail =
      surrogateDiagTailX0RatChunk001Sub001Block001 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block001Head surrogateDiagTailX0RatChunk001Sub001Block001Mid surrogateDiagTailX0RatChunk001Sub001Block001Tail surrogateDiagTailX0RatChunk001Sub001Block001
  ring

def SurrogateDiagonalTailChunk001Sub001Block001HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block001HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block001Head

def SurrogateDiagonalTailChunk001Sub001Block001MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block001MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block001Mid

def SurrogateDiagonalTailChunk001Sub001Block001TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block001TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block001Tail

theorem surrogateDiagonalTailChunk001Sub001Block001_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block001HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block001MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block001TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block001Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block001 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block001HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block001MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block001TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block001Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block001_eq_head_add_mid_add_tail

/-- Block 002 covers tail-support indices [15050,15075) and q from 24807 to 24846. -/

def TailChunk001Sub001Block002Part000SupportExplicit : Finset ℕ :=
  ([24807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part000 : ℚ :=
  (33383702975 : ℚ) / 1460625047005761936

def SurrogateDiagonalTailChunk001Sub001Block002Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24807
    = surrogateDiagTailX0RatChunk001Sub001Block002Part000

theorem surrogateDiagonalTailChunk001Sub001Block002Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part000] using hcert

def TailChunk001Sub001Block002Part001SupportExplicit : Finset ℕ :=
  ([24809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block002Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24809
    = surrogateDiagTailX0RatChunk001Sub001Block002Part001

theorem surrogateDiagonalTailChunk001Sub001Block002Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part001] using hcert

def TailChunk001Sub001Block002Part002SupportExplicit : Finset ℕ :=
  ([24810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part002 : ℚ :=
  (224122231175 : ℚ) / 595959859563565056

def SurrogateDiagonalTailChunk001Sub001Block002Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24810
    = surrogateDiagTailX0RatChunk001Sub001Block002Part002

theorem surrogateDiagonalTailChunk001Sub001Block002Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part002] using hcert

def TailChunk001Sub001Block002Part003SupportExplicit : Finset ℕ :=
  ([24811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part003 : ℚ :=
  (7389885425 : ℚ) / 31721242500293197824

def SurrogateDiagonalTailChunk001Sub001Block002Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24811
    = surrogateDiagTailX0RatChunk001Sub001Block002Part003

theorem surrogateDiagonalTailChunk001Sub001Block002Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part003] using hcert

def TailChunk001Sub001Block002Part004SupportExplicit : Finset ℕ :=
  ([24814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part004 : ℚ :=
  (72625468225 : ℚ) / 15811970940019316736

def SurrogateDiagonalTailChunk001Sub001Block002Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24814
    = surrogateDiagTailX0RatChunk001Sub001Block002Part004

theorem surrogateDiagonalTailChunk001Sub001Block002Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part004] using hcert

def TailChunk001Sub001Block002Part005SupportExplicit : Finset ℕ :=
  ([24815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part005 : ℚ :=
  (448363949275 : ℚ) / 52112854825110208512

def SurrogateDiagonalTailChunk001Sub001Block002Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24815
    = surrogateDiagTailX0RatChunk001Sub001Block002Part005

theorem surrogateDiagonalTailChunk001Sub001Block002Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part005] using hcert

def TailChunk001Sub001Block002Part006SupportExplicit : Finset ℕ :=
  ([24817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part006 : ℚ :=
  (337877750675 : ℚ) / 183052945366667329536

def SurrogateDiagonalTailChunk001Sub001Block002Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24817
    = surrogateDiagTailX0RatChunk001Sub001Block002Part006

theorem surrogateDiagonalTailChunk001Sub001Block002Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part006] using hcert

def TailChunk001Sub001Block002Part007SupportExplicit : Finset ℕ :=
  ([24818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block002Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24818
    = surrogateDiagTailX0RatChunk001Sub001Block002Part007

theorem surrogateDiagonalTailChunk001Sub001Block002Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part007] using hcert

def TailChunk001Sub001Block002Part008SupportExplicit : Finset ℕ :=
  ([24819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part008 : ℚ :=
  (1069312245175 : ℚ) / 46830517094255296512

def SurrogateDiagonalTailChunk001Sub001Block002Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24819
    = surrogateDiagTailX0RatChunk001Sub001Block002Part008

theorem surrogateDiagonalTailChunk001Sub001Block002Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part008] using hcert

def TailChunk001Sub001Block002Part009SupportExplicit : Finset ℕ :=
  ([24821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block002Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24821
    = surrogateDiagTailX0RatChunk001Sub001Block002Part009

theorem surrogateDiagonalTailChunk001Sub001Block002Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part009] using hcert

def TailChunk001Sub001Block002Part010SupportExplicit : Finset ℕ :=
  ([24823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part010 : ℚ :=
  (79132351 : ℚ) / 665179328367820800

def SurrogateDiagonalTailChunk001Sub001Block002Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24823
    = surrogateDiagTailX0RatChunk001Sub001Block002Part010

theorem surrogateDiagonalTailChunk001Sub001Block002Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part010] using hcert

def TailChunk001Sub001Block002Part011SupportExplicit : Finset ℕ :=
  ([24826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block002Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24826
    = surrogateDiagTailX0RatChunk001Sub001Block002Part011

theorem surrogateDiagonalTailChunk001Sub001Block002Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part011] using hcert

def TailChunk001Sub001Block002Part012SupportExplicit : Finset ℕ :=
  ([24827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part012 : ℚ :=
  (6936694313 : ℚ) / 4354435384934400000

def SurrogateDiagonalTailChunk001Sub001Block002Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24827
    = surrogateDiagTailX0RatChunk001Sub001Block002Part012

theorem surrogateDiagonalTailChunk001Sub001Block002Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part012] using hcert

def TailChunk001Sub001Block002Part013SupportExplicit : Finset ℕ :=
  ([24829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part013 : ℚ :=
  (786662505875 : ℚ) / 256186824073349511744

def SurrogateDiagonalTailChunk001Sub001Block002Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24829
    = surrogateDiagTailX0RatChunk001Sub001Block002Part013

theorem surrogateDiagonalTailChunk001Sub001Block002Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part013] using hcert

def TailChunk001Sub001Block002Part014SupportExplicit : Finset ℕ :=
  ([24830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part014 : ℚ :=
  (17761048277 : ℚ) / 345968220576153600

def SurrogateDiagonalTailChunk001Sub001Block002Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24830
    = surrogateDiagTailX0RatChunk001Sub001Block002Part014

theorem surrogateDiagonalTailChunk001Sub001Block002Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part014] using hcert

def TailChunk001Sub001Block002Part015SupportExplicit : Finset ℕ :=
  ([24833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part015 : ℚ :=
  (431775903925 : ℚ) / 763641614313636306048

def SurrogateDiagonalTailChunk001Sub001Block002Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24833
    = surrogateDiagTailX0RatChunk001Sub001Block002Part015

theorem surrogateDiagonalTailChunk001Sub001Block002Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part015] using hcert

def TailChunk001Sub001Block002Part016SupportExplicit : Finset ℕ :=
  ([24834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part016 : ℚ :=
  (1070288567525 : ℚ) / 5865145511062023744

def SurrogateDiagonalTailChunk001Sub001Block002Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24834
    = surrogateDiagTailX0RatChunk001Sub001Block002Part016

theorem surrogateDiagonalTailChunk001Sub001Block002Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part016] using hcert

def TailChunk001Sub001Block002Part017SupportExplicit : Finset ℕ :=
  ([24835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part017 : ℚ :=
  (514190938875 : ℚ) / 129769439952935950336

def SurrogateDiagonalTailChunk001Sub001Block002Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24835
    = surrogateDiagTailX0RatChunk001Sub001Block002Part017

theorem surrogateDiagonalTailChunk001Sub001Block002Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part017] using hcert

def TailChunk001Sub001Block002Part018SupportExplicit : Finset ℕ :=
  ([24837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part018 : ℚ :=
  (290533068475 : ℚ) / 146275586870039543808

def SurrogateDiagonalTailChunk001Sub001Block002Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24837
    = surrogateDiagTailX0RatChunk001Sub001Block002Part018

theorem surrogateDiagonalTailChunk001Sub001Block002Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part018] using hcert

def TailChunk001Sub001Block002Part019SupportExplicit : Finset ℕ :=
  ([24838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part019 : ℚ :=
  (66738137 : ℚ) / 6747020148602880

def SurrogateDiagonalTailChunk001Sub001Block002Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24838
    = surrogateDiagTailX0RatChunk001Sub001Block002Part019

theorem surrogateDiagonalTailChunk001Sub001Block002Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part019] using hcert

def TailChunk001Sub001Block002Part020SupportExplicit : Finset ℕ :=
  ([24839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part020 : ℚ :=
  (1501870411 : ℚ) / 8805134509070860800

def SurrogateDiagonalTailChunk001Sub001Block002Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24839
    = surrogateDiagTailX0RatChunk001Sub001Block002Part020

theorem surrogateDiagonalTailChunk001Sub001Block002Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part020] using hcert

def TailChunk001Sub001Block002Part021SupportExplicit : Finset ℕ :=
  ([24841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block002Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24841
    = surrogateDiagTailX0RatChunk001Sub001Block002Part021

theorem surrogateDiagonalTailChunk001Sub001Block002Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part021] using hcert

def TailChunk001Sub001Block002Part022SupportExplicit : Finset ℕ :=
  ([24842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block002Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24842
    = surrogateDiagTailX0RatChunk001Sub001Block002Part022

theorem surrogateDiagonalTailChunk001Sub001Block002Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part022] using hcert

def TailChunk001Sub001Block002Part023SupportExplicit : Finset ℕ :=
  ([24845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part023 : ℚ :=
  (1543814566375 : ℚ) / 389935856817736777728

def SurrogateDiagonalTailChunk001Sub001Block002Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24845
    = surrogateDiagTailX0RatChunk001Sub001Block002Part023

theorem surrogateDiagonalTailChunk001Sub001Block002Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part023] using hcert

def TailChunk001Sub001Block002Part024SupportExplicit : Finset ℕ :=
  ([24846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block002Part024 : ℚ :=
  (43414401907 : ℚ) / 409681920000000000

def SurrogateDiagonalTailChunk001Sub001Block002Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24846
    = surrogateDiagTailX0RatChunk001Sub001Block002Part024

theorem surrogateDiagonalTailChunk001Sub001Block002Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block002Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block002Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block002Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block002Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block002Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block002HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block002Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block002Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block002Part000
    + surrogateDiagTailX0RatChunk001Sub001Block002Part001
    + surrogateDiagTailX0RatChunk001Sub001Block002Part002
    + surrogateDiagTailX0RatChunk001Sub001Block002Part003
    + surrogateDiagTailX0RatChunk001Sub001Block002Part004
    + surrogateDiagTailX0RatChunk001Sub001Block002Part005
    + surrogateDiagTailX0RatChunk001Sub001Block002Part006
    + surrogateDiagTailX0RatChunk001Sub001Block002Part007
    + surrogateDiagTailX0RatChunk001Sub001Block002Part008
    + surrogateDiagTailX0RatChunk001Sub001Block002Part009

def surrogateDiagonalTailChunk001Sub001Block002MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block002Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block002Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block002Part010
    + surrogateDiagTailX0RatChunk001Sub001Block002Part011
    + surrogateDiagTailX0RatChunk001Sub001Block002Part012
    + surrogateDiagTailX0RatChunk001Sub001Block002Part013
    + surrogateDiagTailX0RatChunk001Sub001Block002Part014
    + surrogateDiagTailX0RatChunk001Sub001Block002Part015
    + surrogateDiagTailX0RatChunk001Sub001Block002Part016
    + surrogateDiagTailX0RatChunk001Sub001Block002Part017
    + surrogateDiagTailX0RatChunk001Sub001Block002Part018
    + surrogateDiagTailX0RatChunk001Sub001Block002Part019

def surrogateDiagonalTailChunk001Sub001Block002TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block002Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block002Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block002Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block002Part020
    + surrogateDiagTailX0RatChunk001Sub001Block002Part021
    + surrogateDiagTailX0RatChunk001Sub001Block002Part022
    + surrogateDiagTailX0RatChunk001Sub001Block002Part023
    + surrogateDiagTailX0RatChunk001Sub001Block002Part024

def surrogateDiagonalTailChunk001Sub001Block002Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block002HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block002MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block002TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block002 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block002Part000
    + surrogateDiagTailX0RatChunk001Sub001Block002Part001
    + surrogateDiagTailX0RatChunk001Sub001Block002Part002
    + surrogateDiagTailX0RatChunk001Sub001Block002Part003
    + surrogateDiagTailX0RatChunk001Sub001Block002Part004
    + surrogateDiagTailX0RatChunk001Sub001Block002Part005
    + surrogateDiagTailX0RatChunk001Sub001Block002Part006
    + surrogateDiagTailX0RatChunk001Sub001Block002Part007
    + surrogateDiagTailX0RatChunk001Sub001Block002Part008
    + surrogateDiagTailX0RatChunk001Sub001Block002Part009
    + surrogateDiagTailX0RatChunk001Sub001Block002Part010
    + surrogateDiagTailX0RatChunk001Sub001Block002Part011
    + surrogateDiagTailX0RatChunk001Sub001Block002Part012
    + surrogateDiagTailX0RatChunk001Sub001Block002Part013
    + surrogateDiagTailX0RatChunk001Sub001Block002Part014
    + surrogateDiagTailX0RatChunk001Sub001Block002Part015
    + surrogateDiagTailX0RatChunk001Sub001Block002Part016
    + surrogateDiagTailX0RatChunk001Sub001Block002Part017
    + surrogateDiagTailX0RatChunk001Sub001Block002Part018
    + surrogateDiagTailX0RatChunk001Sub001Block002Part019
    + surrogateDiagTailX0RatChunk001Sub001Block002Part020
    + surrogateDiagTailX0RatChunk001Sub001Block002Part021
    + surrogateDiagTailX0RatChunk001Sub001Block002Part022
    + surrogateDiagTailX0RatChunk001Sub001Block002Part023
    + surrogateDiagTailX0RatChunk001Sub001Block002Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block002_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block002Head + surrogateDiagTailX0RatChunk001Sub001Block002Mid + surrogateDiagTailX0RatChunk001Sub001Block002Tail =
      surrogateDiagTailX0RatChunk001Sub001Block002 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block002Head surrogateDiagTailX0RatChunk001Sub001Block002Mid surrogateDiagTailX0RatChunk001Sub001Block002Tail surrogateDiagTailX0RatChunk001Sub001Block002
  ring

def SurrogateDiagonalTailChunk001Sub001Block002HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block002HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block002Head

def SurrogateDiagonalTailChunk001Sub001Block002MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block002MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block002Mid

def SurrogateDiagonalTailChunk001Sub001Block002TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block002TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block002Tail

theorem surrogateDiagonalTailChunk001Sub001Block002_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block002HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block002MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block002TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block002Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block002 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block002HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block002MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block002TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block002Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block002_eq_head_add_mid_add_tail

/-- Block 003 covers tail-support indices [15075,15100) and q from 24847 to 24890. -/

def TailChunk001Sub001Block003Part000SupportExplicit : Finset ℕ :=
  ([24847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block003Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24847
    = surrogateDiagTailX0RatChunk001Sub001Block003Part000

theorem surrogateDiagonalTailChunk001Sub001Block003Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part000] using hcert

def TailChunk001Sub001Block003Part001SupportExplicit : Finset ℕ :=
  ([24851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block003Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24851
    = surrogateDiagTailX0RatChunk001Sub001Block003Part001

theorem surrogateDiagonalTailChunk001Sub001Block003Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part001] using hcert

def TailChunk001Sub001Block003Part002SupportExplicit : Finset ℕ :=
  ([24853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part002 : ℚ :=
  (283233305575 : ℚ) / 825190164530201100288

def SurrogateDiagonalTailChunk001Sub001Block003Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24853
    = surrogateDiagTailX0RatChunk001Sub001Block003Part002

theorem surrogateDiagonalTailChunk001Sub001Block003Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part002] using hcert

def TailChunk001Sub001Block003Part003SupportExplicit : Finset ℕ :=
  ([24855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part003 : ℚ :=
  (257770480975 : ℚ) / 19256091694703050752

def SurrogateDiagonalTailChunk001Sub001Block003Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24855
    = surrogateDiagTailX0RatChunk001Sub001Block003Part003

theorem surrogateDiagonalTailChunk001Sub001Block003Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part003] using hcert

def TailChunk001Sub001Block003Part004SupportExplicit : Finset ℕ :=
  ([24857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part004 : ℚ :=
  (129812739625 : ℚ) / 34584191301333712896

def SurrogateDiagonalTailChunk001Sub001Block003Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24857
    = surrogateDiagTailX0RatChunk001Sub001Block003Part004

theorem surrogateDiagonalTailChunk001Sub001Block003Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part004] using hcert

def TailChunk001Sub001Block003Part005SupportExplicit : Finset ℕ :=
  ([24859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block003Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24859
    = surrogateDiagTailX0RatChunk001Sub001Block003Part005

theorem surrogateDiagonalTailChunk001Sub001Block003Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part005] using hcert

def TailChunk001Sub001Block003Part006SupportExplicit : Finset ℕ :=
  ([24861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part006 : ℚ :=
  (41675 : ℚ) / 12570381204206976

def SurrogateDiagonalTailChunk001Sub001Block003Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24861
    = surrogateDiagTailX0RatChunk001Sub001Block003Part006

theorem surrogateDiagonalTailChunk001Sub001Block003Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part006] using hcert

def TailChunk001Sub001Block003Part007SupportExplicit : Finset ℕ :=
  ([24862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part007 : ℚ :=
  (5561896759 : ℚ) / 2074014720000000000

def SurrogateDiagonalTailChunk001Sub001Block003Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24862
    = surrogateDiagTailX0RatChunk001Sub001Block003Part007

theorem surrogateDiagonalTailChunk001Sub001Block003Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part007] using hcert

def TailChunk001Sub001Block003Part008SupportExplicit : Finset ℕ :=
  ([24865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part008 : ℚ :=
  (515433188625 : ℚ) / 130397735468153798656

def SurrogateDiagonalTailChunk001Sub001Block003Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24865
    = surrogateDiagTailX0RatChunk001Sub001Block003Part008

theorem surrogateDiagonalTailChunk001Sub001Block003Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part008] using hcert

def TailChunk001Sub001Block003Part009SupportExplicit : Finset ℕ :=
  ([24866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block003Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24866
    = surrogateDiagTailX0RatChunk001Sub001Block003Part009

theorem surrogateDiagonalTailChunk001Sub001Block003Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part009] using hcert

def TailChunk001Sub001Block003Part010SupportExplicit : Finset ℕ :=
  ([24869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part010 : ℚ :=
  (460630158025 : ℚ) / 692952386557664821248

def SurrogateDiagonalTailChunk001Sub001Block003Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24869
    = surrogateDiagTailX0RatChunk001Sub001Block003Part010

theorem surrogateDiagonalTailChunk001Sub001Block003Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part010] using hcert

def TailChunk001Sub001Block003Part011SupportExplicit : Finset ℕ :=
  ([24870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part011 : ℚ :=
  (1159439593975 : ℚ) / 4814022923675762688

def SurrogateDiagonalTailChunk001Sub001Block003Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24870
    = surrogateDiagTailX0RatChunk001Sub001Block003Part011

theorem surrogateDiagonalTailChunk001Sub001Block003Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part011] using hcert

def TailChunk001Sub001Block003Part012SupportExplicit : Finset ℕ :=
  ([24871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part012 : ℚ :=
  (85251300991 : ℚ) / 8917883668345651200

def SurrogateDiagonalTailChunk001Sub001Block003Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24871
    = surrogateDiagTailX0RatChunk001Sub001Block003Part012

theorem surrogateDiagonalTailChunk001Sub001Block003Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part012] using hcert

def TailChunk001Sub001Block003Part013SupportExplicit : Finset ℕ :=
  ([24873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part013 : ℚ :=
  (5001 : ℚ) / 1511360614659200

def SurrogateDiagonalTailChunk001Sub001Block003Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24873
    = surrogateDiagTailX0RatChunk001Sub001Block003Part013

theorem surrogateDiagonalTailChunk001Sub001Block003Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part013] using hcert

def TailChunk001Sub001Block003Part014SupportExplicit : Finset ℕ :=
  ([24874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block003Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24874
    = surrogateDiagTailX0RatChunk001Sub001Block003Part014

theorem surrogateDiagonalTailChunk001Sub001Block003Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part014] using hcert

def TailChunk001Sub001Block003Part015SupportExplicit : Finset ℕ :=
  ([24877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block003Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24877
    = surrogateDiagTailX0RatChunk001Sub001Block003Part015

theorem surrogateDiagonalTailChunk001Sub001Block003Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part015] using hcert

def TailChunk001Sub001Block003Part016SupportExplicit : Finset ℕ :=
  ([24878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part016 : ℚ :=
  (10982334475 : ℚ) / 597048960253427712

def SurrogateDiagonalTailChunk001Sub001Block003Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24878
    = surrogateDiagTailX0RatChunk001Sub001Block003Part016

theorem surrogateDiagonalTailChunk001Sub001Block003Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part016] using hcert

def TailChunk001Sub001Block003Part017SupportExplicit : Finset ℕ :=
  ([24879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part017 : ℚ :=
  (41675 : ℚ) / 12606830274041856

def SurrogateDiagonalTailChunk001Sub001Block003Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24879
    = surrogateDiagTailX0RatChunk001Sub001Block003Part017

theorem surrogateDiagonalTailChunk001Sub001Block003Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part017] using hcert

def TailChunk001Sub001Block003Part018SupportExplicit : Finset ℕ :=
  ([24881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part018 : ℚ :=
  (1536092275 : ℚ) / 14224704057518726322

def SurrogateDiagonalTailChunk001Sub001Block003Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24881
    = surrogateDiagTailX0RatChunk001Sub001Block003Part018

theorem surrogateDiagonalTailChunk001Sub001Block003Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part018] using hcert

def TailChunk001Sub001Block003Part019SupportExplicit : Finset ℕ :=
  ([24882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part019 : ℚ :=
  (11107489429 : ℚ) / 50992223669452800

def SurrogateDiagonalTailChunk001Sub001Block003Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24882
    = surrogateDiagTailX0RatChunk001Sub001Block003Part019

theorem surrogateDiagonalTailChunk001Sub001Block003Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part019] using hcert

def TailChunk001Sub001Block003Part020SupportExplicit : Finset ℕ :=
  ([24883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part020 : ℚ :=
  (32172709725 : ℚ) / 303658063361876432896

def SurrogateDiagonalTailChunk001Sub001Block003Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24883
    = surrogateDiagTailX0RatChunk001Sub001Block003Part020

theorem surrogateDiagonalTailChunk001Sub001Block003Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part020] using hcert

def TailChunk001Sub001Block003Part021SupportExplicit : Finset ℕ :=
  ([24886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part021 : ℚ :=
  (6825069661 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk001Sub001Block003Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24886
    = surrogateDiagTailX0RatChunk001Sub001Block003Part021

theorem surrogateDiagonalTailChunk001Sub001Block003Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part021] using hcert

def TailChunk001Sub001Block003Part022SupportExplicit : Finset ℕ :=
  ([24887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part022 : ℚ :=
  (522311417 : ℚ) / 2302109903393095680

def SurrogateDiagonalTailChunk001Sub001Block003Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24887
    = surrogateDiagTailX0RatChunk001Sub001Block003Part022

theorem surrogateDiagonalTailChunk001Sub001Block003Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part022] using hcert

def TailChunk001Sub001Block003Part023SupportExplicit : Finset ℕ :=
  ([24889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block003Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24889
    = surrogateDiagTailX0RatChunk001Sub001Block003Part023

theorem surrogateDiagonalTailChunk001Sub001Block003Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part023] using hcert

def TailChunk001Sub001Block003Part024SupportExplicit : Finset ℕ :=
  ([24890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block003Part024 : ℚ :=
  (570369197 : ℚ) / 12794961834270720

def SurrogateDiagonalTailChunk001Sub001Block003Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24890
    = surrogateDiagTailX0RatChunk001Sub001Block003Part024

theorem surrogateDiagonalTailChunk001Sub001Block003Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block003Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block003Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block003Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block003Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block003Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block003HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block003Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block003Part000
    + surrogateDiagTailX0RatChunk001Sub001Block003Part001
    + surrogateDiagTailX0RatChunk001Sub001Block003Part002
    + surrogateDiagTailX0RatChunk001Sub001Block003Part003
    + surrogateDiagTailX0RatChunk001Sub001Block003Part004
    + surrogateDiagTailX0RatChunk001Sub001Block003Part005
    + surrogateDiagTailX0RatChunk001Sub001Block003Part006
    + surrogateDiagTailX0RatChunk001Sub001Block003Part007
    + surrogateDiagTailX0RatChunk001Sub001Block003Part008
    + surrogateDiagTailX0RatChunk001Sub001Block003Part009

def surrogateDiagonalTailChunk001Sub001Block003MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block003Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block003Part010
    + surrogateDiagTailX0RatChunk001Sub001Block003Part011
    + surrogateDiagTailX0RatChunk001Sub001Block003Part012
    + surrogateDiagTailX0RatChunk001Sub001Block003Part013
    + surrogateDiagTailX0RatChunk001Sub001Block003Part014
    + surrogateDiagTailX0RatChunk001Sub001Block003Part015
    + surrogateDiagTailX0RatChunk001Sub001Block003Part016
    + surrogateDiagTailX0RatChunk001Sub001Block003Part017
    + surrogateDiagTailX0RatChunk001Sub001Block003Part018
    + surrogateDiagTailX0RatChunk001Sub001Block003Part019

def surrogateDiagonalTailChunk001Sub001Block003TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block003Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block003Part020
    + surrogateDiagTailX0RatChunk001Sub001Block003Part021
    + surrogateDiagTailX0RatChunk001Sub001Block003Part022
    + surrogateDiagTailX0RatChunk001Sub001Block003Part023
    + surrogateDiagTailX0RatChunk001Sub001Block003Part024

def surrogateDiagonalTailChunk001Sub001Block003Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block003HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block003MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block003TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block003 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block003Part000
    + surrogateDiagTailX0RatChunk001Sub001Block003Part001
    + surrogateDiagTailX0RatChunk001Sub001Block003Part002
    + surrogateDiagTailX0RatChunk001Sub001Block003Part003
    + surrogateDiagTailX0RatChunk001Sub001Block003Part004
    + surrogateDiagTailX0RatChunk001Sub001Block003Part005
    + surrogateDiagTailX0RatChunk001Sub001Block003Part006
    + surrogateDiagTailX0RatChunk001Sub001Block003Part007
    + surrogateDiagTailX0RatChunk001Sub001Block003Part008
    + surrogateDiagTailX0RatChunk001Sub001Block003Part009
    + surrogateDiagTailX0RatChunk001Sub001Block003Part010
    + surrogateDiagTailX0RatChunk001Sub001Block003Part011
    + surrogateDiagTailX0RatChunk001Sub001Block003Part012
    + surrogateDiagTailX0RatChunk001Sub001Block003Part013
    + surrogateDiagTailX0RatChunk001Sub001Block003Part014
    + surrogateDiagTailX0RatChunk001Sub001Block003Part015
    + surrogateDiagTailX0RatChunk001Sub001Block003Part016
    + surrogateDiagTailX0RatChunk001Sub001Block003Part017
    + surrogateDiagTailX0RatChunk001Sub001Block003Part018
    + surrogateDiagTailX0RatChunk001Sub001Block003Part019
    + surrogateDiagTailX0RatChunk001Sub001Block003Part020
    + surrogateDiagTailX0RatChunk001Sub001Block003Part021
    + surrogateDiagTailX0RatChunk001Sub001Block003Part022
    + surrogateDiagTailX0RatChunk001Sub001Block003Part023
    + surrogateDiagTailX0RatChunk001Sub001Block003Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block003_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block003Head + surrogateDiagTailX0RatChunk001Sub001Block003Mid + surrogateDiagTailX0RatChunk001Sub001Block003Tail =
      surrogateDiagTailX0RatChunk001Sub001Block003 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block003Head surrogateDiagTailX0RatChunk001Sub001Block003Mid surrogateDiagTailX0RatChunk001Sub001Block003Tail surrogateDiagTailX0RatChunk001Sub001Block003
  ring

def SurrogateDiagonalTailChunk001Sub001Block003HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block003HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block003Head

def SurrogateDiagonalTailChunk001Sub001Block003MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block003MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block003Mid

def SurrogateDiagonalTailChunk001Sub001Block003TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block003TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block003Tail

theorem surrogateDiagonalTailChunk001Sub001Block003_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block003HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block003MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block003TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block003Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block003 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block003HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block003MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block003TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block003Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block003_eq_head_add_mid_add_tail

/-- Block 004 covers tail-support indices [15100,15125) and q from 24891 to 24933. -/

def TailChunk001Sub001Block004Part000SupportExplicit : Finset ℕ :=
  ([24891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part000 : ℚ :=
  (125025 : ℚ) / 37893520954523648

def SurrogateDiagonalTailChunk001Sub001Block004Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24891
    = surrogateDiagTailX0RatChunk001Sub001Block004Part000

theorem surrogateDiagonalTailChunk001Sub001Block004Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part000] using hcert

def TailChunk001Sub001Block004Part001SupportExplicit : Finset ℕ :=
  ([24893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part001 : ℚ :=
  (23557522103 : ℚ) / 10886088462336000000

def SurrogateDiagonalTailChunk001Sub001Block004Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24893
    = surrogateDiagTailX0RatChunk001Sub001Block004Part001

theorem surrogateDiagonalTailChunk001Sub001Block004Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part001] using hcert

def TailChunk001Sub001Block004Part002SupportExplicit : Finset ℕ :=
  ([24895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part002 : ℚ :=
  (1711528920475 : ℚ) / 282647572584721809408

def SurrogateDiagonalTailChunk001Sub001Block004Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24895
    = surrogateDiagTailX0RatChunk001Sub001Block004Part002

theorem surrogateDiagonalTailChunk001Sub001Block004Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part002] using hcert

def TailChunk001Sub001Block004Part003SupportExplicit : Finset ℕ :=
  ([24897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part003 : ℚ :=
  (148546925425 : ℚ) / 169179960001563721728

def SurrogateDiagonalTailChunk001Sub001Block004Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24897
    = surrogateDiagTailX0RatChunk001Sub001Block004Part003

theorem surrogateDiagonalTailChunk001Sub001Block004Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part003] using hcert

def TailChunk001Sub001Block004Part004SupportExplicit : Finset ℕ :=
  ([24898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part004 : ℚ :=
  (240061541 : ℚ) / 157234544804836800

def SurrogateDiagonalTailChunk001Sub001Block004Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24898
    = surrogateDiagTailX0RatChunk001Sub001Block004Part004

theorem surrogateDiagonalTailChunk001Sub001Block004Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part004] using hcert

def TailChunk001Sub001Block004Part005SupportExplicit : Finset ℕ :=
  ([24899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part005 : ℚ :=
  (792195927625 : ℚ) / 518177879698496145408

def SurrogateDiagonalTailChunk001Sub001Block004Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24899
    = surrogateDiagTailX0RatChunk001Sub001Block004Part005

theorem surrogateDiagonalTailChunk001Sub001Block004Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part005] using hcert

def TailChunk001Sub001Block004Part006SupportExplicit : Finset ℕ :=
  ([24901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part006 : ℚ :=
  (236716495075 : ℚ) / 856473547507916341248

def SurrogateDiagonalTailChunk001Sub001Block004Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24901
    = surrogateDiagTailX0RatChunk001Sub001Block004Part006

theorem surrogateDiagonalTailChunk001Sub001Block004Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part006] using hcert

def TailChunk001Sub001Block004Part007SupportExplicit : Finset ℕ :=
  ([24902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block004Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24902
    = surrogateDiagTailX0RatChunk001Sub001Block004Part007

theorem surrogateDiagonalTailChunk001Sub001Block004Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part007] using hcert

def TailChunk001Sub001Block004Part008SupportExplicit : Finset ℕ :=
  ([24905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part008 : ℚ :=
  (427353370525 : ℚ) / 76246193913873825792

def SurrogateDiagonalTailChunk001Sub001Block004Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24905
    = surrogateDiagTailX0RatChunk001Sub001Block004Part008

theorem surrogateDiagonalTailChunk001Sub001Block004Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part008] using hcert

def TailChunk001Sub001Block004Part009SupportExplicit : Finset ℕ :=
  ([24906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part009 : ℚ :=
  (538573665275 : ℚ) / 3184261121351614464

def SurrogateDiagonalTailChunk001Sub001Block004Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24906
    = surrogateDiagTailX0RatChunk001Sub001Block004Part009

theorem surrogateDiagonalTailChunk001Sub001Block004Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part009] using hcert

def TailChunk001Sub001Block004Part010SupportExplicit : Finset ℕ :=
  ([24907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block004Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24907
    = surrogateDiagTailX0RatChunk001Sub001Block004Part010

theorem surrogateDiagonalTailChunk001Sub001Block004Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part010] using hcert

def TailChunk001Sub001Block004Part011SupportExplicit : Finset ℕ :=
  ([24910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part011 : ℚ :=
  (417783509375 : ℚ) / 10478075653338169344

def SurrogateDiagonalTailChunk001Sub001Block004Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24910
    = surrogateDiagTailX0RatChunk001Sub001Block004Part011

theorem surrogateDiagonalTailChunk001Sub001Block004Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part011] using hcert

def TailChunk001Sub001Block004Part012SupportExplicit : Finset ℕ :=
  ([24911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part012 : ℚ :=
  (59649828025 : ℚ) / 208232323126645289472

def SurrogateDiagonalTailChunk001Sub001Block004Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24911
    = surrogateDiagTailX0RatChunk001Sub001Block004Part012

theorem surrogateDiagonalTailChunk001Sub001Block004Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part012] using hcert

def TailChunk001Sub001Block004Part013SupportExplicit : Finset ℕ :=
  ([24913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part013 : ℚ :=
  (793085177725 : ℚ) / 519344618059748193408

def SurrogateDiagonalTailChunk001Sub001Block004Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24913
    = surrogateDiagTailX0RatChunk001Sub001Block004Part013

theorem surrogateDiagonalTailChunk001Sub001Block004Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part013] using hcert

def TailChunk001Sub001Block004Part014SupportExplicit : Finset ℕ :=
  ([24914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block004Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24914
    = surrogateDiagTailX0RatChunk001Sub001Block004Part014

theorem surrogateDiagonalTailChunk001Sub001Block004Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part014] using hcert

def TailChunk001Sub001Block004Part015SupportExplicit : Finset ℕ :=
  ([24915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part015 : ℚ :=
  (3860399 : ℚ) / 165921177600000

def SurrogateDiagonalTailChunk001Sub001Block004Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24915
    = surrogateDiagTailX0RatChunk001Sub001Block004Part015

theorem surrogateDiagonalTailChunk001Sub001Block004Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part015] using hcert

def TailChunk001Sub001Block004Part016SupportExplicit : Finset ℕ :=
  ([24917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block004Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24917
    = surrogateDiagTailX0RatChunk001Sub001Block004Part016

theorem surrogateDiagonalTailChunk001Sub001Block004Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part016] using hcert

def TailChunk001Sub001Block004Part017SupportExplicit : Finset ℕ :=
  ([24918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part017 : ℚ :=
  (269517270925 : ℚ) / 2972461440641605632

def SurrogateDiagonalTailChunk001Sub001Block004Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24918
    = surrogateDiagTailX0RatChunk001Sub001Block004Part017

theorem surrogateDiagonalTailChunk001Sub001Block004Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part017] using hcert

def TailChunk001Sub001Block004Part018SupportExplicit : Finset ℕ :=
  ([24919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block004Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24919
    = surrogateDiagTailX0RatChunk001Sub001Block004Part018

theorem surrogateDiagonalTailChunk001Sub001Block004Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part018] using hcert

def TailChunk001Sub001Block004Part019SupportExplicit : Finset ℕ :=
  ([24922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part019 : ℚ :=
  (11429530475 : ℚ) / 2613837646031486976

def SurrogateDiagonalTailChunk001Sub001Block004Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24922
    = surrogateDiagTailX0RatChunk001Sub001Block004Part019

theorem surrogateDiagonalTailChunk001Sub001Block004Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part019] using hcert

def TailChunk001Sub001Block004Part020SupportExplicit : Finset ℕ :=
  ([24923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block004Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24923
    = surrogateDiagTailX0RatChunk001Sub001Block004Part020

theorem surrogateDiagonalTailChunk001Sub001Block004Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part020] using hcert

def TailChunk001Sub001Block004Part021SupportExplicit : Finset ℕ :=
  ([24927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part021 : ℚ :=
  (619240402225 : ℚ) / 102586591221678655488

def SurrogateDiagonalTailChunk001Sub001Block004Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24927
    = surrogateDiagTailX0RatChunk001Sub001Block004Part021

theorem surrogateDiagonalTailChunk001Sub001Block004Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part021] using hcert

def TailChunk001Sub001Block004Part022SupportExplicit : Finset ℕ :=
  ([24929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part022 : ℚ :=
  (35934141125 : ℚ) / 304053773442477981696

def SurrogateDiagonalTailChunk001Sub001Block004Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24929
    = surrogateDiagTailX0RatChunk001Sub001Block004Part022

theorem surrogateDiagonalTailChunk001Sub001Block004Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part022] using hcert

def TailChunk001Sub001Block004Part023SupportExplicit : Finset ℕ :=
  ([24931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part023 : ℚ :=
  (17835236325 : ℚ) / 152423176864274628608

def SurrogateDiagonalTailChunk001Sub001Block004Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24931
    = surrogateDiagTailX0RatChunk001Sub001Block004Part023

theorem surrogateDiagonalTailChunk001Sub001Block004Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part023] using hcert

def TailChunk001Sub001Block004Part024SupportExplicit : Finset ℕ :=
  ([24933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block004Part024 : ℚ :=
  (1667 : ℚ) / 508666127702400

def SurrogateDiagonalTailChunk001Sub001Block004Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24933
    = surrogateDiagTailX0RatChunk001Sub001Block004Part024

theorem surrogateDiagonalTailChunk001Sub001Block004Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block004Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block004Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block004Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block004Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block004Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block004HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block004Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block004Part000
    + surrogateDiagTailX0RatChunk001Sub001Block004Part001
    + surrogateDiagTailX0RatChunk001Sub001Block004Part002
    + surrogateDiagTailX0RatChunk001Sub001Block004Part003
    + surrogateDiagTailX0RatChunk001Sub001Block004Part004
    + surrogateDiagTailX0RatChunk001Sub001Block004Part005
    + surrogateDiagTailX0RatChunk001Sub001Block004Part006
    + surrogateDiagTailX0RatChunk001Sub001Block004Part007
    + surrogateDiagTailX0RatChunk001Sub001Block004Part008
    + surrogateDiagTailX0RatChunk001Sub001Block004Part009

def surrogateDiagonalTailChunk001Sub001Block004MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block004Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block004Part010
    + surrogateDiagTailX0RatChunk001Sub001Block004Part011
    + surrogateDiagTailX0RatChunk001Sub001Block004Part012
    + surrogateDiagTailX0RatChunk001Sub001Block004Part013
    + surrogateDiagTailX0RatChunk001Sub001Block004Part014
    + surrogateDiagTailX0RatChunk001Sub001Block004Part015
    + surrogateDiagTailX0RatChunk001Sub001Block004Part016
    + surrogateDiagTailX0RatChunk001Sub001Block004Part017
    + surrogateDiagTailX0RatChunk001Sub001Block004Part018
    + surrogateDiagTailX0RatChunk001Sub001Block004Part019

def surrogateDiagonalTailChunk001Sub001Block004TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block004Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block004Part020
    + surrogateDiagTailX0RatChunk001Sub001Block004Part021
    + surrogateDiagTailX0RatChunk001Sub001Block004Part022
    + surrogateDiagTailX0RatChunk001Sub001Block004Part023
    + surrogateDiagTailX0RatChunk001Sub001Block004Part024

def surrogateDiagonalTailChunk001Sub001Block004Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block004HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block004MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block004TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block004 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block004Part000
    + surrogateDiagTailX0RatChunk001Sub001Block004Part001
    + surrogateDiagTailX0RatChunk001Sub001Block004Part002
    + surrogateDiagTailX0RatChunk001Sub001Block004Part003
    + surrogateDiagTailX0RatChunk001Sub001Block004Part004
    + surrogateDiagTailX0RatChunk001Sub001Block004Part005
    + surrogateDiagTailX0RatChunk001Sub001Block004Part006
    + surrogateDiagTailX0RatChunk001Sub001Block004Part007
    + surrogateDiagTailX0RatChunk001Sub001Block004Part008
    + surrogateDiagTailX0RatChunk001Sub001Block004Part009
    + surrogateDiagTailX0RatChunk001Sub001Block004Part010
    + surrogateDiagTailX0RatChunk001Sub001Block004Part011
    + surrogateDiagTailX0RatChunk001Sub001Block004Part012
    + surrogateDiagTailX0RatChunk001Sub001Block004Part013
    + surrogateDiagTailX0RatChunk001Sub001Block004Part014
    + surrogateDiagTailX0RatChunk001Sub001Block004Part015
    + surrogateDiagTailX0RatChunk001Sub001Block004Part016
    + surrogateDiagTailX0RatChunk001Sub001Block004Part017
    + surrogateDiagTailX0RatChunk001Sub001Block004Part018
    + surrogateDiagTailX0RatChunk001Sub001Block004Part019
    + surrogateDiagTailX0RatChunk001Sub001Block004Part020
    + surrogateDiagTailX0RatChunk001Sub001Block004Part021
    + surrogateDiagTailX0RatChunk001Sub001Block004Part022
    + surrogateDiagTailX0RatChunk001Sub001Block004Part023
    + surrogateDiagTailX0RatChunk001Sub001Block004Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block004_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block004Head + surrogateDiagTailX0RatChunk001Sub001Block004Mid + surrogateDiagTailX0RatChunk001Sub001Block004Tail =
      surrogateDiagTailX0RatChunk001Sub001Block004 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block004Head surrogateDiagTailX0RatChunk001Sub001Block004Mid surrogateDiagTailX0RatChunk001Sub001Block004Tail surrogateDiagTailX0RatChunk001Sub001Block004
  ring

def SurrogateDiagonalTailChunk001Sub001Block004HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block004HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block004Head

def SurrogateDiagonalTailChunk001Sub001Block004MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block004MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block004Mid

def SurrogateDiagonalTailChunk001Sub001Block004TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block004TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block004Tail

theorem surrogateDiagonalTailChunk001Sub001Block004_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block004HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block004MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block004TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block004Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block004 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block004HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block004MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block004TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block004Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block004_eq_head_add_mid_add_tail

/-- Block 005 covers tail-support indices [15125,15150) and q from 24934 to 24973. -/

def TailChunk001Sub001Block005Part000SupportExplicit : Finset ℕ :=
  ([24934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part000 : ℚ :=
  (23853347825 : ℚ) / 718393674637246464

def SurrogateDiagonalTailChunk001Sub001Block005Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24934
    = surrogateDiagTailX0RatChunk001Sub001Block005Part000

theorem surrogateDiagonalTailChunk001Sub001Block005Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part000] using hcert

def TailChunk001Sub001Block005Part001SupportExplicit : Finset ℕ :=
  ([24935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part001 : ℚ :=
  (1555012814125 : ℚ) / 395617888657566517248

def SurrogateDiagonalTailChunk001Sub001Block005Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24935
    = surrogateDiagTailX0RatChunk001Sub001Block005Part001

theorem surrogateDiagonalTailChunk001Sub001Block005Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part001] using hcert

def TailChunk001Sub001Block005Part002SupportExplicit : Finset ℕ :=
  ([24937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part002 : ℚ :=
  (806054783 : ℚ) / 824093510105372100

def SurrogateDiagonalTailChunk001Sub001Block005Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24937
    = surrogateDiagTailX0RatChunk001Sub001Block005Part002

theorem surrogateDiagonalTailChunk001Sub001Block005Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part002] using hcert

def TailChunk001Sub001Block005Part003SupportExplicit : Finset ℕ :=
  ([24938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part003 : ℚ :=
  (4325294375 : ℚ) / 1982577656268324864

def SurrogateDiagonalTailChunk001Sub001Block005Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24938
    = surrogateDiagTailX0RatChunk001Sub001Block005Part003

theorem surrogateDiagonalTailChunk001Sub001Block005Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part003] using hcert

def TailChunk001Sub001Block005Part004SupportExplicit : Finset ℕ :=
  ([24942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part004 : ℚ :=
  (67509130225 : ℚ) / 745983144037688448

def SurrogateDiagonalTailChunk001Sub001Block005Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24942
    = surrogateDiagTailX0RatChunk001Sub001Block005Part004

theorem surrogateDiagonalTailChunk001Sub001Block005Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part004] using hcert

def TailChunk001Sub001Block005Part005SupportExplicit : Finset ℕ :=
  ([24943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block005Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24943
    = surrogateDiagTailX0RatChunk001Sub001Block005Part005

theorem surrogateDiagonalTailChunk001Sub001Block005Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part005] using hcert

def TailChunk001Sub001Block005Part006SupportExplicit : Finset ℕ :=
  ([24945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part006 : ℚ :=
  (129818614625 : ℚ) / 9768342929816457216

def SurrogateDiagonalTailChunk001Sub001Block005Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24945
    = surrogateDiagTailX0RatChunk001Sub001Block005Part006

theorem surrogateDiagonalTailChunk001Sub001Block005Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part006] using hcert

def TailChunk001Sub001Block005Part007SupportExplicit : Finset ℕ :=
  ([24946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block005Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24946
    = surrogateDiagTailX0RatChunk001Sub001Block005Part007

theorem surrogateDiagonalTailChunk001Sub001Block005Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part007] using hcert

def TailChunk001Sub001Block005Part008SupportExplicit : Finset ℕ :=
  ([24947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part008 : ℚ :=
  (2828938693 : ℚ) / 1451478461644800000

def SurrogateDiagonalTailChunk001Sub001Block005Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24947
    = surrogateDiagTailX0RatChunk001Sub001Block005Part008

theorem surrogateDiagonalTailChunk001Sub001Block005Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part008] using hcert

def TailChunk001Sub001Block005Part009SupportExplicit : Finset ℕ :=
  ([24949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part009 : ℚ :=
  (5733287197 : ℚ) / 35919683731862323200

def SurrogateDiagonalTailChunk001Sub001Block005Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24949
    = surrogateDiagTailX0RatChunk001Sub001Block005Part009

theorem surrogateDiagonalTailChunk001Sub001Block005Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part009] using hcert

def TailChunk001Sub001Block005Part010SupportExplicit : Finset ℕ :=
  ([24951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part010 : ℚ :=
  (41675 : ℚ) / 12753419784247296

def SurrogateDiagonalTailChunk001Sub001Block005Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24951
    = surrogateDiagTailX0RatChunk001Sub001Block005Part010

theorem surrogateDiagonalTailChunk001Sub001Block005Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part010] using hcert

def TailChunk001Sub001Block005Part011SupportExplicit : Finset ℕ :=
  ([24953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block005Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24953
    = surrogateDiagTailX0RatChunk001Sub001Block005Part011

theorem surrogateDiagonalTailChunk001Sub001Block005Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part011] using hcert

def TailChunk001Sub001Block005Part012SupportExplicit : Finset ℕ :=
  ([24954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part012 : ℚ :=
  (77227523825 : ℚ) / 854194450995813312

def SurrogateDiagonalTailChunk001Sub001Block005Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24954
    = surrogateDiagTailX0RatChunk001Sub001Block005Part012

theorem surrogateDiagonalTailChunk001Sub001Block005Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part012] using hcert

def TailChunk001Sub001Block005Part013SupportExplicit : Finset ℕ :=
  ([24955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part013 : ℚ :=
  (2153917343 : ℚ) / 174906141209395200

def SurrogateDiagonalTailChunk001Sub001Block005Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24955
    = surrogateDiagTailX0RatChunk001Sub001Block005Part013

theorem surrogateDiagonalTailChunk001Sub001Block005Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part013] using hcert

def TailChunk001Sub001Block005Part014SupportExplicit : Finset ℕ :=
  ([24958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block005Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24958
    = surrogateDiagTailX0RatChunk001Sub001Block005Part014

theorem surrogateDiagonalTailChunk001Sub001Block005Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part014] using hcert

def TailChunk001Sub001Block005Part015SupportExplicit : Finset ℕ :=
  ([24959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part015 : ℚ :=
  (2153256997 : ℚ) / 2205351427337049600

def SurrogateDiagonalTailChunk001Sub001Block005Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24959
    = surrogateDiagTailX0RatChunk001Sub001Block005Part015

theorem surrogateDiagonalTailChunk001Sub001Block005Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part015] using hcert

def TailChunk001Sub001Block005Part016SupportExplicit : Finset ℕ :=
  ([24961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part016 : ℚ :=
  (52511234525 : ℚ) / 459654242778029113344

def SurrogateDiagonalTailChunk001Sub001Block005Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24961
    = surrogateDiagTailX0RatChunk001Sub001Block005Part016

theorem surrogateDiagonalTailChunk001Sub001Block005Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part016] using hcert

def TailChunk001Sub001Block005Part017SupportExplicit : Finset ℕ :=
  ([24962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part017 : ℚ :=
  (11056429825 : ℚ) / 605158167906654912

def SurrogateDiagonalTailChunk001Sub001Block005Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24962
    = surrogateDiagTailX0RatChunk001Sub001Block005Part017

theorem surrogateDiagonalTailChunk001Sub001Block005Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part017] using hcert

def TailChunk001Sub001Block005Part018SupportExplicit : Finset ℕ :=
  ([24963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part018 : ℚ :=
  (43926308125 : ℚ) / 57748054115335274496

def SurrogateDiagonalTailChunk001Sub001Block005Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24963
    = surrogateDiagTailX0RatChunk001Sub001Block005Part018

theorem surrogateDiagonalTailChunk001Sub001Block005Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part018] using hcert

def TailChunk001Sub001Block005Part019SupportExplicit : Finset ℕ :=
  ([24965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part019 : ℚ :=
  (1558754563375 : ℚ) / 397525626676511244288

def SurrogateDiagonalTailChunk001Sub001Block005Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24965
    = surrogateDiagTailX0RatChunk001Sub001Block005Part019

theorem surrogateDiagonalTailChunk001Sub001Block005Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part019] using hcert

def TailChunk001Sub001Block005Part020SupportExplicit : Finset ℕ :=
  ([24967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block005Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24967
    = surrogateDiagTailX0RatChunk001Sub001Block005Part020

theorem surrogateDiagonalTailChunk001Sub001Block005Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part020] using hcert

def TailChunk001Sub001Block005Part021SupportExplicit : Finset ℕ :=
  ([24969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part021 : ℚ :=
  (31890671581 : ℚ) / 3263502314844979200

def SurrogateDiagonalTailChunk001Sub001Block005Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24969
    = surrogateDiagTailX0RatChunk001Sub001Block005Part021

theorem surrogateDiagonalTailChunk001Sub001Block005Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part021] using hcert

def TailChunk001Sub001Block005Part022SupportExplicit : Finset ℕ :=
  ([24970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part022 : ℚ :=
  (241666353 : ℚ) / 4453170393694208

def SurrogateDiagonalTailChunk001Sub001Block005Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24970
    = surrogateDiagTailX0RatChunk001Sub001Block005Part022

theorem surrogateDiagonalTailChunk001Sub001Block005Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part022] using hcert

def TailChunk001Sub001Block005Part023SupportExplicit : Finset ℕ :=
  ([24971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block005Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24971
    = surrogateDiagTailX0RatChunk001Sub001Block005Part023

theorem surrogateDiagonalTailChunk001Sub001Block005Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part023] using hcert

def TailChunk001Sub001Block005Part024SupportExplicit : Finset ℕ :=
  ([24973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block005Part024 : ℚ :=
  (7431132925 : ℚ) / 4774037672001798144

def SurrogateDiagonalTailChunk001Sub001Block005Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24973
    = surrogateDiagTailX0RatChunk001Sub001Block005Part024

theorem surrogateDiagonalTailChunk001Sub001Block005Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block005Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block005Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block005Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block005Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block005Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block005HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block005Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block005Part000
    + surrogateDiagTailX0RatChunk001Sub001Block005Part001
    + surrogateDiagTailX0RatChunk001Sub001Block005Part002
    + surrogateDiagTailX0RatChunk001Sub001Block005Part003
    + surrogateDiagTailX0RatChunk001Sub001Block005Part004
    + surrogateDiagTailX0RatChunk001Sub001Block005Part005
    + surrogateDiagTailX0RatChunk001Sub001Block005Part006
    + surrogateDiagTailX0RatChunk001Sub001Block005Part007
    + surrogateDiagTailX0RatChunk001Sub001Block005Part008
    + surrogateDiagTailX0RatChunk001Sub001Block005Part009

def surrogateDiagonalTailChunk001Sub001Block005MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block005Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block005Part010
    + surrogateDiagTailX0RatChunk001Sub001Block005Part011
    + surrogateDiagTailX0RatChunk001Sub001Block005Part012
    + surrogateDiagTailX0RatChunk001Sub001Block005Part013
    + surrogateDiagTailX0RatChunk001Sub001Block005Part014
    + surrogateDiagTailX0RatChunk001Sub001Block005Part015
    + surrogateDiagTailX0RatChunk001Sub001Block005Part016
    + surrogateDiagTailX0RatChunk001Sub001Block005Part017
    + surrogateDiagTailX0RatChunk001Sub001Block005Part018
    + surrogateDiagTailX0RatChunk001Sub001Block005Part019

def surrogateDiagonalTailChunk001Sub001Block005TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block005Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block005Part020
    + surrogateDiagTailX0RatChunk001Sub001Block005Part021
    + surrogateDiagTailX0RatChunk001Sub001Block005Part022
    + surrogateDiagTailX0RatChunk001Sub001Block005Part023
    + surrogateDiagTailX0RatChunk001Sub001Block005Part024

def surrogateDiagonalTailChunk001Sub001Block005Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block005HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block005MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block005TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block005 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block005Part000
    + surrogateDiagTailX0RatChunk001Sub001Block005Part001
    + surrogateDiagTailX0RatChunk001Sub001Block005Part002
    + surrogateDiagTailX0RatChunk001Sub001Block005Part003
    + surrogateDiagTailX0RatChunk001Sub001Block005Part004
    + surrogateDiagTailX0RatChunk001Sub001Block005Part005
    + surrogateDiagTailX0RatChunk001Sub001Block005Part006
    + surrogateDiagTailX0RatChunk001Sub001Block005Part007
    + surrogateDiagTailX0RatChunk001Sub001Block005Part008
    + surrogateDiagTailX0RatChunk001Sub001Block005Part009
    + surrogateDiagTailX0RatChunk001Sub001Block005Part010
    + surrogateDiagTailX0RatChunk001Sub001Block005Part011
    + surrogateDiagTailX0RatChunk001Sub001Block005Part012
    + surrogateDiagTailX0RatChunk001Sub001Block005Part013
    + surrogateDiagTailX0RatChunk001Sub001Block005Part014
    + surrogateDiagTailX0RatChunk001Sub001Block005Part015
    + surrogateDiagTailX0RatChunk001Sub001Block005Part016
    + surrogateDiagTailX0RatChunk001Sub001Block005Part017
    + surrogateDiagTailX0RatChunk001Sub001Block005Part018
    + surrogateDiagTailX0RatChunk001Sub001Block005Part019
    + surrogateDiagTailX0RatChunk001Sub001Block005Part020
    + surrogateDiagTailX0RatChunk001Sub001Block005Part021
    + surrogateDiagTailX0RatChunk001Sub001Block005Part022
    + surrogateDiagTailX0RatChunk001Sub001Block005Part023
    + surrogateDiagTailX0RatChunk001Sub001Block005Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block005_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block005Head + surrogateDiagTailX0RatChunk001Sub001Block005Mid + surrogateDiagTailX0RatChunk001Sub001Block005Tail =
      surrogateDiagTailX0RatChunk001Sub001Block005 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block005Head surrogateDiagTailX0RatChunk001Sub001Block005Mid surrogateDiagTailX0RatChunk001Sub001Block005Tail surrogateDiagTailX0RatChunk001Sub001Block005
  ring

def SurrogateDiagonalTailChunk001Sub001Block005HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block005HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block005Head

def SurrogateDiagonalTailChunk001Sub001Block005MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block005MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block005Mid

def SurrogateDiagonalTailChunk001Sub001Block005TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block005TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block005Tail

theorem surrogateDiagonalTailChunk001Sub001Block005_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block005HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block005MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block005TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block005Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block005 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block005HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block005MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block005TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block005Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block005_eq_head_add_mid_add_tail

/-- Block 006 covers tail-support indices [15150,15175) and q from 24974 to 25014. -/

def TailChunk001Sub001Block006Part000SupportExplicit : Finset ℕ :=
  ([24974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block006Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24974
    = surrogateDiagTailX0RatChunk001Sub001Block006Part000

theorem surrogateDiagonalTailChunk001Sub001Block006Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part000] using hcert

def TailChunk001Sub001Block006Part001SupportExplicit : Finset ℕ :=
  ([24977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block006Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24977
    = surrogateDiagTailX0RatChunk001Sub001Block006Part001

theorem surrogateDiagonalTailChunk001Sub001Block006Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part001] using hcert

def TailChunk001Sub001Block006Part002SupportExplicit : Finset ℕ :=
  ([24978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part002 : ℚ :=
  (22183119749 : ℚ) / 196769408860569600

def SurrogateDiagonalTailChunk001Sub001Block006Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24978
    = surrogateDiagTailX0RatChunk001Sub001Block006Part002

theorem surrogateDiagonalTailChunk001Sub001Block006Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part002] using hcert

def TailChunk001Sub001Block006Part003SupportExplicit : Finset ℕ :=
  ([24979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block006Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24979
    = surrogateDiagTailX0RatChunk001Sub001Block006Part003

theorem surrogateDiagonalTailChunk001Sub001Block006Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part003] using hcert

def TailChunk001Sub001Block006Part004SupportExplicit : Finset ℕ :=
  ([24981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part004 : ℚ :=
  (3765770363 : ℚ) / 1045499935922749440

def SurrogateDiagonalTailChunk001Sub001Block006Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24981
    = surrogateDiagTailX0RatChunk001Sub001Block006Part004

theorem surrogateDiagonalTailChunk001Sub001Block006Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part004] using hcert

def TailChunk001Sub001Block006Part005SupportExplicit : Finset ℕ :=
  ([24982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block006Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24982
    = surrogateDiagTailX0RatChunk001Sub001Block006Part005

theorem surrogateDiagonalTailChunk001Sub001Block006Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part005] using hcert

def TailChunk001Sub001Block006Part006SupportExplicit : Finset ℕ :=
  ([24983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part006 : ℚ :=
  (10154840375 : ℚ) / 4749120602547910848

def SurrogateDiagonalTailChunk001Sub001Block006Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24983
    = surrogateDiagTailX0RatChunk001Sub001Block006Part006

theorem surrogateDiagonalTailChunk001Sub001Block006Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part006] using hcert

def TailChunk001Sub001Block006Part007SupportExplicit : Finset ℕ :=
  ([24985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part007 : ℚ :=
  (582324486625 : ℚ) / 105545751182122254336

def SurrogateDiagonalTailChunk001Sub001Block006Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24985
    = surrogateDiagTailX0RatChunk001Sub001Block006Part007

theorem surrogateDiagonalTailChunk001Sub001Block006Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part007] using hcert

def TailChunk001Sub001Block006Part008SupportExplicit : Finset ℕ :=
  ([24987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part008 : ℚ :=
  (41675 : ℚ) / 12827192085282816

def SurrogateDiagonalTailChunk001Sub001Block006Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24987
    = surrogateDiagTailX0RatChunk001Sub001Block006Part008

theorem surrogateDiagonalTailChunk001Sub001Block006Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part008] using hcert

def TailChunk001Sub001Block006Part009SupportExplicit : Finset ℕ :=
  ([24989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block006Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24989
    = surrogateDiagTailX0RatChunk001Sub001Block006Part009

theorem surrogateDiagonalTailChunk001Sub001Block006Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part009] using hcert

def TailChunk001Sub001Block006Part010SupportExplicit : Finset ℕ :=
  ([24991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part010 : ℚ :=
  (66446309225 : ℚ) / 454301703100805243904

def SurrogateDiagonalTailChunk001Sub001Block006Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24991
    = surrogateDiagTailX0RatChunk001Sub001Block006Part010

theorem surrogateDiagonalTailChunk001Sub001Block006Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part010] using hcert

def TailChunk001Sub001Block006Part011SupportExplicit : Finset ℕ :=
  ([24994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block006Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24994
    = surrogateDiagTailX0RatChunk001Sub001Block006Part011

theorem surrogateDiagonalTailChunk001Sub001Block006Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part011] using hcert

def TailChunk001Sub001Block006Part012SupportExplicit : Finset ℕ :=
  ([24995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part012 : ℚ :=
  (1562500812625 : ℚ) / 399440255974389762048

def SurrogateDiagonalTailChunk001Sub001Block006Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24995
    = surrogateDiagTailX0RatChunk001Sub001Block006Part012

theorem surrogateDiagonalTailChunk001Sub001Block006Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part012] using hcert

def TailChunk001Sub001Block006Part013SupportExplicit : Finset ℕ :=
  ([24997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part013 : ℚ :=
  (31937247133 : ℚ) / 21055459140674179200

def SurrogateDiagonalTailChunk001Sub001Block006Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24997
    = surrogateDiagTailX0RatChunk001Sub001Block006Part013

theorem surrogateDiagonalTailChunk001Sub001Block006Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part013] using hcert

def TailChunk001Sub001Block006Part014SupportExplicit : Finset ℕ :=
  ([24998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part014 : ℚ :=
  (258277371 : ℚ) / 100086039274547200

def SurrogateDiagonalTailChunk001Sub001Block006Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24998
    = surrogateDiagTailX0RatChunk001Sub001Block006Part014

theorem surrogateDiagonalTailChunk001Sub001Block006Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part014] using hcert

def TailChunk001Sub001Block006Part015SupportExplicit : Finset ℕ :=
  ([24999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part015 : ℚ :=
  (113453321 : ℚ) / 46394923926159360

def SurrogateDiagonalTailChunk001Sub001Block006Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24999
    = surrogateDiagTailX0RatChunk001Sub001Block006Part015

theorem surrogateDiagonalTailChunk001Sub001Block006Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part015] using hcert

def TailChunk001Sub001Block006Part016SupportExplicit : Finset ℕ :=
  ([25001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part016 : ℚ :=
  (17990408092475 : ℚ) / 407386738540118044224

def SurrogateDiagonalTailChunk001Sub001Block006Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25001
    = surrogateDiagTailX0RatChunk001Sub001Block006Part016

theorem surrogateDiagonalTailChunk001Sub001Block006Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part016] using hcert

def TailChunk001Sub001Block006Part017SupportExplicit : Finset ℕ :=
  ([25003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part017 : ℚ :=
  (109710734163 : ℚ) / 2220950669334937600

def SurrogateDiagonalTailChunk001Sub001Block006Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25003
    = surrogateDiagTailX0RatChunk001Sub001Block006Part017

theorem surrogateDiagonalTailChunk001Sub001Block006Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part017] using hcert

def TailChunk001Sub001Block006Part018SupportExplicit : Finset ℕ :=
  ([25005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part018 : ℚ :=
  (56129789475 : ℚ) / 386773426264236032

def SurrogateDiagonalTailChunk001Sub001Block006Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25005
    = surrogateDiagTailX0RatChunk001Sub001Block006Part018

theorem surrogateDiagonalTailChunk001Sub001Block006Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part018] using hcert

def TailChunk001Sub001Block006Part019SupportExplicit : Finset ℕ :=
  ([25006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part019 : ℚ :=
  (2442578265625 : ℚ) / 15271610742906310002

def SurrogateDiagonalTailChunk001Sub001Block006Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25006
    = surrogateDiagTailX0RatChunk001Sub001Block006Part019

theorem surrogateDiagonalTailChunk001Sub001Block006Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part019] using hcert

def TailChunk001Sub001Block006Part020SupportExplicit : Finset ℕ :=
  ([25007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part020 : ℚ :=
  (349869751117 : ℚ) / 7652020564397260800

def SurrogateDiagonalTailChunk001Sub001Block006Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25007
    = surrogateDiagTailX0RatChunk001Sub001Block006Part020

theorem surrogateDiagonalTailChunk001Sub001Block006Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part020] using hcert

def TailChunk001Sub001Block006Part021SupportExplicit : Finset ℕ :=
  ([25009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part021 : ℚ :=
  (60894373627 : ℚ) / 1474720289865596928

def SurrogateDiagonalTailChunk001Sub001Block006Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25009
    = surrogateDiagTailX0RatChunk001Sub001Block006Part021

theorem surrogateDiagonalTailChunk001Sub001Block006Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part021] using hcert

def TailChunk001Sub001Block006Part022SupportExplicit : Finset ℕ :=
  ([25010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part022 : ℚ :=
  (124736616677 : ℚ) / 424758214656000000

def SurrogateDiagonalTailChunk001Sub001Block006Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25010
    = surrogateDiagTailX0RatChunk001Sub001Block006Part022

theorem surrogateDiagonalTailChunk001Sub001Block006Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part022] using hcert

def TailChunk001Sub001Block006Part023SupportExplicit : Finset ℕ :=
  ([25013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part023 : ℚ :=
  (9775783890625 : ℚ) / 244658634550534562592

def SurrogateDiagonalTailChunk001Sub001Block006Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25013
    = surrogateDiagTailX0RatChunk001Sub001Block006Part023

theorem surrogateDiagonalTailChunk001Sub001Block006Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part023] using hcert

def TailChunk001Sub001Block006Part024SupportExplicit : Finset ℕ :=
  ([25014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block006Part024 : ℚ :=
  (467754085 : ℚ) / 816796824939648

def SurrogateDiagonalTailChunk001Sub001Block006Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25014
    = surrogateDiagTailX0RatChunk001Sub001Block006Part024

theorem surrogateDiagonalTailChunk001Sub001Block006Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block006Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block006Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block006Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block006Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block006Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block006HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block006Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block006Part000
    + surrogateDiagTailX0RatChunk001Sub001Block006Part001
    + surrogateDiagTailX0RatChunk001Sub001Block006Part002
    + surrogateDiagTailX0RatChunk001Sub001Block006Part003
    + surrogateDiagTailX0RatChunk001Sub001Block006Part004
    + surrogateDiagTailX0RatChunk001Sub001Block006Part005
    + surrogateDiagTailX0RatChunk001Sub001Block006Part006
    + surrogateDiagTailX0RatChunk001Sub001Block006Part007
    + surrogateDiagTailX0RatChunk001Sub001Block006Part008
    + surrogateDiagTailX0RatChunk001Sub001Block006Part009

def surrogateDiagonalTailChunk001Sub001Block006MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block006Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block006Part010
    + surrogateDiagTailX0RatChunk001Sub001Block006Part011
    + surrogateDiagTailX0RatChunk001Sub001Block006Part012
    + surrogateDiagTailX0RatChunk001Sub001Block006Part013
    + surrogateDiagTailX0RatChunk001Sub001Block006Part014
    + surrogateDiagTailX0RatChunk001Sub001Block006Part015
    + surrogateDiagTailX0RatChunk001Sub001Block006Part016
    + surrogateDiagTailX0RatChunk001Sub001Block006Part017
    + surrogateDiagTailX0RatChunk001Sub001Block006Part018
    + surrogateDiagTailX0RatChunk001Sub001Block006Part019

def surrogateDiagonalTailChunk001Sub001Block006TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block006Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block006Part020
    + surrogateDiagTailX0RatChunk001Sub001Block006Part021
    + surrogateDiagTailX0RatChunk001Sub001Block006Part022
    + surrogateDiagTailX0RatChunk001Sub001Block006Part023
    + surrogateDiagTailX0RatChunk001Sub001Block006Part024

def surrogateDiagonalTailChunk001Sub001Block006Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block006HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block006MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block006TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block006 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block006Part000
    + surrogateDiagTailX0RatChunk001Sub001Block006Part001
    + surrogateDiagTailX0RatChunk001Sub001Block006Part002
    + surrogateDiagTailX0RatChunk001Sub001Block006Part003
    + surrogateDiagTailX0RatChunk001Sub001Block006Part004
    + surrogateDiagTailX0RatChunk001Sub001Block006Part005
    + surrogateDiagTailX0RatChunk001Sub001Block006Part006
    + surrogateDiagTailX0RatChunk001Sub001Block006Part007
    + surrogateDiagTailX0RatChunk001Sub001Block006Part008
    + surrogateDiagTailX0RatChunk001Sub001Block006Part009
    + surrogateDiagTailX0RatChunk001Sub001Block006Part010
    + surrogateDiagTailX0RatChunk001Sub001Block006Part011
    + surrogateDiagTailX0RatChunk001Sub001Block006Part012
    + surrogateDiagTailX0RatChunk001Sub001Block006Part013
    + surrogateDiagTailX0RatChunk001Sub001Block006Part014
    + surrogateDiagTailX0RatChunk001Sub001Block006Part015
    + surrogateDiagTailX0RatChunk001Sub001Block006Part016
    + surrogateDiagTailX0RatChunk001Sub001Block006Part017
    + surrogateDiagTailX0RatChunk001Sub001Block006Part018
    + surrogateDiagTailX0RatChunk001Sub001Block006Part019
    + surrogateDiagTailX0RatChunk001Sub001Block006Part020
    + surrogateDiagTailX0RatChunk001Sub001Block006Part021
    + surrogateDiagTailX0RatChunk001Sub001Block006Part022
    + surrogateDiagTailX0RatChunk001Sub001Block006Part023
    + surrogateDiagTailX0RatChunk001Sub001Block006Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block006_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block006Head + surrogateDiagTailX0RatChunk001Sub001Block006Mid + surrogateDiagTailX0RatChunk001Sub001Block006Tail =
      surrogateDiagTailX0RatChunk001Sub001Block006 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block006Head surrogateDiagTailX0RatChunk001Sub001Block006Mid surrogateDiagTailX0RatChunk001Sub001Block006Tail surrogateDiagTailX0RatChunk001Sub001Block006
  ring

def SurrogateDiagonalTailChunk001Sub001Block006HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block006HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block006Head

def SurrogateDiagonalTailChunk001Sub001Block006MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block006MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block006Mid

def SurrogateDiagonalTailChunk001Sub001Block006TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block006TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block006Tail

theorem surrogateDiagonalTailChunk001Sub001Block006_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block006HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block006MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block006TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block006Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block006 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block006HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block006MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block006TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block006Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block006_eq_head_add_mid_add_tail

/-- Block 007 covers tail-support indices [15175,15200) and q from 25015 to 25055. -/

def TailChunk001Sub001Block007Part000SupportExplicit : Finset ℕ :=
  ([25015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part000 : ℚ :=
  (1563828390625 : ℚ) / 25045032011201920128

def SurrogateDiagonalTailChunk001Sub001Block007Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25015
    = surrogateDiagTailX0RatChunk001Sub001Block007Part000

theorem surrogateDiagonalTailChunk001Sub001Block007Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part000] using hcert

def TailChunk001Sub001Block007Part001SupportExplicit : Finset ℕ :=
  ([25017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part001 : ℚ :=
  (653070886141 : ℚ) / 6686995452560179200

def SurrogateDiagonalTailChunk001Sub001Block007Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25017
    = surrogateDiagTailX0RatChunk001Sub001Block007Part001

theorem surrogateDiagonalTailChunk001Sub001Block007Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part001] using hcert

def TailChunk001Sub001Block007Part002SupportExplicit : Finset ℕ :=
  ([25018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part002 : ℚ :=
  (118414279375 : ℚ) / 515202194991841362

def SurrogateDiagonalTailChunk001Sub001Block007Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25018
    = surrogateDiagTailX0RatChunk001Sub001Block007Part002

theorem surrogateDiagonalTailChunk001Sub001Block007Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part002] using hcert

def TailChunk001Sub001Block007Part003SupportExplicit : Finset ℕ :=
  ([25019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part003 : ℚ :=
  (606610883425 : ℚ) / 14763617176433965056

def SurrogateDiagonalTailChunk001Sub001Block007Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25019
    = surrogateDiagTailX0RatChunk001Sub001Block007Part003

theorem surrogateDiagonalTailChunk001Sub001Block007Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part003] using hcert

def TailChunk001Sub001Block007Part004SupportExplicit : Finset ℕ :=
  ([25021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part004 : ℚ :=
  (1529161093327 : ℚ) / 37228425006162000000

def SurrogateDiagonalTailChunk001Sub001Block007Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25021
    = surrogateDiagTailX0RatChunk001Sub001Block007Part004

theorem surrogateDiagonalTailChunk001Sub001Block007Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part004] using hcert

def TailChunk001Sub001Block007Part005SupportExplicit : Finset ℕ :=
  ([25022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part005 : ℚ :=
  (3913128025 : ℚ) / 24497179756270002

def SurrogateDiagonalTailChunk001Sub001Block007Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25022
    = surrogateDiagTailX0RatChunk001Sub001Block007Part005

theorem surrogateDiagonalTailChunk001Sub001Block007Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part005] using hcert

def TailChunk001Sub001Block007Part006SupportExplicit : Finset ℕ :=
  ([25023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part006 : ℚ :=
  (15790038063025 : ℚ) / 154572881850368575488

def SurrogateDiagonalTailChunk001Sub001Block007Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25023
    = surrogateDiagTailX0RatChunk001Sub001Block007Part006

theorem surrogateDiagonalTailChunk001Sub001Block007Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part006] using hcert

def TailChunk001Sub001Block007Part007SupportExplicit : Finset ℕ :=
  ([25026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part007 : ℚ :=
  (5163424451125 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk001Sub001Block007Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25026
    = surrogateDiagTailX0RatChunk001Sub001Block007Part007

theorem surrogateDiagonalTailChunk001Sub001Block007Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part007] using hcert

def TailChunk001Sub001Block007Part008SupportExplicit : Finset ℕ :=
  ([25027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part008 : ℚ :=
  (9163109129875 : ℚ) / 212142682553673994752

def SurrogateDiagonalTailChunk001Sub001Block007Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25027
    = surrogateDiagTailX0RatChunk001Sub001Block007Part008

theorem surrogateDiagonalTailChunk001Sub001Block007Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part008] using hcert

def TailChunk001Sub001Block007Part009SupportExplicit : Finset ℕ :=
  ([25030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part009 : ℚ :=
  (6653130625525 : ℚ) / 25085112070420482048

def SurrogateDiagonalTailChunk001Sub001Block007Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25030
    = surrogateDiagTailX0RatChunk001Sub001Block007Part009

theorem surrogateDiagonalTailChunk001Sub001Block007Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part009] using hcert

def TailChunk001Sub001Block007Part010SupportExplicit : Finset ℕ :=
  ([25031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part010 : ℚ :=
  (15663774025 : ℚ) / 392581878376350162

def SurrogateDiagonalTailChunk001Sub001Block007Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25031
    = surrogateDiagTailX0RatChunk001Sub001Block007Part010

theorem surrogateDiagonalTailChunk001Sub001Block007Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part010] using hcert

def TailChunk001Sub001Block007Part011SupportExplicit : Finset ℕ :=
  ([25033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part011 : ℚ :=
  (9791423265625 : ℚ) / 245442105654065091072

def SurrogateDiagonalTailChunk001Sub001Block007Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25033
    = surrogateDiagTailX0RatChunk001Sub001Block007Part011

theorem surrogateDiagonalTailChunk001Sub001Block007Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part011] using hcert

def TailChunk001Sub001Block007Part012SupportExplicit : Finset ℕ :=
  ([25034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part012 : ℚ :=
  (2448051390625 : ℚ) / 15340131603379068192

def SurrogateDiagonalTailChunk001Sub001Block007Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25034
    = surrogateDiagTailX0RatChunk001Sub001Block007Part012

theorem surrogateDiagonalTailChunk001Sub001Block007Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part012] using hcert

def TailChunk001Sub001Block007Part013SupportExplicit : Finset ℕ :=
  ([25035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part013 : ℚ :=
  (1434747463625 : ℚ) / 9910167731524141056

def SurrogateDiagonalTailChunk001Sub001Block007Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25035
    = surrogateDiagTailX0RatChunk001Sub001Block007Part013

theorem surrogateDiagonalTailChunk001Sub001Block007Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part013] using hcert

def TailChunk001Sub001Block007Part014SupportExplicit : Finset ℕ :=
  ([25037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part014 : ℚ :=
  (9794552640625 : ℚ) / 245599025400133169952

def SurrogateDiagonalTailChunk001Sub001Block007Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25037
    = surrogateDiagTailX0RatChunk001Sub001Block007Part014

theorem surrogateDiagonalTailChunk001Sub001Block007Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part014] using hcert

def TailChunk001Sub001Block007Part015SupportExplicit : Finset ℕ :=
  ([25041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part015 : ℚ :=
  (624034156789 : ℚ) / 6046040939770675200

def SurrogateDiagonalTailChunk001Sub001Block007Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25041
    = surrogateDiagTailX0RatChunk001Sub001Block007Part015

theorem surrogateDiagonalTailChunk001Sub001Block007Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part015] using hcert

def TailChunk001Sub001Block007Part016SupportExplicit : Finset ℕ :=
  ([25042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part016 : ℚ :=
  (1280525553025 : ℚ) / 7029467279573768064

def SurrogateDiagonalTailChunk001Sub001Block007Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25042
    = surrogateDiagTailX0RatChunk001Sub001Block007Part016

theorem surrogateDiagonalTailChunk001Sub001Block007Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part016] using hcert

def TailChunk001Sub001Block007Part017SupportExplicit : Finset ℕ :=
  ([25043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part017 : ℚ :=
  (156750461875 : ℚ) / 3797933240639789056

def SurrogateDiagonalTailChunk001Sub001Block007Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25043
    = surrogateDiagTailX0RatChunk001Sub001Block007Part017

theorem surrogateDiagonalTailChunk001Sub001Block007Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part017] using hcert

def TailChunk001Sub001Block007Part018SupportExplicit : Finset ℕ :=
  ([25045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part018 : ℚ :=
  (1567582140625 : ℚ) / 25165416486645792768

def SurrogateDiagonalTailChunk001Sub001Block007Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25045
    = surrogateDiagTailX0RatChunk001Sub001Block007Part018

theorem surrogateDiagonalTailChunk001Sub001Block007Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part018] using hcert

def TailChunk001Sub001Block007Part019SupportExplicit : Finset ℕ :=
  ([25046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part019 : ℚ :=
  (1898873086075 : ℚ) / 8280220973752300032

def SurrogateDiagonalTailChunk001Sub001Block007Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25046
    = surrogateDiagTailX0RatChunk001Sub001Block007Part019

theorem surrogateDiagonalTailChunk001Sub001Block007Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part019] using hcert

def TailChunk001Sub001Block007Part020SupportExplicit : Finset ℕ :=
  ([25049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part020 : ℚ :=
  (688886296625 : ℚ) / 16241640219938045952

def SurrogateDiagonalTailChunk001Sub001Block007Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25049
    = surrogateDiagTailX0RatChunk001Sub001Block007Part020

theorem surrogateDiagonalTailChunk001Sub001Block007Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part020] using hcert

def TailChunk001Sub001Block007Part021SupportExplicit : Finset ℕ :=
  ([25051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part021 : ℚ :=
  (1246837822339 : ℚ) / 23772952709509939200

def SurrogateDiagonalTailChunk001Sub001Block007Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25051
    = surrogateDiagTailX0RatChunk001Sub001Block007Part021

theorem surrogateDiagonalTailChunk001Sub001Block007Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part021] using hcert

def TailChunk001Sub001Block007Part022SupportExplicit : Finset ℕ :=
  ([25053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part022 : ℚ :=
  (123374467775 : ℚ) / 969243973150703616

def SurrogateDiagonalTailChunk001Sub001Block007Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25053
    = surrogateDiagTailX0RatChunk001Sub001Block007Part022

theorem surrogateDiagonalTailChunk001Sub001Block007Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part022] using hcert

def TailChunk001Sub001Block007Part023SupportExplicit : Finset ℕ :=
  ([25054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part023 : ℚ :=
  (2451964515625 : ℚ) / 15389216058551767122

def SurrogateDiagonalTailChunk001Sub001Block007Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25054
    = surrogateDiagTailX0RatChunk001Sub001Block007Part023

theorem surrogateDiagonalTailChunk001Sub001Block007Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part023] using hcert

def TailChunk001Sub001Block007Part024SupportExplicit : Finset ℕ :=
  ([25055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block007Part024 : ℚ :=
  (836711675 : ℚ) / 13443008490965376

def SurrogateDiagonalTailChunk001Sub001Block007Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25055
    = surrogateDiagTailX0RatChunk001Sub001Block007Part024

theorem surrogateDiagonalTailChunk001Sub001Block007Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block007Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block007Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block007Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block007Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block007Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block007HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block007Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block007Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block007Part000
    + surrogateDiagTailX0RatChunk001Sub001Block007Part001
    + surrogateDiagTailX0RatChunk001Sub001Block007Part002
    + surrogateDiagTailX0RatChunk001Sub001Block007Part003
    + surrogateDiagTailX0RatChunk001Sub001Block007Part004
    + surrogateDiagTailX0RatChunk001Sub001Block007Part005
    + surrogateDiagTailX0RatChunk001Sub001Block007Part006
    + surrogateDiagTailX0RatChunk001Sub001Block007Part007
    + surrogateDiagTailX0RatChunk001Sub001Block007Part008
    + surrogateDiagTailX0RatChunk001Sub001Block007Part009

def surrogateDiagonalTailChunk001Sub001Block007MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block007Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block007Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block007Part010
    + surrogateDiagTailX0RatChunk001Sub001Block007Part011
    + surrogateDiagTailX0RatChunk001Sub001Block007Part012
    + surrogateDiagTailX0RatChunk001Sub001Block007Part013
    + surrogateDiagTailX0RatChunk001Sub001Block007Part014
    + surrogateDiagTailX0RatChunk001Sub001Block007Part015
    + surrogateDiagTailX0RatChunk001Sub001Block007Part016
    + surrogateDiagTailX0RatChunk001Sub001Block007Part017
    + surrogateDiagTailX0RatChunk001Sub001Block007Part018
    + surrogateDiagTailX0RatChunk001Sub001Block007Part019

def surrogateDiagonalTailChunk001Sub001Block007TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block007Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block007Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block007Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block007Part020
    + surrogateDiagTailX0RatChunk001Sub001Block007Part021
    + surrogateDiagTailX0RatChunk001Sub001Block007Part022
    + surrogateDiagTailX0RatChunk001Sub001Block007Part023
    + surrogateDiagTailX0RatChunk001Sub001Block007Part024

def surrogateDiagonalTailChunk001Sub001Block007Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block007HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block007MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block007TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block007 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block007Part000
    + surrogateDiagTailX0RatChunk001Sub001Block007Part001
    + surrogateDiagTailX0RatChunk001Sub001Block007Part002
    + surrogateDiagTailX0RatChunk001Sub001Block007Part003
    + surrogateDiagTailX0RatChunk001Sub001Block007Part004
    + surrogateDiagTailX0RatChunk001Sub001Block007Part005
    + surrogateDiagTailX0RatChunk001Sub001Block007Part006
    + surrogateDiagTailX0RatChunk001Sub001Block007Part007
    + surrogateDiagTailX0RatChunk001Sub001Block007Part008
    + surrogateDiagTailX0RatChunk001Sub001Block007Part009
    + surrogateDiagTailX0RatChunk001Sub001Block007Part010
    + surrogateDiagTailX0RatChunk001Sub001Block007Part011
    + surrogateDiagTailX0RatChunk001Sub001Block007Part012
    + surrogateDiagTailX0RatChunk001Sub001Block007Part013
    + surrogateDiagTailX0RatChunk001Sub001Block007Part014
    + surrogateDiagTailX0RatChunk001Sub001Block007Part015
    + surrogateDiagTailX0RatChunk001Sub001Block007Part016
    + surrogateDiagTailX0RatChunk001Sub001Block007Part017
    + surrogateDiagTailX0RatChunk001Sub001Block007Part018
    + surrogateDiagTailX0RatChunk001Sub001Block007Part019
    + surrogateDiagTailX0RatChunk001Sub001Block007Part020
    + surrogateDiagTailX0RatChunk001Sub001Block007Part021
    + surrogateDiagTailX0RatChunk001Sub001Block007Part022
    + surrogateDiagTailX0RatChunk001Sub001Block007Part023
    + surrogateDiagTailX0RatChunk001Sub001Block007Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block007_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block007Head + surrogateDiagTailX0RatChunk001Sub001Block007Mid + surrogateDiagTailX0RatChunk001Sub001Block007Tail =
      surrogateDiagTailX0RatChunk001Sub001Block007 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block007Head surrogateDiagTailX0RatChunk001Sub001Block007Mid surrogateDiagTailX0RatChunk001Sub001Block007Tail surrogateDiagTailX0RatChunk001Sub001Block007
  ring

def SurrogateDiagonalTailChunk001Sub001Block007HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block007HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block007Head

def SurrogateDiagonalTailChunk001Sub001Block007MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block007MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block007Mid

def SurrogateDiagonalTailChunk001Sub001Block007TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block007TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block007Tail

theorem surrogateDiagonalTailChunk001Sub001Block007_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block007HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block007MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block007TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block007Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block007 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block007HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block007MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block007TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block007Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block007_eq_head_add_mid_add_tail

/-- Block 008 covers tail-support indices [15200,15225) and q from 25057 to 25094. -/

def TailChunk001Sub001Block008Part000SupportExplicit : Finset ℕ :=
  ([25057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part000 : ℚ :=
  (9810207015625 : ℚ) / 246384753079342989312

def SurrogateDiagonalTailChunk001Sub001Block008Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25057
    = surrogateDiagTailX0RatChunk001Sub001Block008Part000

theorem surrogateDiagonalTailChunk001Sub001Block008Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part000] using hcert

def TailChunk001Sub001Block008Part001SupportExplicit : Finset ℕ :=
  ([25058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part001 : ℚ :=
  (299152369231 : ℚ) / 1243777004155699200

def SurrogateDiagonalTailChunk001Sub001Block008Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25058
    = surrogateDiagTailX0RatChunk001Sub001Block008Part001

theorem surrogateDiagonalTailChunk001Sub001Block008Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part001] using hcert

def TailChunk001Sub001Block008Part002SupportExplicit : Finset ℕ :=
  ([25059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part002 : ℚ :=
  (17439600164725 : ℚ) / 194674372803431497728

def SurrogateDiagonalTailChunk001Sub001Block008Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25059
    = surrogateDiagTailX0RatChunk001Sub001Block008Part002

theorem surrogateDiagonalTailChunk001Sub001Block008Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part002] using hcert

def TailChunk001Sub001Block008Part003SupportExplicit : Finset ℕ :=
  ([25061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part003 : ℚ :=
  (737521115725 : ℚ) / 16502026604720149656

def SurrogateDiagonalTailChunk001Sub001Block008Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25061
    = surrogateDiagTailX0RatChunk001Sub001Block008Part003

theorem surrogateDiagonalTailChunk001Sub001Block008Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part003] using hcert

def TailChunk001Sub001Block008Part004SupportExplicit : Finset ℕ :=
  ([25062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part004 : ℚ :=
  (4360368582325 : ℚ) / 12167148300214468608

def SurrogateDiagonalTailChunk001Sub001Block008Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25062
    = surrogateDiagTailX0RatChunk001Sub001Block008Part004

theorem surrogateDiagonalTailChunk001Sub001Block008Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part004] using hcert

def TailChunk001Sub001Block008Part005SupportExplicit : Finset ℕ :=
  ([25063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part005 : ℚ :=
  (1522809915133 : ℚ) / 36868007246639923200

def SurrogateDiagonalTailChunk001Sub001Block008Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25063
    = surrogateDiagTailX0RatChunk001Sub001Block008Part005

theorem surrogateDiagonalTailChunk001Sub001Block008Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part005] using hcert

def TailChunk001Sub001Block008Part006SupportExplicit : Finset ℕ :=
  ([25066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part006 : ℚ :=
  (95269152073 : ℚ) / 572331045820500000

def SurrogateDiagonalTailChunk001Sub001Block008Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25066
    = surrogateDiagTailX0RatChunk001Sub001Block008Part006

theorem surrogateDiagonalTailChunk001Sub001Block008Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part006] using hcert

def TailChunk001Sub001Block008Part007SupportExplicit : Finset ℕ :=
  ([25067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part007 : ℚ :=
  (237133731029 : ℚ) / 4258473548648048640

def SurrogateDiagonalTailChunk001Sub001Block008Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25067
    = surrogateDiagTailX0RatChunk001Sub001Block008Part007

theorem surrogateDiagonalTailChunk001Sub001Block008Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part007] using hcert

def TailChunk001Sub001Block008Part008SupportExplicit : Finset ℕ :=
  ([25069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part008 : ℚ :=
  (44998465117 : ℚ) / 842817650592153600

def SurrogateDiagonalTailChunk001Sub001Block008Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25069
    = surrogateDiagTailX0RatChunk001Sub001Block008Part008

theorem surrogateDiagonalTailChunk001Sub001Block008Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part008] using hcert

def TailChunk001Sub001Block008Part009SupportExplicit : Finset ℕ :=
  ([25070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part009 : ℚ :=
  (6145482565975 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk001Sub001Block008Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25070
    = surrogateDiagTailX0RatChunk001Sub001Block008Part009

theorem surrogateDiagonalTailChunk001Sub001Block008Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part009] using hcert

def TailChunk001Sub001Block008Part010SupportExplicit : Finset ℕ :=
  ([25071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part010 : ℚ :=
  (26819723101 : ℚ) / 283809846770270208

def SurrogateDiagonalTailChunk001Sub001Block008Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25071
    = surrogateDiagTailX0RatChunk001Sub001Block008Part010

theorem surrogateDiagonalTailChunk001Sub001Block008Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part010] using hcert

def TailChunk001Sub001Block008Part011SupportExplicit : Finset ℕ :=
  ([25073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part011 : ℚ :=
  (9822739515625 : ℚ) / 247014691404465119232

def SurrogateDiagonalTailChunk001Sub001Block008Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25073
    = surrogateDiagTailX0RatChunk001Sub001Block008Part011

theorem surrogateDiagonalTailChunk001Sub001Block008Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part011] using hcert

def TailChunk001Sub001Block008Part012SupportExplicit : Finset ℕ :=
  ([25077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part012 : ℚ :=
  (15101930877475 : ℚ) / 140932753787032731648

def SurrogateDiagonalTailChunk001Sub001Block008Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25077
    = surrogateDiagTailX0RatChunk001Sub001Block008Part012

theorem surrogateDiagonalTailChunk001Sub001Block008Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part012] using hcert

def TailChunk001Sub001Block008Part013SupportExplicit : Finset ℕ :=
  ([25078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part013 : ℚ :=
  (2456664390625 : ℚ) / 15448272784052670642

def SurrogateDiagonalTailChunk001Sub001Block008Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25078
    = surrogateDiagTailX0RatChunk001Sub001Block008Part013

theorem surrogateDiagonalTailChunk001Sub001Block008Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part013] using hcert

def TailChunk001Sub001Block008Part014SupportExplicit : Finset ℕ :=
  ([25079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part014 : ℚ :=
  (98504510351 : ℚ) / 2302109903393095680

def SurrogateDiagonalTailChunk001Sub001Block008Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25079
    = surrogateDiagTailX0RatChunk001Sub001Block008Part014

theorem surrogateDiagonalTailChunk001Sub001Block008Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part014] using hcert

def TailChunk001Sub001Block008Part015SupportExplicit : Finset ℕ :=
  ([25081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part015 : ℚ :=
  (3207888525025 : ℚ) / 59277745389545580672

def SurrogateDiagonalTailChunk001Sub001Block008Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25081
    = surrogateDiagTailX0RatChunk001Sub001Block008Part015

theorem surrogateDiagonalTailChunk001Sub001Block008Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part015] using hcert

def TailChunk001Sub001Block008Part016SupportExplicit : Finset ℕ :=
  ([25082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part016 : ℚ :=
  (3931917025 : ℚ) / 24733011315700512

def SurrogateDiagonalTailChunk001Sub001Block008Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25082
    = surrogateDiagTailX0RatChunk001Sub001Block008Part016

theorem surrogateDiagonalTailChunk001Sub001Block008Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part016] using hcert

def TailChunk001Sub001Block008Part017SupportExplicit : Finset ℕ :=
  ([25085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part017 : ℚ :=
  (23389663509925 : ℚ) / 344360030169578078208

def SurrogateDiagonalTailChunk001Sub001Block008Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25085
    = surrogateDiagTailX0RatChunk001Sub001Block008Part017

theorem surrogateDiagonalTailChunk001Sub001Block008Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part017] using hcert

def TailChunk001Sub001Block008Part018SupportExplicit : Finset ℕ :=
  ([25086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part018 : ℚ :=
  (4153785602725 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk001Sub001Block008Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25086
    = surrogateDiagTailX0RatChunk001Sub001Block008Part018

theorem surrogateDiagonalTailChunk001Sub001Block008Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part018] using hcert

def TailChunk001Sub001Block008Part019SupportExplicit : Finset ℕ :=
  ([25087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part019 : ℚ :=
  (9833712015625 : ℚ) / 247566877637520547602

def SurrogateDiagonalTailChunk001Sub001Block008Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25087
    = surrogateDiagTailX0RatChunk001Sub001Block008Part019

theorem surrogateDiagonalTailChunk001Sub001Block008Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part019] using hcert

def TailChunk001Sub001Block008Part020SupportExplicit : Finset ℕ :=
  ([25089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part020 : ℚ :=
  (17481385163725 : ℚ) / 195608397145695247488

def SurrogateDiagonalTailChunk001Sub001Block008Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25089
    = surrogateDiagTailX0RatChunk001Sub001Block008Part020

theorem surrogateDiagonalTailChunk001Sub001Block008Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part020] using hcert

def TailChunk001Sub001Block008Part021SupportExplicit : Finset ℕ :=
  ([25090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part021 : ℚ :=
  (1462252116175 : ℚ) / 4509586605622689792

def SurrogateDiagonalTailChunk001Sub001Block008Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25090
    = surrogateDiagTailX0RatChunk001Sub001Block008Part021

theorem surrogateDiagonalTailChunk001Sub001Block008Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part021] using hcert

def TailChunk001Sub001Block008Part022SupportExplicit : Finset ℕ :=
  ([25091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part022 : ℚ :=
  (65638638443 : ℚ) / 1351438361625600000

def SurrogateDiagonalTailChunk001Sub001Block008Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25091
    = surrogateDiagTailX0RatChunk001Sub001Block008Part022

theorem surrogateDiagonalTailChunk001Sub001Block008Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part022] using hcert

def TailChunk001Sub001Block008Part023SupportExplicit : Finset ℕ :=
  ([25093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part023 : ℚ :=
  (120571613871 : ℚ) / 2756146632704053600

def SurrogateDiagonalTailChunk001Sub001Block008Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25093
    = surrogateDiagTailX0RatChunk001Sub001Block008Part023

theorem surrogateDiagonalTailChunk001Sub001Block008Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part023] using hcert

def TailChunk001Sub001Block008Part024SupportExplicit : Finset ℕ :=
  ([25094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block008Part024 : ℚ :=
  (2459800140625 : ℚ) / 15487738254063569682

def SurrogateDiagonalTailChunk001Sub001Block008Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25094
    = surrogateDiagTailX0RatChunk001Sub001Block008Part024

theorem surrogateDiagonalTailChunk001Sub001Block008Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block008Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block008Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block008Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block008Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block008Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block008HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block008Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block008Part000
    + surrogateDiagTailX0RatChunk001Sub001Block008Part001
    + surrogateDiagTailX0RatChunk001Sub001Block008Part002
    + surrogateDiagTailX0RatChunk001Sub001Block008Part003
    + surrogateDiagTailX0RatChunk001Sub001Block008Part004
    + surrogateDiagTailX0RatChunk001Sub001Block008Part005
    + surrogateDiagTailX0RatChunk001Sub001Block008Part006
    + surrogateDiagTailX0RatChunk001Sub001Block008Part007
    + surrogateDiagTailX0RatChunk001Sub001Block008Part008
    + surrogateDiagTailX0RatChunk001Sub001Block008Part009

def surrogateDiagonalTailChunk001Sub001Block008MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block008Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block008Part010
    + surrogateDiagTailX0RatChunk001Sub001Block008Part011
    + surrogateDiagTailX0RatChunk001Sub001Block008Part012
    + surrogateDiagTailX0RatChunk001Sub001Block008Part013
    + surrogateDiagTailX0RatChunk001Sub001Block008Part014
    + surrogateDiagTailX0RatChunk001Sub001Block008Part015
    + surrogateDiagTailX0RatChunk001Sub001Block008Part016
    + surrogateDiagTailX0RatChunk001Sub001Block008Part017
    + surrogateDiagTailX0RatChunk001Sub001Block008Part018
    + surrogateDiagTailX0RatChunk001Sub001Block008Part019

def surrogateDiagonalTailChunk001Sub001Block008TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block008Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block008Part020
    + surrogateDiagTailX0RatChunk001Sub001Block008Part021
    + surrogateDiagTailX0RatChunk001Sub001Block008Part022
    + surrogateDiagTailX0RatChunk001Sub001Block008Part023
    + surrogateDiagTailX0RatChunk001Sub001Block008Part024

def surrogateDiagonalTailChunk001Sub001Block008Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block008HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block008MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block008TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block008 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block008Part000
    + surrogateDiagTailX0RatChunk001Sub001Block008Part001
    + surrogateDiagTailX0RatChunk001Sub001Block008Part002
    + surrogateDiagTailX0RatChunk001Sub001Block008Part003
    + surrogateDiagTailX0RatChunk001Sub001Block008Part004
    + surrogateDiagTailX0RatChunk001Sub001Block008Part005
    + surrogateDiagTailX0RatChunk001Sub001Block008Part006
    + surrogateDiagTailX0RatChunk001Sub001Block008Part007
    + surrogateDiagTailX0RatChunk001Sub001Block008Part008
    + surrogateDiagTailX0RatChunk001Sub001Block008Part009
    + surrogateDiagTailX0RatChunk001Sub001Block008Part010
    + surrogateDiagTailX0RatChunk001Sub001Block008Part011
    + surrogateDiagTailX0RatChunk001Sub001Block008Part012
    + surrogateDiagTailX0RatChunk001Sub001Block008Part013
    + surrogateDiagTailX0RatChunk001Sub001Block008Part014
    + surrogateDiagTailX0RatChunk001Sub001Block008Part015
    + surrogateDiagTailX0RatChunk001Sub001Block008Part016
    + surrogateDiagTailX0RatChunk001Sub001Block008Part017
    + surrogateDiagTailX0RatChunk001Sub001Block008Part018
    + surrogateDiagTailX0RatChunk001Sub001Block008Part019
    + surrogateDiagTailX0RatChunk001Sub001Block008Part020
    + surrogateDiagTailX0RatChunk001Sub001Block008Part021
    + surrogateDiagTailX0RatChunk001Sub001Block008Part022
    + surrogateDiagTailX0RatChunk001Sub001Block008Part023
    + surrogateDiagTailX0RatChunk001Sub001Block008Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block008_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block008Head + surrogateDiagTailX0RatChunk001Sub001Block008Mid + surrogateDiagTailX0RatChunk001Sub001Block008Tail =
      surrogateDiagTailX0RatChunk001Sub001Block008 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block008Head surrogateDiagTailX0RatChunk001Sub001Block008Mid surrogateDiagTailX0RatChunk001Sub001Block008Tail surrogateDiagTailX0RatChunk001Sub001Block008
  ring

def SurrogateDiagonalTailChunk001Sub001Block008HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block008HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block008Head

def SurrogateDiagonalTailChunk001Sub001Block008MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block008MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block008Mid

def SurrogateDiagonalTailChunk001Sub001Block008TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block008TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block008Tail

theorem surrogateDiagonalTailChunk001Sub001Block008_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block008HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block008MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block008TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block008Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block008 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block008HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block008MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block008TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block008Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block008_eq_head_add_mid_add_tail

/-- Block 009 covers tail-support indices [15225,15250) and q from 25095 to 25133. -/

def TailChunk001Sub001Block009Part000SupportExplicit : Finset ℕ :=
  ([25095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part000 : ℚ :=
  (1088422472975 : ℚ) / 5323651891370459136

def SurrogateDiagonalTailChunk001Sub001Block009Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25095
    = surrogateDiagTailX0RatChunk001Sub001Block009Part000

theorem surrogateDiagonalTailChunk001Sub001Block009Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part000] using hcert

def TailChunk001Sub001Block009Part001SupportExplicit : Finset ℕ :=
  ([25097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part001 : ℚ :=
  (9841553265625 : ℚ) / 247961862805153976832

def SurrogateDiagonalTailChunk001Sub001Block009Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25097
    = surrogateDiagTailX0RatChunk001Sub001Block009Part001

theorem surrogateDiagonalTailChunk001Sub001Block009Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part001] using hcert

def TailChunk001Sub001Block009Part002SupportExplicit : Finset ℕ :=
  ([25098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part002 : ℚ :=
  (2088873819875 : ℚ) / 5371293219443441664

def SurrogateDiagonalTailChunk001Sub001Block009Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25098
    = surrogateDiagTailX0RatChunk001Sub001Block009Part002

theorem surrogateDiagonalTailChunk001Sub001Block009Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part002] using hcert

def TailChunk001Sub001Block009Part003SupportExplicit : Finset ℕ :=
  ([25099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part003 : ℚ :=
  (129520417121 : ℚ) / 2897876748673843200

def SurrogateDiagonalTailChunk001Sub001Block009Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25099
    = surrogateDiagTailX0RatChunk001Sub001Block009Part003

theorem surrogateDiagonalTailChunk001Sub001Block009Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part003] using hcert

def TailChunk001Sub001Block009Part004SupportExplicit : Finset ℕ :=
  ([25102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part004 : ℚ :=
  (64701846127 : ℚ) / 223198832504332800

def SurrogateDiagonalTailChunk001Sub001Block009Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25102
    = surrogateDiagTailX0RatChunk001Sub001Block009Part004

theorem surrogateDiagonalTailChunk001Sub001Block009Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part004] using hcert

def TailChunk001Sub001Block009Part005SupportExplicit : Finset ℕ :=
  ([25103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part005 : ℚ :=
  (1359823861837 : ℚ) / 28776705378973747200

def SurrogateDiagonalTailChunk001Sub001Block009Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25103
    = surrogateDiagTailX0RatChunk001Sub001Block009Part005

theorem surrogateDiagonalTailChunk001Sub001Block009Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part005] using hcert

def TailChunk001Sub001Block009Part006SupportExplicit : Finset ℕ :=
  ([25105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part006 : ℚ :=
  (2520165025 : ℚ) / 40651979020290048

def SurrogateDiagonalTailChunk001Sub001Block009Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25105
    = surrogateDiagTailX0RatChunk001Sub001Block009Part006

theorem surrogateDiagonalTailChunk001Sub001Block009Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part006] using hcert

def TailChunk001Sub001Block009Part007SupportExplicit : Finset ℕ :=
  ([25106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part007 : ℚ :=
  (2462153265625 : ℚ) / 15517386942886973952

def SurrogateDiagonalTailChunk001Sub001Block009Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25106
    = surrogateDiagTailX0RatChunk001Sub001Block009Part007

theorem surrogateDiagonalTailChunk001Sub001Block009Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part007] using hcert

def TailChunk001Sub001Block009Part008SupportExplicit : Finset ℕ :=
  ([25107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part008 : ℚ :=
  (17506480163125 : ℚ) / 196170422586620510208

def SurrogateDiagonalTailChunk001Sub001Block009Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25107
    = surrogateDiagTailX0RatChunk001Sub001Block009Part008

theorem surrogateDiagonalTailChunk001Sub001Block009Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part008] using hcert

def TailChunk001Sub001Block009Part009SupportExplicit : Finset ℕ :=
  ([25109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part009 : ℚ :=
  (114161516461 : ℚ) / 1835720052100300800

def SurrogateDiagonalTailChunk001Sub001Block009Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25109
    = surrogateDiagTailX0RatChunk001Sub001Block009Part009

theorem surrogateDiagonalTailChunk001Sub001Block009Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part009] using hcert

def TailChunk001Sub001Block009Part010SupportExplicit : Finset ℕ :=
  ([25111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part010 : ℚ :=
  (15764058025 : ℚ) / 397625017348059282

def SurrogateDiagonalTailChunk001Sub001Block009Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25111
    = surrogateDiagTailX0RatChunk001Sub001Block009Part010

theorem surrogateDiagonalTailChunk001Sub001Block009Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part010] using hcert

def TailChunk001Sub001Block009Part011SupportExplicit : Finset ℕ :=
  ([25113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part011 : ℚ :=
  (196459791537 : ℚ) / 1779671916544000000

def SurrogateDiagonalTailChunk001Sub001Block009Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25113
    = surrogateDiagTailX0RatChunk001Sub001Block009Part011

theorem surrogateDiagonalTailChunk001Sub001Block009Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part011] using hcert

def TailChunk001Sub001Block009Part012SupportExplicit : Finset ℕ :=
  ([25114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part012 : ℚ :=
  (1031415193175 : ℚ) / 5947732968804974592

def SurrogateDiagonalTailChunk001Sub001Block009Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25114
    = surrogateDiagTailX0RatChunk001Sub001Block009Part012

theorem surrogateDiagonalTailChunk001Sub001Block009Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part012] using hcert

def TailChunk001Sub001Block009Part013SupportExplicit : Finset ℕ :=
  ([25115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part013 : ℚ :=
  (525452796875 : ℚ) / 8482667036758598016

def SurrogateDiagonalTailChunk001Sub001Block009Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25115
    = surrogateDiagTailX0RatChunk001Sub001Block009Part013

theorem surrogateDiagonalTailChunk001Sub001Block009Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part013] using hcert

def TailChunk001Sub001Block009Part014SupportExplicit : Finset ℕ :=
  ([25117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part014 : ℚ :=
  (9857245140625 : ℚ) / 248753250871198792992

def SurrogateDiagonalTailChunk001Sub001Block009Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25117
    = surrogateDiagTailX0RatChunk001Sub001Block009Part014

theorem surrogateDiagonalTailChunk001Sub001Block009Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part014] using hcert

def TailChunk001Sub001Block009Part015SupportExplicit : Finset ℕ :=
  ([25118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part015 : ℚ :=
  (179817239381 : ℚ) / 996145132356633600

def SurrogateDiagonalTailChunk001Sub001Block009Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25118
    = surrogateDiagTailX0RatChunk001Sub001Block009Part015

theorem surrogateDiagonalTailChunk001Sub001Block009Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part015] using hcert

def TailChunk001Sub001Block009Part016SupportExplicit : Finset ℕ :=
  ([25121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part016 : ℚ :=
  (15776616025 : ℚ) / 398258808841961472

def SurrogateDiagonalTailChunk001Sub001Block009Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25121
    = surrogateDiagTailX0RatChunk001Sub001Block009Part016

theorem surrogateDiagonalTailChunk001Sub001Block009Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part016] using hcert

def TailChunk001Sub001Block009Part017SupportExplicit : Finset ℕ :=
  ([25122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part017 : ℚ :=
  (1047838962775 : ℚ) / 2706940036656340992

def SurrogateDiagonalTailChunk001Sub001Block009Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25122
    = surrogateDiagTailX0RatChunk001Sub001Block009Part017

theorem surrogateDiagonalTailChunk001Sub001Block009Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part017] using hcert

def TailChunk001Sub001Block009Part018SupportExplicit : Finset ℕ :=
  ([25123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part018 : ℚ :=
  (27087308766625 : ℚ) / 462303089367038558208

def SurrogateDiagonalTailChunk001Sub001Block009Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25123
    = surrogateDiagTailX0RatChunk001Sub001Block009Part018

theorem surrogateDiagonalTailChunk001Sub001Block009Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part018] using hcert

def TailChunk001Sub001Block009Part019SupportExplicit : Finset ℕ :=
  ([25126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part019 : ℚ :=
  (4462314406175 : ℚ) / 24305370247442202624

def SurrogateDiagonalTailChunk001Sub001Block009Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25126
    = surrogateDiagTailX0RatChunk001Sub001Block009Part019

theorem surrogateDiagonalTailChunk001Sub001Block009Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part019] using hcert

def TailChunk001Sub001Block009Part020SupportExplicit : Finset ℕ :=
  ([25127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part020 : ℚ :=
  (9865095765625 : ℚ) / 249149654522940815922

def SurrogateDiagonalTailChunk001Sub001Block009Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25127
    = surrogateDiagTailX0RatChunk001Sub001Block009Part020

theorem surrogateDiagonalTailChunk001Sub001Block009Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part020] using hcert

def TailChunk001Sub001Block009Part021SupportExplicit : Finset ℕ :=
  ([25129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part021 : ℚ :=
  (1261706758675 : ℚ) / 26755715369781264384

def SurrogateDiagonalTailChunk001Sub001Block009Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25129
    = surrogateDiagTailX0RatChunk001Sub001Block009Part021

theorem surrogateDiagonalTailChunk001Sub001Block009Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part021] using hcert

def TailChunk001Sub001Block009Part022SupportExplicit : Finset ℕ :=
  ([25130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part022 : ℚ :=
  (5246573054425 : ℚ) / 13627115355673755648

def SurrogateDiagonalTailChunk001Sub001Block009Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25130
    = surrogateDiagTailX0RatChunk001Sub001Block009Part022

theorem surrogateDiagonalTailChunk001Sub001Block009Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part022] using hcert

def TailChunk001Sub001Block009Part023SupportExplicit : Finset ℕ :=
  ([25131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part023 : ℚ :=
  (17539968162325 : ℚ) / 196921672747472683008

def SurrogateDiagonalTailChunk001Sub001Block009Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25131
    = surrogateDiagTailX0RatChunk001Sub001Block009Part023

theorem surrogateDiagonalTailChunk001Sub001Block009Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part023] using hcert

def TailChunk001Sub001Block009Part024SupportExplicit : Finset ℕ :=
  ([25133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block009Part024 : ℚ :=
  (376330789837 : ℚ) / 8979920932965580800

def SurrogateDiagonalTailChunk001Sub001Block009Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 25133
    = surrogateDiagTailX0RatChunk001Sub001Block009Part024

theorem surrogateDiagonalTailChunk001Sub001Block009Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block009Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block009Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block009Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block009Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block009Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block009HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block009Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block009Part000
    + surrogateDiagTailX0RatChunk001Sub001Block009Part001
    + surrogateDiagTailX0RatChunk001Sub001Block009Part002
    + surrogateDiagTailX0RatChunk001Sub001Block009Part003
    + surrogateDiagTailX0RatChunk001Sub001Block009Part004
    + surrogateDiagTailX0RatChunk001Sub001Block009Part005
    + surrogateDiagTailX0RatChunk001Sub001Block009Part006
    + surrogateDiagTailX0RatChunk001Sub001Block009Part007
    + surrogateDiagTailX0RatChunk001Sub001Block009Part008
    + surrogateDiagTailX0RatChunk001Sub001Block009Part009

def surrogateDiagonalTailChunk001Sub001Block009MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block009Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block009Part010
    + surrogateDiagTailX0RatChunk001Sub001Block009Part011
    + surrogateDiagTailX0RatChunk001Sub001Block009Part012
    + surrogateDiagTailX0RatChunk001Sub001Block009Part013
    + surrogateDiagTailX0RatChunk001Sub001Block009Part014
    + surrogateDiagTailX0RatChunk001Sub001Block009Part015
    + surrogateDiagTailX0RatChunk001Sub001Block009Part016
    + surrogateDiagTailX0RatChunk001Sub001Block009Part017
    + surrogateDiagTailX0RatChunk001Sub001Block009Part018
    + surrogateDiagTailX0RatChunk001Sub001Block009Part019

def surrogateDiagonalTailChunk001Sub001Block009TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block009Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block009Part020
    + surrogateDiagTailX0RatChunk001Sub001Block009Part021
    + surrogateDiagTailX0RatChunk001Sub001Block009Part022
    + surrogateDiagTailX0RatChunk001Sub001Block009Part023
    + surrogateDiagTailX0RatChunk001Sub001Block009Part024

def surrogateDiagonalTailChunk001Sub001Block009Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block009HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block009MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block009TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block009 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block009Part000
    + surrogateDiagTailX0RatChunk001Sub001Block009Part001
    + surrogateDiagTailX0RatChunk001Sub001Block009Part002
    + surrogateDiagTailX0RatChunk001Sub001Block009Part003
    + surrogateDiagTailX0RatChunk001Sub001Block009Part004
    + surrogateDiagTailX0RatChunk001Sub001Block009Part005
    + surrogateDiagTailX0RatChunk001Sub001Block009Part006
    + surrogateDiagTailX0RatChunk001Sub001Block009Part007
    + surrogateDiagTailX0RatChunk001Sub001Block009Part008
    + surrogateDiagTailX0RatChunk001Sub001Block009Part009
    + surrogateDiagTailX0RatChunk001Sub001Block009Part010
    + surrogateDiagTailX0RatChunk001Sub001Block009Part011
    + surrogateDiagTailX0RatChunk001Sub001Block009Part012
    + surrogateDiagTailX0RatChunk001Sub001Block009Part013
    + surrogateDiagTailX0RatChunk001Sub001Block009Part014
    + surrogateDiagTailX0RatChunk001Sub001Block009Part015
    + surrogateDiagTailX0RatChunk001Sub001Block009Part016
    + surrogateDiagTailX0RatChunk001Sub001Block009Part017
    + surrogateDiagTailX0RatChunk001Sub001Block009Part018
    + surrogateDiagTailX0RatChunk001Sub001Block009Part019
    + surrogateDiagTailX0RatChunk001Sub001Block009Part020
    + surrogateDiagTailX0RatChunk001Sub001Block009Part021
    + surrogateDiagTailX0RatChunk001Sub001Block009Part022
    + surrogateDiagTailX0RatChunk001Sub001Block009Part023
    + surrogateDiagTailX0RatChunk001Sub001Block009Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block009_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block009Head + surrogateDiagTailX0RatChunk001Sub001Block009Mid + surrogateDiagTailX0RatChunk001Sub001Block009Tail =
      surrogateDiagTailX0RatChunk001Sub001Block009 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block009Head surrogateDiagTailX0RatChunk001Sub001Block009Mid surrogateDiagTailX0RatChunk001Sub001Block009Tail surrogateDiagTailX0RatChunk001Sub001Block009
  ring

def SurrogateDiagonalTailChunk001Sub001Block009HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block009HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block009Head

def SurrogateDiagonalTailChunk001Sub001Block009MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block009MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block009Mid

def SurrogateDiagonalTailChunk001Sub001Block009TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block009TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block009Tail

theorem surrogateDiagonalTailChunk001Sub001Block009_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block009HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block009MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block009TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block009Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block009 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block009HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block009MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block009TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block009Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block009_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
