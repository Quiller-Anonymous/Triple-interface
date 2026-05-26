import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [160,170). -/

/-- Block 160 covers tail-support indices [9000,9025) and q from 14858 to 14898. -/

def TailChunk000Sub001Block160Part000SupportExplicit : Finset ℕ :=
  ([14858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part000 : ℚ :=
  (102096852025 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk000Sub001Block160Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14858
    = surrogateDiagTailX0RatChunk000Sub001Block160Part000

theorem surrogateDiagonalTailChunk000Sub001Block160Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part000] using hcert

def TailChunk000Sub001Block160Part001SupportExplicit : Finset ℕ :=
  ([14861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part001 : ℚ :=
  (15535645883 : ℚ) / 880778633910681600

def SurrogateDiagonalTailChunk000Sub001Block160Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14861
    = surrogateDiagTailX0RatChunk000Sub001Block160Part001

theorem surrogateDiagonalTailChunk000Sub001Block160Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part001] using hcert

def TailChunk000Sub001Block160Part002SupportExplicit : Finset ℕ :=
  ([14862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part002 : ℚ :=
  (383396806475 : ℚ) / 751829577683887104

def SurrogateDiagonalTailChunk000Sub001Block160Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14862
    = surrogateDiagTailX0RatChunk000Sub001Block160Part002

theorem surrogateDiagonalTailChunk000Sub001Block160Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part002] using hcert

def TailChunk000Sub001Block160Part003SupportExplicit : Finset ℕ :=
  ([14863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part003 : ℚ :=
  (77554040275 : ℚ) / 113864908016279912448

def SurrogateDiagonalTailChunk000Sub001Block160Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14863
    = surrogateDiagTailX0RatChunk000Sub001Block160Part003

theorem surrogateDiagonalTailChunk000Sub001Block160Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part003] using hcert

def TailChunk000Sub001Block160Part004SupportExplicit : Finset ℕ :=
  ([14865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part004 : ℚ :=
  (11292519791 : ℚ) / 78707763544227840

def SurrogateDiagonalTailChunk000Sub001Block160Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14865
    = surrogateDiagTailX0RatChunk000Sub001Block160Part004

theorem surrogateDiagonalTailChunk000Sub001Block160Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part004] using hcert

def TailChunk000Sub001Block160Part005SupportExplicit : Finset ℕ :=
  ([14866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block160Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14866
    = surrogateDiagTailX0RatChunk000Sub001Block160Part005

theorem surrogateDiagonalTailChunk000Sub001Block160Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part005] using hcert

def TailChunk000Sub001Block160Part006SupportExplicit : Finset ℕ :=
  ([14867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block160Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14867
    = surrogateDiagTailX0RatChunk000Sub001Block160Part006

theorem surrogateDiagonalTailChunk000Sub001Block160Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part006] using hcert

def TailChunk000Sub001Block160Part007SupportExplicit : Finset ℕ :=
  ([14869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block160Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14869
    = surrogateDiagTailX0RatChunk000Sub001Block160Part007

theorem surrogateDiagonalTailChunk000Sub001Block160Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part007] using hcert

def TailChunk000Sub001Block160Part008SupportExplicit : Finset ℕ :=
  ([14870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part008 : ℚ :=
  (25945088575 : ℚ) / 195084192013235328

def SurrogateDiagonalTailChunk000Sub001Block160Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14870
    = surrogateDiagTailX0RatChunk000Sub001Block160Part008

theorem surrogateDiagonalTailChunk000Sub001Block160Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part008] using hcert

def TailChunk000Sub001Block160Part009SupportExplicit : Finset ℕ :=
  ([14871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part009 : ℚ :=
  (1958859775 : ℚ) / 30786191724903552

def SurrogateDiagonalTailChunk000Sub001Block160Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14871
    = surrogateDiagTailX0RatChunk000Sub001Block160Part009

theorem surrogateDiagonalTailChunk000Sub001Block160Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part009] using hcert

def TailChunk000Sub001Block160Part010SupportExplicit : Finset ℕ :=
  ([14873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part010 : ℚ :=
  (75860844625 : ℚ) / 114489765422538265728

def SurrogateDiagonalTailChunk000Sub001Block160Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14873
    = surrogateDiagTailX0RatChunk000Sub001Block160Part010

theorem surrogateDiagonalTailChunk000Sub001Block160Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part010] using hcert

def TailChunk000Sub001Block160Part011SupportExplicit : Finset ℕ :=
  ([14874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part011 : ℚ :=
  (34914471925 : ℚ) / 57957534973476864

def SurrogateDiagonalTailChunk000Sub001Block160Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14874
    = surrogateDiagTailX0RatChunk000Sub001Block160Part011

theorem surrogateDiagonalTailChunk000Sub001Block160Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part011] using hcert

def TailChunk000Sub001Block160Part012SupportExplicit : Finset ℕ :=
  ([14878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part012 : ℚ :=
  (66518649625 : ℚ) / 6809854112240191488

def SurrogateDiagonalTailChunk000Sub001Block160Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14878
    = surrogateDiagTailX0RatChunk000Sub001Block160Part012

theorem surrogateDiagonalTailChunk000Sub001Block160Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part012] using hcert

def TailChunk000Sub001Block160Part013SupportExplicit : Finset ℕ :=
  ([14879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block160Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14879
    = surrogateDiagTailX0RatChunk000Sub001Block160Part013

theorem surrogateDiagonalTailChunk000Sub001Block160Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part013] using hcert

def TailChunk000Sub001Block160Part014SupportExplicit : Finset ℕ :=
  ([14881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part014 : ℚ :=
  (17935854975 : ℚ) / 8500929374891450464

def SurrogateDiagonalTailChunk000Sub001Block160Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14881
    = surrogateDiagTailX0RatChunk000Sub001Block160Part014

theorem surrogateDiagonalTailChunk000Sub001Block160Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part014] using hcert

def TailChunk000Sub001Block160Part015SupportExplicit : Finset ℕ :=
  ([14882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part015 : ℚ :=
  (354043523275 : ℚ) / 4122208243001881728

def SurrogateDiagonalTailChunk000Sub001Block160Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14882
    = surrogateDiagTailX0RatChunk000Sub001Block160Part015

theorem surrogateDiagonalTailChunk000Sub001Block160Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part015] using hcert

def TailChunk000Sub001Block160Part016SupportExplicit : Finset ℕ :=
  ([14885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part016 : ℚ :=
  (629529530975 : ℚ) / 17934992554667802624

def SurrogateDiagonalTailChunk000Sub001Block160Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14885
    = surrogateDiagTailX0RatChunk000Sub001Block160Part016

theorem surrogateDiagonalTailChunk000Sub001Block160Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part016] using hcert

def TailChunk000Sub001Block160Part017SupportExplicit : Finset ℕ :=
  ([14887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block160Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14887
    = surrogateDiagTailX0RatChunk000Sub001Block160Part017

theorem surrogateDiagonalTailChunk000Sub001Block160Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part017] using hcert

def TailChunk000Sub001Block160Part018SupportExplicit : Finset ℕ :=
  ([14889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part018 : ℚ :=
  (167512575125 : ℚ) / 1447579300697505792

def SurrogateDiagonalTailChunk000Sub001Block160Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14889
    = surrogateDiagTailX0RatChunk000Sub001Block160Part018

theorem surrogateDiagonalTailChunk000Sub001Block160Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part018] using hcert

def TailChunk000Sub001Block160Part019SupportExplicit : Finset ℕ :=
  ([14890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part019 : ℚ :=
  (277226843675 : ℚ) / 1569092524629295104

def SurrogateDiagonalTailChunk000Sub001Block160Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14890
    = surrogateDiagTailX0RatChunk000Sub001Block160Part019

theorem surrogateDiagonalTailChunk000Sub001Block160Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part019] using hcert

def TailChunk000Sub001Block160Part020SupportExplicit : Finset ℕ :=
  ([14891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block160Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14891
    = surrogateDiagTailX0RatChunk000Sub001Block160Part020

theorem surrogateDiagonalTailChunk000Sub001Block160Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part020] using hcert

def TailChunk000Sub001Block160Part021SupportExplicit : Finset ℕ :=
  ([14893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part021 : ℚ :=
  (148939009 : ℚ) / 160536695350886400

def SurrogateDiagonalTailChunk000Sub001Block160Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14893
    = surrogateDiagTailX0RatChunk000Sub001Block160Part021

theorem surrogateDiagonalTailChunk000Sub001Block160Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part021] using hcert

def TailChunk000Sub001Block160Part022SupportExplicit : Finset ℕ :=
  ([14894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part022 : ℚ :=
  (2704184637 : ℚ) / 69622943329638400

def SurrogateDiagonalTailChunk000Sub001Block160Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14894
    = surrogateDiagTailX0RatChunk000Sub001Block160Part022

theorem surrogateDiagonalTailChunk000Sub001Block160Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part022] using hcert

def TailChunk000Sub001Block160Part023SupportExplicit : Finset ℕ :=
  ([14897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block160Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14897
    = surrogateDiagTailX0RatChunk000Sub001Block160Part023

theorem surrogateDiagonalTailChunk000Sub001Block160Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part023] using hcert

def TailChunk000Sub001Block160Part024SupportExplicit : Finset ℕ :=
  ([14898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block160Part024 : ℚ :=
  (30886773397 : ℚ) / 43246027572019200

def SurrogateDiagonalTailChunk000Sub001Block160Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14898
    = surrogateDiagTailX0RatChunk000Sub001Block160Part024

theorem surrogateDiagonalTailChunk000Sub001Block160Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block160Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block160Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block160Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block160Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block160Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block160Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block160HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block160Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block160Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block160Part000
    + surrogateDiagTailX0RatChunk000Sub001Block160Part001
    + surrogateDiagTailX0RatChunk000Sub001Block160Part002
    + surrogateDiagTailX0RatChunk000Sub001Block160Part003
    + surrogateDiagTailX0RatChunk000Sub001Block160Part004
    + surrogateDiagTailX0RatChunk000Sub001Block160Part005
    + surrogateDiagTailX0RatChunk000Sub001Block160Part006
    + surrogateDiagTailX0RatChunk000Sub001Block160Part007
    + surrogateDiagTailX0RatChunk000Sub001Block160Part008
    + surrogateDiagTailX0RatChunk000Sub001Block160Part009

def surrogateDiagonalTailChunk000Sub001Block160MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block160Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block160Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block160Part010
    + surrogateDiagTailX0RatChunk000Sub001Block160Part011
    + surrogateDiagTailX0RatChunk000Sub001Block160Part012
    + surrogateDiagTailX0RatChunk000Sub001Block160Part013
    + surrogateDiagTailX0RatChunk000Sub001Block160Part014
    + surrogateDiagTailX0RatChunk000Sub001Block160Part015
    + surrogateDiagTailX0RatChunk000Sub001Block160Part016
    + surrogateDiagTailX0RatChunk000Sub001Block160Part017
    + surrogateDiagTailX0RatChunk000Sub001Block160Part018
    + surrogateDiagTailX0RatChunk000Sub001Block160Part019

def surrogateDiagonalTailChunk000Sub001Block160TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block160Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block160Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block160Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block160Part020
    + surrogateDiagTailX0RatChunk000Sub001Block160Part021
    + surrogateDiagTailX0RatChunk000Sub001Block160Part022
    + surrogateDiagTailX0RatChunk000Sub001Block160Part023
    + surrogateDiagTailX0RatChunk000Sub001Block160Part024

def surrogateDiagonalTailChunk000Sub001Block160Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block160HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block160MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block160TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block160 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block160Part000
    + surrogateDiagTailX0RatChunk000Sub001Block160Part001
    + surrogateDiagTailX0RatChunk000Sub001Block160Part002
    + surrogateDiagTailX0RatChunk000Sub001Block160Part003
    + surrogateDiagTailX0RatChunk000Sub001Block160Part004
    + surrogateDiagTailX0RatChunk000Sub001Block160Part005
    + surrogateDiagTailX0RatChunk000Sub001Block160Part006
    + surrogateDiagTailX0RatChunk000Sub001Block160Part007
    + surrogateDiagTailX0RatChunk000Sub001Block160Part008
    + surrogateDiagTailX0RatChunk000Sub001Block160Part009
    + surrogateDiagTailX0RatChunk000Sub001Block160Part010
    + surrogateDiagTailX0RatChunk000Sub001Block160Part011
    + surrogateDiagTailX0RatChunk000Sub001Block160Part012
    + surrogateDiagTailX0RatChunk000Sub001Block160Part013
    + surrogateDiagTailX0RatChunk000Sub001Block160Part014
    + surrogateDiagTailX0RatChunk000Sub001Block160Part015
    + surrogateDiagTailX0RatChunk000Sub001Block160Part016
    + surrogateDiagTailX0RatChunk000Sub001Block160Part017
    + surrogateDiagTailX0RatChunk000Sub001Block160Part018
    + surrogateDiagTailX0RatChunk000Sub001Block160Part019
    + surrogateDiagTailX0RatChunk000Sub001Block160Part020
    + surrogateDiagTailX0RatChunk000Sub001Block160Part021
    + surrogateDiagTailX0RatChunk000Sub001Block160Part022
    + surrogateDiagTailX0RatChunk000Sub001Block160Part023
    + surrogateDiagTailX0RatChunk000Sub001Block160Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block160_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block160Head + surrogateDiagTailX0RatChunk000Sub001Block160Mid + surrogateDiagTailX0RatChunk000Sub001Block160Tail =
      surrogateDiagTailX0RatChunk000Sub001Block160 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block160Head surrogateDiagTailX0RatChunk000Sub001Block160Mid surrogateDiagTailX0RatChunk000Sub001Block160Tail surrogateDiagTailX0RatChunk000Sub001Block160
  ring

def SurrogateDiagonalTailChunk000Sub001Block160HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block160HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block160Head

def SurrogateDiagonalTailChunk000Sub001Block160MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block160MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block160Mid

def SurrogateDiagonalTailChunk000Sub001Block160TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block160TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block160Tail

theorem surrogateDiagonalTailChunk000Sub001Block160_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block160HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block160MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block160TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block160Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block160 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block160HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block160MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block160TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block160Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block160_eq_head_add_mid_add_tail

/-- Block 161 covers tail-support indices [9025,9050) and q from 14899 to 14937. -/

def TailChunk000Sub001Block161Part000SupportExplicit : Finset ℕ :=
  ([14899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part000 : ℚ :=
  (113883113275 : ℚ) / 111636578130374903808

def SurrogateDiagonalTailChunk000Sub001Block161Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14899
    = surrogateDiagTailX0RatChunk000Sub001Block161Part000

theorem surrogateDiagonalTailChunk000Sub001Block161Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part000] using hcert

def TailChunk000Sub001Block161Part001SupportExplicit : Finset ℕ :=
  ([14901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part001 : ℚ :=
  (770973656675 : ℚ) / 12165884995587745344

def SurrogateDiagonalTailChunk000Sub001Block161Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14901
    = surrogateDiagTailX0RatChunk000Sub001Block161Part001

theorem surrogateDiagonalTailChunk000Sub001Block161Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part001] using hcert

def TailChunk000Sub001Block161Part002SupportExplicit : Finset ℕ :=
  ([14902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block161Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14902
    = surrogateDiagTailX0RatChunk000Sub001Block161Part002

theorem surrogateDiagonalTailChunk000Sub001Block161Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part002] using hcert

def TailChunk000Sub001Block161Part003SupportExplicit : Finset ℕ :=
  ([14903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part003 : ℚ :=
  (964407025 : ℚ) / 75344190258806784

def SurrogateDiagonalTailChunk000Sub001Block161Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14903
    = surrogateDiagTailX0RatChunk000Sub001Block161Part003

theorem surrogateDiagonalTailChunk000Sub001Block161Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part003] using hcert

def TailChunk000Sub001Block161Part004SupportExplicit : Finset ℕ :=
  ([14905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part004 : ℚ :=
  (1068077009 : ℚ) / 30239134617600000

def SurrogateDiagonalTailChunk000Sub001Block161Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14905
    = surrogateDiagTailX0RatChunk000Sub001Block161Part004

theorem surrogateDiagonalTailChunk000Sub001Block161Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part004] using hcert

def TailChunk000Sub001Block161Part005SupportExplicit : Finset ℕ :=
  ([14906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part005 : ℚ :=
  (86273474275 : ℚ) / 6601138509434585088

def SurrogateDiagonalTailChunk000Sub001Block161Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14906
    = surrogateDiagTailX0RatChunk000Sub001Block161Part005

theorem surrogateDiagonalTailChunk000Sub001Block161Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part005] using hcert

def TailChunk000Sub001Block161Part006SupportExplicit : Finset ℕ :=
  ([14907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part006 : ℚ :=
  (385797265825 : ℚ) / 6092747762777137152

def SurrogateDiagonalTailChunk000Sub001Block161Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14907
    = surrogateDiagTailX0RatChunk000Sub001Block161Part006

theorem surrogateDiagonalTailChunk000Sub001Block161Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part006] using hcert

def TailChunk000Sub001Block161Part007SupportExplicit : Finset ℕ :=
  ([14909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part007 : ℚ :=
  (244611811525 : ℚ) / 96499089172246560768

def SurrogateDiagonalTailChunk000Sub001Block161Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14909
    = surrogateDiagTailX0RatChunk000Sub001Block161Part007

theorem surrogateDiagonalTailChunk000Sub001Block161Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part007] using hcert

def TailChunk000Sub001Block161Part008SupportExplicit : Finset ℕ :=
  ([14910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part008 : ℚ :=
  (176726393 : ℚ) / 78691703193600

def SurrogateDiagonalTailChunk000Sub001Block161Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14910
    = surrogateDiagTailX0RatChunk000Sub001Block161Part008

theorem surrogateDiagonalTailChunk000Sub001Block161Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part008] using hcert

def TailChunk000Sub001Block161Part009SupportExplicit : Finset ℕ :=
  ([14911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part009 : ℚ :=
  (485948333 : ℚ) / 56433482588749824

def SurrogateDiagonalTailChunk000Sub001Block161Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14911
    = surrogateDiagTailX0RatChunk000Sub001Block161Part009

theorem surrogateDiagonalTailChunk000Sub001Block161Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part009] using hcert

def TailChunk000Sub001Block161Part010SupportExplicit : Finset ℕ :=
  ([14914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block161Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14914
    = surrogateDiagTailX0RatChunk000Sub001Block161Part010

theorem surrogateDiagonalTailChunk000Sub001Block161Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part010] using hcert

def TailChunk000Sub001Block161Part011SupportExplicit : Finset ℕ :=
  ([14915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part011 : ℚ :=
  (1212935097925 : ℚ) / 39797449289315647488

def SurrogateDiagonalTailChunk000Sub001Block161Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14915
    = surrogateDiagTailX0RatChunk000Sub001Block161Part011

theorem surrogateDiagonalTailChunk000Sub001Block161Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part011] using hcert

def TailChunk000Sub001Block161Part012SupportExplicit : Finset ℕ :=
  ([14917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part012 : ℚ :=
  (11377477427 : ℚ) / 1334075073990465600

def SurrogateDiagonalTailChunk000Sub001Block161Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14917
    = surrogateDiagTailX0RatChunk000Sub001Block161Part012

theorem surrogateDiagonalTailChunk000Sub001Block161Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part012] using hcert

def TailChunk000Sub001Block161Part013SupportExplicit : Finset ℕ :=
  ([14918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block161Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14918
    = surrogateDiagTailX0RatChunk000Sub001Block161Part013

theorem surrogateDiagonalTailChunk000Sub001Block161Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part013] using hcert

def TailChunk000Sub001Block161Part014SupportExplicit : Finset ℕ :=
  ([14919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part014 : ℚ :=
  (48302314475 : ℚ) / 764049231258713664

def SurrogateDiagonalTailChunk000Sub001Block161Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14919
    = surrogateDiagTailX0RatChunk000Sub001Block161Part014

theorem surrogateDiagonalTailChunk000Sub001Block161Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part014] using hcert

def TailChunk000Sub001Block161Part015SupportExplicit : Finset ℕ :=
  ([14921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part015 : ℚ :=
  (2317033975 : ℚ) / 2065069421001300672

def SurrogateDiagonalTailChunk000Sub001Block161Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14921
    = surrogateDiagTailX0RatChunk000Sub001Block161Part015

theorem surrogateDiagonalTailChunk000Sub001Block161Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part015] using hcert

def TailChunk000Sub001Block161Part016SupportExplicit : Finset ℕ :=
  ([14923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block161Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14923
    = surrogateDiagTailX0RatChunk000Sub001Block161Part016

theorem surrogateDiagonalTailChunk000Sub001Block161Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part016] using hcert

def TailChunk000Sub001Block161Part017SupportExplicit : Finset ℕ :=
  ([14926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part017 : ℚ :=
  (200434945975 : ℚ) / 376949567079088128

def SurrogateDiagonalTailChunk000Sub001Block161Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14926
    = surrogateDiagTailX0RatChunk000Sub001Block161Part017

theorem surrogateDiagonalTailChunk000Sub001Block161Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part017] using hcert

def TailChunk000Sub001Block161Part018SupportExplicit : Finset ℕ :=
  ([14927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part018 : ℚ :=
  (4397310747 : ℚ) / 441914546398899200

def SurrogateDiagonalTailChunk000Sub001Block161Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14927
    = surrogateDiagTailX0RatChunk000Sub001Block161Part018

theorem surrogateDiagonalTailChunk000Sub001Block161Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part018] using hcert

def TailChunk000Sub001Block161Part019SupportExplicit : Finset ℕ :=
  ([14929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block161Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14929
    = surrogateDiagTailX0RatChunk000Sub001Block161Part019

theorem surrogateDiagonalTailChunk000Sub001Block161Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part019] using hcert

def TailChunk000Sub001Block161Part020SupportExplicit : Finset ℕ :=
  ([14930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part020 : ℚ :=
  (1322601019325 : ℚ) / 1586032641370374144

def SurrogateDiagonalTailChunk000Sub001Block161Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14930
    = surrogateDiagTailX0RatChunk000Sub001Block161Part020

theorem surrogateDiagonalTailChunk000Sub001Block161Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part020] using hcert

def TailChunk000Sub001Block161Part021SupportExplicit : Finset ℕ :=
  ([14933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part021 : ℚ :=
  (25435287875 : ℚ) / 38793258430411309056

def SurrogateDiagonalTailChunk000Sub001Block161Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14933
    = surrogateDiagTailX0RatChunk000Sub001Block161Part021

theorem surrogateDiagonalTailChunk000Sub001Block161Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part021] using hcert

def TailChunk000Sub001Block161Part022SupportExplicit : Finset ℕ :=
  ([14934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part022 : ℚ :=
  (14363442881 : ℚ) / 9596221375703040

def SurrogateDiagonalTailChunk000Sub001Block161Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14934
    = surrogateDiagTailX0RatChunk000Sub001Block161Part022

theorem surrogateDiagonalTailChunk000Sub001Block161Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part022] using hcert

def TailChunk000Sub001Block161Part023SupportExplicit : Finset ℕ :=
  ([14935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part023 : ℚ :=
  (168760794625 : ℚ) / 6084173590137667584

def SurrogateDiagonalTailChunk000Sub001Block161Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14935
    = surrogateDiagTailX0RatChunk000Sub001Block161Part023

theorem surrogateDiagonalTailChunk000Sub001Block161Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part023] using hcert

def TailChunk000Sub001Block161Part024SupportExplicit : Finset ℕ :=
  ([14937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block161Part024 : ℚ :=
  (192466868975 : ℚ) / 2208184160818139136

def SurrogateDiagonalTailChunk000Sub001Block161Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14937
    = surrogateDiagTailX0RatChunk000Sub001Block161Part024

theorem surrogateDiagonalTailChunk000Sub001Block161Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block161Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block161Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block161Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block161Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block161Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block161Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block161HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block161Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block161Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block161Part000
    + surrogateDiagTailX0RatChunk000Sub001Block161Part001
    + surrogateDiagTailX0RatChunk000Sub001Block161Part002
    + surrogateDiagTailX0RatChunk000Sub001Block161Part003
    + surrogateDiagTailX0RatChunk000Sub001Block161Part004
    + surrogateDiagTailX0RatChunk000Sub001Block161Part005
    + surrogateDiagTailX0RatChunk000Sub001Block161Part006
    + surrogateDiagTailX0RatChunk000Sub001Block161Part007
    + surrogateDiagTailX0RatChunk000Sub001Block161Part008
    + surrogateDiagTailX0RatChunk000Sub001Block161Part009

def surrogateDiagonalTailChunk000Sub001Block161MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block161Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block161Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block161Part010
    + surrogateDiagTailX0RatChunk000Sub001Block161Part011
    + surrogateDiagTailX0RatChunk000Sub001Block161Part012
    + surrogateDiagTailX0RatChunk000Sub001Block161Part013
    + surrogateDiagTailX0RatChunk000Sub001Block161Part014
    + surrogateDiagTailX0RatChunk000Sub001Block161Part015
    + surrogateDiagTailX0RatChunk000Sub001Block161Part016
    + surrogateDiagTailX0RatChunk000Sub001Block161Part017
    + surrogateDiagTailX0RatChunk000Sub001Block161Part018
    + surrogateDiagTailX0RatChunk000Sub001Block161Part019

def surrogateDiagonalTailChunk000Sub001Block161TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block161Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block161Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block161Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block161Part020
    + surrogateDiagTailX0RatChunk000Sub001Block161Part021
    + surrogateDiagTailX0RatChunk000Sub001Block161Part022
    + surrogateDiagTailX0RatChunk000Sub001Block161Part023
    + surrogateDiagTailX0RatChunk000Sub001Block161Part024

def surrogateDiagonalTailChunk000Sub001Block161Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block161HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block161MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block161TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block161 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block161Part000
    + surrogateDiagTailX0RatChunk000Sub001Block161Part001
    + surrogateDiagTailX0RatChunk000Sub001Block161Part002
    + surrogateDiagTailX0RatChunk000Sub001Block161Part003
    + surrogateDiagTailX0RatChunk000Sub001Block161Part004
    + surrogateDiagTailX0RatChunk000Sub001Block161Part005
    + surrogateDiagTailX0RatChunk000Sub001Block161Part006
    + surrogateDiagTailX0RatChunk000Sub001Block161Part007
    + surrogateDiagTailX0RatChunk000Sub001Block161Part008
    + surrogateDiagTailX0RatChunk000Sub001Block161Part009
    + surrogateDiagTailX0RatChunk000Sub001Block161Part010
    + surrogateDiagTailX0RatChunk000Sub001Block161Part011
    + surrogateDiagTailX0RatChunk000Sub001Block161Part012
    + surrogateDiagTailX0RatChunk000Sub001Block161Part013
    + surrogateDiagTailX0RatChunk000Sub001Block161Part014
    + surrogateDiagTailX0RatChunk000Sub001Block161Part015
    + surrogateDiagTailX0RatChunk000Sub001Block161Part016
    + surrogateDiagTailX0RatChunk000Sub001Block161Part017
    + surrogateDiagTailX0RatChunk000Sub001Block161Part018
    + surrogateDiagTailX0RatChunk000Sub001Block161Part019
    + surrogateDiagTailX0RatChunk000Sub001Block161Part020
    + surrogateDiagTailX0RatChunk000Sub001Block161Part021
    + surrogateDiagTailX0RatChunk000Sub001Block161Part022
    + surrogateDiagTailX0RatChunk000Sub001Block161Part023
    + surrogateDiagTailX0RatChunk000Sub001Block161Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block161_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block161Head + surrogateDiagTailX0RatChunk000Sub001Block161Mid + surrogateDiagTailX0RatChunk000Sub001Block161Tail =
      surrogateDiagTailX0RatChunk000Sub001Block161 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block161Head surrogateDiagTailX0RatChunk000Sub001Block161Mid surrogateDiagTailX0RatChunk000Sub001Block161Tail surrogateDiagTailX0RatChunk000Sub001Block161
  ring

def SurrogateDiagonalTailChunk000Sub001Block161HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block161HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block161Head

def SurrogateDiagonalTailChunk000Sub001Block161MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block161MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block161Mid

def SurrogateDiagonalTailChunk000Sub001Block161TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block161TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block161Tail

theorem surrogateDiagonalTailChunk000Sub001Block161_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block161HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block161MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block161TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block161Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block161 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block161HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block161MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block161TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block161Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block161_eq_head_add_mid_add_tail

/-- Block 162 covers tail-support indices [9050,9075) and q from 14938 to 14978. -/

def TailChunk000Sub001Block162Part000SupportExplicit : Finset ℕ :=
  ([14938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part000 : ℚ :=
  (386086411 : ℚ) / 430067692339200

def SurrogateDiagonalTailChunk000Sub001Block162Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14938
    = surrogateDiagTailX0RatChunk000Sub001Block162Part000

theorem surrogateDiagonalTailChunk000Sub001Block162Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part000] using hcert

def TailChunk000Sub001Block162Part001SupportExplicit : Finset ℕ :=
  ([14939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block162Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14939
    = surrogateDiagTailX0RatChunk000Sub001Block162Part001

theorem surrogateDiagonalTailChunk000Sub001Block162Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part001] using hcert

def TailChunk000Sub001Block162Part002SupportExplicit : Finset ℕ :=
  ([14941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part002 : ℚ :=
  (22051159225 : ℚ) / 28810746256213592352

def SurrogateDiagonalTailChunk000Sub001Block162Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14941
    = surrogateDiagTailX0RatChunk000Sub001Block162Part002

theorem surrogateDiagonalTailChunk000Sub001Block162Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part002] using hcert

def TailChunk000Sub001Block162Part003SupportExplicit : Finset ℕ :=
  ([14942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part003 : ℚ :=
  (13287569221 : ℚ) / 26879230771200000

def SurrogateDiagonalTailChunk000Sub001Block162Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14942
    = surrogateDiagTailX0RatChunk000Sub001Block162Part003

theorem surrogateDiagonalTailChunk000Sub001Block162Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part003] using hcert

def TailChunk000Sub001Block162Part004SupportExplicit : Finset ℕ :=
  ([14943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part004 : ℚ :=
  (16201579575 : ℚ) / 198557796650713088

def SurrogateDiagonalTailChunk000Sub001Block162Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14943
    = surrogateDiagTailX0RatChunk000Sub001Block162Part004

theorem surrogateDiagonalTailChunk000Sub001Block162Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part004] using hcert

def TailChunk000Sub001Block162Part005SupportExplicit : Finset ℕ :=
  ([14946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part005 : ℚ :=
  (923795040875 : ℚ) / 654879728333635584

def SurrogateDiagonalTailChunk000Sub001Block162Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14946
    = surrogateDiagTailX0RatChunk000Sub001Block162Part005

theorem surrogateDiagonalTailChunk000Sub001Block162Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part005] using hcert

def TailChunk000Sub001Block162Part006SupportExplicit : Finset ℕ :=
  ([14947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block162Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14947
    = surrogateDiagTailX0RatChunk000Sub001Block162Part006

theorem surrogateDiagonalTailChunk000Sub001Block162Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part006] using hcert

def TailChunk000Sub001Block162Part007SupportExplicit : Finset ℕ :=
  ([14951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block162Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14951
    = surrogateDiagTailX0RatChunk000Sub001Block162Part007

theorem surrogateDiagonalTailChunk000Sub001Block162Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part007] using hcert

def TailChunk000Sub001Block162Part008SupportExplicit : Finset ℕ :=
  ([14953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part008 : ℚ :=
  (118532107475 : ℚ) / 50093003002452554304

def SurrogateDiagonalTailChunk000Sub001Block162Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14953
    = surrogateDiagTailX0RatChunk000Sub001Block162Part008

theorem surrogateDiagonalTailChunk000Sub001Block162Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part008] using hcert

def TailChunk000Sub001Block162Part009SupportExplicit : Finset ℕ :=
  ([14954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part009 : ℚ :=
  (873523890625 : ℚ) / 1952738273068061472

def SurrogateDiagonalTailChunk000Sub001Block162Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14954
    = surrogateDiagTailX0RatChunk000Sub001Block162Part009

theorem surrogateDiagonalTailChunk000Sub001Block162Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part009] using hcert

def TailChunk000Sub001Block162Part010SupportExplicit : Finset ℕ :=
  ([14955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part010 : ℚ :=
  (1428696312325 : ℚ) / 10079155849265676288

def SurrogateDiagonalTailChunk000Sub001Block162Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14955
    = surrogateDiagTailX0RatChunk000Sub001Block162Part010

theorem surrogateDiagonalTailChunk000Sub001Block162Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part010] using hcert

def TailChunk000Sub001Block162Part011SupportExplicit : Finset ℕ :=
  ([14957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block162Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14957
    = surrogateDiagTailX0RatChunk000Sub001Block162Part011

theorem surrogateDiagonalTailChunk000Sub001Block162Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part011] using hcert

def TailChunk000Sub001Block162Part012SupportExplicit : Finset ℕ :=
  ([14959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part012 : ℚ :=
  (15870378475 : ℚ) / 1249231981437960192

def SurrogateDiagonalTailChunk000Sub001Block162Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14959
    = surrogateDiagTailX0RatChunk000Sub001Block162Part012

theorem surrogateDiagonalTailChunk000Sub001Block162Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part012] using hcert

def TailChunk000Sub001Block162Part013SupportExplicit : Finset ℕ :=
  ([14961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part013 : ℚ :=
  (777193656425 : ℚ) / 12363059020548953664

def SurrogateDiagonalTailChunk000Sub001Block162Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14961
    = surrogateDiagTailX0RatChunk000Sub001Block162Part013

theorem surrogateDiagonalTailChunk000Sub001Block162Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part013] using hcert

def TailChunk000Sub001Block162Part014SupportExplicit : Finset ℕ :=
  ([14962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part014 : ℚ :=
  (1399134025 : ℚ) / 3131073349612032

def SurrogateDiagonalTailChunk000Sub001Block162Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14962
    = surrogateDiagTailX0RatChunk000Sub001Block162Part014

theorem surrogateDiagonalTailChunk000Sub001Block162Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part014] using hcert

def TailChunk000Sub001Block162Part015SupportExplicit : Finset ℕ :=
  ([14963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part015 : ℚ :=
  (2227864699 : ℚ) / 604577451312000000

def SurrogateDiagonalTailChunk000Sub001Block162Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14963
    = surrogateDiagTailX0RatChunk000Sub001Block162Part015

theorem surrogateDiagonalTailChunk000Sub001Block162Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part015] using hcert

def TailChunk000Sub001Block162Part016SupportExplicit : Finset ℕ :=
  ([14965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part016 : ℚ :=
  (6574665427 : ℚ) / 440389316955340800

def SurrogateDiagonalTailChunk000Sub001Block162Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14965
    = surrogateDiagTailX0RatChunk000Sub001Block162Part016

theorem surrogateDiagonalTailChunk000Sub001Block162Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part016] using hcert

def TailChunk000Sub001Block162Part017SupportExplicit : Finset ℕ :=
  ([14966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part017 : ℚ :=
  (2853945325375 : ℚ) / 4216157937353115648

def SurrogateDiagonalTailChunk000Sub001Block162Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14966
    = surrogateDiagTailX0RatChunk000Sub001Block162Part017

theorem surrogateDiagonalTailChunk000Sub001Block162Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part017] using hcert

def TailChunk000Sub001Block162Part018SupportExplicit : Finset ℕ :=
  ([14969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block162Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14969
    = surrogateDiagTailX0RatChunk000Sub001Block162Part018

theorem surrogateDiagonalTailChunk000Sub001Block162Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part018] using hcert

def TailChunk000Sub001Block162Part019SupportExplicit : Finset ℕ :=
  ([14970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part019 : ℚ :=
  (729848426675 : ℚ) / 314973620289552384

def SurrogateDiagonalTailChunk000Sub001Block162Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14970
    = surrogateDiagTailX0RatChunk000Sub001Block162Part019

theorem surrogateDiagonalTailChunk000Sub001Block162Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part019] using hcert

def TailChunk000Sub001Block162Part020SupportExplicit : Finset ℕ :=
  ([14971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part020 : ℚ :=
  (6203329623 : ℚ) / 1140568121344000000

def SurrogateDiagonalTailChunk000Sub001Block162Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14971
    = surrogateDiagTailX0RatChunk000Sub001Block162Part020

theorem surrogateDiagonalTailChunk000Sub001Block162Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part020] using hcert

def TailChunk000Sub001Block162Part021SupportExplicit : Finset ℕ :=
  ([14973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part021 : ℚ :=
  (6977359313 : ℚ) / 43726535302348800

def SurrogateDiagonalTailChunk000Sub001Block162Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14973
    = surrogateDiagTailX0RatChunk000Sub001Block162Part021

theorem surrogateDiagonalTailChunk000Sub001Block162Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part021] using hcert

def TailChunk000Sub001Block162Part022SupportExplicit : Finset ℕ :=
  ([14974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part022 : ℚ :=
  (875862015625 : ℚ) / 1963207292769974802

def SurrogateDiagonalTailChunk000Sub001Block162Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14974
    = surrogateDiagTailX0RatChunk000Sub001Block162Part022

theorem surrogateDiagonalTailChunk000Sub001Block162Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part022] using hcert

def TailChunk000Sub001Block162Part023SupportExplicit : Finset ℕ :=
  ([14977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part023 : ℚ :=
  (178853343 : ℚ) / 59559841575731200

def SurrogateDiagonalTailChunk000Sub001Block162Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14977
    = surrogateDiagTailX0RatChunk000Sub001Block162Part023

theorem surrogateDiagonalTailChunk000Sub001Block162Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part023] using hcert

def TailChunk000Sub001Block162Part024SupportExplicit : Finset ℕ :=
  ([14978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block162Part024 : ℚ :=
  (876330015625 : ℚ) / 1965306137743982592

def SurrogateDiagonalTailChunk000Sub001Block162Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14978
    = surrogateDiagTailX0RatChunk000Sub001Block162Part024

theorem surrogateDiagonalTailChunk000Sub001Block162Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block162Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block162Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block162Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block162Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block162Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block162Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block162HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block162Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block162Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block162Part000
    + surrogateDiagTailX0RatChunk000Sub001Block162Part001
    + surrogateDiagTailX0RatChunk000Sub001Block162Part002
    + surrogateDiagTailX0RatChunk000Sub001Block162Part003
    + surrogateDiagTailX0RatChunk000Sub001Block162Part004
    + surrogateDiagTailX0RatChunk000Sub001Block162Part005
    + surrogateDiagTailX0RatChunk000Sub001Block162Part006
    + surrogateDiagTailX0RatChunk000Sub001Block162Part007
    + surrogateDiagTailX0RatChunk000Sub001Block162Part008
    + surrogateDiagTailX0RatChunk000Sub001Block162Part009

def surrogateDiagonalTailChunk000Sub001Block162MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block162Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block162Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block162Part010
    + surrogateDiagTailX0RatChunk000Sub001Block162Part011
    + surrogateDiagTailX0RatChunk000Sub001Block162Part012
    + surrogateDiagTailX0RatChunk000Sub001Block162Part013
    + surrogateDiagTailX0RatChunk000Sub001Block162Part014
    + surrogateDiagTailX0RatChunk000Sub001Block162Part015
    + surrogateDiagTailX0RatChunk000Sub001Block162Part016
    + surrogateDiagTailX0RatChunk000Sub001Block162Part017
    + surrogateDiagTailX0RatChunk000Sub001Block162Part018
    + surrogateDiagTailX0RatChunk000Sub001Block162Part019

def surrogateDiagonalTailChunk000Sub001Block162TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block162Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block162Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block162Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block162Part020
    + surrogateDiagTailX0RatChunk000Sub001Block162Part021
    + surrogateDiagTailX0RatChunk000Sub001Block162Part022
    + surrogateDiagTailX0RatChunk000Sub001Block162Part023
    + surrogateDiagTailX0RatChunk000Sub001Block162Part024

def surrogateDiagonalTailChunk000Sub001Block162Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block162HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block162MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block162TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block162 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block162Part000
    + surrogateDiagTailX0RatChunk000Sub001Block162Part001
    + surrogateDiagTailX0RatChunk000Sub001Block162Part002
    + surrogateDiagTailX0RatChunk000Sub001Block162Part003
    + surrogateDiagTailX0RatChunk000Sub001Block162Part004
    + surrogateDiagTailX0RatChunk000Sub001Block162Part005
    + surrogateDiagTailX0RatChunk000Sub001Block162Part006
    + surrogateDiagTailX0RatChunk000Sub001Block162Part007
    + surrogateDiagTailX0RatChunk000Sub001Block162Part008
    + surrogateDiagTailX0RatChunk000Sub001Block162Part009
    + surrogateDiagTailX0RatChunk000Sub001Block162Part010
    + surrogateDiagTailX0RatChunk000Sub001Block162Part011
    + surrogateDiagTailX0RatChunk000Sub001Block162Part012
    + surrogateDiagTailX0RatChunk000Sub001Block162Part013
    + surrogateDiagTailX0RatChunk000Sub001Block162Part014
    + surrogateDiagTailX0RatChunk000Sub001Block162Part015
    + surrogateDiagTailX0RatChunk000Sub001Block162Part016
    + surrogateDiagTailX0RatChunk000Sub001Block162Part017
    + surrogateDiagTailX0RatChunk000Sub001Block162Part018
    + surrogateDiagTailX0RatChunk000Sub001Block162Part019
    + surrogateDiagTailX0RatChunk000Sub001Block162Part020
    + surrogateDiagTailX0RatChunk000Sub001Block162Part021
    + surrogateDiagTailX0RatChunk000Sub001Block162Part022
    + surrogateDiagTailX0RatChunk000Sub001Block162Part023
    + surrogateDiagTailX0RatChunk000Sub001Block162Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block162_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block162Head + surrogateDiagTailX0RatChunk000Sub001Block162Mid + surrogateDiagTailX0RatChunk000Sub001Block162Tail =
      surrogateDiagTailX0RatChunk000Sub001Block162 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block162Head surrogateDiagTailX0RatChunk000Sub001Block162Mid surrogateDiagTailX0RatChunk000Sub001Block162Tail surrogateDiagTailX0RatChunk000Sub001Block162
  ring

def SurrogateDiagonalTailChunk000Sub001Block162HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block162HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block162Head

def SurrogateDiagonalTailChunk000Sub001Block162MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block162MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block162Mid

def SurrogateDiagonalTailChunk000Sub001Block162TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block162TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block162Tail

theorem surrogateDiagonalTailChunk000Sub001Block162_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block162HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block162MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block162TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block162Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block162 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block162HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block162MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block162TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block162Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block162_eq_head_add_mid_add_tail

/-- Block 163 covers tail-support indices [9075,9100) and q from 14979 to 15015. -/

def TailChunk000Sub001Block163Part000SupportExplicit : Finset ℕ :=
  ([14979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part000 : ℚ :=
  (389532265675 : ℚ) / 6211337916820488192

def SurrogateDiagonalTailChunk000Sub001Block163Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14979
    = surrogateDiagTailX0RatChunk000Sub001Block163Part000

theorem surrogateDiagonalTailChunk000Sub001Block163Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part000] using hcert

def TailChunk000Sub001Block163Part001SupportExplicit : Finset ℕ :=
  ([14981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part001 : ℚ :=
  (500543587 : ℚ) / 667203243966000000

def SurrogateDiagonalTailChunk000Sub001Block163Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14981
    = surrogateDiagTailX0RatChunk000Sub001Block163Part001

theorem surrogateDiagonalTailChunk000Sub001Block163Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part001] using hcert

def TailChunk000Sub001Block163Part002SupportExplicit : Finset ℕ :=
  ([14982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part002 : ℚ :=
  (34478230793 : ℚ) / 20874236220441600

def SurrogateDiagonalTailChunk000Sub001Block163Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14982
    = surrogateDiagTailX0RatChunk000Sub001Block163Part002

theorem surrogateDiagonalTailChunk000Sub001Block163Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part002] using hcert

def TailChunk000Sub001Block163Part003SupportExplicit : Finset ℕ :=
  ([14983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block163Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14983
    = surrogateDiagTailX0RatChunk000Sub001Block163Part003

theorem surrogateDiagonalTailChunk000Sub001Block163Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part003] using hcert

def TailChunk000Sub001Block163Part004SupportExplicit : Finset ℕ :=
  ([14986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part004 : ℚ :=
  (377133259625 : ℚ) / 792462105816377472

def SurrogateDiagonalTailChunk000Sub001Block163Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14986
    = surrogateDiagTailX0RatChunk000Sub001Block163Part004

theorem surrogateDiagonalTailChunk000Sub001Block163Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part004] using hcert

def TailChunk000Sub001Block163Part005SupportExplicit : Finset ℕ :=
  ([14987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part005 : ℚ :=
  (11484206087 : ℚ) / 1359305109828633600

def SurrogateDiagonalTailChunk000Sub001Block163Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14987
    = surrogateDiagTailX0RatChunk000Sub001Block163Part005

theorem surrogateDiagonalTailChunk000Sub001Block163Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part005] using hcert

def TailChunk000Sub001Block163Part006SupportExplicit : Finset ℕ :=
  ([14989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part006 : ℚ :=
  (167665006325 : ℚ) / 45659564381929734144

def SurrogateDiagonalTailChunk000Sub001Block163Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14989
    = surrogateDiagTailX0RatChunk000Sub001Block163Part006

theorem surrogateDiagonalTailChunk000Sub001Block163Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part006] using hcert

def TailChunk000Sub001Block163Part007SupportExplicit : Finset ℕ :=
  ([14990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part007 : ℚ :=
  (120292736925 : ℚ) / 153495194295052288

def SurrogateDiagonalTailChunk000Sub001Block163Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14990
    = surrogateDiagTailX0RatChunk000Sub001Block163Part007

theorem surrogateDiagonalTailChunk000Sub001Block163Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part007] using hcert

def TailChunk000Sub001Block163Part008SupportExplicit : Finset ℕ :=
  ([14991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part008 : ℚ :=
  (784265899175 : ℚ) / 9894914173323961344

def SurrogateDiagonalTailChunk000Sub001Block163Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14991
    = surrogateDiagTailX0RatChunk000Sub001Block163Part008

theorem surrogateDiagonalTailChunk000Sub001Block163Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part008] using hcert

def TailChunk000Sub001Block163Part009SupportExplicit : Finset ℕ :=
  ([14993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part009 : ℚ :=
  (4230991467 : ℚ) / 458774269029171200

def SurrogateDiagonalTailChunk000Sub001Block163Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14993
    = surrogateDiagTailX0RatChunk000Sub001Block163Part009

theorem surrogateDiagonalTailChunk000Sub001Block163Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part009] using hcert

def TailChunk000Sub001Block163Part010SupportExplicit : Finset ℕ :=
  ([14995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part010 : ℚ :=
  (1124526025225 : ℚ) / 51712238558205954048

def SurrogateDiagonalTailChunk000Sub001Block163Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14995
    = surrogateDiagTailX0RatChunk000Sub001Block163Part010

theorem surrogateDiagonalTailChunk000Sub001Block163Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part010] using hcert

def TailChunk000Sub001Block163Part011SupportExplicit : Finset ℕ :=
  ([14997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part011 : ℚ :=
  (111562522325 : ℚ) / 1783215428457097152

def SurrogateDiagonalTailChunk000Sub001Block163Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14997
    = surrogateDiagTailX0RatChunk000Sub001Block163Part011

theorem surrogateDiagonalTailChunk000Sub001Block163Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part011] using hcert

def TailChunk000Sub001Block163Part012SupportExplicit : Finset ℕ :=
  ([14998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part012 : ℚ :=
  (878671890625 : ℚ) / 1975825617206230002

def SurrogateDiagonalTailChunk000Sub001Block163Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14998
    = surrogateDiagTailX0RatChunk000Sub001Block163Part012

theorem surrogateDiagonalTailChunk000Sub001Block163Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part012] using hcert

def TailChunk000Sub001Block163Part013SupportExplicit : Finset ℕ :=
  ([14999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part013 : ℚ :=
  (13189682525 : ℚ) / 14452623184818514176

def SurrogateDiagonalTailChunk000Sub001Block163Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14999
    = surrogateDiagTailX0RatChunk000Sub001Block163Part013

theorem surrogateDiagonalTailChunk000Sub001Block163Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part013] using hcert

def TailChunk000Sub001Block163Part014SupportExplicit : Finset ℕ :=
  ([15001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part014 : ℚ :=
  (287640295175 : ℚ) / 34109843807892170304

def SurrogateDiagonalTailChunk000Sub001Block163Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15001
    = surrogateDiagTailX0RatChunk000Sub001Block163Part014

theorem surrogateDiagonalTailChunk000Sub001Block163Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part014] using hcert

def TailChunk000Sub001Block163Part015SupportExplicit : Finset ℕ :=
  ([15002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part015 : ℚ :=
  (456623375 : ℚ) / 825729969291264

def SurrogateDiagonalTailChunk000Sub001Block163Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15002
    = surrogateDiagTailX0RatChunk000Sub001Block163Part015

theorem surrogateDiagonalTailChunk000Sub001Block163Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part015] using hcert

def TailChunk000Sub001Block163Part016SupportExplicit : Finset ℕ :=
  ([15005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part016 : ℚ :=
  (15013669663 : ℚ) / 691338240000000000

def SurrogateDiagonalTailChunk000Sub001Block163Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15005
    = surrogateDiagTailX0RatChunk000Sub001Block163Part016

theorem surrogateDiagonalTailChunk000Sub001Block163Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part016] using hcert

def TailChunk000Sub001Block163Part017SupportExplicit : Finset ℕ :=
  ([15006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part017 : ℚ :=
  (74405388433 : ℚ) / 53094776832000000

def SurrogateDiagonalTailChunk000Sub001Block163Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15006
    = surrogateDiagTailX0RatChunk000Sub001Block163Part017

theorem surrogateDiagonalTailChunk000Sub001Block163Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part017] using hcert

def TailChunk000Sub001Block163Part018SupportExplicit : Finset ℕ :=
  ([15007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part018 : ℚ :=
  (118891370725 : ℚ) / 114114543237558355968

def SurrogateDiagonalTailChunk000Sub001Block163Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15007
    = surrogateDiagTailX0RatChunk000Sub001Block163Part018

theorem surrogateDiagonalTailChunk000Sub001Block163Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part018] using hcert

def TailChunk000Sub001Block163Part019SupportExplicit : Finset ℕ :=
  ([15009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part019 : ℚ :=
  (782187656225 : ℚ) / 12522516005600960064

def SurrogateDiagonalTailChunk000Sub001Block163Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15009
    = surrogateDiagTailX0RatChunk000Sub001Block163Part019

theorem surrogateDiagonalTailChunk000Sub001Block163Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part019] using hcert

def TailChunk000Sub001Block163Part020SupportExplicit : Finset ℕ :=
  ([15010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part020 : ℚ :=
  (582791433925 : ℚ) / 621835145145556992

def SurrogateDiagonalTailChunk000Sub001Block163Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15010
    = surrogateDiagTailX0RatChunk000Sub001Block163Part020

theorem surrogateDiagonalTailChunk000Sub001Block163Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part020] using hcert

def TailChunk000Sub001Block163Part021SupportExplicit : Finset ℕ :=
  ([15011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part021 : ℚ :=
  (247905423025 : ℚ) / 99170186514588499968

def SurrogateDiagonalTailChunk000Sub001Block163Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15011
    = surrogateDiagTailX0RatChunk000Sub001Block163Part021

theorem surrogateDiagonalTailChunk000Sub001Block163Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part021] using hcert

def TailChunk000Sub001Block163Part022SupportExplicit : Finset ℕ :=
  ([15013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block163Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15013
    = surrogateDiagTailX0RatChunk000Sub001Block163Part022

theorem surrogateDiagonalTailChunk000Sub001Block163Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part022] using hcert

def TailChunk000Sub001Block163Part023SupportExplicit : Finset ℕ :=
  ([15014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part023 : ℚ :=
  (880547640625 : ℚ) / 1984271560257870162

def SurrogateDiagonalTailChunk000Sub001Block163Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15014
    = surrogateDiagTailX0RatChunk000Sub001Block163Part023

theorem surrogateDiagonalTailChunk000Sub001Block163Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part023] using hcert

def TailChunk000Sub001Block163Part024SupportExplicit : Finset ℕ :=
  ([15015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block163Part024 : ℚ :=
  (1202196277 : ℚ) / 2446607316418560

def SurrogateDiagonalTailChunk000Sub001Block163Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15015
    = surrogateDiagTailX0RatChunk000Sub001Block163Part024

theorem surrogateDiagonalTailChunk000Sub001Block163Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block163Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block163Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block163Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block163Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block163Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block163Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block163HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block163Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block163Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block163Part000
    + surrogateDiagTailX0RatChunk000Sub001Block163Part001
    + surrogateDiagTailX0RatChunk000Sub001Block163Part002
    + surrogateDiagTailX0RatChunk000Sub001Block163Part003
    + surrogateDiagTailX0RatChunk000Sub001Block163Part004
    + surrogateDiagTailX0RatChunk000Sub001Block163Part005
    + surrogateDiagTailX0RatChunk000Sub001Block163Part006
    + surrogateDiagTailX0RatChunk000Sub001Block163Part007
    + surrogateDiagTailX0RatChunk000Sub001Block163Part008
    + surrogateDiagTailX0RatChunk000Sub001Block163Part009

def surrogateDiagonalTailChunk000Sub001Block163MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block163Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block163Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block163Part010
    + surrogateDiagTailX0RatChunk000Sub001Block163Part011
    + surrogateDiagTailX0RatChunk000Sub001Block163Part012
    + surrogateDiagTailX0RatChunk000Sub001Block163Part013
    + surrogateDiagTailX0RatChunk000Sub001Block163Part014
    + surrogateDiagTailX0RatChunk000Sub001Block163Part015
    + surrogateDiagTailX0RatChunk000Sub001Block163Part016
    + surrogateDiagTailX0RatChunk000Sub001Block163Part017
    + surrogateDiagTailX0RatChunk000Sub001Block163Part018
    + surrogateDiagTailX0RatChunk000Sub001Block163Part019

def surrogateDiagonalTailChunk000Sub001Block163TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block163Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block163Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block163Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block163Part020
    + surrogateDiagTailX0RatChunk000Sub001Block163Part021
    + surrogateDiagTailX0RatChunk000Sub001Block163Part022
    + surrogateDiagTailX0RatChunk000Sub001Block163Part023
    + surrogateDiagTailX0RatChunk000Sub001Block163Part024

def surrogateDiagonalTailChunk000Sub001Block163Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block163HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block163MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block163TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block163 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block163Part000
    + surrogateDiagTailX0RatChunk000Sub001Block163Part001
    + surrogateDiagTailX0RatChunk000Sub001Block163Part002
    + surrogateDiagTailX0RatChunk000Sub001Block163Part003
    + surrogateDiagTailX0RatChunk000Sub001Block163Part004
    + surrogateDiagTailX0RatChunk000Sub001Block163Part005
    + surrogateDiagTailX0RatChunk000Sub001Block163Part006
    + surrogateDiagTailX0RatChunk000Sub001Block163Part007
    + surrogateDiagTailX0RatChunk000Sub001Block163Part008
    + surrogateDiagTailX0RatChunk000Sub001Block163Part009
    + surrogateDiagTailX0RatChunk000Sub001Block163Part010
    + surrogateDiagTailX0RatChunk000Sub001Block163Part011
    + surrogateDiagTailX0RatChunk000Sub001Block163Part012
    + surrogateDiagTailX0RatChunk000Sub001Block163Part013
    + surrogateDiagTailX0RatChunk000Sub001Block163Part014
    + surrogateDiagTailX0RatChunk000Sub001Block163Part015
    + surrogateDiagTailX0RatChunk000Sub001Block163Part016
    + surrogateDiagTailX0RatChunk000Sub001Block163Part017
    + surrogateDiagTailX0RatChunk000Sub001Block163Part018
    + surrogateDiagTailX0RatChunk000Sub001Block163Part019
    + surrogateDiagTailX0RatChunk000Sub001Block163Part020
    + surrogateDiagTailX0RatChunk000Sub001Block163Part021
    + surrogateDiagTailX0RatChunk000Sub001Block163Part022
    + surrogateDiagTailX0RatChunk000Sub001Block163Part023
    + surrogateDiagTailX0RatChunk000Sub001Block163Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block163_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block163Head + surrogateDiagTailX0RatChunk000Sub001Block163Mid + surrogateDiagTailX0RatChunk000Sub001Block163Tail =
      surrogateDiagTailX0RatChunk000Sub001Block163 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block163Head surrogateDiagTailX0RatChunk000Sub001Block163Mid surrogateDiagTailX0RatChunk000Sub001Block163Tail surrogateDiagTailX0RatChunk000Sub001Block163
  ring

def SurrogateDiagonalTailChunk000Sub001Block163HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block163HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block163Head

def SurrogateDiagonalTailChunk000Sub001Block163MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block163MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block163Mid

def SurrogateDiagonalTailChunk000Sub001Block163TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block163TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block163Tail

theorem surrogateDiagonalTailChunk000Sub001Block163_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block163HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block163MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block163TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block163Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block163 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block163HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block163MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block163TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block163Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block163_eq_head_add_mid_add_tail

/-- Block 164 covers tail-support indices [9100,9125) and q from 15017 to 15061. -/

def TailChunk000Sub001Block164Part000SupportExplicit : Finset ℕ :=
  ([15017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block164Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15017
    = surrogateDiagTailX0RatChunk000Sub001Block164Part000

theorem surrogateDiagonalTailChunk000Sub001Block164Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part000] using hcert

def TailChunk000Sub001Block164Part001SupportExplicit : Finset ℕ :=
  ([15018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part001 : ℚ :=
  (489297281275 : ℚ) / 391954876100320032

def SurrogateDiagonalTailChunk000Sub001Block164Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15018
    = surrogateDiagTailX0RatChunk000Sub001Block164Part001

theorem surrogateDiagonalTailChunk000Sub001Block164Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part001] using hcert

def TailChunk000Sub001Block164Part002SupportExplicit : Finset ℕ :=
  ([15019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part002 : ℚ :=
  (18259900875 : ℚ) / 8821180709222024704

def SurrogateDiagonalTailChunk000Sub001Block164Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15019
    = surrogateDiagTailX0RatChunk000Sub001Block164Part002

theorem surrogateDiagonalTailChunk000Sub001Block164Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part002] using hcert

def TailChunk000Sub001Block164Part003SupportExplicit : Finset ℕ :=
  ([15022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part003 : ℚ :=
  (7730536075 : ℚ) / 9753935262253056

def SurrogateDiagonalTailChunk000Sub001Block164Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15022
    = surrogateDiagTailX0RatChunk000Sub001Block164Part003

theorem surrogateDiagonalTailChunk000Sub001Block164Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part003] using hcert

def TailChunk000Sub001Block164Part004SupportExplicit : Finset ℕ :=
  ([15023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part004 : ℚ :=
  (819201043 : ℚ) / 1186785656613388800

def SurrogateDiagonalTailChunk000Sub001Block164Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15023
    = surrogateDiagTailX0RatChunk000Sub001Block164Part004

theorem surrogateDiagonalTailChunk000Sub001Block164Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part004] using hcert

def TailChunk000Sub001Block164Part005SupportExplicit : Finset ℕ :=
  ([15026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part005 : ℚ :=
  (224370301 : ℚ) / 393424733532864

def SurrogateDiagonalTailChunk000Sub001Block164Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15026
    = surrogateDiagTailX0RatChunk000Sub001Block164Part005

theorem surrogateDiagonalTailChunk000Sub001Block164Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part005] using hcert

def TailChunk000Sub001Block164Part006SupportExplicit : Finset ℕ :=
  ([15027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part006 : ℚ :=
  (392032265575 : ℚ) / 6291354121661448192

def SurrogateDiagonalTailChunk000Sub001Block164Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15027
    = surrogateDiagTailX0RatChunk000Sub001Block164Part006

theorem surrogateDiagonalTailChunk000Sub001Block164Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part006] using hcert

def TailChunk000Sub001Block164Part007SupportExplicit : Finset ℕ :=
  ([15029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part007 : ℚ :=
  (7754767775 : ℚ) / 418199974369099776

def SurrogateDiagonalTailChunk000Sub001Block164Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15029
    = surrogateDiagTailX0RatChunk000Sub001Block164Part007

theorem surrogateDiagonalTailChunk000Sub001Block164Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part007] using hcert

def TailChunk000Sub001Block164Part008SupportExplicit : Finset ℕ :=
  ([15031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block164Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15031
    = surrogateDiagTailX0RatChunk000Sub001Block164Part008

theorem surrogateDiagonalTailChunk000Sub001Block164Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part008] using hcert

def TailChunk000Sub001Block164Part009SupportExplicit : Finset ℕ :=
  ([15033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part009 : ℚ :=
  (6277525249 : ℚ) / 100822563682240320

def SurrogateDiagonalTailChunk000Sub001Block164Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15033
    = surrogateDiagTailX0RatChunk000Sub001Block164Part009

theorem surrogateDiagonalTailChunk000Sub001Block164Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part009] using hcert

def TailChunk000Sub001Block164Part010SupportExplicit : Finset ℕ :=
  ([15034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part010 : ℚ :=
  (882895140625 : ℚ) / 1994867032968828192

def SurrogateDiagonalTailChunk000Sub001Block164Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15034
    = surrogateDiagTailX0RatChunk000Sub001Block164Part010

theorem surrogateDiagonalTailChunk000Sub001Block164Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part010] using hcert

def TailChunk000Sub001Block164Part011SupportExplicit : Finset ℕ :=
  ([15035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part011 : ℚ :=
  (13297781 : ℚ) / 860135384678400

def SurrogateDiagonalTailChunk000Sub001Block164Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15035
    = surrogateDiagTailX0RatChunk000Sub001Block164Part011

theorem surrogateDiagonalTailChunk000Sub001Block164Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part011] using hcert

def TailChunk000Sub001Block164Part012SupportExplicit : Finset ℕ :=
  ([15037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part012 : ℚ :=
  (6257816847 : ℚ) / 1160829384098262400

def SurrogateDiagonalTailChunk000Sub001Block164Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15037
    = surrogateDiagTailX0RatChunk000Sub001Block164Part012

theorem surrogateDiagonalTailChunk000Sub001Block164Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part012] using hcert

def TailChunk000Sub001Block164Part013SupportExplicit : Finset ℕ :=
  ([15038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part013 : ℚ :=
  (3424070537425 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk000Sub001Block164Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15038
    = surrogateDiagTailX0RatChunk000Sub001Block164Part013

theorem surrogateDiagonalTailChunk000Sub001Block164Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part013] using hcert

def TailChunk000Sub001Block164Part014SupportExplicit : Finset ℕ :=
  ([15042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part014 : ℚ :=
  (1840694716225 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk000Sub001Block164Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15042
    = surrogateDiagTailX0RatChunk000Sub001Block164Part014

theorem surrogateDiagonalTailChunk000Sub001Block164Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part014] using hcert

def TailChunk000Sub001Block164Part015SupportExplicit : Finset ℕ :=
  ([15045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part015 : ℚ :=
  (1419719539525 : ℚ) / 7595890784587481088

def SurrogateDiagonalTailChunk000Sub001Block164Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15045
    = surrogateDiagTailX0RatChunk000Sub001Block164Part015

theorem surrogateDiagonalTailChunk000Sub001Block164Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part015] using hcert

def TailChunk000Sub001Block164Part016SupportExplicit : Finset ℕ :=
  ([15046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part016 : ℚ :=
  (884305140625 : ℚ) / 2001244649942619282

def SurrogateDiagonalTailChunk000Sub001Block164Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15046
    = surrogateDiagTailX0RatChunk000Sub001Block164Part016

theorem surrogateDiagonalTailChunk000Sub001Block164Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part016] using hcert

def TailChunk000Sub001Block164Part017SupportExplicit : Finset ℕ :=
  ([15047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part017 : ℚ :=
  (431371297 : ℚ) / 382886373930393600

def SurrogateDiagonalTailChunk000Sub001Block164Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15047
    = surrogateDiagTailX0RatChunk000Sub001Block164Part017

theorem surrogateDiagonalTailChunk000Sub001Block164Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part017] using hcert

def TailChunk000Sub001Block164Part018SupportExplicit : Finset ℕ :=
  ([15049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part018 : ℚ :=
  (518612619 : ℚ) / 799801955072000000

def SurrogateDiagonalTailChunk000Sub001Block164Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15049
    = surrogateDiagTailX0RatChunk000Sub001Block164Part018

theorem surrogateDiagonalTailChunk000Sub001Block164Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part018] using hcert

def TailChunk000Sub001Block164Part019SupportExplicit : Finset ℕ :=
  ([15051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part019 : ℚ :=
  (393549489175 : ℚ) / 5380625471399657472

def SurrogateDiagonalTailChunk000Sub001Block164Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15051
    = surrogateDiagTailX0RatChunk000Sub001Block164Part019

theorem surrogateDiagonalTailChunk000Sub001Block164Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part019] using hcert

def TailChunk000Sub001Block164Part020SupportExplicit : Finset ℕ :=
  ([15053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block164Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15053
    = surrogateDiagTailX0RatChunk000Sub001Block164Part020

theorem surrogateDiagonalTailChunk000Sub001Block164Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part020] using hcert

def TailChunk000Sub001Block164Part021SupportExplicit : Finset ℕ :=
  ([15054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part021 : ℚ :=
  (444302410975 : ℚ) / 281849162851418112

def SurrogateDiagonalTailChunk000Sub001Block164Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15054
    = surrogateDiagTailX0RatChunk000Sub001Block164Part021

theorem surrogateDiagonalTailChunk000Sub001Block164Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part021] using hcert

def TailChunk000Sub001Block164Part022SupportExplicit : Finset ℕ :=
  ([15055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part022 : ℚ :=
  (1513352163 : ℚ) / 140120454984366080

def SurrogateDiagonalTailChunk000Sub001Block164Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15055
    = surrogateDiagTailX0RatChunk000Sub001Block164Part022

theorem surrogateDiagonalTailChunk000Sub001Block164Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part022] using hcert

def TailChunk000Sub001Block164Part023SupportExplicit : Finset ℕ :=
  ([15058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part023 : ℚ :=
  (885716265625 : ℚ) / 2007637546704056832

def SurrogateDiagonalTailChunk000Sub001Block164Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15058
    = surrogateDiagTailX0RatChunk000Sub001Block164Part023

theorem surrogateDiagonalTailChunk000Sub001Block164Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part023] using hcert

def TailChunk000Sub001Block164Part024SupportExplicit : Finset ℕ :=
  ([15061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block164Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block164Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15061
    = surrogateDiagTailX0RatChunk000Sub001Block164Part024

theorem surrogateDiagonalTailChunk000Sub001Block164Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block164Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block164Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block164Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block164Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block164Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block164Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block164HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block164Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block164Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block164Part000
    + surrogateDiagTailX0RatChunk000Sub001Block164Part001
    + surrogateDiagTailX0RatChunk000Sub001Block164Part002
    + surrogateDiagTailX0RatChunk000Sub001Block164Part003
    + surrogateDiagTailX0RatChunk000Sub001Block164Part004
    + surrogateDiagTailX0RatChunk000Sub001Block164Part005
    + surrogateDiagTailX0RatChunk000Sub001Block164Part006
    + surrogateDiagTailX0RatChunk000Sub001Block164Part007
    + surrogateDiagTailX0RatChunk000Sub001Block164Part008
    + surrogateDiagTailX0RatChunk000Sub001Block164Part009

def surrogateDiagonalTailChunk000Sub001Block164MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block164Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block164Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block164Part010
    + surrogateDiagTailX0RatChunk000Sub001Block164Part011
    + surrogateDiagTailX0RatChunk000Sub001Block164Part012
    + surrogateDiagTailX0RatChunk000Sub001Block164Part013
    + surrogateDiagTailX0RatChunk000Sub001Block164Part014
    + surrogateDiagTailX0RatChunk000Sub001Block164Part015
    + surrogateDiagTailX0RatChunk000Sub001Block164Part016
    + surrogateDiagTailX0RatChunk000Sub001Block164Part017
    + surrogateDiagTailX0RatChunk000Sub001Block164Part018
    + surrogateDiagTailX0RatChunk000Sub001Block164Part019

def surrogateDiagonalTailChunk000Sub001Block164TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block164Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block164Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block164Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block164Part020
    + surrogateDiagTailX0RatChunk000Sub001Block164Part021
    + surrogateDiagTailX0RatChunk000Sub001Block164Part022
    + surrogateDiagTailX0RatChunk000Sub001Block164Part023
    + surrogateDiagTailX0RatChunk000Sub001Block164Part024

def surrogateDiagonalTailChunk000Sub001Block164Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block164HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block164MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block164TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block164 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block164Part000
    + surrogateDiagTailX0RatChunk000Sub001Block164Part001
    + surrogateDiagTailX0RatChunk000Sub001Block164Part002
    + surrogateDiagTailX0RatChunk000Sub001Block164Part003
    + surrogateDiagTailX0RatChunk000Sub001Block164Part004
    + surrogateDiagTailX0RatChunk000Sub001Block164Part005
    + surrogateDiagTailX0RatChunk000Sub001Block164Part006
    + surrogateDiagTailX0RatChunk000Sub001Block164Part007
    + surrogateDiagTailX0RatChunk000Sub001Block164Part008
    + surrogateDiagTailX0RatChunk000Sub001Block164Part009
    + surrogateDiagTailX0RatChunk000Sub001Block164Part010
    + surrogateDiagTailX0RatChunk000Sub001Block164Part011
    + surrogateDiagTailX0RatChunk000Sub001Block164Part012
    + surrogateDiagTailX0RatChunk000Sub001Block164Part013
    + surrogateDiagTailX0RatChunk000Sub001Block164Part014
    + surrogateDiagTailX0RatChunk000Sub001Block164Part015
    + surrogateDiagTailX0RatChunk000Sub001Block164Part016
    + surrogateDiagTailX0RatChunk000Sub001Block164Part017
    + surrogateDiagTailX0RatChunk000Sub001Block164Part018
    + surrogateDiagTailX0RatChunk000Sub001Block164Part019
    + surrogateDiagTailX0RatChunk000Sub001Block164Part020
    + surrogateDiagTailX0RatChunk000Sub001Block164Part021
    + surrogateDiagTailX0RatChunk000Sub001Block164Part022
    + surrogateDiagTailX0RatChunk000Sub001Block164Part023
    + surrogateDiagTailX0RatChunk000Sub001Block164Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block164_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block164Head + surrogateDiagTailX0RatChunk000Sub001Block164Mid + surrogateDiagTailX0RatChunk000Sub001Block164Tail =
      surrogateDiagTailX0RatChunk000Sub001Block164 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block164Head surrogateDiagTailX0RatChunk000Sub001Block164Mid surrogateDiagTailX0RatChunk000Sub001Block164Tail surrogateDiagTailX0RatChunk000Sub001Block164
  ring

def SurrogateDiagonalTailChunk000Sub001Block164HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block164HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block164Head

def SurrogateDiagonalTailChunk000Sub001Block164MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block164MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block164Mid

def SurrogateDiagonalTailChunk000Sub001Block164TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block164TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block164Tail

theorem surrogateDiagonalTailChunk000Sub001Block164_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block164HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block164MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block164TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block164Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block164 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block164HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block164MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block164TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block164Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block164_eq_head_add_mid_add_tail

/-- Block 165 covers tail-support indices [9125,9150) and q from 15062 to 15098. -/

def TailChunk000Sub001Block165Part000SupportExplicit : Finset ℕ :=
  ([15062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part000 : ℚ :=
  (135561255525 : ℚ) / 260606128909647872

def SurrogateDiagonalTailChunk000Sub001Block165Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15062
    = surrogateDiagTailX0RatChunk000Sub001Block165Part000

theorem surrogateDiagonalTailChunk000Sub001Block165Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part000] using hcert

def TailChunk000Sub001Block165Part001SupportExplicit : Finset ℕ :=
  ([15063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part001 : ℚ :=
  (787825031 : ℚ) / 12703743443840640

def SurrogateDiagonalTailChunk000Sub001Block165Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15063
    = surrogateDiagTailX0RatChunk000Sub001Block165Part001

theorem surrogateDiagonalTailChunk000Sub001Block165Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part001] using hcert

def TailChunk000Sub001Block165Part002SupportExplicit : Finset ℕ :=
  ([15065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part002 : ℚ :=
  (47954853697 : ℚ) / 1713132475679539200

def SurrogateDiagonalTailChunk000Sub001Block165Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15065
    = surrogateDiagTailX0RatChunk000Sub001Block165Part002

theorem surrogateDiagonalTailChunk000Sub001Block165Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part002] using hcert

def TailChunk000Sub001Block165Part003SupportExplicit : Finset ℕ :=
  ([15067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part003 : ℚ :=
  (5687388649 : ℚ) / 705418532359372800

def SurrogateDiagonalTailChunk000Sub001Block165Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15067
    = surrogateDiagTailX0RatChunk000Sub001Block165Part003

theorem surrogateDiagonalTailChunk000Sub001Block165Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part003] using hcert

def TailChunk000Sub001Block165Part004SupportExplicit : Finset ℕ :=
  ([15069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part004 : ℚ :=
  (788452655975 : ℚ) / 12724000555137897024

def SurrogateDiagonalTailChunk000Sub001Block165Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15069
    = surrogateDiagTailX0RatChunk000Sub001Block165Part004

theorem surrogateDiagonalTailChunk000Sub001Block165Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part004] using hcert

def TailChunk000Sub001Block165Part005SupportExplicit : Finset ℕ :=
  ([15070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part005 : ℚ :=
  (94750856503 : ℚ) / 87595631719219200

def SurrogateDiagonalTailChunk000Sub001Block165Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15070
    = surrogateDiagTailX0RatChunk000Sub001Block165Part005

theorem surrogateDiagonalTailChunk000Sub001Block165Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part005] using hcert

def TailChunk000Sub001Block165Part006SupportExplicit : Finset ℕ :=
  ([15071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part006 : ℚ :=
  (290323508675 : ℚ) / 34751290167541776384

def SurrogateDiagonalTailChunk000Sub001Block165Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15071
    = surrogateDiagTailX0RatChunk000Sub001Block165Part006

theorem surrogateDiagonalTailChunk000Sub001Block165Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part006] using hcert

def TailChunk000Sub001Block165Part007SupportExplicit : Finset ℕ :=
  ([15073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block165Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15073
    = surrogateDiagTailX0RatChunk000Sub001Block165Part007

theorem surrogateDiagonalTailChunk000Sub001Block165Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part007] using hcert

def TailChunk000Sub001Block165Part008SupportExplicit : Finset ℕ :=
  ([15074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part008 : ℚ :=
  (887599515625 : ℚ) / 2016185219762429952

def SurrogateDiagonalTailChunk000Sub001Block165Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15074
    = surrogateDiagTailX0RatChunk000Sub001Block165Part008

theorem surrogateDiagonalTailChunk000Sub001Block165Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part008] using hcert

def TailChunk000Sub001Block165Part009SupportExplicit : Finset ℕ :=
  ([15077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block165Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15077
    = surrogateDiagTailX0RatChunk000Sub001Block165Part009

theorem surrogateDiagonalTailChunk000Sub001Block165Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part009] using hcert

def TailChunk000Sub001Block165Part010SupportExplicit : Finset ℕ :=
  ([15078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part010 : ℚ :=
  (28616645725 : ℚ) / 31544248508504064

def SurrogateDiagonalTailChunk000Sub001Block165Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15078
    = surrogateDiagTailX0RatChunk000Sub001Block165Part010

theorem surrogateDiagonalTailChunk000Sub001Block165Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part010] using hcert

def TailChunk000Sub001Block165Part011SupportExplicit : Finset ℕ :=
  ([15079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part011 : ℚ :=
  (49846256625 : ℚ) / 16830244557073154048

def SurrogateDiagonalTailChunk000Sub001Block165Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15079
    = surrogateDiagTailX0RatChunk000Sub001Block165Part011

theorem surrogateDiagonalTailChunk000Sub001Block165Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part011] using hcert

def TailChunk000Sub001Block165Part012SupportExplicit : Finset ℕ :=
  ([15081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part012 : ℚ :=
  (31834144559 : ℚ) / 345968220576153600

def SurrogateDiagonalTailChunk000Sub001Block165Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15081
    = surrogateDiagTailX0RatChunk000Sub001Block165Part012

theorem surrogateDiagonalTailChunk000Sub001Block165Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part012] using hcert

def TailChunk000Sub001Block165Part013SupportExplicit : Finset ℕ :=
  ([15082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block165Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15082
    = surrogateDiagTailX0RatChunk000Sub001Block165Part013

theorem surrogateDiagonalTailChunk000Sub001Block165Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part013] using hcert

def TailChunk000Sub001Block165Part014SupportExplicit : Finset ℕ :=
  ([15083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block165Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15083
    = surrogateDiagTailX0RatChunk000Sub001Block165Part014

theorem surrogateDiagonalTailChunk000Sub001Block165Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part014] using hcert

def TailChunk000Sub001Block165Part015SupportExplicit : Finset ℕ :=
  ([15085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part015 : ℚ :=
  (51604283317 : ℚ) / 1134502975800115200

def SurrogateDiagonalTailChunk000Sub001Block165Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15085
    = surrogateDiagTailX0RatChunk000Sub001Block165Part015

theorem surrogateDiagonalTailChunk000Sub001Block165Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part015] using hcert

def TailChunk000Sub001Block165Part016SupportExplicit : Finset ℕ :=
  ([15086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part016 : ℚ :=
  (204827525 : ℚ) / 9961451323566336

def SurrogateDiagonalTailChunk000Sub001Block165Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15086
    = surrogateDiagTailX0RatChunk000Sub001Block165Part016

theorem surrogateDiagonalTailChunk000Sub001Block165Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part016] using hcert

def TailChunk000Sub001Block165Part017SupportExplicit : Finset ℕ :=
  ([15087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part017 : ℚ :=
  (395085852175 : ℚ) / 5653815576421642752

def SurrogateDiagonalTailChunk000Sub001Block165Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15087
    = surrogateDiagTailX0RatChunk000Sub001Block165Part017

theorem surrogateDiagonalTailChunk000Sub001Block165Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part017] using hcert

def TailChunk000Sub001Block165Part018SupportExplicit : Finset ℕ :=
  ([15089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part018 : ℚ :=
  (82636543 : ℚ) / 120620097019964880

def SurrogateDiagonalTailChunk000Sub001Block165Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15089
    = surrogateDiagTailX0RatChunk000Sub001Block165Part018

theorem surrogateDiagonalTailChunk000Sub001Block165Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part018] using hcert

def TailChunk000Sub001Block165Part019SupportExplicit : Finset ℕ :=
  ([15090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part019 : ℚ :=
  (758345821825 : ℚ) / 650431664324640768

def SurrogateDiagonalTailChunk000Sub001Block165Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15090
    = surrogateDiagTailX0RatChunk000Sub001Block165Part019

theorem surrogateDiagonalTailChunk000Sub001Block165Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part019] using hcert

def TailChunk000Sub001Block165Part020SupportExplicit : Finset ℕ :=
  ([15091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block165Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15091
    = surrogateDiagTailX0RatChunk000Sub001Block165Part020

theorem surrogateDiagonalTailChunk000Sub001Block165Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part020] using hcert

def TailChunk000Sub001Block165Part021SupportExplicit : Finset ℕ :=
  ([15094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block165Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15094
    = surrogateDiagTailX0RatChunk000Sub001Block165Part021

theorem surrogateDiagonalTailChunk000Sub001Block165Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part021] using hcert

def TailChunk000Sub001Block165Part022SupportExplicit : Finset ℕ :=
  ([15095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part022 : ℚ :=
  (379854337075 : ℚ) / 17702007125801342976

def SurrogateDiagonalTailChunk000Sub001Block165Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15095
    = surrogateDiagTailX0RatChunk000Sub001Block165Part022

theorem surrogateDiagonalTailChunk000Sub001Block165Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part022] using hcert

def TailChunk000Sub001Block165Part023SupportExplicit : Finset ℕ :=
  ([15097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part023 : ℚ :=
  (139303801 : ℚ) / 100439474626949760

def SurrogateDiagonalTailChunk000Sub001Block165Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15097
    = surrogateDiagTailX0RatChunk000Sub001Block165Part023

theorem surrogateDiagonalTailChunk000Sub001Block165Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part023] using hcert

def TailChunk000Sub001Block165Part024SupportExplicit : Finset ℕ :=
  ([15098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block165Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block165Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15098
    = surrogateDiagTailX0RatChunk000Sub001Block165Part024

theorem surrogateDiagonalTailChunk000Sub001Block165Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block165Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block165Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block165Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block165Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block165Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block165Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block165HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block165Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block165Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block165Part000
    + surrogateDiagTailX0RatChunk000Sub001Block165Part001
    + surrogateDiagTailX0RatChunk000Sub001Block165Part002
    + surrogateDiagTailX0RatChunk000Sub001Block165Part003
    + surrogateDiagTailX0RatChunk000Sub001Block165Part004
    + surrogateDiagTailX0RatChunk000Sub001Block165Part005
    + surrogateDiagTailX0RatChunk000Sub001Block165Part006
    + surrogateDiagTailX0RatChunk000Sub001Block165Part007
    + surrogateDiagTailX0RatChunk000Sub001Block165Part008
    + surrogateDiagTailX0RatChunk000Sub001Block165Part009

def surrogateDiagonalTailChunk000Sub001Block165MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block165Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block165Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block165Part010
    + surrogateDiagTailX0RatChunk000Sub001Block165Part011
    + surrogateDiagTailX0RatChunk000Sub001Block165Part012
    + surrogateDiagTailX0RatChunk000Sub001Block165Part013
    + surrogateDiagTailX0RatChunk000Sub001Block165Part014
    + surrogateDiagTailX0RatChunk000Sub001Block165Part015
    + surrogateDiagTailX0RatChunk000Sub001Block165Part016
    + surrogateDiagTailX0RatChunk000Sub001Block165Part017
    + surrogateDiagTailX0RatChunk000Sub001Block165Part018
    + surrogateDiagTailX0RatChunk000Sub001Block165Part019

def surrogateDiagonalTailChunk000Sub001Block165TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block165Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block165Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block165Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block165Part020
    + surrogateDiagTailX0RatChunk000Sub001Block165Part021
    + surrogateDiagTailX0RatChunk000Sub001Block165Part022
    + surrogateDiagTailX0RatChunk000Sub001Block165Part023
    + surrogateDiagTailX0RatChunk000Sub001Block165Part024

def surrogateDiagonalTailChunk000Sub001Block165Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block165HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block165MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block165TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block165 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block165Part000
    + surrogateDiagTailX0RatChunk000Sub001Block165Part001
    + surrogateDiagTailX0RatChunk000Sub001Block165Part002
    + surrogateDiagTailX0RatChunk000Sub001Block165Part003
    + surrogateDiagTailX0RatChunk000Sub001Block165Part004
    + surrogateDiagTailX0RatChunk000Sub001Block165Part005
    + surrogateDiagTailX0RatChunk000Sub001Block165Part006
    + surrogateDiagTailX0RatChunk000Sub001Block165Part007
    + surrogateDiagTailX0RatChunk000Sub001Block165Part008
    + surrogateDiagTailX0RatChunk000Sub001Block165Part009
    + surrogateDiagTailX0RatChunk000Sub001Block165Part010
    + surrogateDiagTailX0RatChunk000Sub001Block165Part011
    + surrogateDiagTailX0RatChunk000Sub001Block165Part012
    + surrogateDiagTailX0RatChunk000Sub001Block165Part013
    + surrogateDiagTailX0RatChunk000Sub001Block165Part014
    + surrogateDiagTailX0RatChunk000Sub001Block165Part015
    + surrogateDiagTailX0RatChunk000Sub001Block165Part016
    + surrogateDiagTailX0RatChunk000Sub001Block165Part017
    + surrogateDiagTailX0RatChunk000Sub001Block165Part018
    + surrogateDiagTailX0RatChunk000Sub001Block165Part019
    + surrogateDiagTailX0RatChunk000Sub001Block165Part020
    + surrogateDiagTailX0RatChunk000Sub001Block165Part021
    + surrogateDiagTailX0RatChunk000Sub001Block165Part022
    + surrogateDiagTailX0RatChunk000Sub001Block165Part023
    + surrogateDiagTailX0RatChunk000Sub001Block165Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block165_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block165Head + surrogateDiagTailX0RatChunk000Sub001Block165Mid + surrogateDiagTailX0RatChunk000Sub001Block165Tail =
      surrogateDiagTailX0RatChunk000Sub001Block165 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block165Head surrogateDiagTailX0RatChunk000Sub001Block165Mid surrogateDiagTailX0RatChunk000Sub001Block165Tail surrogateDiagTailX0RatChunk000Sub001Block165
  ring

def SurrogateDiagonalTailChunk000Sub001Block165HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block165HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block165Head

def SurrogateDiagonalTailChunk000Sub001Block165MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block165MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block165Mid

def SurrogateDiagonalTailChunk000Sub001Block165TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block165TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block165Tail

theorem surrogateDiagonalTailChunk000Sub001Block165_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block165HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block165MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block165TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block165Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block165 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block165HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block165MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block165TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block165Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block165_eq_head_add_mid_add_tail

/-- Block 166 covers tail-support indices [9150,9175) and q from 15099 to 15139. -/

def TailChunk000Sub001Block166Part000SupportExplicit : Finset ℕ :=
  ([15099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part000 : ℚ :=
  (182976045575 : ℚ) / 1531112530031511552

def SurrogateDiagonalTailChunk000Sub001Block166Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15099
    = surrogateDiagTailX0RatChunk000Sub001Block166Part000

theorem surrogateDiagonalTailChunk000Sub001Block166Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part000] using hcert

def TailChunk000Sub001Block166Part001SupportExplicit : Finset ℕ :=
  ([15101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block166Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15101
    = surrogateDiagTailX0RatChunk000Sub001Block166Part001

theorem surrogateDiagonalTailChunk000Sub001Block166Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part001] using hcert

def TailChunk000Sub001Block166Part002SupportExplicit : Finset ℕ :=
  ([15103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part002 : ℚ :=
  (2033905219 : ℚ) / 506296885337241600

def SurrogateDiagonalTailChunk000Sub001Block166Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15103
    = surrogateDiagTailX0RatChunk000Sub001Block166Part002

theorem surrogateDiagonalTailChunk000Sub001Block166Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part002] using hcert

def TailChunk000Sub001Block166Part003SupportExplicit : Finset ℕ :=
  ([15105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part003 : ℚ :=
  (798250124375 : ℚ) / 3930612275487965184

def SurrogateDiagonalTailChunk000Sub001Block166Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15105
    = surrogateDiagTailX0RatChunk000Sub001Block166Part003

theorem surrogateDiagonalTailChunk000Sub001Block166Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part003] using hcert

def TailChunk000Sub001Block166Part004SupportExplicit : Finset ℕ :=
  ([15106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part004 : ℚ :=
  (480221934775 : ℚ) / 3038171280930275328

def SurrogateDiagonalTailChunk000Sub001Block166Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15106
    = surrogateDiagTailX0RatChunk000Sub001Block166Part004

theorem surrogateDiagonalTailChunk000Sub001Block166Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part004] using hcert

def TailChunk000Sub001Block166Part005SupportExplicit : Finset ℕ :=
  ([15107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block166Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15107
    = surrogateDiagTailX0RatChunk000Sub001Block166Part005

theorem surrogateDiagonalTailChunk000Sub001Block166Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part005] using hcert

def TailChunk000Sub001Block166Part006SupportExplicit : Finset ℕ :=
  ([15109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part006 : ℚ :=
  (7097084929 : ℚ) / 4495027469824819200

def SurrogateDiagonalTailChunk000Sub001Block166Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15109
    = surrogateDiagTailX0RatChunk000Sub001Block166Part006

theorem surrogateDiagonalTailChunk000Sub001Block166Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part006] using hcert

def TailChunk000Sub001Block166Part007SupportExplicit : Finset ℕ :=
  ([15110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part007 : ℚ :=
  (3806218509 : ℚ) / 22186221999795200

def SurrogateDiagonalTailChunk000Sub001Block166Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15110
    = surrogateDiagTailX0RatChunk000Sub001Block166Part007

theorem surrogateDiagonalTailChunk000Sub001Block166Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part007] using hcert

def TailChunk000Sub001Block166Part008SupportExplicit : Finset ℕ :=
  ([15113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part008 : ℚ :=
  (391469375825 : ℚ) / 26764798359622385664

def SurrogateDiagonalTailChunk000Sub001Block166Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15113
    = surrogateDiagTailX0RatChunk000Sub001Block166Part008

theorem surrogateDiagonalTailChunk000Sub001Block166Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part008] using hcert

def TailChunk000Sub001Block166Part009SupportExplicit : Finset ℕ :=
  ([15114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part009 : ℚ :=
  (1681649263 : ℚ) / 2276106714316800

def SurrogateDiagonalTailChunk000Sub001Block166Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15114
    = surrogateDiagTailX0RatChunk000Sub001Block166Part009

theorem surrogateDiagonalTailChunk000Sub001Block166Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part009] using hcert

def TailChunk000Sub001Block166Part010SupportExplicit : Finset ℕ :=
  ([15115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part010 : ℚ :=
  (1142582406025 : ℚ) / 53388124456357152768

def SurrogateDiagonalTailChunk000Sub001Block166Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15115
    = surrogateDiagTailX0RatChunk000Sub001Block166Part010

theorem surrogateDiagonalTailChunk000Sub001Block166Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part010] using hcert

def TailChunk000Sub001Block166Part011SupportExplicit : Finset ℕ :=
  ([15117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part011 : ℚ :=
  (793482655775 : ℚ) / 12886930861300820544

def SurrogateDiagonalTailChunk000Sub001Block166Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15117
    = surrogateDiagTailX0RatChunk000Sub001Block166Part011

theorem surrogateDiagonalTailChunk000Sub001Block166Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part011] using hcert

def TailChunk000Sub001Block166Part012SupportExplicit : Finset ℕ :=
  ([15118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block166Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15118
    = surrogateDiagTailX0RatChunk000Sub001Block166Part012

theorem surrogateDiagonalTailChunk000Sub001Block166Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part012] using hcert

def TailChunk000Sub001Block166Part013SupportExplicit : Finset ℕ :=
  ([15119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part013 : ℚ :=
  (425366318875 : ℚ) / 94531457789401909248

def SurrogateDiagonalTailChunk000Sub001Block166Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15119
    = surrogateDiagTailX0RatChunk000Sub001Block166Part013

theorem surrogateDiagonalTailChunk000Sub001Block166Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part013] using hcert

def TailChunk000Sub001Block166Part014SupportExplicit : Finset ℕ :=
  ([15121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block166Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15121
    = surrogateDiagTailX0RatChunk000Sub001Block166Part014

theorem surrogateDiagonalTailChunk000Sub001Block166Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part014] using hcert

def TailChunk000Sub001Block166Part015SupportExplicit : Finset ℕ :=
  ([15122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block166Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15122
    = surrogateDiagTailX0RatChunk000Sub001Block166Part015

theorem surrogateDiagonalTailChunk000Sub001Block166Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part015] using hcert

def TailChunk000Sub001Block166Part016SupportExplicit : Finset ℕ :=
  ([15126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part016 : ℚ :=
  (15885322259 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub001Block166Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15126
    = surrogateDiagTailX0RatChunk000Sub001Block166Part016

theorem surrogateDiagonalTailChunk000Sub001Block166Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part016] using hcert

def TailChunk000Sub001Block166Part017SupportExplicit : Finset ℕ :=
  ([15127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part017 : ℚ :=
  (11699163107 : ℚ) / 1410837064718745600

def SurrogateDiagonalTailChunk000Sub001Block166Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15127
    = surrogateDiagTailX0RatChunk000Sub001Block166Part017

theorem surrogateDiagonalTailChunk000Sub001Block166Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part017] using hcert

def TailChunk000Sub001Block166Part018SupportExplicit : Finset ℕ :=
  ([15130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part018 : ℚ :=
  (165849338025 : ℚ) / 838602569386295296

def SurrogateDiagonalTailChunk000Sub001Block166Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15130
    = surrogateDiagTailX0RatChunk000Sub001Block166Part018

theorem surrogateDiagonalTailChunk000Sub001Block166Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part018] using hcert

def TailChunk000Sub001Block166Part019SupportExplicit : Finset ℕ :=
  ([15131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block166Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15131
    = surrogateDiagTailX0RatChunk000Sub001Block166Part019

theorem surrogateDiagonalTailChunk000Sub001Block166Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part019] using hcert

def TailChunk000Sub001Block166Part020SupportExplicit : Finset ℕ :=
  ([15133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part020 : ℚ :=
  (15090358025 : ℚ) / 12931086143470436352

def SurrogateDiagonalTailChunk000Sub001Block166Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15133
    = surrogateDiagTailX0RatChunk000Sub001Block166Part020

theorem surrogateDiagonalTailChunk000Sub001Block166Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part020] using hcert

def TailChunk000Sub001Block166Part021SupportExplicit : Finset ℕ :=
  ([15134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part021 : ℚ :=
  (49283466425 : ℚ) / 377669054492116992

def SurrogateDiagonalTailChunk000Sub001Block166Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15134
    = surrogateDiagTailX0RatChunk000Sub001Block166Part021

theorem surrogateDiagonalTailChunk000Sub001Block166Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part021] using hcert

def TailChunk000Sub001Block166Part022SupportExplicit : Finset ℕ :=
  ([15135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part022 : ℚ :=
  (1463269527025 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk000Sub001Block166Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15135
    = surrogateDiagTailX0RatChunk000Sub001Block166Part022

theorem surrogateDiagonalTailChunk000Sub001Block166Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part022] using hcert

def TailChunk000Sub001Block166Part023SupportExplicit : Finset ℕ :=
  ([15137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block166Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15137
    = surrogateDiagTailX0RatChunk000Sub001Block166Part023

theorem surrogateDiagonalTailChunk000Sub001Block166Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part023] using hcert

def TailChunk000Sub001Block166Part024SupportExplicit : Finset ℕ :=
  ([15139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block166Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block166Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15139
    = surrogateDiagTailX0RatChunk000Sub001Block166Part024

theorem surrogateDiagonalTailChunk000Sub001Block166Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block166Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block166Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block166Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block166Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block166Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block166Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block166HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block166Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block166Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block166Part000
    + surrogateDiagTailX0RatChunk000Sub001Block166Part001
    + surrogateDiagTailX0RatChunk000Sub001Block166Part002
    + surrogateDiagTailX0RatChunk000Sub001Block166Part003
    + surrogateDiagTailX0RatChunk000Sub001Block166Part004
    + surrogateDiagTailX0RatChunk000Sub001Block166Part005
    + surrogateDiagTailX0RatChunk000Sub001Block166Part006
    + surrogateDiagTailX0RatChunk000Sub001Block166Part007
    + surrogateDiagTailX0RatChunk000Sub001Block166Part008
    + surrogateDiagTailX0RatChunk000Sub001Block166Part009

def surrogateDiagonalTailChunk000Sub001Block166MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block166Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block166Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block166Part010
    + surrogateDiagTailX0RatChunk000Sub001Block166Part011
    + surrogateDiagTailX0RatChunk000Sub001Block166Part012
    + surrogateDiagTailX0RatChunk000Sub001Block166Part013
    + surrogateDiagTailX0RatChunk000Sub001Block166Part014
    + surrogateDiagTailX0RatChunk000Sub001Block166Part015
    + surrogateDiagTailX0RatChunk000Sub001Block166Part016
    + surrogateDiagTailX0RatChunk000Sub001Block166Part017
    + surrogateDiagTailX0RatChunk000Sub001Block166Part018
    + surrogateDiagTailX0RatChunk000Sub001Block166Part019

def surrogateDiagonalTailChunk000Sub001Block166TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block166Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block166Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block166Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block166Part020
    + surrogateDiagTailX0RatChunk000Sub001Block166Part021
    + surrogateDiagTailX0RatChunk000Sub001Block166Part022
    + surrogateDiagTailX0RatChunk000Sub001Block166Part023
    + surrogateDiagTailX0RatChunk000Sub001Block166Part024

def surrogateDiagonalTailChunk000Sub001Block166Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block166HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block166MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block166TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block166 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block166Part000
    + surrogateDiagTailX0RatChunk000Sub001Block166Part001
    + surrogateDiagTailX0RatChunk000Sub001Block166Part002
    + surrogateDiagTailX0RatChunk000Sub001Block166Part003
    + surrogateDiagTailX0RatChunk000Sub001Block166Part004
    + surrogateDiagTailX0RatChunk000Sub001Block166Part005
    + surrogateDiagTailX0RatChunk000Sub001Block166Part006
    + surrogateDiagTailX0RatChunk000Sub001Block166Part007
    + surrogateDiagTailX0RatChunk000Sub001Block166Part008
    + surrogateDiagTailX0RatChunk000Sub001Block166Part009
    + surrogateDiagTailX0RatChunk000Sub001Block166Part010
    + surrogateDiagTailX0RatChunk000Sub001Block166Part011
    + surrogateDiagTailX0RatChunk000Sub001Block166Part012
    + surrogateDiagTailX0RatChunk000Sub001Block166Part013
    + surrogateDiagTailX0RatChunk000Sub001Block166Part014
    + surrogateDiagTailX0RatChunk000Sub001Block166Part015
    + surrogateDiagTailX0RatChunk000Sub001Block166Part016
    + surrogateDiagTailX0RatChunk000Sub001Block166Part017
    + surrogateDiagTailX0RatChunk000Sub001Block166Part018
    + surrogateDiagTailX0RatChunk000Sub001Block166Part019
    + surrogateDiagTailX0RatChunk000Sub001Block166Part020
    + surrogateDiagTailX0RatChunk000Sub001Block166Part021
    + surrogateDiagTailX0RatChunk000Sub001Block166Part022
    + surrogateDiagTailX0RatChunk000Sub001Block166Part023
    + surrogateDiagTailX0RatChunk000Sub001Block166Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block166_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block166Head + surrogateDiagTailX0RatChunk000Sub001Block166Mid + surrogateDiagTailX0RatChunk000Sub001Block166Tail =
      surrogateDiagTailX0RatChunk000Sub001Block166 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block166Head surrogateDiagTailX0RatChunk000Sub001Block166Mid surrogateDiagTailX0RatChunk000Sub001Block166Tail surrogateDiagTailX0RatChunk000Sub001Block166
  ring

def SurrogateDiagonalTailChunk000Sub001Block166HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block166HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block166Head

def SurrogateDiagonalTailChunk000Sub001Block166MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block166MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block166Mid

def SurrogateDiagonalTailChunk000Sub001Block166TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block166TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block166Tail

theorem surrogateDiagonalTailChunk000Sub001Block166_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block166HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block166MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block166TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block166Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block166 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block166HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block166MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block166TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block166Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block166_eq_head_add_mid_add_tail

/-- Block 167 covers tail-support indices [9175,9200) and q from 15142 to 15182. -/

def TailChunk000Sub001Block167Part000SupportExplicit : Finset ℕ :=
  ([15142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part000 : ℚ :=
  (441974125 : ℚ) / 59252154503528448

def SurrogateDiagonalTailChunk000Sub001Block167Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15142
    = surrogateDiagTailX0RatChunk000Sub001Block167Part000

theorem surrogateDiagonalTailChunk000Sub001Block167Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part000] using hcert

def TailChunk000Sub001Block167Part001SupportExplicit : Finset ℕ :=
  ([15143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part001 : ℚ :=
  (121495389725 : ℚ) / 52691329235151627264

def SurrogateDiagonalTailChunk000Sub001Block167Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15143
    = surrogateDiagTailX0RatChunk000Sub001Block167Part001

theorem surrogateDiagonalTailChunk000Sub001Block167Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part001] using hcert

def TailChunk000Sub001Block167Part002SupportExplicit : Finset ℕ :=
  ([15145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part002 : ℚ :=
  (257324403875 : ℚ) / 12818065698991374336

def SurrogateDiagonalTailChunk000Sub001Block167Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15145
    = surrogateDiagTailX0RatChunk000Sub001Block167Part002

theorem surrogateDiagonalTailChunk000Sub001Block167Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part002] using hcert

def TailChunk000Sub001Block167Part003SupportExplicit : Finset ℕ :=
  ([15146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block167Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15146
    = surrogateDiagTailX0RatChunk000Sub001Block167Part003

theorem surrogateDiagonalTailChunk000Sub001Block167Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part003] using hcert

def TailChunk000Sub001Block167Part004SupportExplicit : Finset ℕ :=
  ([15149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block167Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15149
    = surrogateDiagTailX0RatChunk000Sub001Block167Part004

theorem surrogateDiagonalTailChunk000Sub001Block167Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part004] using hcert

def TailChunk000Sub001Block167Part005SupportExplicit : Finset ℕ :=
  ([15151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part005 : ℚ :=
  (76391146975 : ℚ) / 123378142196237027328

def SurrogateDiagonalTailChunk000Sub001Block167Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15151
    = surrogateDiagTailX0RatChunk000Sub001Block167Part005

theorem surrogateDiagonalTailChunk000Sub001Block167Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part005] using hcert

def TailChunk000Sub001Block167Part006SupportExplicit : Finset ℕ :=
  ([15153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part006 : ℚ :=
  (255049979797 : ℚ) / 1040812130802000000

def SurrogateDiagonalTailChunk000Sub001Block167Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15153
    = surrogateDiagTailX0RatChunk000Sub001Block167Part006

theorem surrogateDiagonalTailChunk000Sub001Block167Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part006] using hcert

def TailChunk000Sub001Block167Part007SupportExplicit : Finset ℕ :=
  ([15154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part007 : ℚ :=
  (897045765625 : ℚ) / 2059333723539190272

def SurrogateDiagonalTailChunk000Sub001Block167Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15154
    = surrogateDiagTailX0RatChunk000Sub001Block167Part007

theorem surrogateDiagonalTailChunk000Sub001Block167Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part007] using hcert

def TailChunk000Sub001Block167Part008SupportExplicit : Finset ℕ :=
  ([15155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part008 : ℚ :=
  (1268859340825 : ℚ) / 4815657180906651648

def SurrogateDiagonalTailChunk000Sub001Block167Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15155
    = surrogateDiagTailX0RatChunk000Sub001Block167Part008

theorem surrogateDiagonalTailChunk000Sub001Block167Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part008] using hcert

def TailChunk000Sub001Block167Part009SupportExplicit : Finset ℕ :=
  ([15157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part009 : ℚ :=
  (6647425053875 : ℚ) / 54902378683255354944

def SurrogateDiagonalTailChunk000Sub001Block167Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15157
    = surrogateDiagTailX0RatChunk000Sub001Block167Part009

theorem surrogateDiagonalTailChunk000Sub001Block167Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part009] using hcert

def TailChunk000Sub001Block167Part010SupportExplicit : Finset ℕ :=
  ([15158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part010 : ℚ :=
  (55306721381 : ℚ) / 75821996054937600

def SurrogateDiagonalTailChunk000Sub001Block167Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15158
    = surrogateDiagTailX0RatChunk000Sub001Block167Part010

theorem surrogateDiagonalTailChunk000Sub001Block167Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part010] using hcert

def TailChunk000Sub001Block167Part011SupportExplicit : Finset ℕ :=
  ([15159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part011 : ℚ :=
  (240673302193 : ℚ) / 892795330017331200

def SurrogateDiagonalTailChunk000Sub001Block167Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15159
    = surrogateDiagTailX0RatChunk000Sub001Block167Part011

theorem surrogateDiagonalTailChunk000Sub001Block167Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part011] using hcert

def TailChunk000Sub001Block167Part012SupportExplicit : Finset ℕ :=
  ([15161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part012 : ℚ :=
  (5746398025 : ℚ) / 52830370376643072

def SurrogateDiagonalTailChunk000Sub001Block167Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15161
    = surrogateDiagTailX0RatChunk000Sub001Block167Part012

theorem surrogateDiagonalTailChunk000Sub001Block167Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part012] using hcert

def TailChunk000Sub001Block167Part013SupportExplicit : Finset ℕ :=
  ([15163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part013 : ℚ :=
  (4624031956125 : ℚ) / 40511417517799899136

def SurrogateDiagonalTailChunk000Sub001Block167Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15163
    = surrogateDiagTailX0RatChunk000Sub001Block167Part013

theorem surrogateDiagonalTailChunk000Sub001Block167Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part013] using hcert

def TailChunk000Sub001Block167Part014SupportExplicit : Finset ℕ :=
  ([15166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part014 : ℚ :=
  (898467015625 : ℚ) / 2065865238087141522

def SurrogateDiagonalTailChunk000Sub001Block167Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15166
    = surrogateDiagTailX0RatChunk000Sub001Block167Part014

theorem surrogateDiagonalTailChunk000Sub001Block167Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part014] using hcert

def TailChunk000Sub001Block167Part015SupportExplicit : Finset ℕ :=
  ([15167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part015 : ℚ :=
  (249962344325 : ℚ) / 2113232282177006592

def SurrogateDiagonalTailChunk000Sub001Block167Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15167
    = surrogateDiagTailX0RatChunk000Sub001Block167Part015

theorem surrogateDiagonalTailChunk000Sub001Block167Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part015] using hcert

def TailChunk000Sub001Block167Part016SupportExplicit : Finset ℕ :=
  ([15169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part016 : ℚ :=
  (10798082807 : ℚ) / 54657289745694720

def SurrogateDiagonalTailChunk000Sub001Block167Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15169
    = surrogateDiagTailX0RatChunk000Sub001Block167Part016

theorem surrogateDiagonalTailChunk000Sub001Block167Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part016] using hcert

def TailChunk000Sub001Block167Part017SupportExplicit : Finset ℕ :=
  ([15170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part017 : ℚ :=
  (5384518009 : ℚ) / 6116518291046400

def SurrogateDiagonalTailChunk000Sub001Block167Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15170
    = surrogateDiagTailX0RatChunk000Sub001Block167Part017

theorem surrogateDiagonalTailChunk000Sub001Block167Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part017] using hcert

def TailChunk000Sub001Block167Part018SupportExplicit : Finset ℕ :=
  ([15171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part018 : ℚ :=
  (2812188174275 : ℚ) / 9400884835584835584

def SurrogateDiagonalTailChunk000Sub001Block167Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15171
    = surrogateDiagTailX0RatChunk000Sub001Block167Part018

theorem surrogateDiagonalTailChunk000Sub001Block167Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part018] using hcert

def TailChunk000Sub001Block167Part019SupportExplicit : Finset ℕ :=
  ([15173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part019 : ℚ :=
  (3597186390625 : ℚ) / 33123651269380921632

def SurrogateDiagonalTailChunk000Sub001Block167Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15173
    = surrogateDiagTailX0RatChunk000Sub001Block167Part019

theorem surrogateDiagonalTailChunk000Sub001Block167Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part019] using hcert

def TailChunk000Sub001Block167Part020SupportExplicit : Finset ℕ :=
  ([15177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part020 : ℚ :=
  (6396465494125 : ℚ) / 26185576610368291968

def SurrogateDiagonalTailChunk000Sub001Block167Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15177
    = surrogateDiagTailX0RatChunk000Sub001Block167Part020

theorem surrogateDiagonalTailChunk000Sub001Block167Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part020] using hcert

def TailChunk000Sub001Block167Part021SupportExplicit : Finset ℕ :=
  ([15178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part021 : ℚ :=
  (899889390625 : ℚ) / 2072412277156476192

def SurrogateDiagonalTailChunk000Sub001Block167Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15178
    = surrogateDiagTailX0RatChunk000Sub001Block167Part021

theorem surrogateDiagonalTailChunk000Sub001Block167Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part021] using hcert

def TailChunk000Sub001Block167Part022SupportExplicit : Finset ℕ :=
  ([15179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part022 : ℚ :=
  (13775633988175 : ℚ) / 119452343479113351168

def SurrogateDiagonalTailChunk000Sub001Block167Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15179
    = surrogateDiagTailX0RatChunk000Sub001Block167Part022

theorem surrogateDiagonalTailChunk000Sub001Block167Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part022] using hcert

def TailChunk000Sub001Block167Part023SupportExplicit : Finset ℕ :=
  ([15181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part023 : ℚ :=
  (11487718095325 : ℚ) / 77024366778812203008

def SurrogateDiagonalTailChunk000Sub001Block167Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15181
    = surrogateDiagTailX0RatChunk000Sub001Block167Part023

theorem surrogateDiagonalTailChunk000Sub001Block167Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part023] using hcert

def TailChunk000Sub001Block167Part024SupportExplicit : Finset ℕ :=
  ([15182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block167Part024 : ℚ :=
  (1440582025 : ℚ) / 3319356924247122

def SurrogateDiagonalTailChunk000Sub001Block167Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15182
    = surrogateDiagTailX0RatChunk000Sub001Block167Part024

theorem surrogateDiagonalTailChunk000Sub001Block167Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block167Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block167Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block167Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block167Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block167Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block167Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block167HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block167Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block167Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block167Part000
    + surrogateDiagTailX0RatChunk000Sub001Block167Part001
    + surrogateDiagTailX0RatChunk000Sub001Block167Part002
    + surrogateDiagTailX0RatChunk000Sub001Block167Part003
    + surrogateDiagTailX0RatChunk000Sub001Block167Part004
    + surrogateDiagTailX0RatChunk000Sub001Block167Part005
    + surrogateDiagTailX0RatChunk000Sub001Block167Part006
    + surrogateDiagTailX0RatChunk000Sub001Block167Part007
    + surrogateDiagTailX0RatChunk000Sub001Block167Part008
    + surrogateDiagTailX0RatChunk000Sub001Block167Part009

def surrogateDiagonalTailChunk000Sub001Block167MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block167Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block167Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block167Part010
    + surrogateDiagTailX0RatChunk000Sub001Block167Part011
    + surrogateDiagTailX0RatChunk000Sub001Block167Part012
    + surrogateDiagTailX0RatChunk000Sub001Block167Part013
    + surrogateDiagTailX0RatChunk000Sub001Block167Part014
    + surrogateDiagTailX0RatChunk000Sub001Block167Part015
    + surrogateDiagTailX0RatChunk000Sub001Block167Part016
    + surrogateDiagTailX0RatChunk000Sub001Block167Part017
    + surrogateDiagTailX0RatChunk000Sub001Block167Part018
    + surrogateDiagTailX0RatChunk000Sub001Block167Part019

def surrogateDiagonalTailChunk000Sub001Block167TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block167Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block167Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block167Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block167Part020
    + surrogateDiagTailX0RatChunk000Sub001Block167Part021
    + surrogateDiagTailX0RatChunk000Sub001Block167Part022
    + surrogateDiagTailX0RatChunk000Sub001Block167Part023
    + surrogateDiagTailX0RatChunk000Sub001Block167Part024

def surrogateDiagonalTailChunk000Sub001Block167Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block167HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block167MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block167TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block167 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block167Part000
    + surrogateDiagTailX0RatChunk000Sub001Block167Part001
    + surrogateDiagTailX0RatChunk000Sub001Block167Part002
    + surrogateDiagTailX0RatChunk000Sub001Block167Part003
    + surrogateDiagTailX0RatChunk000Sub001Block167Part004
    + surrogateDiagTailX0RatChunk000Sub001Block167Part005
    + surrogateDiagTailX0RatChunk000Sub001Block167Part006
    + surrogateDiagTailX0RatChunk000Sub001Block167Part007
    + surrogateDiagTailX0RatChunk000Sub001Block167Part008
    + surrogateDiagTailX0RatChunk000Sub001Block167Part009
    + surrogateDiagTailX0RatChunk000Sub001Block167Part010
    + surrogateDiagTailX0RatChunk000Sub001Block167Part011
    + surrogateDiagTailX0RatChunk000Sub001Block167Part012
    + surrogateDiagTailX0RatChunk000Sub001Block167Part013
    + surrogateDiagTailX0RatChunk000Sub001Block167Part014
    + surrogateDiagTailX0RatChunk000Sub001Block167Part015
    + surrogateDiagTailX0RatChunk000Sub001Block167Part016
    + surrogateDiagTailX0RatChunk000Sub001Block167Part017
    + surrogateDiagTailX0RatChunk000Sub001Block167Part018
    + surrogateDiagTailX0RatChunk000Sub001Block167Part019
    + surrogateDiagTailX0RatChunk000Sub001Block167Part020
    + surrogateDiagTailX0RatChunk000Sub001Block167Part021
    + surrogateDiagTailX0RatChunk000Sub001Block167Part022
    + surrogateDiagTailX0RatChunk000Sub001Block167Part023
    + surrogateDiagTailX0RatChunk000Sub001Block167Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block167_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block167Head + surrogateDiagTailX0RatChunk000Sub001Block167Mid + surrogateDiagTailX0RatChunk000Sub001Block167Tail =
      surrogateDiagTailX0RatChunk000Sub001Block167 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block167Head surrogateDiagTailX0RatChunk000Sub001Block167Mid surrogateDiagTailX0RatChunk000Sub001Block167Tail surrogateDiagTailX0RatChunk000Sub001Block167
  ring

def SurrogateDiagonalTailChunk000Sub001Block167HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block167HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block167Head

def SurrogateDiagonalTailChunk000Sub001Block167MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block167MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block167Mid

def SurrogateDiagonalTailChunk000Sub001Block167TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block167TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block167Tail

theorem surrogateDiagonalTailChunk000Sub001Block167_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block167HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block167MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block167TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block167Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block167 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block167HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block167MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block167TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block167Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block167_eq_head_add_mid_add_tail

/-- Block 168 covers tail-support indices [9200,9225) and q from 15185 to 15222. -/

def TailChunk000Sub001Block168Part000SupportExplicit : Finset ℕ :=
  ([15185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part000 : ℚ :=
  (9795549144775 : ℚ) / 54384343846864846848

def SurrogateDiagonalTailChunk000Sub001Block168Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15185
    = surrogateDiagTailX0RatChunk000Sub001Block168Part000

theorem surrogateDiagonalTailChunk000Sub001Block168Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part000] using hcert

def TailChunk000Sub001Block168Part001SupportExplicit : Finset ℕ :=
  ([15186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part001 : ℚ :=
  (5003065423 : ℚ) / 4097971511416200

def SurrogateDiagonalTailChunk000Sub001Block168Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15186
    = surrogateDiagTailX0RatChunk000Sub001Block168Part001

theorem surrogateDiagonalTailChunk000Sub001Block168Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part001] using hcert

def TailChunk000Sub001Block168Part002SupportExplicit : Finset ℕ :=
  ([15187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part002 : ℚ :=
  (3603827640625 : ℚ) / 33246080316638040402

def SurrogateDiagonalTailChunk000Sub001Block168Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15187
    = surrogateDiagTailX0RatChunk000Sub001Block168Part002

theorem surrogateDiagonalTailChunk000Sub001Block168Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part002] using hcert

def TailChunk000Sub001Block168Part003SupportExplicit : Finset ℕ :=
  ([15189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part003 : ℚ :=
  (245466473869 : ℚ) / 937707185472307200

def SurrogateDiagonalTailChunk000Sub001Block168Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15189
    = surrogateDiagTailX0RatChunk000Sub001Block168Part003

theorem surrogateDiagonalTailChunk000Sub001Block168Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part003] using hcert

def TailChunk000Sub001Block168Part004SupportExplicit : Finset ℕ :=
  ([15191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part004 : ℚ :=
  (121445756101 : ℚ) / 906866176968000000

def SurrogateDiagonalTailChunk000Sub001Block168Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15191
    = surrogateDiagTailX0RatChunk000Sub001Block168Part004

theorem surrogateDiagonalTailChunk000Sub001Block168Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part004] using hcert

def TailChunk000Sub001Block168Part005SupportExplicit : Finset ℕ :=
  ([15193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part005 : ℚ :=
  (3606675765625 : ℚ) / 33298653669200589312

def SurrogateDiagonalTailChunk000Sub001Block168Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15193
    = surrogateDiagTailX0RatChunk000Sub001Block168Part005

theorem surrogateDiagonalTailChunk000Sub001Block168Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part005] using hcert

def TailChunk000Sub001Block168Part006SupportExplicit : Finset ℕ :=
  ([15194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part006 : ℚ :=
  (6990759161 : ℚ) / 15159067111980960

def SurrogateDiagonalTailChunk000Sub001Block168Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15194
    = surrogateDiagTailX0RatChunk000Sub001Block168Part006

theorem surrogateDiagonalTailChunk000Sub001Block168Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part006] using hcert

def TailChunk000Sub001Block168Part007SupportExplicit : Finset ℕ :=
  ([15195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part007 : ℚ :=
  (4547002837825 : ℚ) / 10742586438886883328

def SurrogateDiagonalTailChunk000Sub001Block168Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15195
    = surrogateDiagTailX0RatChunk000Sub001Block168Part007

theorem surrogateDiagonalTailChunk000Sub001Block168Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part007] using hcert

def TailChunk000Sub001Block168Part008SupportExplicit : Finset ℕ :=
  ([15197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part008 : ℚ :=
  (58185377875 : ℚ) / 314973620289552384

def SurrogateDiagonalTailChunk000Sub001Block168Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15197
    = surrogateDiagTailX0RatChunk000Sub001Block168Part008

theorem surrogateDiagonalTailChunk000Sub001Block168Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part008] using hcert

def TailChunk000Sub001Block168Part009SupportExplicit : Finset ℕ :=
  ([15198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part009 : ℚ :=
  (307898334675 : ℚ) / 209663283710394368

def SurrogateDiagonalTailChunk000Sub001Block168Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15198
    = surrogateDiagTailX0RatChunk000Sub001Block168Part009

theorem surrogateDiagonalTailChunk000Sub001Block168Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part009] using hcert

def TailChunk000Sub001Block168Part010SupportExplicit : Finset ℕ :=
  ([15199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part010 : ℚ :=
  (3609525015625 : ℚ) / 33351289349381069202

def SurrogateDiagonalTailChunk000Sub001Block168Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15199
    = surrogateDiagTailX0RatChunk000Sub001Block168Part010

theorem surrogateDiagonalTailChunk000Sub001Block168Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part010] using hcert

def TailChunk000Sub001Block168Part011SupportExplicit : Finset ℕ :=
  ([15202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part011 : ℚ :=
  (4210426649 : ℚ) / 7557218141400000

def SurrogateDiagonalTailChunk000Sub001Block168Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15202
    = surrogateDiagTailX0RatChunk000Sub001Block168Part011

theorem surrogateDiagonalTailChunk000Sub001Block168Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part011] using hcert

def TailChunk000Sub001Block168Part012SupportExplicit : Finset ℕ :=
  ([15203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part012 : ℚ :=
  (533934049963 : ℚ) / 4445834745567283200

def SurrogateDiagonalTailChunk000Sub001Block168Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15203
    = surrogateDiagTailX0RatChunk000Sub001Block168Part012

theorem surrogateDiagonalTailChunk000Sub001Block168Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part012] using hcert

def TailChunk000Sub001Block168Part013SupportExplicit : Finset ℕ :=
  ([15205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part013 : ℚ :=
  (392854983019 : ℚ) / 2186860851049267200

def SurrogateDiagonalTailChunk000Sub001Block168Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15205
    = surrogateDiagTailX0RatChunk000Sub001Block168Part013

theorem surrogateDiagonalTailChunk000Sub001Block168Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part013] using hcert

def TailChunk000Sub001Block168Part014SupportExplicit : Finset ℕ :=
  ([15206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part014 : ℚ :=
  (903212640625 : ℚ) / 2087749212901320402

def SurrogateDiagonalTailChunk000Sub001Block168Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15206
    = surrogateDiagTailX0RatChunk000Sub001Block168Part014

theorem surrogateDiagonalTailChunk000Sub001Block168Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part014] using hcert

def TailChunk000Sub001Block168Part015SupportExplicit : Finset ℕ :=
  ([15207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part015 : ℚ :=
  (677168573975 : ℚ) / 2554288620932431872

def SurrogateDiagonalTailChunk000Sub001Block168Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15207
    = surrogateDiagTailX0RatChunk000Sub001Block168Part015

theorem surrogateDiagonalTailChunk000Sub001Block168Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part015] using hcert

def TailChunk000Sub001Block168Part016SupportExplicit : Finset ℕ :=
  ([15209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part016 : ℚ :=
  (777468427375 : ℚ) / 6876443081328422976

def SurrogateDiagonalTailChunk000Sub001Block168Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15209
    = surrogateDiagTailX0RatChunk000Sub001Block168Part016

theorem surrogateDiagonalTailChunk000Sub001Block168Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part016] using hcert

def TailChunk000Sub001Block168Part017SupportExplicit : Finset ℕ :=
  ([15211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part017 : ℚ :=
  (406711031521 : ℚ) / 2426303873758003200

def SurrogateDiagonalTailChunk000Sub001Block168Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15211
    = surrogateDiagTailX0RatChunk000Sub001Block168Part017

theorem surrogateDiagonalTailChunk000Sub001Block168Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part017] using hcert

def TailChunk000Sub001Block168Part018SupportExplicit : Finset ℕ :=
  ([15213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part018 : ℚ :=
  (55474513909 : ℚ) / 179134059648000000

def SurrogateDiagonalTailChunk000Sub001Block168Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15213
    = surrogateDiagTailX0RatChunk000Sub001Block168Part018

theorem surrogateDiagonalTailChunk000Sub001Block168Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part018] using hcert

def TailChunk000Sub001Block168Part019SupportExplicit : Finset ℕ :=
  ([15214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part019 : ℚ :=
  (904163265625 : ℚ) / 2092146787393150962

def SurrogateDiagonalTailChunk000Sub001Block168Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15214
    = surrogateDiagTailX0RatChunk000Sub001Block168Part019

theorem surrogateDiagonalTailChunk000Sub001Block168Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part019] using hcert

def TailChunk000Sub001Block168Part020SupportExplicit : Finset ℕ :=
  ([15215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part020 : ℚ :=
  (8332794216175 : ℚ) / 42114026304278888448

def SurrogateDiagonalTailChunk000Sub001Block168Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15215
    = surrogateDiagTailX0RatChunk000Sub001Block168Part020

theorem surrogateDiagonalTailChunk000Sub001Block168Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part020] using hcert

def TailChunk000Sub001Block168Part021SupportExplicit : Finset ℕ :=
  ([15217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part021 : ℚ :=
  (3618079515625 : ℚ) / 33509570848143777792

def SurrogateDiagonalTailChunk000Sub001Block168Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15217
    = surrogateDiagTailX0RatChunk000Sub001Block168Part021

theorem surrogateDiagonalTailChunk000Sub001Block168Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part021] using hcert

def TailChunk000Sub001Block168Part022SupportExplicit : Finset ℕ :=
  ([15218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part022 : ℚ :=
  (2950892768275 : ℚ) / 4507660108155120768

def SurrogateDiagonalTailChunk000Sub001Block168Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15218
    = surrogateDiagTailX0RatChunk000Sub001Block168Part022

theorem surrogateDiagonalTailChunk000Sub001Block168Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part022] using hcert

def TailChunk000Sub001Block168Part023SupportExplicit : Finset ℕ :=
  ([15221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part023 : ℚ :=
  (109211053169 : ℚ) / 934084541552400000

def SurrogateDiagonalTailChunk000Sub001Block168Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15221
    = surrogateDiagTailX0RatChunk000Sub001Block168Part023

theorem surrogateDiagonalTailChunk000Sub001Block168Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part023] using hcert

def TailChunk000Sub001Block168Part024SupportExplicit : Finset ℕ :=
  ([15222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block168Part024 : ℚ :=
  (119729624425 : ℚ) / 88051345090708608

def SurrogateDiagonalTailChunk000Sub001Block168Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15222
    = surrogateDiagTailX0RatChunk000Sub001Block168Part024

theorem surrogateDiagonalTailChunk000Sub001Block168Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block168Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block168Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block168Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block168Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block168Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block168Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block168HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block168Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block168Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block168Part000
    + surrogateDiagTailX0RatChunk000Sub001Block168Part001
    + surrogateDiagTailX0RatChunk000Sub001Block168Part002
    + surrogateDiagTailX0RatChunk000Sub001Block168Part003
    + surrogateDiagTailX0RatChunk000Sub001Block168Part004
    + surrogateDiagTailX0RatChunk000Sub001Block168Part005
    + surrogateDiagTailX0RatChunk000Sub001Block168Part006
    + surrogateDiagTailX0RatChunk000Sub001Block168Part007
    + surrogateDiagTailX0RatChunk000Sub001Block168Part008
    + surrogateDiagTailX0RatChunk000Sub001Block168Part009

def surrogateDiagonalTailChunk000Sub001Block168MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block168Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block168Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block168Part010
    + surrogateDiagTailX0RatChunk000Sub001Block168Part011
    + surrogateDiagTailX0RatChunk000Sub001Block168Part012
    + surrogateDiagTailX0RatChunk000Sub001Block168Part013
    + surrogateDiagTailX0RatChunk000Sub001Block168Part014
    + surrogateDiagTailX0RatChunk000Sub001Block168Part015
    + surrogateDiagTailX0RatChunk000Sub001Block168Part016
    + surrogateDiagTailX0RatChunk000Sub001Block168Part017
    + surrogateDiagTailX0RatChunk000Sub001Block168Part018
    + surrogateDiagTailX0RatChunk000Sub001Block168Part019

def surrogateDiagonalTailChunk000Sub001Block168TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block168Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block168Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block168Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block168Part020
    + surrogateDiagTailX0RatChunk000Sub001Block168Part021
    + surrogateDiagTailX0RatChunk000Sub001Block168Part022
    + surrogateDiagTailX0RatChunk000Sub001Block168Part023
    + surrogateDiagTailX0RatChunk000Sub001Block168Part024

def surrogateDiagonalTailChunk000Sub001Block168Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block168HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block168MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block168TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block168 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block168Part000
    + surrogateDiagTailX0RatChunk000Sub001Block168Part001
    + surrogateDiagTailX0RatChunk000Sub001Block168Part002
    + surrogateDiagTailX0RatChunk000Sub001Block168Part003
    + surrogateDiagTailX0RatChunk000Sub001Block168Part004
    + surrogateDiagTailX0RatChunk000Sub001Block168Part005
    + surrogateDiagTailX0RatChunk000Sub001Block168Part006
    + surrogateDiagTailX0RatChunk000Sub001Block168Part007
    + surrogateDiagTailX0RatChunk000Sub001Block168Part008
    + surrogateDiagTailX0RatChunk000Sub001Block168Part009
    + surrogateDiagTailX0RatChunk000Sub001Block168Part010
    + surrogateDiagTailX0RatChunk000Sub001Block168Part011
    + surrogateDiagTailX0RatChunk000Sub001Block168Part012
    + surrogateDiagTailX0RatChunk000Sub001Block168Part013
    + surrogateDiagTailX0RatChunk000Sub001Block168Part014
    + surrogateDiagTailX0RatChunk000Sub001Block168Part015
    + surrogateDiagTailX0RatChunk000Sub001Block168Part016
    + surrogateDiagTailX0RatChunk000Sub001Block168Part017
    + surrogateDiagTailX0RatChunk000Sub001Block168Part018
    + surrogateDiagTailX0RatChunk000Sub001Block168Part019
    + surrogateDiagTailX0RatChunk000Sub001Block168Part020
    + surrogateDiagTailX0RatChunk000Sub001Block168Part021
    + surrogateDiagTailX0RatChunk000Sub001Block168Part022
    + surrogateDiagTailX0RatChunk000Sub001Block168Part023
    + surrogateDiagTailX0RatChunk000Sub001Block168Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block168_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block168Head + surrogateDiagTailX0RatChunk000Sub001Block168Mid + surrogateDiagTailX0RatChunk000Sub001Block168Tail =
      surrogateDiagTailX0RatChunk000Sub001Block168 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block168Head surrogateDiagTailX0RatChunk000Sub001Block168Mid surrogateDiagTailX0RatChunk000Sub001Block168Tail surrogateDiagTailX0RatChunk000Sub001Block168
  ring

def SurrogateDiagonalTailChunk000Sub001Block168HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block168HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block168Head

def SurrogateDiagonalTailChunk000Sub001Block168MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block168MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block168Mid

def SurrogateDiagonalTailChunk000Sub001Block168TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block168TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block168Tail

theorem surrogateDiagonalTailChunk000Sub001Block168_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block168HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block168MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block168TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block168Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block168 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block168HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block168MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block168TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block168Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block168_eq_head_add_mid_add_tail

/-- Block 169 covers tail-support indices [9225,9250) and q from 15223 to 15263. -/

def TailChunk000Sub001Block169Part000SupportExplicit : Finset ℕ :=
  ([15223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part000 : ℚ :=
  (253350128153 : ℚ) / 1943234828579865600

def SurrogateDiagonalTailChunk000Sub001Block169Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15223
    = surrogateDiagTailX0RatChunk000Sub001Block169Part000

theorem surrogateDiagonalTailChunk000Sub001Block169Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part000] using hcert

def TailChunk000Sub001Block169Part001SupportExplicit : Finset ℕ :=
  ([15226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part001 : ℚ :=
  (54899969 : ℚ) / 112268554180992

def SurrogateDiagonalTailChunk000Sub001Block169Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15226
    = surrogateDiagTailX0RatChunk000Sub001Block169Part001

theorem surrogateDiagonalTailChunk000Sub001Block169Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part001] using hcert

def TailChunk000Sub001Block169Part002SupportExplicit : Finset ℕ :=
  ([15227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part002 : ℚ :=
  (3622836390625 : ℚ) / 33597748080548524722

def SurrogateDiagonalTailChunk000Sub001Block169Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15227
    = surrogateDiagTailX0RatChunk000Sub001Block169Part002

theorem surrogateDiagonalTailChunk000Sub001Block169Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part002] using hcert

def TailChunk000Sub001Block169Part003SupportExplicit : Finset ℕ :=
  ([15229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part003 : ℚ :=
  (14095898421025 : ℚ) / 125779592815614885888

def SurrogateDiagonalTailChunk000Sub001Block169Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15229
    = surrogateDiagTailX0RatChunk000Sub001Block169Part003

theorem surrogateDiagonalTailChunk000Sub001Block169Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part003] using hcert

def TailChunk000Sub001Block169Part004SupportExplicit : Finset ℕ :=
  ([15230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part004 : ℚ :=
  (869233387275 : ℚ) / 1144996552934496256

def SurrogateDiagonalTailChunk000Sub001Block169Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15230
    = surrogateDiagTailX0RatChunk000Sub001Block169Part004

theorem surrogateDiagonalTailChunk000Sub001Block169Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part004] using hcert

def TailChunk000Sub001Block169Part005SupportExplicit : Finset ℕ :=
  ([15231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part005 : ℚ :=
  (6442068492325 : ℚ) / 26560319516990097408

def SurrogateDiagonalTailChunk000Sub001Block169Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15231
    = surrogateDiagTailX0RatChunk000Sub001Block169Part005

theorem surrogateDiagonalTailChunk000Sub001Block169Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part005] using hcert

def TailChunk000Sub001Block169Part006SupportExplicit : Finset ℕ :=
  ([15233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part006 : ℚ :=
  (3625692015625 : ℚ) / 33650737881255247872

def SurrogateDiagonalTailChunk000Sub001Block169Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15233
    = surrogateDiagTailX0RatChunk000Sub001Block169Part006

theorem surrogateDiagonalTailChunk000Sub001Block169Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part006] using hcert

def TailChunk000Sub001Block169Part007SupportExplicit : Finset ℕ :=
  ([15234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part007 : ℚ :=
  (251737274525 : ℚ) / 207502496226485136

def SurrogateDiagonalTailChunk000Sub001Block169Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15234
    = surrogateDiagTailX0RatChunk000Sub001Block169Part007

theorem surrogateDiagonalTailChunk000Sub001Block169Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part007] using hcert

def TailChunk000Sub001Block169Part008SupportExplicit : Finset ℕ :=
  ([15235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part008 : ℚ :=
  (5817205249 : ℚ) / 27514991561932800

def SurrogateDiagonalTailChunk000Sub001Block169Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15235
    = surrogateDiagTailX0RatChunk000Sub001Block169Part008

theorem surrogateDiagonalTailChunk000Sub001Block169Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part008] using hcert

def TailChunk000Sub001Block169Part009SupportExplicit : Finset ℕ :=
  ([15238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part009 : ℚ :=
  (134648055757 : ℚ) / 268792307712000000

def SurrogateDiagonalTailChunk000Sub001Block169Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15238
    = surrogateDiagTailX0RatChunk000Sub001Block169Part009

theorem surrogateDiagonalTailChunk000Sub001Block169Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part009] using hcert

def TailChunk000Sub001Block169Part010SupportExplicit : Finset ℕ :=
  ([15241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part010 : ℚ :=
  (5807202025 : ℚ) / 53954381476311552

def SurrogateDiagonalTailChunk000Sub001Block169Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15241
    = surrogateDiagTailX0RatChunk000Sub001Block169Part010

theorem surrogateDiagonalTailChunk000Sub001Block169Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part010] using hcert

def TailChunk000Sub001Block169Part011SupportExplicit : Finset ℕ :=
  ([15242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part011 : ℚ :=
  (1451991025 : ℚ) / 3372148842269472

def SurrogateDiagonalTailChunk000Sub001Block169Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15242
    = surrogateDiagTailX0RatChunk000Sub001Block169Part011

theorem surrogateDiagonalTailChunk000Sub001Block169Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part011] using hcert

def TailChunk000Sub001Block169Part012SupportExplicit : Finset ℕ :=
  ([15243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part012 : ℚ :=
  (258088979677 : ℚ) / 1065765560025907200

def SurrogateDiagonalTailChunk000Sub001Block169Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15243
    = surrogateDiagTailX0RatChunk000Sub001Block169Part012

theorem surrogateDiagonalTailChunk000Sub001Block169Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part012] using hcert

def TailChunk000Sub001Block169Part013SupportExplicit : Finset ℕ :=
  ([15245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part013 : ℚ :=
  (9873127446475 : ℚ) / 55249286631743029248

def SurrogateDiagonalTailChunk000Sub001Block169Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15245
    = surrogateDiagTailX0RatChunk000Sub001Block169Part013

theorem surrogateDiagonalTailChunk000Sub001Block169Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part013] using hcert

def TailChunk000Sub001Block169Part014SupportExplicit : Finset ℕ :=
  ([15247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part014 : ℚ :=
  (3525131079025 : ℚ) / 31444898203903721472

def SurrogateDiagonalTailChunk000Sub001Block169Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15247
    = surrogateDiagTailX0RatChunk000Sub001Block169Part014

theorem surrogateDiagonalTailChunk000Sub001Block169Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part014] using hcert

def TailChunk000Sub001Block169Part015SupportExplicit : Finset ℕ :=
  ([15249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part015 : ℚ :=
  (809836836475 : ℚ) / 2122712753759059968

def SurrogateDiagonalTailChunk000Sub001Block169Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15249
    = surrogateDiagTailX0RatChunk000Sub001Block169Part015

theorem surrogateDiagonalTailChunk000Sub001Block169Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part015] using hcert

def TailChunk000Sub001Block169Part016SupportExplicit : Finset ℕ :=
  ([15251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part016 : ℚ :=
  (565598190979 : ℚ) / 5063512500000000000

def SurrogateDiagonalTailChunk000Sub001Block169Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15251
    = surrogateDiagTailX0RatChunk000Sub001Block169Part016

theorem surrogateDiagonalTailChunk000Sub001Block169Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part016] using hcert

def TailChunk000Sub001Block169Part017SupportExplicit : Finset ℕ :=
  ([15253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part017 : ℚ :=
  (10972351123225 : ℚ) / 72922804414167362688

def SurrogateDiagonalTailChunk000Sub001Block169Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15253
    = surrogateDiagTailX0RatChunk000Sub001Block169Part017

theorem surrogateDiagonalTailChunk000Sub001Block169Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part017] using hcert

def TailChunk000Sub001Block169Part018SupportExplicit : Finset ℕ :=
  ([15254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part018 : ℚ :=
  (164288702925 : ℚ) / 344861612706408448

def SurrogateDiagonalTailChunk000Sub001Block169Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15254
    = surrogateDiagTailX0RatChunk000Sub001Block169Part018

theorem surrogateDiagonalTailChunk000Sub001Block169Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part018] using hcert

def TailChunk000Sub001Block169Part019SupportExplicit : Finset ℕ :=
  ([15257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part019 : ℚ :=
  (3069145907 : ℚ) / 19594959232204800

def SurrogateDiagonalTailChunk000Sub001Block169Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15257
    = surrogateDiagTailX0RatChunk000Sub001Block169Part019

theorem surrogateDiagonalTailChunk000Sub001Block169Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part019] using hcert

def TailChunk000Sub001Block169Part020SupportExplicit : Finset ℕ :=
  ([15258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part020 : ℚ :=
  (505062303025 : ℚ) / 417627448704943392

def SurrogateDiagonalTailChunk000Sub001Block169Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15258
    = surrogateDiagTailX0RatChunk000Sub001Block169Part020

theorem surrogateDiagonalTailChunk000Sub001Block169Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part020] using hcert

def TailChunk000Sub001Block169Part021SupportExplicit : Finset ℕ :=
  ([15259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part021 : ℚ :=
  (3638079390625 : ℚ) / 33881085012958995762

def SurrogateDiagonalTailChunk000Sub001Block169Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15259
    = surrogateDiagTailX0RatChunk000Sub001Block169Part021

theorem surrogateDiagonalTailChunk000Sub001Block169Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part021] using hcert

def TailChunk000Sub001Block169Part022SupportExplicit : Finset ℕ :=
  ([15261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part022 : ℚ :=
  (6467473491325 : ℚ) / 26770240010239206528

def SurrogateDiagonalTailChunk000Sub001Block169Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15261
    = surrogateDiagTailX0RatChunk000Sub001Block169Part022

theorem surrogateDiagonalTailChunk000Sub001Block169Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part022] using hcert

def TailChunk000Sub001Block169Part023SupportExplicit : Finset ℕ :=
  ([15262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part023 : ℚ :=
  (204161907625 : ℚ) / 382139846210544768

def SurrogateDiagonalTailChunk000Sub001Block169Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15262
    = surrogateDiagTailX0RatChunk000Sub001Block169Part023

theorem surrogateDiagonalTailChunk000Sub001Block169Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part023] using hcert

def TailChunk000Sub001Block169Part024SupportExplicit : Finset ℕ :=
  ([15263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block169Part024 : ℚ :=
  (3639987015625 : ℚ) / 33916627716448669842

def SurrogateDiagonalTailChunk000Sub001Block169Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 15263
    = surrogateDiagTailX0RatChunk000Sub001Block169Part024

theorem surrogateDiagonalTailChunk000Sub001Block169Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block169Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block169Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block169Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block169Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block169Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block169Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block169HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block169Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block169Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block169Part000
    + surrogateDiagTailX0RatChunk000Sub001Block169Part001
    + surrogateDiagTailX0RatChunk000Sub001Block169Part002
    + surrogateDiagTailX0RatChunk000Sub001Block169Part003
    + surrogateDiagTailX0RatChunk000Sub001Block169Part004
    + surrogateDiagTailX0RatChunk000Sub001Block169Part005
    + surrogateDiagTailX0RatChunk000Sub001Block169Part006
    + surrogateDiagTailX0RatChunk000Sub001Block169Part007
    + surrogateDiagTailX0RatChunk000Sub001Block169Part008
    + surrogateDiagTailX0RatChunk000Sub001Block169Part009

def surrogateDiagonalTailChunk000Sub001Block169MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block169Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block169Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block169Part010
    + surrogateDiagTailX0RatChunk000Sub001Block169Part011
    + surrogateDiagTailX0RatChunk000Sub001Block169Part012
    + surrogateDiagTailX0RatChunk000Sub001Block169Part013
    + surrogateDiagTailX0RatChunk000Sub001Block169Part014
    + surrogateDiagTailX0RatChunk000Sub001Block169Part015
    + surrogateDiagTailX0RatChunk000Sub001Block169Part016
    + surrogateDiagTailX0RatChunk000Sub001Block169Part017
    + surrogateDiagTailX0RatChunk000Sub001Block169Part018
    + surrogateDiagTailX0RatChunk000Sub001Block169Part019

def surrogateDiagonalTailChunk000Sub001Block169TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block169Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block169Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block169Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block169Part020
    + surrogateDiagTailX0RatChunk000Sub001Block169Part021
    + surrogateDiagTailX0RatChunk000Sub001Block169Part022
    + surrogateDiagTailX0RatChunk000Sub001Block169Part023
    + surrogateDiagTailX0RatChunk000Sub001Block169Part024

def surrogateDiagonalTailChunk000Sub001Block169Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block169HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block169MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block169TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block169 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block169Part000
    + surrogateDiagTailX0RatChunk000Sub001Block169Part001
    + surrogateDiagTailX0RatChunk000Sub001Block169Part002
    + surrogateDiagTailX0RatChunk000Sub001Block169Part003
    + surrogateDiagTailX0RatChunk000Sub001Block169Part004
    + surrogateDiagTailX0RatChunk000Sub001Block169Part005
    + surrogateDiagTailX0RatChunk000Sub001Block169Part006
    + surrogateDiagTailX0RatChunk000Sub001Block169Part007
    + surrogateDiagTailX0RatChunk000Sub001Block169Part008
    + surrogateDiagTailX0RatChunk000Sub001Block169Part009
    + surrogateDiagTailX0RatChunk000Sub001Block169Part010
    + surrogateDiagTailX0RatChunk000Sub001Block169Part011
    + surrogateDiagTailX0RatChunk000Sub001Block169Part012
    + surrogateDiagTailX0RatChunk000Sub001Block169Part013
    + surrogateDiagTailX0RatChunk000Sub001Block169Part014
    + surrogateDiagTailX0RatChunk000Sub001Block169Part015
    + surrogateDiagTailX0RatChunk000Sub001Block169Part016
    + surrogateDiagTailX0RatChunk000Sub001Block169Part017
    + surrogateDiagTailX0RatChunk000Sub001Block169Part018
    + surrogateDiagTailX0RatChunk000Sub001Block169Part019
    + surrogateDiagTailX0RatChunk000Sub001Block169Part020
    + surrogateDiagTailX0RatChunk000Sub001Block169Part021
    + surrogateDiagTailX0RatChunk000Sub001Block169Part022
    + surrogateDiagTailX0RatChunk000Sub001Block169Part023
    + surrogateDiagTailX0RatChunk000Sub001Block169Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block169_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block169Head + surrogateDiagTailX0RatChunk000Sub001Block169Mid + surrogateDiagTailX0RatChunk000Sub001Block169Tail =
      surrogateDiagTailX0RatChunk000Sub001Block169 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block169Head surrogateDiagTailX0RatChunk000Sub001Block169Mid surrogateDiagTailX0RatChunk000Sub001Block169Tail surrogateDiagTailX0RatChunk000Sub001Block169
  ring

def SurrogateDiagonalTailChunk000Sub001Block169HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block169HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block169Head

def SurrogateDiagonalTailChunk000Sub001Block169MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block169MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block169Mid

def SurrogateDiagonalTailChunk000Sub001Block169TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block169TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block169Tail

theorem surrogateDiagonalTailChunk000Sub001Block169_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block169HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block169MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block169TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block169Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block169 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block169HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block169MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block169TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block169Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block169_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
