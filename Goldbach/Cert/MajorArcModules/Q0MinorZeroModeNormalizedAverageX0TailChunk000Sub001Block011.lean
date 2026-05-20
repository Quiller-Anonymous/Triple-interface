import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [11,12). -/

/-- Block 011 covers tail-support indices [5275,5300) and q from 8723 to 8762. -/

def TailChunk000Sub001Block011Part000SupportExplicit : Finset ℕ :=
  ([8723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part000 : ℚ :=
  (5395916527 : ℚ) / 89597435904000000

def SurrogateDiagonalTailChunk000Sub001Block011Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8723
    = surrogateDiagTailX0RatChunk000Sub001Block011Part000

theorem surrogateDiagonalTailChunk000Sub001Block011Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part000] using hcert

def TailChunk000Sub001Block011Part001SupportExplicit : Finset ℕ :=
  ([8726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part001 : ℚ :=
  (297433890625 : ℚ) / 226313005661632242

def SurrogateDiagonalTailChunk000Sub001Block011Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8726
    = surrogateDiagTailX0RatChunk000Sub001Block011Part001

theorem surrogateDiagonalTailChunk000Sub001Block011Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part001] using hcert

def TailChunk000Sub001Block011Part002SupportExplicit : Finset ℕ :=
  ([8727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part002 : ℚ :=
  (528735711275 : ℚ) / 1430521714799453184

def SurrogateDiagonalTailChunk000Sub001Block011Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8727
    = surrogateDiagTailX0RatChunk000Sub001Block011Part002

theorem surrogateDiagonalTailChunk000Sub001Block011Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part002] using hcert

def TailChunk000Sub001Block011Part003SupportExplicit : Finset ℕ :=
  ([8729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part003 : ℚ :=
  (470926150675 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk000Sub001Block011Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8729
    = surrogateDiagTailX0RatChunk000Sub001Block011Part003

theorem surrogateDiagonalTailChunk000Sub001Block011Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part003] using hcert

def TailChunk000Sub001Block011Part004SupportExplicit : Finset ℕ :=
  ([8731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8731
    = surrogateDiagTailX0RatChunk000Sub001Block011Part004

theorem surrogateDiagonalTailChunk000Sub001Block011Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part004] using hcert

def TailChunk000Sub001Block011Part005SupportExplicit : Finset ℕ :=
  ([8733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part005 : ℚ :=
  (41854611181 : ℚ) / 98364628992000000

def SurrogateDiagonalTailChunk000Sub001Block011Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8733
    = surrogateDiagTailX0RatChunk000Sub001Block011Part005

theorem surrogateDiagonalTailChunk000Sub001Block011Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part005] using hcert

def TailChunk000Sub001Block011Part006SupportExplicit : Finset ℕ :=
  ([8734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part006 : ℚ :=
  (14680601087 : ℚ) / 8198725369190400

def SurrogateDiagonalTailChunk000Sub001Block011Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8734
    = surrogateDiagTailX0RatChunk000Sub001Block011Part006

theorem surrogateDiagonalTailChunk000Sub001Block011Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part006] using hcert

def TailChunk000Sub001Block011Part007SupportExplicit : Finset ℕ :=
  ([8735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part007 : ℚ :=
  (143154564175 : ℚ) / 1487249358754632192

def SurrogateDiagonalTailChunk000Sub001Block011Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8735
    = surrogateDiagTailX0RatChunk000Sub001Block011Part007

theorem surrogateDiagonalTailChunk000Sub001Block011Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part007] using hcert

def TailChunk000Sub001Block011Part008SupportExplicit : Finset ℕ :=
  ([8737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8737
    = surrogateDiagTailX0RatChunk000Sub001Block011Part008

theorem surrogateDiagonalTailChunk000Sub001Block011Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part008] using hcert

def TailChunk000Sub001Block011Part009SupportExplicit : Finset ℕ :=
  ([8738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part009 : ℚ :=
  (281876813875 : ℚ) / 175957044816248832

def SurrogateDiagonalTailChunk000Sub001Block011Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8738
    = surrogateDiagTailX0RatChunk000Sub001Block011Part009

theorem surrogateDiagonalTailChunk000Sub001Block011Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part009] using hcert

def TailChunk000Sub001Block011Part010SupportExplicit : Finset ℕ :=
  ([8741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8741
    = surrogateDiagTailX0RatChunk000Sub001Block011Part010

theorem surrogateDiagonalTailChunk000Sub001Block011Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part010] using hcert

def TailChunk000Sub001Block011Part011SupportExplicit : Finset ℕ :=
  ([8742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part011 : ℚ :=
  (30393462349 : ℚ) / 5803943532595200

def SurrogateDiagonalTailChunk000Sub001Block011Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8742
    = surrogateDiagTailX0RatChunk000Sub001Block011Part011

theorem surrogateDiagonalTailChunk000Sub001Block011Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part011] using hcert

def TailChunk000Sub001Block011Part012SupportExplicit : Finset ℕ :=
  ([8743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part012 : ℚ :=
  (391016811925 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk000Sub001Block011Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8743
    = surrogateDiagTailX0RatChunk000Sub001Block011Part012

theorem surrogateDiagonalTailChunk000Sub001Block011Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part012] using hcert

def TailChunk000Sub001Block011Part013SupportExplicit : Finset ℕ :=
  ([8745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part013 : ℚ :=
  (9610603963 : ℚ) / 7488592202956800

def SurrogateDiagonalTailChunk000Sub001Block011Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8745
    = surrogateDiagTailX0RatChunk000Sub001Block011Part013

theorem surrogateDiagonalTailChunk000Sub001Block011Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part013] using hcert

def TailChunk000Sub001Block011Part014SupportExplicit : Finset ℕ :=
  ([8746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part014 : ℚ :=
  (298798890625 : ℚ) / 228395467271622432

def SurrogateDiagonalTailChunk000Sub001Block011Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8746
    = surrogateDiagTailX0RatChunk000Sub001Block011Part014

theorem surrogateDiagonalTailChunk000Sub001Block011Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part014] using hcert

def TailChunk000Sub001Block011Part015SupportExplicit : Finset ℕ :=
  ([8747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8747
    = surrogateDiagTailX0RatChunk000Sub001Block011Part015

theorem surrogateDiagonalTailChunk000Sub001Block011Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part015] using hcert

def TailChunk000Sub001Block011Part016SupportExplicit : Finset ℕ :=
  ([8749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part016 : ℚ :=
  (397965325 : ℚ) / 18357200521003008

def SurrogateDiagonalTailChunk000Sub001Block011Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8749
    = surrogateDiagTailX0RatChunk000Sub001Block011Part016

theorem surrogateDiagonalTailChunk000Sub001Block011Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part016] using hcert

def TailChunk000Sub001Block011Part017SupportExplicit : Finset ℕ :=
  ([8751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part017 : ℚ :=
  (531647128475 : ℚ) / 1446328434628076544

def SurrogateDiagonalTailChunk000Sub001Block011Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8751
    = surrogateDiagTailX0RatChunk000Sub001Block011Part017

theorem surrogateDiagonalTailChunk000Sub001Block011Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part017] using hcert

def TailChunk000Sub001Block011Part018SupportExplicit : Finset ℕ :=
  ([8753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8753
    = surrogateDiagTailX0RatChunk000Sub001Block011Part018

theorem surrogateDiagonalTailChunk000Sub001Block011Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part018] using hcert

def TailChunk000Sub001Block011Part019SupportExplicit : Finset ℕ :=
  ([8754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part019 : ℚ :=
  (930805958275 : ℚ) / 180791054328509568

def SurrogateDiagonalTailChunk000Sub001Block011Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8754
    = surrogateDiagTailX0RatChunk000Sub001Block011Part019

theorem surrogateDiagonalTailChunk000Sub001Block011Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part019] using hcert

def TailChunk000Sub001Block011Part020SupportExplicit : Finset ℕ :=
  ([8755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part020 : ℚ :=
  (23923215725 : ℚ) / 168183612900900864

def SurrogateDiagonalTailChunk000Sub001Block011Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8755
    = surrogateDiagTailX0RatChunk000Sub001Block011Part020

theorem surrogateDiagonalTailChunk000Sub001Block011Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part020] using hcert

def TailChunk000Sub001Block011Part021SupportExplicit : Finset ℕ :=
  ([8758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part021 : ℚ :=
  (73422583 : ℚ) / 49401878400000

def SurrogateDiagonalTailChunk000Sub001Block011Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8758
    = surrogateDiagTailX0RatChunk000Sub001Block011Part021

theorem surrogateDiagonalTailChunk000Sub001Block011Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part021] using hcert

def TailChunk000Sub001Block011Part022SupportExplicit : Finset ℕ :=
  ([8759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part022 : ℚ :=
  (80429587 : ℚ) / 6268259015202816

def SurrogateDiagonalTailChunk000Sub001Block011Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8759
    = surrogateDiagTailX0RatChunk000Sub001Block011Part022

theorem surrogateDiagonalTailChunk000Sub001Block011Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part022] using hcert

def TailChunk000Sub001Block011Part023SupportExplicit : Finset ℕ :=
  ([8761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block011Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8761
    = surrogateDiagTailX0RatChunk000Sub001Block011Part023

theorem surrogateDiagonalTailChunk000Sub001Block011Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part023] using hcert

def TailChunk000Sub001Block011Part024SupportExplicit : Finset ℕ :=
  ([8762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block011Part024 : ℚ :=
  (124312177475 : ℚ) / 73428802084012032

def SurrogateDiagonalTailChunk000Sub001Block011Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8762
    = surrogateDiagTailX0RatChunk000Sub001Block011Part024

theorem surrogateDiagonalTailChunk000Sub001Block011Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block011Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block011Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block011Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block011Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block011Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block011HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block011Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block011Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block011Part000
    + surrogateDiagTailX0RatChunk000Sub001Block011Part001
    + surrogateDiagTailX0RatChunk000Sub001Block011Part002
    + surrogateDiagTailX0RatChunk000Sub001Block011Part003
    + surrogateDiagTailX0RatChunk000Sub001Block011Part004
    + surrogateDiagTailX0RatChunk000Sub001Block011Part005
    + surrogateDiagTailX0RatChunk000Sub001Block011Part006
    + surrogateDiagTailX0RatChunk000Sub001Block011Part007
    + surrogateDiagTailX0RatChunk000Sub001Block011Part008
    + surrogateDiagTailX0RatChunk000Sub001Block011Part009

def surrogateDiagonalTailChunk000Sub001Block011MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block011Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block011Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block011Part010
    + surrogateDiagTailX0RatChunk000Sub001Block011Part011
    + surrogateDiagTailX0RatChunk000Sub001Block011Part012
    + surrogateDiagTailX0RatChunk000Sub001Block011Part013
    + surrogateDiagTailX0RatChunk000Sub001Block011Part014
    + surrogateDiagTailX0RatChunk000Sub001Block011Part015
    + surrogateDiagTailX0RatChunk000Sub001Block011Part016
    + surrogateDiagTailX0RatChunk000Sub001Block011Part017
    + surrogateDiagTailX0RatChunk000Sub001Block011Part018
    + surrogateDiagTailX0RatChunk000Sub001Block011Part019

def surrogateDiagonalTailChunk000Sub001Block011TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block011Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block011Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block011Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block011Part020
    + surrogateDiagTailX0RatChunk000Sub001Block011Part021
    + surrogateDiagTailX0RatChunk000Sub001Block011Part022
    + surrogateDiagTailX0RatChunk000Sub001Block011Part023
    + surrogateDiagTailX0RatChunk000Sub001Block011Part024

def surrogateDiagonalTailChunk000Sub001Block011Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block011HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block011MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block011TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block011 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block011Part000
    + surrogateDiagTailX0RatChunk000Sub001Block011Part001
    + surrogateDiagTailX0RatChunk000Sub001Block011Part002
    + surrogateDiagTailX0RatChunk000Sub001Block011Part003
    + surrogateDiagTailX0RatChunk000Sub001Block011Part004
    + surrogateDiagTailX0RatChunk000Sub001Block011Part005
    + surrogateDiagTailX0RatChunk000Sub001Block011Part006
    + surrogateDiagTailX0RatChunk000Sub001Block011Part007
    + surrogateDiagTailX0RatChunk000Sub001Block011Part008
    + surrogateDiagTailX0RatChunk000Sub001Block011Part009
    + surrogateDiagTailX0RatChunk000Sub001Block011Part010
    + surrogateDiagTailX0RatChunk000Sub001Block011Part011
    + surrogateDiagTailX0RatChunk000Sub001Block011Part012
    + surrogateDiagTailX0RatChunk000Sub001Block011Part013
    + surrogateDiagTailX0RatChunk000Sub001Block011Part014
    + surrogateDiagTailX0RatChunk000Sub001Block011Part015
    + surrogateDiagTailX0RatChunk000Sub001Block011Part016
    + surrogateDiagTailX0RatChunk000Sub001Block011Part017
    + surrogateDiagTailX0RatChunk000Sub001Block011Part018
    + surrogateDiagTailX0RatChunk000Sub001Block011Part019
    + surrogateDiagTailX0RatChunk000Sub001Block011Part020
    + surrogateDiagTailX0RatChunk000Sub001Block011Part021
    + surrogateDiagTailX0RatChunk000Sub001Block011Part022
    + surrogateDiagTailX0RatChunk000Sub001Block011Part023
    + surrogateDiagTailX0RatChunk000Sub001Block011Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block011_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block011Head + surrogateDiagTailX0RatChunk000Sub001Block011Mid + surrogateDiagTailX0RatChunk000Sub001Block011Tail =
      surrogateDiagTailX0RatChunk000Sub001Block011 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block011Head surrogateDiagTailX0RatChunk000Sub001Block011Mid surrogateDiagTailX0RatChunk000Sub001Block011Tail surrogateDiagTailX0RatChunk000Sub001Block011
  ring

def SurrogateDiagonalTailChunk000Sub001Block011HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block011HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block011Head

def SurrogateDiagonalTailChunk000Sub001Block011MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block011MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block011Mid

def SurrogateDiagonalTailChunk000Sub001Block011TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block011TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block011Tail

theorem surrogateDiagonalTailChunk000Sub001Block011_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block011HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block011MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block011TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block011Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block011 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block011HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block011MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block011TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block011Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block011_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
