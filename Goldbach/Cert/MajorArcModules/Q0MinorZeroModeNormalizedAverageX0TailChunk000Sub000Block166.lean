import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [166,167). -/

/-- Block 166 covers tail-support indices [4150,4175) and q from 6878 to 6918. -/

def TailChunk000Sub000Block166Part000SupportExplicit : Finset ℕ :=
  ([6878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part000 : ℚ :=
  (28659408187 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk000Sub000Block166Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6878
    = surrogateDiagTailX0RatChunk000Sub000Block166Part000

theorem surrogateDiagonalTailChunk000Sub000Block166Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part000] using hcert

def TailChunk000Sub000Block166Part001SupportExplicit : Finset ℕ :=
  ([6879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part001 : ℚ :=
  (821266271675 : ℚ) / 552046040204534784

def SurrogateDiagonalTailChunk000Sub000Block166Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6879
    = surrogateDiagTailX0RatChunk000Sub000Block166Part001

theorem surrogateDiagonalTailChunk000Sub000Block166Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part001] using hcert

def TailChunk000Sub000Block166Part002SupportExplicit : Finset ℕ :=
  ([6881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part002 : ℚ :=
  (2413116011875 : ℚ) / 3013545906065720448

def SurrogateDiagonalTailChunk000Sub000Block166Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6881
    = surrogateDiagTailX0RatChunk000Sub000Block166Part002

theorem surrogateDiagonalTailChunk000Sub000Block166Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part002] using hcert

def TailChunk000Sub000Block166Part003SupportExplicit : Finset ℕ :=
  ([6882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part003 : ℚ :=
  (1383969529 : ℚ) / 120956538470400

def SurrogateDiagonalTailChunk000Sub000Block166Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6882
    = surrogateDiagTailX0RatChunk000Sub000Block166Part003

theorem surrogateDiagonalTailChunk000Sub000Block166Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part003] using hcert

def TailChunk000Sub000Block166Part004SupportExplicit : Finset ℕ :=
  ([6883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part004 : ℚ :=
  (740245140625 : ℚ) / 1402250297094232722

def SurrogateDiagonalTailChunk000Sub000Block166Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6883
    = surrogateDiagTailX0RatChunk000Sub000Block166Part004

theorem surrogateDiagonalTailChunk000Sub000Block166Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part004] using hcert

def TailChunk000Sub000Block166Part005SupportExplicit : Finset ℕ :=
  ([6886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part005 : ℚ :=
  (1874374591 : ℚ) / 631849967124480

def SurrogateDiagonalTailChunk000Sub000Block166Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6886
    = surrogateDiagTailX0RatChunk000Sub000Block166Part005

theorem surrogateDiagonalTailChunk000Sub000Block166Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part005] using hcert

def TailChunk000Sub000Block166Part006SupportExplicit : Finset ℕ :=
  ([6887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part006 : ℚ :=
  (1436871497 : ℚ) / 2549611183472640

def SurrogateDiagonalTailChunk000Sub000Block166Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6887
    = surrogateDiagTailX0RatChunk000Sub000Block166Part006

theorem surrogateDiagonalTailChunk000Sub000Block166Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part006] using hcert

def TailChunk000Sub000Block166Part007SupportExplicit : Finset ℕ :=
  ([6890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part007 : ℚ :=
  (203595638075 : ℚ) / 32350718316773376

def SurrogateDiagonalTailChunk000Sub000Block166Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6890
    = surrogateDiagTailX0RatChunk000Sub000Block166Part007

theorem surrogateDiagonalTailChunk000Sub000Block166Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part007] using hcert

def TailChunk000Sub000Block166Part008SupportExplicit : Finset ℕ :=
  ([6891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part008 : ℚ :=
  (824134230425 : ℚ) / 555909864770125824

def SurrogateDiagonalTailChunk000Sub000Block166Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6891
    = surrogateDiagTailX0RatChunk000Sub000Block166Part008

theorem surrogateDiagonalTailChunk000Sub000Block166Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part008] using hcert

def TailChunk000Sub000Block166Part009SupportExplicit : Finset ℕ :=
  ([6893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part009 : ℚ :=
  (115038398281 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub000Block166Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6893
    = surrogateDiagTailX0RatChunk000Sub000Block166Part009

theorem surrogateDiagonalTailChunk000Sub000Block166Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part009] using hcert

def TailChunk000Sub000Block166Part010SupportExplicit : Finset ℕ :=
  ([6895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part010 : ℚ :=
  (922283713625 : ℚ) / 612161645151780864

def SurrogateDiagonalTailChunk000Sub000Block166Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6895
    = surrogateDiagTailX0RatChunk000Sub000Block166Part010

theorem surrogateDiagonalTailChunk000Sub000Block166Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part010] using hcert

def TailChunk000Sub000Block166Part011SupportExplicit : Finset ℕ :=
  ([6898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part011 : ℚ :=
  (1486652734975 : ℚ) / 353423877640439808

def SurrogateDiagonalTailChunk000Sub000Block166Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6898
    = surrogateDiagTailX0RatChunk000Sub000Block166Part011

theorem surrogateDiagonalTailChunk000Sub000Block166Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part011] using hcert

def TailChunk000Sub000Block166Part012SupportExplicit : Finset ℕ :=
  ([6899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part012 : ℚ :=
  (743690640625 : ℚ) / 1415336242158312402

def SurrogateDiagonalTailChunk000Sub000Block166Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6899
    = surrogateDiagTailX0RatChunk000Sub000Block166Part012

theorem surrogateDiagonalTailChunk000Sub000Block166Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part012] using hcert

def TailChunk000Sub000Block166Part013SupportExplicit : Finset ℕ :=
  ([6901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part013 : ℚ :=
  (2884032181825 : ℚ) / 5135743061701135488

def SurrogateDiagonalTailChunk000Sub000Block166Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6901
    = surrogateDiagTailX0RatChunk000Sub000Block166Part013

theorem surrogateDiagonalTailChunk000Sub000Block166Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part013] using hcert

def TailChunk000Sub000Block166Part014SupportExplicit : Finset ℕ :=
  ([6902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part014 : ℚ :=
  (119777684975 : ℚ) / 14504454732644352

def SurrogateDiagonalTailChunk000Sub000Block166Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6902
    = surrogateDiagTailX0RatChunk000Sub000Block166Part014

theorem surrogateDiagonalTailChunk000Sub000Block166Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part014] using hcert

def TailChunk000Sub000Block166Part015SupportExplicit : Finset ℕ :=
  ([6905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part015 : ℚ :=
  (85761341317 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk000Sub000Block166Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6905
    = surrogateDiagTailX0RatChunk000Sub000Block166Part015

theorem surrogateDiagonalTailChunk000Sub000Block166Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part015] using hcert

def TailChunk000Sub000Block166Part016SupportExplicit : Finset ℕ :=
  ([6906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part016 : ℚ :=
  (16545723947 : ℚ) / 1399484841000000

def SurrogateDiagonalTailChunk000Sub000Block166Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6906
    = surrogateDiagTailX0RatChunk000Sub000Block166Part016

theorem surrogateDiagonalTailChunk000Sub000Block166Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part016] using hcert

def TailChunk000Sub000Block166Part017SupportExplicit : Finset ℕ :=
  ([6907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part017 : ℚ :=
  (745416390625 : ℚ) / 1421913454402525362

def SurrogateDiagonalTailChunk000Sub000Block166Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6907
    = surrogateDiagTailX0RatChunk000Sub000Block166Part017

theorem surrogateDiagonalTailChunk000Sub000Block166Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part017] using hcert

def TailChunk000Sub000Block166Part018SupportExplicit : Finset ℕ :=
  ([6910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part018 : ℚ :=
  (44095874959 : ℚ) / 5803943532595200

def SurrogateDiagonalTailChunk000Sub000Block166Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6910
    = surrogateDiagTailX0RatChunk000Sub000Block166Part018

theorem surrogateDiagonalTailChunk000Sub000Block166Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part018] using hcert

def TailChunk000Sub000Block166Part019SupportExplicit : Finset ℕ :=
  ([6911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part019 : ℚ :=
  (1194048025 : ℚ) / 2280337029820722

def SurrogateDiagonalTailChunk000Sub000Block166Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6911
    = surrogateDiagTailX0RatChunk000Sub000Block166Part019

theorem surrogateDiagonalTailChunk000Sub000Block166Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part019] using hcert

def TailChunk000Sub000Block166Part020SupportExplicit : Finset ℕ :=
  ([6913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part020 : ℚ :=
  (113869193047 : ℚ) / 196781273521027200

def SurrogateDiagonalTailChunk000Sub000Block166Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6913
    = surrogateDiagTailX0RatChunk000Sub000Block166Part020

theorem surrogateDiagonalTailChunk000Sub000Block166Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part020] using hcert

def TailChunk000Sub000Block166Part021SupportExplicit : Finset ℕ :=
  ([6914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part021 : ℚ :=
  (1493557353775 : ℚ) / 356715346733826048

def SurrogateDiagonalTailChunk000Sub000Block166Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6914
    = surrogateDiagTailX0RatChunk000Sub000Block166Part021

theorem surrogateDiagonalTailChunk000Sub000Block166Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part021] using hcert

def TailChunk000Sub000Block166Part022SupportExplicit : Finset ℕ :=
  ([6915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part022 : ℚ :=
  (3743037259 : ℚ) / 1146457981747200

def SurrogateDiagonalTailChunk000Sub000Block166Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6915
    = surrogateDiagTailX0RatChunk000Sub000Block166Part022

theorem surrogateDiagonalTailChunk000Sub000Block166Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part022] using hcert

def TailChunk000Sub000Block166Part023SupportExplicit : Finset ℕ :=
  ([6917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part023 : ℚ :=
  (747576390625 : ℚ) / 1430167175036719392

def SurrogateDiagonalTailChunk000Sub000Block166Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6917
    = surrogateDiagTailX0RatChunk000Sub000Block166Part023

theorem surrogateDiagonalTailChunk000Sub000Block166Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part023] using hcert

def TailChunk000Sub000Block166Part024SupportExplicit : Finset ℕ :=
  ([6918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block166Part024 : ℚ :=
  (581332316425 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk000Sub000Block166Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6918
    = surrogateDiagTailX0RatChunk000Sub000Block166Part024

theorem surrogateDiagonalTailChunk000Sub000Block166Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block166Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block166Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block166Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block166Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block166Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block166Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block166HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block166Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block166Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block166Part000
    + surrogateDiagTailX0RatChunk000Sub000Block166Part001
    + surrogateDiagTailX0RatChunk000Sub000Block166Part002
    + surrogateDiagTailX0RatChunk000Sub000Block166Part003
    + surrogateDiagTailX0RatChunk000Sub000Block166Part004
    + surrogateDiagTailX0RatChunk000Sub000Block166Part005
    + surrogateDiagTailX0RatChunk000Sub000Block166Part006
    + surrogateDiagTailX0RatChunk000Sub000Block166Part007
    + surrogateDiagTailX0RatChunk000Sub000Block166Part008
    + surrogateDiagTailX0RatChunk000Sub000Block166Part009

def surrogateDiagonalTailChunk000Sub000Block166MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block166Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block166Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block166Part010
    + surrogateDiagTailX0RatChunk000Sub000Block166Part011
    + surrogateDiagTailX0RatChunk000Sub000Block166Part012
    + surrogateDiagTailX0RatChunk000Sub000Block166Part013
    + surrogateDiagTailX0RatChunk000Sub000Block166Part014
    + surrogateDiagTailX0RatChunk000Sub000Block166Part015
    + surrogateDiagTailX0RatChunk000Sub000Block166Part016
    + surrogateDiagTailX0RatChunk000Sub000Block166Part017
    + surrogateDiagTailX0RatChunk000Sub000Block166Part018
    + surrogateDiagTailX0RatChunk000Sub000Block166Part019

def surrogateDiagonalTailChunk000Sub000Block166TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block166Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block166Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block166Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block166Part020
    + surrogateDiagTailX0RatChunk000Sub000Block166Part021
    + surrogateDiagTailX0RatChunk000Sub000Block166Part022
    + surrogateDiagTailX0RatChunk000Sub000Block166Part023
    + surrogateDiagTailX0RatChunk000Sub000Block166Part024

def surrogateDiagonalTailChunk000Sub000Block166Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block166HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block166MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block166TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block166 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block166Part000
    + surrogateDiagTailX0RatChunk000Sub000Block166Part001
    + surrogateDiagTailX0RatChunk000Sub000Block166Part002
    + surrogateDiagTailX0RatChunk000Sub000Block166Part003
    + surrogateDiagTailX0RatChunk000Sub000Block166Part004
    + surrogateDiagTailX0RatChunk000Sub000Block166Part005
    + surrogateDiagTailX0RatChunk000Sub000Block166Part006
    + surrogateDiagTailX0RatChunk000Sub000Block166Part007
    + surrogateDiagTailX0RatChunk000Sub000Block166Part008
    + surrogateDiagTailX0RatChunk000Sub000Block166Part009
    + surrogateDiagTailX0RatChunk000Sub000Block166Part010
    + surrogateDiagTailX0RatChunk000Sub000Block166Part011
    + surrogateDiagTailX0RatChunk000Sub000Block166Part012
    + surrogateDiagTailX0RatChunk000Sub000Block166Part013
    + surrogateDiagTailX0RatChunk000Sub000Block166Part014
    + surrogateDiagTailX0RatChunk000Sub000Block166Part015
    + surrogateDiagTailX0RatChunk000Sub000Block166Part016
    + surrogateDiagTailX0RatChunk000Sub000Block166Part017
    + surrogateDiagTailX0RatChunk000Sub000Block166Part018
    + surrogateDiagTailX0RatChunk000Sub000Block166Part019
    + surrogateDiagTailX0RatChunk000Sub000Block166Part020
    + surrogateDiagTailX0RatChunk000Sub000Block166Part021
    + surrogateDiagTailX0RatChunk000Sub000Block166Part022
    + surrogateDiagTailX0RatChunk000Sub000Block166Part023
    + surrogateDiagTailX0RatChunk000Sub000Block166Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block166_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block166Head + surrogateDiagTailX0RatChunk000Sub000Block166Mid + surrogateDiagTailX0RatChunk000Sub000Block166Tail =
      surrogateDiagTailX0RatChunk000Sub000Block166 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block166Head surrogateDiagTailX0RatChunk000Sub000Block166Mid surrogateDiagTailX0RatChunk000Sub000Block166Tail surrogateDiagTailX0RatChunk000Sub000Block166
  ring

def SurrogateDiagonalTailChunk000Sub000Block166HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block166HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block166Head

def SurrogateDiagonalTailChunk000Sub000Block166MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block166MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block166Mid

def SurrogateDiagonalTailChunk000Sub000Block166TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block166TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block166Tail

theorem surrogateDiagonalTailChunk000Sub000Block166_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block166HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block166MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block166TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block166Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block166 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block166HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block166MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block166TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block166Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block166_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
