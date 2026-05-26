import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [140,150). -/

/-- Block 140 covers tail-support indices [13500,13525) and q from 22259 to 22297. -/

def TailChunk001Sub000Block140Part000SupportExplicit : Finset ℕ :=
  ([22259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block140Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22259
    = surrogateDiagTailX0RatChunk001Sub000Block140Part000

theorem surrogateDiagonalTailChunk001Sub000Block140Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part000] using hcert

def TailChunk001Sub000Block140Part001SupportExplicit : Finset ℕ :=
  ([22261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part001 : ℚ :=
  (13616954875 : ℚ) / 82951681693653663744

def SurrogateDiagonalTailChunk001Sub000Block140Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22261
    = surrogateDiagTailX0RatChunk001Sub000Block140Part001

theorem surrogateDiagonalTailChunk001Sub000Block140Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part001] using hcert

def TailChunk001Sub000Block140Part002SupportExplicit : Finset ℕ :=
  ([22262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part002 : ℚ :=
  (3097479025 : ℚ) / 15348555450880722

def SurrogateDiagonalTailChunk001Sub000Block140Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22262
    = surrogateDiagTailX0RatChunk001Sub000Block140Part002

theorem surrogateDiagonalTailChunk001Sub000Block140Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part002] using hcert

def TailChunk001Sub000Block140Part003SupportExplicit : Finset ℕ :=
  ([22263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part003 : ℚ :=
  (45067548617 : ℚ) / 1433558974464000000

def SurrogateDiagonalTailChunk001Sub000Block140Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22263
    = surrogateDiagTailX0RatChunk001Sub000Block140Part003

theorem surrogateDiagonalTailChunk001Sub000Block140Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part003] using hcert

def TailChunk001Sub000Block140Part004SupportExplicit : Finset ℕ :=
  ([22265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part004 : ℚ :=
  (554000993 : ℚ) / 92894621545267200

def SurrogateDiagonalTailChunk001Sub000Block140Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22265
    = surrogateDiagTailX0RatChunk001Sub000Block140Part004

theorem surrogateDiagonalTailChunk001Sub000Block140Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part004] using hcert

def TailChunk001Sub000Block140Part005SupportExplicit : Finset ℕ :=
  ([22267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part005 : ℚ :=
  (25355996353 : ℚ) / 13255628730923059200

def SurrogateDiagonalTailChunk001Sub000Block140Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22267
    = surrogateDiagTailX0RatChunk001Sub000Block140Part005

theorem surrogateDiagonalTailChunk001Sub000Block140Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part005] using hcert

def TailChunk001Sub000Block140Part006SupportExplicit : Finset ℕ :=
  ([22269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part006 : ℚ :=
  (56888251 : ℚ) / 1520368156828800

def SurrogateDiagonalTailChunk001Sub000Block140Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22269
    = surrogateDiagTailX0RatChunk001Sub000Block140Part006

theorem surrogateDiagonalTailChunk001Sub000Block140Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part006] using hcert

def TailChunk001Sub000Block140Part007SupportExplicit : Finset ℕ :=
  ([22270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part007 : ℚ :=
  (189999025831 : ℚ) / 479269900989235200

def SurrogateDiagonalTailChunk001Sub000Block140Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22270
    = surrogateDiagTailX0RatChunk001Sub000Block140Part007

theorem surrogateDiagonalTailChunk001Sub000Block140Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part007] using hcert

def TailChunk001Sub000Block140Part008SupportExplicit : Finset ℕ :=
  ([22271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block140Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22271
    = surrogateDiagTailX0RatChunk001Sub000Block140Part008

theorem surrogateDiagonalTailChunk001Sub000Block140Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part008] using hcert

def TailChunk001Sub000Block140Part009SupportExplicit : Finset ℕ :=
  ([22273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block140Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22273
    = surrogateDiagTailX0RatChunk001Sub000Block140Part009

theorem surrogateDiagonalTailChunk001Sub000Block140Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part009] using hcert

def TailChunk001Sub000Block140Part010SupportExplicit : Finset ℕ :=
  ([22274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part010 : ℚ :=
  (173878380575 : ℚ) / 529284342560891904

def SurrogateDiagonalTailChunk001Sub000Block140Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22274
    = surrogateDiagTailX0RatChunk001Sub000Block140Part010

theorem surrogateDiagonalTailChunk001Sub000Block140Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part010] using hcert

def TailChunk001Sub000Block140Part011SupportExplicit : Finset ℕ :=
  ([22277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block140Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22277
    = surrogateDiagTailX0RatChunk001Sub000Block140Part011

theorem surrogateDiagonalTailChunk001Sub000Block140Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part011] using hcert

def TailChunk001Sub000Block140Part012SupportExplicit : Finset ℕ :=
  ([22278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part012 : ℚ :=
  (4097545785625 : ℚ) / 6630657249378060288

def SurrogateDiagonalTailChunk001Sub000Block140Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22278
    = surrogateDiagTailX0RatChunk001Sub000Block140Part012

theorem surrogateDiagonalTailChunk001Sub000Block140Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part012] using hcert

def TailChunk001Sub000Block140Part013SupportExplicit : Finset ℕ :=
  ([22279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block140Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22279
    = surrogateDiagTailX0RatChunk001Sub000Block140Part013

theorem surrogateDiagonalTailChunk001Sub000Block140Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part013] using hcert

def TailChunk001Sub000Block140Part014SupportExplicit : Finset ℕ :=
  ([22281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part014 : ℚ :=
  (19816337227 : ℚ) / 2618395798700851200

def SurrogateDiagonalTailChunk001Sub000Block140Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22281
    = surrogateDiagTailX0RatChunk001Sub000Block140Part014

theorem surrogateDiagonalTailChunk001Sub000Block140Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part014] using hcert

def TailChunk001Sub000Block140Part015SupportExplicit : Finset ℕ :=
  ([22282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part015 : ℚ :=
  (6828264406825 : ℚ) / 27838568649290416128

def SurrogateDiagonalTailChunk001Sub000Block140Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22282
    = surrogateDiagTailX0RatChunk001Sub000Block140Part015

theorem surrogateDiagonalTailChunk001Sub000Block140Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part015] using hcert

def TailChunk001Sub000Block140Part016SupportExplicit : Finset ℕ :=
  ([22283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block140Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22283
    = surrogateDiagTailX0RatChunk001Sub000Block140Part016

theorem surrogateDiagonalTailChunk001Sub000Block140Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part016] using hcert

def TailChunk001Sub000Block140Part017SupportExplicit : Finset ℕ :=
  ([22285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part017 : ℚ :=
  (414082210125 : ℚ) / 84125236495996420096

def SurrogateDiagonalTailChunk001Sub000Block140Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22285
    = surrogateDiagTailX0RatChunk001Sub000Block140Part017

theorem surrogateDiagonalTailChunk001Sub000Block140Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part017] using hcert

def TailChunk001Sub000Block140Part018SupportExplicit : Finset ℕ :=
  ([22286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part018 : ℚ :=
  (266437128721 : ℚ) / 1049080706922547200

def SurrogateDiagonalTailChunk001Sub000Block140Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22286
    = surrogateDiagTailX0RatChunk001Sub000Block140Part018

theorem surrogateDiagonalTailChunk001Sub000Block140Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part018] using hcert

def TailChunk001Sub000Block140Part019SupportExplicit : Finset ℕ :=
  ([22287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part019 : ℚ :=
  (104259880475 : ℚ) / 10746233315905241088

def SurrogateDiagonalTailChunk001Sub000Block140Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22287
    = surrogateDiagTailX0RatChunk001Sub000Block140Part019

theorem surrogateDiagonalTailChunk001Sub000Block140Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part019] using hcert

def TailChunk001Sub000Block140Part020SupportExplicit : Finset ℕ :=
  ([22289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part020 : ℚ :=
  (2346316609 : ℚ) / 5382817488392032800

def SurrogateDiagonalTailChunk001Sub000Block140Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22289
    = surrogateDiagTailX0RatChunk001Sub000Block140Part020

theorem surrogateDiagonalTailChunk001Sub000Block140Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part020] using hcert

def TailChunk001Sub000Block140Part021SupportExplicit : Finset ℕ :=
  ([22290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part021 : ℚ :=
  (1257054841325 : ℚ) / 1552288472266850304

def SurrogateDiagonalTailChunk001Sub000Block140Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22290
    = surrogateDiagTailX0RatChunk001Sub000Block140Part021

theorem surrogateDiagonalTailChunk001Sub000Block140Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part021] using hcert

def TailChunk001Sub000Block140Part022SupportExplicit : Finset ℕ :=
  ([22291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block140Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22291
    = surrogateDiagTailX0RatChunk001Sub000Block140Part022

theorem surrogateDiagonalTailChunk001Sub000Block140Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part022] using hcert

def TailChunk001Sub000Block140Part023SupportExplicit : Finset ℕ :=
  ([22294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part023 : ℚ :=
  (859716503 : ℚ) / 4063585101069312

def SurrogateDiagonalTailChunk001Sub000Block140Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22294
    = surrogateDiagTailX0RatChunk001Sub000Block140Part023

theorem surrogateDiagonalTailChunk001Sub000Block140Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part023] using hcert

def TailChunk001Sub000Block140Part024SupportExplicit : Finset ℕ :=
  ([22297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block140Part024 : ℚ :=
  (30897845923 : ℚ) / 16851734737988995200

def SurrogateDiagonalTailChunk001Sub000Block140Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22297
    = surrogateDiagTailX0RatChunk001Sub000Block140Part024

theorem surrogateDiagonalTailChunk001Sub000Block140Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block140Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block140Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block140Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block140Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block140Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block140Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block140HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block140Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block140Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block140Part000
    + surrogateDiagTailX0RatChunk001Sub000Block140Part001
    + surrogateDiagTailX0RatChunk001Sub000Block140Part002
    + surrogateDiagTailX0RatChunk001Sub000Block140Part003
    + surrogateDiagTailX0RatChunk001Sub000Block140Part004
    + surrogateDiagTailX0RatChunk001Sub000Block140Part005
    + surrogateDiagTailX0RatChunk001Sub000Block140Part006
    + surrogateDiagTailX0RatChunk001Sub000Block140Part007
    + surrogateDiagTailX0RatChunk001Sub000Block140Part008
    + surrogateDiagTailX0RatChunk001Sub000Block140Part009

def surrogateDiagonalTailChunk001Sub000Block140MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block140Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block140Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block140Part010
    + surrogateDiagTailX0RatChunk001Sub000Block140Part011
    + surrogateDiagTailX0RatChunk001Sub000Block140Part012
    + surrogateDiagTailX0RatChunk001Sub000Block140Part013
    + surrogateDiagTailX0RatChunk001Sub000Block140Part014
    + surrogateDiagTailX0RatChunk001Sub000Block140Part015
    + surrogateDiagTailX0RatChunk001Sub000Block140Part016
    + surrogateDiagTailX0RatChunk001Sub000Block140Part017
    + surrogateDiagTailX0RatChunk001Sub000Block140Part018
    + surrogateDiagTailX0RatChunk001Sub000Block140Part019

def surrogateDiagonalTailChunk001Sub000Block140TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block140Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block140Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block140Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block140Part020
    + surrogateDiagTailX0RatChunk001Sub000Block140Part021
    + surrogateDiagTailX0RatChunk001Sub000Block140Part022
    + surrogateDiagTailX0RatChunk001Sub000Block140Part023
    + surrogateDiagTailX0RatChunk001Sub000Block140Part024

def surrogateDiagonalTailChunk001Sub000Block140Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block140HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block140MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block140TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block140 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block140Part000
    + surrogateDiagTailX0RatChunk001Sub000Block140Part001
    + surrogateDiagTailX0RatChunk001Sub000Block140Part002
    + surrogateDiagTailX0RatChunk001Sub000Block140Part003
    + surrogateDiagTailX0RatChunk001Sub000Block140Part004
    + surrogateDiagTailX0RatChunk001Sub000Block140Part005
    + surrogateDiagTailX0RatChunk001Sub000Block140Part006
    + surrogateDiagTailX0RatChunk001Sub000Block140Part007
    + surrogateDiagTailX0RatChunk001Sub000Block140Part008
    + surrogateDiagTailX0RatChunk001Sub000Block140Part009
    + surrogateDiagTailX0RatChunk001Sub000Block140Part010
    + surrogateDiagTailX0RatChunk001Sub000Block140Part011
    + surrogateDiagTailX0RatChunk001Sub000Block140Part012
    + surrogateDiagTailX0RatChunk001Sub000Block140Part013
    + surrogateDiagTailX0RatChunk001Sub000Block140Part014
    + surrogateDiagTailX0RatChunk001Sub000Block140Part015
    + surrogateDiagTailX0RatChunk001Sub000Block140Part016
    + surrogateDiagTailX0RatChunk001Sub000Block140Part017
    + surrogateDiagTailX0RatChunk001Sub000Block140Part018
    + surrogateDiagTailX0RatChunk001Sub000Block140Part019
    + surrogateDiagTailX0RatChunk001Sub000Block140Part020
    + surrogateDiagTailX0RatChunk001Sub000Block140Part021
    + surrogateDiagTailX0RatChunk001Sub000Block140Part022
    + surrogateDiagTailX0RatChunk001Sub000Block140Part023
    + surrogateDiagTailX0RatChunk001Sub000Block140Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block140_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block140Head + surrogateDiagTailX0RatChunk001Sub000Block140Mid + surrogateDiagTailX0RatChunk001Sub000Block140Tail =
      surrogateDiagTailX0RatChunk001Sub000Block140 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block140Head surrogateDiagTailX0RatChunk001Sub000Block140Mid surrogateDiagTailX0RatChunk001Sub000Block140Tail surrogateDiagTailX0RatChunk001Sub000Block140
  ring

def SurrogateDiagonalTailChunk001Sub000Block140HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block140HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block140Head

def SurrogateDiagonalTailChunk001Sub000Block140MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block140MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block140Mid

def SurrogateDiagonalTailChunk001Sub000Block140TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block140TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block140Tail

theorem surrogateDiagonalTailChunk001Sub000Block140_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block140HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block140MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block140TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block140Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block140 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block140HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block140MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block140TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block140Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block140_eq_head_add_mid_add_tail

/-- Block 141 covers tail-support indices [13525,13550) and q from 22298 to 22337. -/

def TailChunk001Sub000Block141Part000SupportExplicit : Finset ℕ :=
  ([22298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part000 : ℚ :=
  (1942190640625 : ℚ) / 9655054013823589152

def SurrogateDiagonalTailChunk001Sub000Block141Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22298
    = surrogateDiagTailX0RatChunk001Sub000Block141Part000

theorem surrogateDiagonalTailChunk001Sub000Block141Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part000] using hcert

def TailChunk001Sub000Block141Part001SupportExplicit : Finset ℕ :=
  ([22299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part001 : ℚ :=
  (125025 : ℚ) / 24406909507371008

def SurrogateDiagonalTailChunk001Sub000Block141Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22299
    = surrogateDiagTailX0RatChunk001Sub000Block141Part001

theorem surrogateDiagonalTailChunk001Sub000Block141Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part001] using hcert

def TailChunk001Sub000Block141Part002SupportExplicit : Finset ℕ :=
  ([22301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part002 : ℚ :=
  (229694805175 : ℚ) / 534692219264201392128

def SurrogateDiagonalTailChunk001Sub000Block141Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22301
    = surrogateDiagTailX0RatChunk001Sub000Block141Part002

theorem surrogateDiagonalTailChunk001Sub000Block141Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part002] using hcert

def TailChunk001Sub000Block141Part003SupportExplicit : Finset ℕ :=
  ([22303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block141Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22303
    = surrogateDiagTailX0RatChunk001Sub000Block141Part003

theorem surrogateDiagonalTailChunk001Sub000Block141Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part003] using hcert

def TailChunk001Sub000Block141Part004SupportExplicit : Finset ℕ :=
  ([22305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part004 : ℚ :=
  (103842420425 : ℚ) / 6242694144423530496

def SurrogateDiagonalTailChunk001Sub000Block141Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22305
    = surrogateDiagTailX0RatChunk001Sub000Block141Part004

theorem surrogateDiagonalTailChunk001Sub000Block141Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part004] using hcert

def TailChunk001Sub000Block141Part005SupportExplicit : Finset ℕ :=
  ([22306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part005 : ℚ :=
  (2377354346725 : ℚ) / 10317775847684708736

def SurrogateDiagonalTailChunk001Sub000Block141Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22306
    = surrogateDiagTailX0RatChunk001Sub000Block141Part005

theorem surrogateDiagonalTailChunk001Sub000Block141Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part005] using hcert

def TailChunk001Sub000Block141Part006SupportExplicit : Finset ℕ :=
  ([22307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block141Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22307
    = surrogateDiagTailX0RatChunk001Sub000Block141Part006

theorem surrogateDiagonalTailChunk001Sub000Block141Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part006] using hcert

def TailChunk001Sub000Block141Part007SupportExplicit : Finset ℕ :=
  ([22309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part007 : ℚ :=
  (635222790875 : ℚ) / 166949433841576209984

def SurrogateDiagonalTailChunk001Sub000Block141Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22309
    = surrogateDiagTailX0RatChunk001Sub000Block141Part007

theorem surrogateDiagonalTailChunk001Sub000Block141Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part007] using hcert

def TailChunk001Sub000Block141Part008SupportExplicit : Finset ℕ :=
  ([22310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part008 : ℚ :=
  (4882201063225 : ℚ) / 12736276522554359808

def SurrogateDiagonalTailChunk001Sub000Block141Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22310
    = surrogateDiagTailX0RatChunk001Sub000Block141Part008

theorem surrogateDiagonalTailChunk001Sub000Block141Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part008] using hcert

def TailChunk001Sub000Block141Part009SupportExplicit : Finset ℕ :=
  ([22313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part009 : ℚ :=
  (5934690589 : ℚ) / 22756076565988147200

def SurrogateDiagonalTailChunk001Sub000Block141Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22313
    = surrogateDiagTailX0RatChunk001Sub000Block141Part009

theorem surrogateDiagonalTailChunk001Sub000Block141Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part009] using hcert

def TailChunk001Sub000Block141Part010SupportExplicit : Finset ℕ :=
  ([22314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part010 : ℚ :=
  (314227784375 : ℚ) / 695011031788115328

def SurrogateDiagonalTailChunk001Sub000Block141Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22314
    = surrogateDiagTailX0RatChunk001Sub000Block141Part010

theorem surrogateDiagonalTailChunk001Sub000Block141Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part010] using hcert

def TailChunk001Sub000Block141Part011SupportExplicit : Finset ℕ :=
  ([22315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part011 : ℚ :=
  (415196959875 : ℚ) / 84579250683992283136

def SurrogateDiagonalTailChunk001Sub000Block141Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22315
    = surrogateDiagTailX0RatChunk001Sub000Block141Part011

theorem surrogateDiagonalTailChunk001Sub000Block141Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part011] using hcert

def TailChunk001Sub000Block141Part012SupportExplicit : Finset ℕ :=
  ([22317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part012 : ℚ :=
  (225121325 : ℚ) / 180992800325320704

def SurrogateDiagonalTailChunk001Sub000Block141Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22317
    = surrogateDiagTailX0RatChunk001Sub000Block141Part012

theorem surrogateDiagonalTailChunk001Sub000Block141Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part012] using hcert

def TailChunk001Sub000Block141Part013SupportExplicit : Finset ℕ :=
  ([22318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part013 : ℚ :=
  (1945676265625 : ℚ) / 9689743834335426162

def SurrogateDiagonalTailChunk001Sub000Block141Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22318
    = surrogateDiagTailX0RatChunk001Sub000Block141Part013

theorem surrogateDiagonalTailChunk001Sub000Block141Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part013] using hcert

def TailChunk001Sub000Block141Part014SupportExplicit : Finset ℕ :=
  ([22319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part014 : ℚ :=
  (1723743157 : ℚ) / 1409864602425177600

def SurrogateDiagonalTailChunk001Sub000Block141Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22319
    = surrogateDiagTailX0RatChunk001Sub000Block141Part014

theorem surrogateDiagonalTailChunk001Sub000Block141Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part014] using hcert

def TailChunk001Sub000Block141Part015SupportExplicit : Finset ℕ :=
  ([22321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part015 : ℚ :=
  (37098491989 : ℚ) / 13592262868992000000

def SurrogateDiagonalTailChunk001Sub000Block141Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22321
    = surrogateDiagTailX0RatChunk001Sub000Block141Part015

theorem surrogateDiagonalTailChunk001Sub000Block141Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part015] using hcert

def TailChunk001Sub000Block141Part016SupportExplicit : Finset ℕ :=
  ([22322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part016 : ℚ :=
  (3114198025 : ℚ) / 15514708800655872

def SurrogateDiagonalTailChunk001Sub000Block141Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22322
    = surrogateDiagTailX0RatChunk001Sub000Block141Part016

theorem surrogateDiagonalTailChunk001Sub000Block141Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part016] using hcert

def TailChunk001Sub000Block141Part017SupportExplicit : Finset ℕ :=
  ([22323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part017 : ℚ :=
  (779282641075 : ℚ) / 65955331888030107648

def SurrogateDiagonalTailChunk001Sub000Block141Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22323
    = surrogateDiagTailX0RatChunk001Sub000Block141Part017

theorem surrogateDiagonalTailChunk001Sub000Block141Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part017] using hcert

def TailChunk001Sub000Block141Part018SupportExplicit : Finset ℕ :=
  ([22327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part018 : ℚ :=
  (110511936475 : ℚ) / 583205276451293349888

def SurrogateDiagonalTailChunk001Sub000Block141Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22327
    = surrogateDiagTailX0RatChunk001Sub000Block141Part018

theorem surrogateDiagonalTailChunk001Sub000Block141Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part018] using hcert

def TailChunk001Sub000Block141Part019SupportExplicit : Finset ℕ :=
  ([22330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part019 : ℚ :=
  (1611667021 : ℚ) / 2266321051975680

def SurrogateDiagonalTailChunk001Sub000Block141Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22330
    = surrogateDiagTailX0RatChunk001Sub000Block141Part019

theorem surrogateDiagonalTailChunk001Sub000Block141Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part019] using hcert

def TailChunk001Sub000Block141Part020SupportExplicit : Finset ℕ :=
  ([22331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part020 : ℚ :=
  (7801586675 : ℚ) / 49097717700989313024

def SurrogateDiagonalTailChunk001Sub000Block141Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22331
    = surrogateDiagTailX0RatChunk001Sub000Block141Part020

theorem surrogateDiagonalTailChunk001Sub000Block141Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part020] using hcert

def TailChunk001Sub000Block141Part021SupportExplicit : Finset ℕ :=
  ([22333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part021 : ℚ :=
  (52269017 : ℚ) / 75427865283585408

def SurrogateDiagonalTailChunk001Sub000Block141Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22333
    = surrogateDiagTailX0RatChunk001Sub000Block141Part021

theorem surrogateDiagonalTailChunk001Sub000Block141Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part021] using hcert

def TailChunk001Sub000Block141Part022SupportExplicit : Finset ℕ :=
  ([22334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part022 : ℚ :=
  (3407017142225 : ℚ) / 14049827716166820864

def SurrogateDiagonalTailChunk001Sub000Block141Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22334
    = surrogateDiagTailX0RatChunk001Sub000Block141Part022

theorem surrogateDiagonalTailChunk001Sub000Block141Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part022] using hcert

def TailChunk001Sub000Block141Part023SupportExplicit : Finset ℕ :=
  ([22335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part023 : ℚ :=
  (346626663775 : ℚ) / 12552740197034360832

def SurrogateDiagonalTailChunk001Sub000Block141Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22335
    = surrogateDiagTailX0RatChunk001Sub000Block141Part023

theorem surrogateDiagonalTailChunk001Sub000Block141Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part023] using hcert

def TailChunk001Sub000Block141Part024SupportExplicit : Finset ℕ :=
  ([22337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block141Part024 : ℚ :=
  (25472658887 : ℚ) / 6711577173433281600

def SurrogateDiagonalTailChunk001Sub000Block141Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22337
    = surrogateDiagTailX0RatChunk001Sub000Block141Part024

theorem surrogateDiagonalTailChunk001Sub000Block141Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block141Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block141Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block141Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block141Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block141Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block141Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block141HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block141Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block141Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block141Part000
    + surrogateDiagTailX0RatChunk001Sub000Block141Part001
    + surrogateDiagTailX0RatChunk001Sub000Block141Part002
    + surrogateDiagTailX0RatChunk001Sub000Block141Part003
    + surrogateDiagTailX0RatChunk001Sub000Block141Part004
    + surrogateDiagTailX0RatChunk001Sub000Block141Part005
    + surrogateDiagTailX0RatChunk001Sub000Block141Part006
    + surrogateDiagTailX0RatChunk001Sub000Block141Part007
    + surrogateDiagTailX0RatChunk001Sub000Block141Part008
    + surrogateDiagTailX0RatChunk001Sub000Block141Part009

def surrogateDiagonalTailChunk001Sub000Block141MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block141Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block141Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block141Part010
    + surrogateDiagTailX0RatChunk001Sub000Block141Part011
    + surrogateDiagTailX0RatChunk001Sub000Block141Part012
    + surrogateDiagTailX0RatChunk001Sub000Block141Part013
    + surrogateDiagTailX0RatChunk001Sub000Block141Part014
    + surrogateDiagTailX0RatChunk001Sub000Block141Part015
    + surrogateDiagTailX0RatChunk001Sub000Block141Part016
    + surrogateDiagTailX0RatChunk001Sub000Block141Part017
    + surrogateDiagTailX0RatChunk001Sub000Block141Part018
    + surrogateDiagTailX0RatChunk001Sub000Block141Part019

def surrogateDiagonalTailChunk001Sub000Block141TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block141Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block141Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block141Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block141Part020
    + surrogateDiagTailX0RatChunk001Sub000Block141Part021
    + surrogateDiagTailX0RatChunk001Sub000Block141Part022
    + surrogateDiagTailX0RatChunk001Sub000Block141Part023
    + surrogateDiagTailX0RatChunk001Sub000Block141Part024

def surrogateDiagonalTailChunk001Sub000Block141Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block141HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block141MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block141TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block141 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block141Part000
    + surrogateDiagTailX0RatChunk001Sub000Block141Part001
    + surrogateDiagTailX0RatChunk001Sub000Block141Part002
    + surrogateDiagTailX0RatChunk001Sub000Block141Part003
    + surrogateDiagTailX0RatChunk001Sub000Block141Part004
    + surrogateDiagTailX0RatChunk001Sub000Block141Part005
    + surrogateDiagTailX0RatChunk001Sub000Block141Part006
    + surrogateDiagTailX0RatChunk001Sub000Block141Part007
    + surrogateDiagTailX0RatChunk001Sub000Block141Part008
    + surrogateDiagTailX0RatChunk001Sub000Block141Part009
    + surrogateDiagTailX0RatChunk001Sub000Block141Part010
    + surrogateDiagTailX0RatChunk001Sub000Block141Part011
    + surrogateDiagTailX0RatChunk001Sub000Block141Part012
    + surrogateDiagTailX0RatChunk001Sub000Block141Part013
    + surrogateDiagTailX0RatChunk001Sub000Block141Part014
    + surrogateDiagTailX0RatChunk001Sub000Block141Part015
    + surrogateDiagTailX0RatChunk001Sub000Block141Part016
    + surrogateDiagTailX0RatChunk001Sub000Block141Part017
    + surrogateDiagTailX0RatChunk001Sub000Block141Part018
    + surrogateDiagTailX0RatChunk001Sub000Block141Part019
    + surrogateDiagTailX0RatChunk001Sub000Block141Part020
    + surrogateDiagTailX0RatChunk001Sub000Block141Part021
    + surrogateDiagTailX0RatChunk001Sub000Block141Part022
    + surrogateDiagTailX0RatChunk001Sub000Block141Part023
    + surrogateDiagTailX0RatChunk001Sub000Block141Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block141_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block141Head + surrogateDiagTailX0RatChunk001Sub000Block141Mid + surrogateDiagTailX0RatChunk001Sub000Block141Tail =
      surrogateDiagTailX0RatChunk001Sub000Block141 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block141Head surrogateDiagTailX0RatChunk001Sub000Block141Mid surrogateDiagTailX0RatChunk001Sub000Block141Tail surrogateDiagTailX0RatChunk001Sub000Block141
  ring

def SurrogateDiagonalTailChunk001Sub000Block141HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block141HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block141Head

def SurrogateDiagonalTailChunk001Sub000Block141MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block141MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block141Mid

def SurrogateDiagonalTailChunk001Sub000Block141TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block141TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block141Tail

theorem surrogateDiagonalTailChunk001Sub000Block141_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block141HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block141MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block141TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block141Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block141 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block141HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block141MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block141TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block141Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block141_eq_head_add_mid_add_tail

/-- Block 142 covers tail-support indices [13550,13575) and q from 22339 to 22378. -/

def TailChunk001Sub000Block142Part000SupportExplicit : Finset ℕ :=
  ([22339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part000 : ℚ :=
  (254605111 : ℚ) / 1464392820000000000

def SurrogateDiagonalTailChunk001Sub000Block142Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22339
    = surrogateDiagTailX0RatChunk001Sub000Block142Part000

theorem surrogateDiagonalTailChunk001Sub000Block142Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part000] using hcert

def TailChunk001Sub000Block142Part001SupportExplicit : Finset ℕ :=
  ([22341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part001 : ℚ :=
  (1006997577 : ℚ) / 222793418654842880

def SurrogateDiagonalTailChunk001Sub000Block142Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22341
    = surrogateDiagTailX0RatChunk001Sub000Block142Part001

theorem surrogateDiagonalTailChunk001Sub000Block142Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part001] using hcert

def TailChunk001Sub000Block142Part002SupportExplicit : Finset ℕ :=
  ([22342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part002 : ℚ :=
  (3119781025 : ℚ) / 15570391862891442

def SurrogateDiagonalTailChunk001Sub000Block142Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22342
    = surrogateDiagTailX0RatChunk001Sub000Block142Part002

theorem surrogateDiagonalTailChunk001Sub000Block142Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part002] using hcert

def TailChunk001Sub000Block142Part003SupportExplicit : Finset ℕ :=
  ([22343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block142Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22343
    = surrogateDiagTailX0RatChunk001Sub000Block142Part003

theorem surrogateDiagonalTailChunk001Sub000Block142Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part003] using hcert

def TailChunk001Sub000Block142Part004SupportExplicit : Finset ℕ :=
  ([22345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part004 : ℚ :=
  (100481907481 : ℚ) / 8917883668345651200

def SurrogateDiagonalTailChunk001Sub000Block142Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22345
    = surrogateDiagTailX0RatChunk001Sub000Block142Part004

theorem surrogateDiagonalTailChunk001Sub000Block142Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part004] using hcert

def TailChunk001Sub000Block142Part005SupportExplicit : Finset ℕ :=
  ([22346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part005 : ℚ :=
  (1950561390625 : ℚ) / 9738466523172025632

def SurrogateDiagonalTailChunk001Sub000Block142Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22346
    = surrogateDiagTailX0RatChunk001Sub000Block142Part005

theorem surrogateDiagonalTailChunk001Sub000Block142Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part005] using hcert

def TailChunk001Sub000Block142Part006SupportExplicit : Finset ℕ :=
  ([22349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block142Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22349
    = surrogateDiagTailX0RatChunk001Sub000Block142Part006

theorem surrogateDiagonalTailChunk001Sub000Block142Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part006] using hcert

def TailChunk001Sub000Block142Part007SupportExplicit : Finset ℕ :=
  ([22351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part007 : ℚ :=
  (2096962871 : ℚ) / 420933793732761600

def SurrogateDiagonalTailChunk001Sub000Block142Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22351
    = surrogateDiagTailX0RatChunk001Sub000Block142Part007

theorem surrogateDiagonalTailChunk001Sub000Block142Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part007] using hcert

def TailChunk001Sub000Block142Part008SupportExplicit : Finset ℕ :=
  ([22353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part008 : ℚ :=
  (5001 : ℚ) / 985768802000000

def SurrogateDiagonalTailChunk001Sub000Block142Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22353
    = surrogateDiagTailX0RatChunk001Sub000Block142Part008

theorem surrogateDiagonalTailChunk001Sub000Block142Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part008] using hcert

def TailChunk001Sub000Block142Part009SupportExplicit : Finset ℕ :=
  ([22354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part009 : ℚ :=
  (1951958265625 : ℚ) / 9752420977712067072

def SurrogateDiagonalTailChunk001Sub000Block142Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22354
    = surrogateDiagTailX0RatChunk001Sub000Block142Part009

theorem surrogateDiagonalTailChunk001Sub000Block142Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part009] using hcert

def TailChunk001Sub000Block142Part010SupportExplicit : Finset ℕ :=
  ([22355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part010 : ℚ :=
  (1452972855175 : ℚ) / 197675078574290239488

def SurrogateDiagonalTailChunk001Sub000Block142Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22355
    = surrogateDiagTailX0RatChunk001Sub000Block142Part010

theorem surrogateDiagonalTailChunk001Sub000Block142Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part010] using hcert

def TailChunk001Sub000Block142Part011SupportExplicit : Finset ℕ :=
  ([22357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part011 : ℚ :=
  (7448725 : ℚ) / 38437827619198176

def SurrogateDiagonalTailChunk001Sub000Block142Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22357
    = surrogateDiagTailX0RatChunk001Sub000Block142Part011

theorem surrogateDiagonalTailChunk001Sub000Block142Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part011] using hcert

def TailChunk001Sub000Block142Part012SupportExplicit : Finset ℕ :=
  ([22358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part012 : ℚ :=
  (216150350125 : ℚ) / 750940240020880896

def SurrogateDiagonalTailChunk001Sub000Block142Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22358
    = surrogateDiagTailX0RatChunk001Sub000Block142Part012

theorem surrogateDiagonalTailChunk001Sub000Block142Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part012] using hcert

def TailChunk001Sub000Block142Part013SupportExplicit : Finset ℕ :=
  ([22359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part013 : ℚ :=
  (168993144625 : ℚ) / 105618216150953361408

def SurrogateDiagonalTailChunk001Sub000Block142Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22359
    = surrogateDiagTailX0RatChunk001Sub000Block142Part013

theorem surrogateDiagonalTailChunk001Sub000Block142Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part013] using hcert

def TailChunk001Sub000Block142Part014SupportExplicit : Finset ℕ :=
  ([22361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part014 : ℚ :=
  (44664207725 : ℚ) / 192568291713379725696

def SurrogateDiagonalTailChunk001Sub000Block142Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22361
    = surrogateDiagTailX0RatChunk001Sub000Block142Part014

theorem surrogateDiagonalTailChunk001Sub000Block142Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part014] using hcert

def TailChunk001Sub000Block142Part015SupportExplicit : Finset ℕ :=
  ([22362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part015 : ℚ :=
  (3471393627325 : ℚ) / 7711133887264814208

def SurrogateDiagonalTailChunk001Sub000Block142Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22362
    = surrogateDiagTailX0RatChunk001Sub000Block142Part015

theorem surrogateDiagonalTailChunk001Sub000Block142Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part015] using hcert

def TailChunk001Sub000Block142Part016SupportExplicit : Finset ℕ :=
  ([22363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part016 : ℚ :=
  (22340484407 : ℚ) / 6627814365461529600

def SurrogateDiagonalTailChunk001Sub000Block142Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22363
    = surrogateDiagTailX0RatChunk001Sub000Block142Part016

theorem surrogateDiagonalTailChunk001Sub000Block142Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part016] using hcert

def TailChunk001Sub000Block142Part017SupportExplicit : Finset ℕ :=
  ([22366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part017 : ℚ :=
  (301341143767 : ℚ) / 1422254785374259200

def SurrogateDiagonalTailChunk001Sub000Block142Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22366
    = surrogateDiagTailX0RatChunk001Sub000Block142Part017

theorem surrogateDiagonalTailChunk001Sub000Block142Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part017] using hcert

def TailChunk001Sub000Block142Part018SupportExplicit : Finset ℕ :=
  ([22367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block142Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22367
    = surrogateDiagTailX0RatChunk001Sub000Block142Part018

theorem surrogateDiagonalTailChunk001Sub000Block142Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part018] using hcert

def TailChunk001Sub000Block142Part019SupportExplicit : Finset ℕ :=
  ([22369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block142Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22369
    = surrogateDiagTailX0RatChunk001Sub000Block142Part019

theorem surrogateDiagonalTailChunk001Sub000Block142Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part019] using hcert

def TailChunk001Sub000Block142Part020SupportExplicit : Finset ℕ :=
  ([22370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part020 : ℚ :=
  (5313927324775 : ℚ) / 16001254070038069248

def SurrogateDiagonalTailChunk001Sub000Block142Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22370
    = surrogateDiagTailX0RatChunk001Sub000Block142Part020

theorem surrogateDiagonalTailChunk001Sub000Block142Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part020] using hcert

def TailChunk001Sub000Block142Part021SupportExplicit : Finset ℕ :=
  ([22371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part021 : ℚ :=
  (125025 : ℚ) / 24723706785824768

def SurrogateDiagonalTailChunk001Sub000Block142Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22371
    = surrogateDiagTailX0RatChunk001Sub000Block142Part021

theorem surrogateDiagonalTailChunk001Sub000Block142Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part021] using hcert

def TailChunk001Sub000Block142Part022SupportExplicit : Finset ℕ :=
  ([22373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part022 : ℚ :=
  (11164625591 : ℚ) / 9076023806400921600

def SurrogateDiagonalTailChunk001Sub000Block142Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22373
    = surrogateDiagTailX0RatChunk001Sub000Block142Part022

theorem surrogateDiagonalTailChunk001Sub000Block142Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part022] using hcert

def TailChunk001Sub000Block142Part023SupportExplicit : Finset ℕ :=
  ([22377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part023 : ℚ :=
  (41675 : ℚ) / 8250081681257856

def SurrogateDiagonalTailChunk001Sub000Block142Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22377
    = surrogateDiagTailX0RatChunk001Sub000Block142Part023

theorem surrogateDiagonalTailChunk001Sub000Block142Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part023] using hcert

def TailChunk001Sub000Block142Part024SupportExplicit : Finset ℕ :=
  ([22378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block142Part024 : ℚ :=
  (7571811188275 : ℚ) / 36027568552026066048

def SurrogateDiagonalTailChunk001Sub000Block142Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22378
    = surrogateDiagTailX0RatChunk001Sub000Block142Part024

theorem surrogateDiagonalTailChunk001Sub000Block142Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block142Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block142Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block142Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block142Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block142Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block142Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block142HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block142Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block142Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block142Part000
    + surrogateDiagTailX0RatChunk001Sub000Block142Part001
    + surrogateDiagTailX0RatChunk001Sub000Block142Part002
    + surrogateDiagTailX0RatChunk001Sub000Block142Part003
    + surrogateDiagTailX0RatChunk001Sub000Block142Part004
    + surrogateDiagTailX0RatChunk001Sub000Block142Part005
    + surrogateDiagTailX0RatChunk001Sub000Block142Part006
    + surrogateDiagTailX0RatChunk001Sub000Block142Part007
    + surrogateDiagTailX0RatChunk001Sub000Block142Part008
    + surrogateDiagTailX0RatChunk001Sub000Block142Part009

def surrogateDiagonalTailChunk001Sub000Block142MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block142Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block142Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block142Part010
    + surrogateDiagTailX0RatChunk001Sub000Block142Part011
    + surrogateDiagTailX0RatChunk001Sub000Block142Part012
    + surrogateDiagTailX0RatChunk001Sub000Block142Part013
    + surrogateDiagTailX0RatChunk001Sub000Block142Part014
    + surrogateDiagTailX0RatChunk001Sub000Block142Part015
    + surrogateDiagTailX0RatChunk001Sub000Block142Part016
    + surrogateDiagTailX0RatChunk001Sub000Block142Part017
    + surrogateDiagTailX0RatChunk001Sub000Block142Part018
    + surrogateDiagTailX0RatChunk001Sub000Block142Part019

def surrogateDiagonalTailChunk001Sub000Block142TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block142Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block142Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block142Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block142Part020
    + surrogateDiagTailX0RatChunk001Sub000Block142Part021
    + surrogateDiagTailX0RatChunk001Sub000Block142Part022
    + surrogateDiagTailX0RatChunk001Sub000Block142Part023
    + surrogateDiagTailX0RatChunk001Sub000Block142Part024

def surrogateDiagonalTailChunk001Sub000Block142Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block142HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block142MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block142TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block142 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block142Part000
    + surrogateDiagTailX0RatChunk001Sub000Block142Part001
    + surrogateDiagTailX0RatChunk001Sub000Block142Part002
    + surrogateDiagTailX0RatChunk001Sub000Block142Part003
    + surrogateDiagTailX0RatChunk001Sub000Block142Part004
    + surrogateDiagTailX0RatChunk001Sub000Block142Part005
    + surrogateDiagTailX0RatChunk001Sub000Block142Part006
    + surrogateDiagTailX0RatChunk001Sub000Block142Part007
    + surrogateDiagTailX0RatChunk001Sub000Block142Part008
    + surrogateDiagTailX0RatChunk001Sub000Block142Part009
    + surrogateDiagTailX0RatChunk001Sub000Block142Part010
    + surrogateDiagTailX0RatChunk001Sub000Block142Part011
    + surrogateDiagTailX0RatChunk001Sub000Block142Part012
    + surrogateDiagTailX0RatChunk001Sub000Block142Part013
    + surrogateDiagTailX0RatChunk001Sub000Block142Part014
    + surrogateDiagTailX0RatChunk001Sub000Block142Part015
    + surrogateDiagTailX0RatChunk001Sub000Block142Part016
    + surrogateDiagTailX0RatChunk001Sub000Block142Part017
    + surrogateDiagTailX0RatChunk001Sub000Block142Part018
    + surrogateDiagTailX0RatChunk001Sub000Block142Part019
    + surrogateDiagTailX0RatChunk001Sub000Block142Part020
    + surrogateDiagTailX0RatChunk001Sub000Block142Part021
    + surrogateDiagTailX0RatChunk001Sub000Block142Part022
    + surrogateDiagTailX0RatChunk001Sub000Block142Part023
    + surrogateDiagTailX0RatChunk001Sub000Block142Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block142_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block142Head + surrogateDiagTailX0RatChunk001Sub000Block142Mid + surrogateDiagTailX0RatChunk001Sub000Block142Tail =
      surrogateDiagTailX0RatChunk001Sub000Block142 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block142Head surrogateDiagTailX0RatChunk001Sub000Block142Mid surrogateDiagTailX0RatChunk001Sub000Block142Tail surrogateDiagTailX0RatChunk001Sub000Block142
  ring

def SurrogateDiagonalTailChunk001Sub000Block142HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block142HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block142Head

def SurrogateDiagonalTailChunk001Sub000Block142MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block142MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block142Mid

def SurrogateDiagonalTailChunk001Sub000Block142TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block142TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block142Tail

theorem surrogateDiagonalTailChunk001Sub000Block142_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block142HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block142MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block142TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block142Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block142 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block142HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block142MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block142TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block142Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block142_eq_head_add_mid_add_tail

/-- Block 143 covers tail-support indices [13575,13600) and q from 22379 to 22421. -/

def TailChunk001Sub000Block143Part000SupportExplicit : Finset ℕ :=
  ([22379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part000 : ℚ :=
  (113600450075 : ℚ) / 34415092590594160896

def SurrogateDiagonalTailChunk001Sub000Block143Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22379
    = surrogateDiagTailX0RatChunk001Sub000Block143Part000

theorem surrogateDiagonalTailChunk001Sub000Block143Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part000] using hcert

def TailChunk001Sub000Block143Part001SupportExplicit : Finset ℕ :=
  ([22381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block143Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22381
    = surrogateDiagTailX0RatChunk001Sub000Block143Part001

theorem surrogateDiagonalTailChunk001Sub000Block143Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part001] using hcert

def TailChunk001Sub000Block143Part002SupportExplicit : Finset ℕ :=
  ([22386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part002 : ℚ :=
  (24491616349 : ℚ) / 27524332309708800

def SurrogateDiagonalTailChunk001Sub000Block143Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22386
    = surrogateDiagTailX0RatChunk001Sub000Block143Part002

theorem surrogateDiagonalTailChunk001Sub000Block143Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part002] using hcert

def TailChunk001Sub000Block143Part003SupportExplicit : Finset ℕ :=
  ([22387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part003 : ℚ :=
  (12561587 : ℚ) / 53843396333961600

def SurrogateDiagonalTailChunk001Sub000Block143Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22387
    = surrogateDiagTailX0RatChunk001Sub000Block143Part003

theorem surrogateDiagonalTailChunk001Sub000Block143Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part003] using hcert

def TailChunk001Sub000Block143Part004SupportExplicit : Finset ℕ :=
  ([22389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part004 : ℚ :=
  (3355233534625 : ℚ) / 96499089172246560768

def SurrogateDiagonalTailChunk001Sub000Block143Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22389
    = surrogateDiagTailX0RatChunk001Sub000Block143Part004

theorem surrogateDiagonalTailChunk001Sub000Block143Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part004] using hcert

def TailChunk001Sub000Block143Part005SupportExplicit : Finset ℕ :=
  ([22390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part005 : ℚ :=
  (5323435469725 : ℚ) / 16058580493875038208

def SurrogateDiagonalTailChunk001Sub000Block143Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22390
    = surrogateDiagTailX0RatChunk001Sub000Block143Part005

theorem surrogateDiagonalTailChunk001Sub000Block143Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part005] using hcert

def TailChunk001Sub000Block143Part006SupportExplicit : Finset ℕ :=
  ([22391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block143Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22391
    = surrogateDiagTailX0RatChunk001Sub000Block143Part006

theorem surrogateDiagonalTailChunk001Sub000Block143Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part006] using hcert

def TailChunk001Sub000Block143Part007SupportExplicit : Finset ℕ :=
  ([22394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part007 : ℚ :=
  (1958950140625 : ℚ) / 9822418335457081632

def SurrogateDiagonalTailChunk001Sub000Block143Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22394
    = surrogateDiagTailX0RatChunk001Sub000Block143Part007

theorem surrogateDiagonalTailChunk001Sub000Block143Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part007] using hcert

def TailChunk001Sub000Block143Part008SupportExplicit : Finset ℕ :=
  ([22395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part008 : ℚ :=
  (765876274825 : ℚ) / 12688261130962993152

def SurrogateDiagonalTailChunk001Sub000Block143Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22395
    = surrogateDiagTailX0RatChunk001Sub000Block143Part008

theorem surrogateDiagonalTailChunk001Sub000Block143Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part008] using hcert

def TailChunk001Sub000Block143Part009SupportExplicit : Finset ℕ :=
  ([22397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block143Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22397
    = surrogateDiagTailX0RatChunk001Sub000Block143Part009

theorem surrogateDiagonalTailChunk001Sub000Block143Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part009] using hcert

def TailChunk001Sub000Block143Part010SupportExplicit : Finset ℕ :=
  ([22398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part010 : ℚ :=
  (2176883117675 : ℚ) / 3880461564625019904

def SurrogateDiagonalTailChunk001Sub000Block143Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22398
    = surrogateDiagTailX0RatChunk001Sub000Block143Part010

theorem surrogateDiagonalTailChunk001Sub000Block143Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part010] using hcert

def TailChunk001Sub000Block143Part011SupportExplicit : Finset ℕ :=
  ([22399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part011 : ℚ :=
  (9991455575 : ℚ) / 8141349604367847168

def SurrogateDiagonalTailChunk001Sub000Block143Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22399
    = surrogateDiagTailX0RatChunk001Sub000Block143Part011

theorem surrogateDiagonalTailChunk001Sub000Block143Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part011] using hcert

def TailChunk001Sub000Block143Part012SupportExplicit : Finset ℕ :=
  ([22402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part012 : ℚ :=
  (7285576008325 : ℚ) / 32678541066959365248

def SurrogateDiagonalTailChunk001Sub000Block143Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22402
    = surrogateDiagTailX0RatChunk001Sub000Block143Part012

theorem surrogateDiagonalTailChunk001Sub000Block143Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part012] using hcert

def TailChunk001Sub000Block143Part013SupportExplicit : Finset ℕ :=
  ([22403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part013 : ℚ :=
  (7275883831 : ℚ) / 22756076565988147200

def SurrogateDiagonalTailChunk001Sub000Block143Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22403
    = surrogateDiagTailX0RatChunk001Sub000Block143Part013

theorem surrogateDiagonalTailChunk001Sub000Block143Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part013] using hcert

def TailChunk001Sub000Block143Part014SupportExplicit : Finset ℕ :=
  ([22405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part014 : ℚ :=
  (3348401673 : ℚ) / 687618594732769280

def SurrogateDiagonalTailChunk001Sub000Block143Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22405
    = surrogateDiagTailX0RatChunk001Sub000Block143Part014

theorem surrogateDiagonalTailChunk001Sub000Block143Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part014] using hcert

def TailChunk001Sub000Block143Part015SupportExplicit : Finset ℕ :=
  ([22406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part015 : ℚ :=
  (169590755025 : ℚ) / 731410302726569984

def SurrogateDiagonalTailChunk001Sub000Block143Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22406
    = surrogateDiagTailX0RatChunk001Sub000Block143Part015

theorem surrogateDiagonalTailChunk001Sub000Block143Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part015] using hcert

def TailChunk001Sub000Block143Part016SupportExplicit : Finset ℕ :=
  ([22407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part016 : ℚ :=
  (4497866131 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk001Sub000Block143Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22407
    = surrogateDiagTailX0RatChunk001Sub000Block143Part016

theorem surrogateDiagonalTailChunk001Sub000Block143Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part016] using hcert

def TailChunk001Sub000Block143Part017SupportExplicit : Finset ℕ :=
  ([22409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block143Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22409
    = surrogateDiagTailX0RatChunk001Sub000Block143Part017

theorem surrogateDiagonalTailChunk001Sub000Block143Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part017] using hcert

def TailChunk001Sub000Block143Part018SupportExplicit : Finset ℕ :=
  ([22411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part018 : ℚ :=
  (6427857625 : ℚ) / 32731811800659542016

def SurrogateDiagonalTailChunk001Sub000Block143Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22411
    = surrogateDiagTailX0RatChunk001Sub000Block143Part018

theorem surrogateDiagonalTailChunk001Sub000Block143Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part018] using hcert

def TailChunk001Sub000Block143Part019SupportExplicit : Finset ℕ :=
  ([22413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part019 : ℚ :=
  (136251705517 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub000Block143Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22413
    = surrogateDiagTailX0RatChunk001Sub000Block143Part019

theorem surrogateDiagonalTailChunk001Sub000Block143Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part019] using hcert

def TailChunk001Sub000Block143Part020SupportExplicit : Finset ℕ :=
  ([22414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part020 : ℚ :=
  (60825753163 : ℚ) / 212379107328000000

def SurrogateDiagonalTailChunk001Sub000Block143Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22414
    = surrogateDiagTailX0RatChunk001Sub000Block143Part020

theorem surrogateDiagonalTailChunk001Sub000Block143Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part020] using hcert

def TailChunk001Sub000Block143Part021SupportExplicit : Finset ℕ :=
  ([22415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part021 : ℚ :=
  (1256770877125 : ℚ) / 258317740339969148928

def SurrogateDiagonalTailChunk001Sub000Block143Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22415
    = surrogateDiagTailX0RatChunk001Sub000Block143Part021

theorem surrogateDiagonalTailChunk001Sub000Block143Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part021] using hcert

def TailChunk001Sub000Block143Part022SupportExplicit : Finset ℕ :=
  ([22417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part022 : ℚ :=
  (269162039425 : ℚ) / 545918969796866899968

def SurrogateDiagonalTailChunk001Sub000Block143Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22417
    = surrogateDiagTailX0RatChunk001Sub000Block143Part022

theorem surrogateDiagonalTailChunk001Sub000Block143Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part022] using hcert

def TailChunk001Sub000Block143Part023SupportExplicit : Finset ℕ :=
  ([22418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part023 : ℚ :=
  (269604342769 : ℚ) / 1074182226462595200

def SurrogateDiagonalTailChunk001Sub000Block143Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22418
    = surrogateDiagTailX0RatChunk001Sub000Block143Part023

theorem surrogateDiagonalTailChunk001Sub000Block143Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part023] using hcert

def TailChunk001Sub000Block143Part024SupportExplicit : Finset ℕ :=
  ([22421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block143Part024 : ℚ :=
  (642675159925 : ℚ) / 340656884907658685568

def SurrogateDiagonalTailChunk001Sub000Block143Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22421
    = surrogateDiagTailX0RatChunk001Sub000Block143Part024

theorem surrogateDiagonalTailChunk001Sub000Block143Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block143Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block143Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block143Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block143Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block143Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block143Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block143HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block143Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block143Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block143Part000
    + surrogateDiagTailX0RatChunk001Sub000Block143Part001
    + surrogateDiagTailX0RatChunk001Sub000Block143Part002
    + surrogateDiagTailX0RatChunk001Sub000Block143Part003
    + surrogateDiagTailX0RatChunk001Sub000Block143Part004
    + surrogateDiagTailX0RatChunk001Sub000Block143Part005
    + surrogateDiagTailX0RatChunk001Sub000Block143Part006
    + surrogateDiagTailX0RatChunk001Sub000Block143Part007
    + surrogateDiagTailX0RatChunk001Sub000Block143Part008
    + surrogateDiagTailX0RatChunk001Sub000Block143Part009

def surrogateDiagonalTailChunk001Sub000Block143MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block143Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block143Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block143Part010
    + surrogateDiagTailX0RatChunk001Sub000Block143Part011
    + surrogateDiagTailX0RatChunk001Sub000Block143Part012
    + surrogateDiagTailX0RatChunk001Sub000Block143Part013
    + surrogateDiagTailX0RatChunk001Sub000Block143Part014
    + surrogateDiagTailX0RatChunk001Sub000Block143Part015
    + surrogateDiagTailX0RatChunk001Sub000Block143Part016
    + surrogateDiagTailX0RatChunk001Sub000Block143Part017
    + surrogateDiagTailX0RatChunk001Sub000Block143Part018
    + surrogateDiagTailX0RatChunk001Sub000Block143Part019

def surrogateDiagonalTailChunk001Sub000Block143TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block143Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block143Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block143Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block143Part020
    + surrogateDiagTailX0RatChunk001Sub000Block143Part021
    + surrogateDiagTailX0RatChunk001Sub000Block143Part022
    + surrogateDiagTailX0RatChunk001Sub000Block143Part023
    + surrogateDiagTailX0RatChunk001Sub000Block143Part024

def surrogateDiagonalTailChunk001Sub000Block143Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block143HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block143MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block143TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block143 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block143Part000
    + surrogateDiagTailX0RatChunk001Sub000Block143Part001
    + surrogateDiagTailX0RatChunk001Sub000Block143Part002
    + surrogateDiagTailX0RatChunk001Sub000Block143Part003
    + surrogateDiagTailX0RatChunk001Sub000Block143Part004
    + surrogateDiagTailX0RatChunk001Sub000Block143Part005
    + surrogateDiagTailX0RatChunk001Sub000Block143Part006
    + surrogateDiagTailX0RatChunk001Sub000Block143Part007
    + surrogateDiagTailX0RatChunk001Sub000Block143Part008
    + surrogateDiagTailX0RatChunk001Sub000Block143Part009
    + surrogateDiagTailX0RatChunk001Sub000Block143Part010
    + surrogateDiagTailX0RatChunk001Sub000Block143Part011
    + surrogateDiagTailX0RatChunk001Sub000Block143Part012
    + surrogateDiagTailX0RatChunk001Sub000Block143Part013
    + surrogateDiagTailX0RatChunk001Sub000Block143Part014
    + surrogateDiagTailX0RatChunk001Sub000Block143Part015
    + surrogateDiagTailX0RatChunk001Sub000Block143Part016
    + surrogateDiagTailX0RatChunk001Sub000Block143Part017
    + surrogateDiagTailX0RatChunk001Sub000Block143Part018
    + surrogateDiagTailX0RatChunk001Sub000Block143Part019
    + surrogateDiagTailX0RatChunk001Sub000Block143Part020
    + surrogateDiagTailX0RatChunk001Sub000Block143Part021
    + surrogateDiagTailX0RatChunk001Sub000Block143Part022
    + surrogateDiagTailX0RatChunk001Sub000Block143Part023
    + surrogateDiagTailX0RatChunk001Sub000Block143Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block143_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block143Head + surrogateDiagTailX0RatChunk001Sub000Block143Mid + surrogateDiagTailX0RatChunk001Sub000Block143Tail =
      surrogateDiagTailX0RatChunk001Sub000Block143 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block143Head surrogateDiagTailX0RatChunk001Sub000Block143Mid surrogateDiagTailX0RatChunk001Sub000Block143Tail surrogateDiagTailX0RatChunk001Sub000Block143
  ring

def SurrogateDiagonalTailChunk001Sub000Block143HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block143HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block143Head

def SurrogateDiagonalTailChunk001Sub000Block143MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block143MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block143Mid

def SurrogateDiagonalTailChunk001Sub000Block143TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block143TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block143Tail

theorem surrogateDiagonalTailChunk001Sub000Block143_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block143HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block143MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block143TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block143Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block143 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block143HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block143MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block143TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block143Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block143_eq_head_add_mid_add_tail

/-- Block 144 covers tail-support indices [13600,13625) and q from 22422 to 22463. -/

def TailChunk001Sub000Block144Part000SupportExplicit : Finset ℕ :=
  ([22422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part000 : ℚ :=
  (18359220131 : ℚ) / 29865811968000000

def SurrogateDiagonalTailChunk001Sub000Block144Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22422
    = surrogateDiagTailX0RatChunk001Sub000Block144Part000

theorem surrogateDiagonalTailChunk001Sub000Block144Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part000] using hcert

def TailChunk001Sub000Block144Part001SupportExplicit : Finset ℕ :=
  ([22423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part001 : ℚ :=
  (27548288775 : ℚ) / 41208535877417304064

def SurrogateDiagonalTailChunk001Sub000Block144Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22423
    = surrogateDiagTailX0RatChunk001Sub000Block144Part001

theorem surrogateDiagonalTailChunk001Sub000Block144Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part001] using hcert

def TailChunk001Sub000Block144Part002SupportExplicit : Finset ℕ :=
  ([22426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part002 : ℚ :=
  (1964552640625 : ℚ) / 9878686968322159392

def SurrogateDiagonalTailChunk001Sub000Block144Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22426
    = surrogateDiagTailX0RatChunk001Sub000Block144Part002

theorem surrogateDiagonalTailChunk001Sub000Block144Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part002] using hcert

def TailChunk001Sub000Block144Part003SupportExplicit : Finset ℕ :=
  ([22427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part003 : ℚ :=
  (1028157667 : ℚ) / 3250868080855449600

def SurrogateDiagonalTailChunk001Sub000Block144Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22427
    = surrogateDiagTailX0RatChunk001Sub000Block144Part003

theorem surrogateDiagonalTailChunk001Sub000Block144Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part003] using hcert

def TailChunk001Sub000Block144Part004SupportExplicit : Finset ℕ :=
  ([22429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part004 : ℚ :=
  (1305511069 : ℚ) / 1078409205034264200

def SurrogateDiagonalTailChunk001Sub000Block144Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22429
    = surrogateDiagTailX0RatChunk001Sub000Block144Part004

theorem surrogateDiagonalTailChunk001Sub000Block144Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part004] using hcert

def TailChunk001Sub000Block144Part005SupportExplicit : Finset ℕ :=
  ([22430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part005 : ℚ :=
  (1885671499275 : ℚ) / 5391231768581380096

def SurrogateDiagonalTailChunk001Sub000Block144Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22430
    = surrogateDiagTailX0RatChunk001Sub000Block144Part005

theorem surrogateDiagonalTailChunk001Sub000Block144Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part005] using hcert

def TailChunk001Sub000Block144Part006SupportExplicit : Finset ℕ :=
  ([22431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part006 : ℚ :=
  (62389035725 : ℚ) / 2231700883506355968

def SurrogateDiagonalTailChunk001Sub000Block144Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22431
    = surrogateDiagTailX0RatChunk001Sub000Block144Part006

theorem surrogateDiagonalTailChunk001Sub000Block144Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part006] using hcert

def TailChunk001Sub000Block144Part007SupportExplicit : Finset ℕ :=
  ([22433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block144Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22433
    = surrogateDiagTailX0RatChunk001Sub000Block144Part007

theorem surrogateDiagonalTailChunk001Sub000Block144Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part007] using hcert

def TailChunk001Sub000Block144Part008SupportExplicit : Finset ℕ :=
  ([22434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part008 : ℚ :=
  (545971840775 : ℚ) / 976369136534030736

def SurrogateDiagonalTailChunk001Sub000Block144Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22434
    = surrogateDiagTailX0RatChunk001Sub000Block144Part008

theorem surrogateDiagonalTailChunk001Sub000Block144Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part008] using hcert

def TailChunk001Sub000Block144Part009SupportExplicit : Finset ℕ :=
  ([22435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part009 : ℚ :=
  (2933732399 : ℚ) / 278369543556956160

def SurrogateDiagonalTailChunk001Sub000Block144Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22435
    = surrogateDiagTailX0RatChunk001Sub000Block144Part009

theorem surrogateDiagonalTailChunk001Sub000Block144Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part009] using hcert

def TailChunk001Sub000Block144Part010SupportExplicit : Finset ℕ :=
  ([22438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part010 : ℚ :=
  (6924270538675 : ℚ) / 28627334088875624448

def SurrogateDiagonalTailChunk001Sub000Block144Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22438
    = surrogateDiagTailX0RatChunk001Sub000Block144Part010

theorem surrogateDiagonalTailChunk001Sub000Block144Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part010] using hcert

def TailChunk001Sub000Block144Part011SupportExplicit : Finset ℕ :=
  ([22439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part011 : ℚ :=
  (14140555573 : ℚ) / 20356583916058675200

def SurrogateDiagonalTailChunk001Sub000Block144Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22439
    = surrogateDiagTailX0RatChunk001Sub000Block144Part011

theorem surrogateDiagonalTailChunk001Sub000Block144Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part011] using hcert

def TailChunk001Sub000Block144Part012SupportExplicit : Finset ℕ :=
  ([22441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block144Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22441
    = surrogateDiagTailX0RatChunk001Sub000Block144Part012

theorem surrogateDiagonalTailChunk001Sub000Block144Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part012] using hcert

def TailChunk001Sub000Block144Part013SupportExplicit : Finset ℕ :=
  ([22443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part013 : ℚ :=
  (6995050001 : ℚ) / 250485867968962560

def SurrogateDiagonalTailChunk001Sub000Block144Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22443
    = surrogateDiagTailX0RatChunk001Sub000Block144Part013

theorem surrogateDiagonalTailChunk001Sub000Block144Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part013] using hcert

def TailChunk001Sub000Block144Part014SupportExplicit : Finset ℕ :=
  ([22447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block144Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22447
    = surrogateDiagTailX0RatChunk001Sub000Block144Part014

theorem surrogateDiagonalTailChunk001Sub000Block144Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part014] using hcert

def TailChunk001Sub000Block144Part015SupportExplicit : Finset ℕ :=
  ([22449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part015 : ℚ :=
  (102586949975 : ℚ) / 2108078968676557824

def SurrogateDiagonalTailChunk001Sub000Block144Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22449
    = surrogateDiagTailX0RatChunk001Sub000Block144Part015

theorem surrogateDiagonalTailChunk001Sub000Block144Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part015] using hcert

def TailChunk001Sub000Block144Part016SupportExplicit : Finset ℕ :=
  ([22451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part016 : ℚ :=
  (23509207 : ℚ) / 6065759684395008

def SurrogateDiagonalTailChunk001Sub000Block144Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22451
    = surrogateDiagTailX0RatChunk001Sub000Block144Part016

theorem surrogateDiagonalTailChunk001Sub000Block144Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part016] using hcert

def TailChunk001Sub000Block144Part017SupportExplicit : Finset ℕ :=
  ([22453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block144Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22453
    = surrogateDiagTailX0RatChunk001Sub000Block144Part017

theorem surrogateDiagonalTailChunk001Sub000Block144Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part017] using hcert

def TailChunk001Sub000Block144Part018SupportExplicit : Finset ℕ :=
  ([22454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part018 : ℚ :=
  (64758549925 : ℚ) / 36823288275741984768

def SurrogateDiagonalTailChunk001Sub000Block144Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22454
    = surrogateDiagTailX0RatChunk001Sub000Block144Part018

theorem surrogateDiagonalTailChunk001Sub000Block144Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part018] using hcert

def TailChunk001Sub000Block144Part019SupportExplicit : Finset ℕ :=
  ([22457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part019 : ℚ :=
  (1601227073 : ℚ) / 1809130187862835200

def SurrogateDiagonalTailChunk001Sub000Block144Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22457
    = surrogateDiagTailX0RatChunk001Sub000Block144Part019

theorem surrogateDiagonalTailChunk001Sub000Block144Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part019] using hcert

def TailChunk001Sub000Block144Part020SupportExplicit : Finset ℕ :=
  ([22458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part020 : ℚ :=
  (904434704725 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk001Sub000Block144Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22458
    = surrogateDiagTailX0RatChunk001Sub000Block144Part020

theorem surrogateDiagonalTailChunk001Sub000Block144Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part020] using hcert

def TailChunk001Sub000Block144Part021SupportExplicit : Finset ℕ :=
  ([22459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part021 : ℚ :=
  (194601565075 : ℚ) / 566405365356078778368

def SurrogateDiagonalTailChunk001Sub000Block144Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22459
    = surrogateDiagTailX0RatChunk001Sub000Block144Part021

theorem surrogateDiagonalTailChunk001Sub000Block144Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part021] using hcert

def TailChunk001Sub000Block144Part022SupportExplicit : Finset ℕ :=
  ([22461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part022 : ℚ :=
  (1751568625175 : ℚ) / 62822633368639193664

def SurrogateDiagonalTailChunk001Sub000Block144Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22461
    = surrogateDiagTailX0RatChunk001Sub000Block144Part022

theorem surrogateDiagonalTailChunk001Sub000Block144Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part022] using hcert

def TailChunk001Sub000Block144Part023SupportExplicit : Finset ℕ :=
  ([22462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part023 : ℚ :=
  (12862429 : ℚ) / 1061420241600000

def SurrogateDiagonalTailChunk001Sub000Block144Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22462
    = surrogateDiagTailX0RatChunk001Sub000Block144Part023

theorem surrogateDiagonalTailChunk001Sub000Block144Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part023] using hcert

def TailChunk001Sub000Block144Part024SupportExplicit : Finset ℕ :=
  ([22463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block144Part024 : ℚ :=
  (644012783075 : ℚ) / 171608700719836053504

def SurrogateDiagonalTailChunk001Sub000Block144Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22463
    = surrogateDiagTailX0RatChunk001Sub000Block144Part024

theorem surrogateDiagonalTailChunk001Sub000Block144Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block144Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block144Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block144Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block144Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block144Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block144Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block144HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block144Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block144Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block144Part000
    + surrogateDiagTailX0RatChunk001Sub000Block144Part001
    + surrogateDiagTailX0RatChunk001Sub000Block144Part002
    + surrogateDiagTailX0RatChunk001Sub000Block144Part003
    + surrogateDiagTailX0RatChunk001Sub000Block144Part004
    + surrogateDiagTailX0RatChunk001Sub000Block144Part005
    + surrogateDiagTailX0RatChunk001Sub000Block144Part006
    + surrogateDiagTailX0RatChunk001Sub000Block144Part007
    + surrogateDiagTailX0RatChunk001Sub000Block144Part008
    + surrogateDiagTailX0RatChunk001Sub000Block144Part009

def surrogateDiagonalTailChunk001Sub000Block144MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block144Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block144Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block144Part010
    + surrogateDiagTailX0RatChunk001Sub000Block144Part011
    + surrogateDiagTailX0RatChunk001Sub000Block144Part012
    + surrogateDiagTailX0RatChunk001Sub000Block144Part013
    + surrogateDiagTailX0RatChunk001Sub000Block144Part014
    + surrogateDiagTailX0RatChunk001Sub000Block144Part015
    + surrogateDiagTailX0RatChunk001Sub000Block144Part016
    + surrogateDiagTailX0RatChunk001Sub000Block144Part017
    + surrogateDiagTailX0RatChunk001Sub000Block144Part018
    + surrogateDiagTailX0RatChunk001Sub000Block144Part019

def surrogateDiagonalTailChunk001Sub000Block144TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block144Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block144Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block144Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block144Part020
    + surrogateDiagTailX0RatChunk001Sub000Block144Part021
    + surrogateDiagTailX0RatChunk001Sub000Block144Part022
    + surrogateDiagTailX0RatChunk001Sub000Block144Part023
    + surrogateDiagTailX0RatChunk001Sub000Block144Part024

def surrogateDiagonalTailChunk001Sub000Block144Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block144HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block144MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block144TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block144 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block144Part000
    + surrogateDiagTailX0RatChunk001Sub000Block144Part001
    + surrogateDiagTailX0RatChunk001Sub000Block144Part002
    + surrogateDiagTailX0RatChunk001Sub000Block144Part003
    + surrogateDiagTailX0RatChunk001Sub000Block144Part004
    + surrogateDiagTailX0RatChunk001Sub000Block144Part005
    + surrogateDiagTailX0RatChunk001Sub000Block144Part006
    + surrogateDiagTailX0RatChunk001Sub000Block144Part007
    + surrogateDiagTailX0RatChunk001Sub000Block144Part008
    + surrogateDiagTailX0RatChunk001Sub000Block144Part009
    + surrogateDiagTailX0RatChunk001Sub000Block144Part010
    + surrogateDiagTailX0RatChunk001Sub000Block144Part011
    + surrogateDiagTailX0RatChunk001Sub000Block144Part012
    + surrogateDiagTailX0RatChunk001Sub000Block144Part013
    + surrogateDiagTailX0RatChunk001Sub000Block144Part014
    + surrogateDiagTailX0RatChunk001Sub000Block144Part015
    + surrogateDiagTailX0RatChunk001Sub000Block144Part016
    + surrogateDiagTailX0RatChunk001Sub000Block144Part017
    + surrogateDiagTailX0RatChunk001Sub000Block144Part018
    + surrogateDiagTailX0RatChunk001Sub000Block144Part019
    + surrogateDiagTailX0RatChunk001Sub000Block144Part020
    + surrogateDiagTailX0RatChunk001Sub000Block144Part021
    + surrogateDiagTailX0RatChunk001Sub000Block144Part022
    + surrogateDiagTailX0RatChunk001Sub000Block144Part023
    + surrogateDiagTailX0RatChunk001Sub000Block144Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block144_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block144Head + surrogateDiagTailX0RatChunk001Sub000Block144Mid + surrogateDiagTailX0RatChunk001Sub000Block144Tail =
      surrogateDiagTailX0RatChunk001Sub000Block144 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block144Head surrogateDiagTailX0RatChunk001Sub000Block144Mid surrogateDiagTailX0RatChunk001Sub000Block144Tail surrogateDiagTailX0RatChunk001Sub000Block144
  ring

def SurrogateDiagonalTailChunk001Sub000Block144HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block144HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block144Head

def SurrogateDiagonalTailChunk001Sub000Block144MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block144MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block144Mid

def SurrogateDiagonalTailChunk001Sub000Block144TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block144TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block144Tail

theorem surrogateDiagonalTailChunk001Sub000Block144_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block144HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block144MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block144TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block144Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block144 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block144HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block144MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block144TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block144Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block144_eq_head_add_mid_add_tail

/-- Block 145 covers tail-support indices [13625,13650) and q from 22465 to 22503. -/

def TailChunk001Sub000Block145Part000SupportExplicit : Finset ℕ :=
  ([22465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part000 : ℚ :=
  (420793208625 : ℚ) / 86876948830176772096

def SurrogateDiagonalTailChunk001Sub000Block145Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22465
    = surrogateDiagTailX0RatChunk001Sub000Block145Part000

theorem surrogateDiagonalTailChunk001Sub000Block145Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part000] using hcert

def TailChunk001Sub000Block145Part001SupportExplicit : Finset ℕ :=
  ([22466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part001 : ℚ :=
  (4041041625 : ℚ) / 1710593112660062848

def SurrogateDiagonalTailChunk001Sub000Block145Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22466
    = surrogateDiagTailX0RatChunk001Sub000Block145Part001

theorem surrogateDiagonalTailChunk001Sub000Block145Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part001] using hcert

def TailChunk001Sub000Block145Part002SupportExplicit : Finset ℕ :=
  ([22467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part002 : ℚ :=
  (876252250075 : ℚ) / 31444898203903721472

def SurrogateDiagonalTailChunk001Sub000Block145Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22467
    = surrogateDiagTailX0RatChunk001Sub000Block145Part002

theorem surrogateDiagonalTailChunk001Sub000Block145Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part002] using hcert

def TailChunk001Sub000Block145Part003SupportExplicit : Finset ℕ :=
  ([22469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block145Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22469
    = surrogateDiagTailX0RatChunk001Sub000Block145Part003

theorem surrogateDiagonalTailChunk001Sub000Block145Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part003] using hcert

def TailChunk001Sub000Block145Part004SupportExplicit : Finset ℕ :=
  ([22470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part004 : ℚ :=
  (4442442325 : ℚ) / 7758209773928448

def SurrogateDiagonalTailChunk001Sub000Block145Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22470
    = surrogateDiagTailX0RatChunk001Sub000Block145Part004

theorem surrogateDiagonalTailChunk001Sub000Block145Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part004] using hcert

def TailChunk001Sub000Block145Part005SupportExplicit : Finset ℕ :=
  ([22471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part005 : ℚ :=
  (101435591925 : ℚ) / 177172208220125003776

def SurrogateDiagonalTailChunk001Sub000Block145Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22471
    = surrogateDiagTailX0RatChunk001Sub000Block145Part005

theorem surrogateDiagonalTailChunk001Sub000Block145Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part005] using hcert

def TailChunk001Sub000Block145Part006SupportExplicit : Finset ℕ :=
  ([22474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part006 : ℚ :=
  (3906891947 : ℚ) / 621888502077849600

def SurrogateDiagonalTailChunk001Sub000Block145Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22474
    = surrogateDiagTailX0RatChunk001Sub000Block145Part006

theorem surrogateDiagonalTailChunk001Sub000Block145Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part006] using hcert

def TailChunk001Sub000Block145Part007SupportExplicit : Finset ℕ :=
  ([22478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block145Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22478
    = surrogateDiagTailX0RatChunk001Sub000Block145Part007

theorem surrogateDiagonalTailChunk001Sub000Block145Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part007] using hcert

def TailChunk001Sub000Block145Part008SupportExplicit : Finset ℕ :=
  ([22479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part008 : ℚ :=
  (10650804475 : ℚ) / 352205380362834432

def SurrogateDiagonalTailChunk001Sub000Block145Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22479
    = surrogateDiagTailX0RatChunk001Sub000Block145Part008

theorem surrogateDiagonalTailChunk001Sub000Block145Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part008] using hcert

def TailChunk001Sub000Block145Part009SupportExplicit : Finset ℕ :=
  ([22481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block145Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22481
    = surrogateDiagTailX0RatChunk001Sub000Block145Part009

theorem surrogateDiagonalTailChunk001Sub000Block145Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part009] using hcert

def TailChunk001Sub000Block145Part010SupportExplicit : Finset ℕ :=
  ([22483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block145Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22483
    = surrogateDiagTailX0RatChunk001Sub000Block145Part010

theorem surrogateDiagonalTailChunk001Sub000Block145Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part010] using hcert

def TailChunk001Sub000Block145Part011SupportExplicit : Finset ℕ :=
  ([22485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part011 : ℚ :=
  (61409235375 : ℚ) / 1074466360065366016

def SurrogateDiagonalTailChunk001Sub000Block145Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22485
    = surrogateDiagTailX0RatChunk001Sub000Block145Part011

theorem surrogateDiagonalTailChunk001Sub000Block145Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part011] using hcert

def TailChunk001Sub000Block145Part012SupportExplicit : Finset ℕ :=
  ([22486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block145Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22486
    = surrogateDiagTailX0RatChunk001Sub000Block145Part012

theorem surrogateDiagonalTailChunk001Sub000Block145Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part012] using hcert

def TailChunk001Sub000Block145Part013SupportExplicit : Finset ℕ :=
  ([22487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part013 : ℚ :=
  (96543887875 : ℚ) / 604727488863011340288

def SurrogateDiagonalTailChunk001Sub000Block145Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22487
    = surrogateDiagTailX0RatChunk001Sub000Block145Part013

theorem surrogateDiagonalTailChunk001Sub000Block145Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part013] using hcert

def TailChunk001Sub000Block145Part014SupportExplicit : Finset ℕ :=
  ([22489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part014 : ℚ :=
  (6156629375 : ℚ) / 21396476857042191744

def SurrogateDiagonalTailChunk001Sub000Block145Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22489
    = surrogateDiagTailX0RatChunk001Sub000Block145Part014

theorem surrogateDiagonalTailChunk001Sub000Block145Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part014] using hcert

def TailChunk001Sub000Block145Part015SupportExplicit : Finset ℕ :=
  ([22490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part015 : ℚ :=
  (736066905025 : ℚ) / 11617310472193179648

def SurrogateDiagonalTailChunk001Sub000Block145Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22490
    = surrogateDiagTailX0RatChunk001Sub000Block145Part015

theorem surrogateDiagonalTailChunk001Sub000Block145Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part015] using hcert

def TailChunk001Sub000Block145Part016SupportExplicit : Finset ℕ :=
  ([22493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part016 : ℚ :=
  (52968797 : ℚ) / 296696414153347200

def SurrogateDiagonalTailChunk001Sub000Block145Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22493
    = surrogateDiagTailX0RatChunk001Sub000Block145Part016

theorem surrogateDiagonalTailChunk001Sub000Block145Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part016] using hcert

def TailChunk001Sub000Block145Part017SupportExplicit : Finset ℕ :=
  ([22494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part017 : ℚ :=
  (452990408525 : ℚ) / 3227510228835492864

def SurrogateDiagonalTailChunk001Sub000Block145Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22494
    = surrogateDiagTailX0RatChunk001Sub000Block145Part017

theorem surrogateDiagonalTailChunk001Sub000Block145Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part017] using hcert

def TailChunk001Sub000Block145Part018SupportExplicit : Finset ℕ :=
  ([22495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part018 : ℚ :=
  (2367350923 : ℚ) / 283809846770270208

def SurrogateDiagonalTailChunk001Sub000Block145Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22495
    = surrogateDiagTailX0RatChunk001Sub000Block145Part018

theorem surrogateDiagonalTailChunk001Sub000Block145Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part018] using hcert

def TailChunk001Sub000Block145Part019SupportExplicit : Finset ℕ :=
  ([22497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part019 : ℚ :=
  (1757187625025 : ℚ) / 63226419750599360064

def SurrogateDiagonalTailChunk001Sub000Block145Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22497
    = surrogateDiagTailX0RatChunk001Sub000Block145Part019

theorem surrogateDiagonalTailChunk001Sub000Block145Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part019] using hcert

def TailChunk001Sub000Block145Part020SupportExplicit : Finset ℕ :=
  ([22498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part020 : ℚ :=
  (26960440675 : ℚ) / 1197681990365653056

def SurrogateDiagonalTailChunk001Sub000Block145Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22498
    = surrogateDiagTailX0RatChunk001Sub000Block145Part020

theorem surrogateDiagonalTailChunk001Sub000Block145Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part020] using hcert

def TailChunk001Sub000Block145Part021SupportExplicit : Finset ℕ :=
  ([22499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part021 : ℚ :=
  (3718429933 : ℚ) / 24293984385312000000

def SurrogateDiagonalTailChunk001Sub000Block145Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22499
    = surrogateDiagTailX0RatChunk001Sub000Block145Part021

theorem surrogateDiagonalTailChunk001Sub000Block145Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part021] using hcert

def TailChunk001Sub000Block145Part022SupportExplicit : Finset ℕ :=
  ([22501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block145Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22501
    = surrogateDiagTailX0RatChunk001Sub000Block145Part022

theorem surrogateDiagonalTailChunk001Sub000Block145Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part022] using hcert

def TailChunk001Sub000Block145Part023SupportExplicit : Finset ℕ :=
  ([22502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block145Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22502
    = surrogateDiagTailX0RatChunk001Sub000Block145Part023

theorem surrogateDiagonalTailChunk001Sub000Block145Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part023] using hcert

def TailChunk001Sub000Block145Part024SupportExplicit : Finset ℕ :=
  ([22503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block145Part024 : ℚ :=
  (242039375 : ℚ) / 6605839754330112

def SurrogateDiagonalTailChunk001Sub000Block145Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22503
    = surrogateDiagTailX0RatChunk001Sub000Block145Part024

theorem surrogateDiagonalTailChunk001Sub000Block145Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block145Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block145Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block145Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block145Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block145Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block145Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block145HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block145Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block145Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block145Part000
    + surrogateDiagTailX0RatChunk001Sub000Block145Part001
    + surrogateDiagTailX0RatChunk001Sub000Block145Part002
    + surrogateDiagTailX0RatChunk001Sub000Block145Part003
    + surrogateDiagTailX0RatChunk001Sub000Block145Part004
    + surrogateDiagTailX0RatChunk001Sub000Block145Part005
    + surrogateDiagTailX0RatChunk001Sub000Block145Part006
    + surrogateDiagTailX0RatChunk001Sub000Block145Part007
    + surrogateDiagTailX0RatChunk001Sub000Block145Part008
    + surrogateDiagTailX0RatChunk001Sub000Block145Part009

def surrogateDiagonalTailChunk001Sub000Block145MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block145Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block145Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block145Part010
    + surrogateDiagTailX0RatChunk001Sub000Block145Part011
    + surrogateDiagTailX0RatChunk001Sub000Block145Part012
    + surrogateDiagTailX0RatChunk001Sub000Block145Part013
    + surrogateDiagTailX0RatChunk001Sub000Block145Part014
    + surrogateDiagTailX0RatChunk001Sub000Block145Part015
    + surrogateDiagTailX0RatChunk001Sub000Block145Part016
    + surrogateDiagTailX0RatChunk001Sub000Block145Part017
    + surrogateDiagTailX0RatChunk001Sub000Block145Part018
    + surrogateDiagTailX0RatChunk001Sub000Block145Part019

def surrogateDiagonalTailChunk001Sub000Block145TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block145Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block145Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block145Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block145Part020
    + surrogateDiagTailX0RatChunk001Sub000Block145Part021
    + surrogateDiagTailX0RatChunk001Sub000Block145Part022
    + surrogateDiagTailX0RatChunk001Sub000Block145Part023
    + surrogateDiagTailX0RatChunk001Sub000Block145Part024

def surrogateDiagonalTailChunk001Sub000Block145Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block145HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block145MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block145TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block145 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block145Part000
    + surrogateDiagTailX0RatChunk001Sub000Block145Part001
    + surrogateDiagTailX0RatChunk001Sub000Block145Part002
    + surrogateDiagTailX0RatChunk001Sub000Block145Part003
    + surrogateDiagTailX0RatChunk001Sub000Block145Part004
    + surrogateDiagTailX0RatChunk001Sub000Block145Part005
    + surrogateDiagTailX0RatChunk001Sub000Block145Part006
    + surrogateDiagTailX0RatChunk001Sub000Block145Part007
    + surrogateDiagTailX0RatChunk001Sub000Block145Part008
    + surrogateDiagTailX0RatChunk001Sub000Block145Part009
    + surrogateDiagTailX0RatChunk001Sub000Block145Part010
    + surrogateDiagTailX0RatChunk001Sub000Block145Part011
    + surrogateDiagTailX0RatChunk001Sub000Block145Part012
    + surrogateDiagTailX0RatChunk001Sub000Block145Part013
    + surrogateDiagTailX0RatChunk001Sub000Block145Part014
    + surrogateDiagTailX0RatChunk001Sub000Block145Part015
    + surrogateDiagTailX0RatChunk001Sub000Block145Part016
    + surrogateDiagTailX0RatChunk001Sub000Block145Part017
    + surrogateDiagTailX0RatChunk001Sub000Block145Part018
    + surrogateDiagTailX0RatChunk001Sub000Block145Part019
    + surrogateDiagTailX0RatChunk001Sub000Block145Part020
    + surrogateDiagTailX0RatChunk001Sub000Block145Part021
    + surrogateDiagTailX0RatChunk001Sub000Block145Part022
    + surrogateDiagTailX0RatChunk001Sub000Block145Part023
    + surrogateDiagTailX0RatChunk001Sub000Block145Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block145_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block145Head + surrogateDiagTailX0RatChunk001Sub000Block145Mid + surrogateDiagTailX0RatChunk001Sub000Block145Tail =
      surrogateDiagTailX0RatChunk001Sub000Block145 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block145Head surrogateDiagTailX0RatChunk001Sub000Block145Mid surrogateDiagTailX0RatChunk001Sub000Block145Tail surrogateDiagTailX0RatChunk001Sub000Block145
  ring

def SurrogateDiagonalTailChunk001Sub000Block145HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block145HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block145Head

def SurrogateDiagonalTailChunk001Sub000Block145MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block145MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block145Mid

def SurrogateDiagonalTailChunk001Sub000Block145TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block145TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block145Tail

theorem surrogateDiagonalTailChunk001Sub000Block145_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block145HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block145MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block145TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block145Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block145 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block145HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block145MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block145TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block145Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block145_eq_head_add_mid_add_tail

/-- Block 146 covers tail-support indices [13650,13675) and q from 22505 to 22546. -/

def TailChunk001Sub000Block146Part000SupportExplicit : Finset ℕ :=
  ([22505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part000 : ℚ :=
  (157329774875 : ℚ) / 11744396148919394304

def SurrogateDiagonalTailChunk001Sub000Block146Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22505
    = surrogateDiagTailX0RatChunk001Sub000Block146Part000

theorem surrogateDiagonalTailChunk001Sub000Block146Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part000] using hcert

def TailChunk001Sub000Block146Part001SupportExplicit : Finset ℕ :=
  ([22507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part001 : ℚ :=
  (970458893 : ℚ) / 4789137833466685440

def SurrogateDiagonalTailChunk001Sub000Block146Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22507
    = surrogateDiagTailX0RatChunk001Sub000Block146Part001

theorem surrogateDiagonalTailChunk001Sub000Block146Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part001] using hcert

def TailChunk001Sub000Block146Part002SupportExplicit : Finset ℕ :=
  ([22510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part002 : ℚ :=
  (8452485163 : ℚ) / 218743740000000000

def SurrogateDiagonalTailChunk001Sub000Block146Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22510
    = surrogateDiagTailX0RatChunk001Sub000Block146Part002

theorem surrogateDiagonalTailChunk001Sub000Block146Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part002] using hcert

def TailChunk001Sub000Block146Part003SupportExplicit : Finset ℕ :=
  ([22511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block146Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22511
    = surrogateDiagTailX0RatChunk001Sub000Block146Part003

theorem surrogateDiagonalTailChunk001Sub000Block146Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part003] using hcert

def TailChunk001Sub000Block146Part004SupportExplicit : Finset ℕ :=
  ([22513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part004 : ℚ :=
  (28516041675 : ℚ) / 97413359619483969728

def SurrogateDiagonalTailChunk001Sub000Block146Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22513
    = surrogateDiagTailX0RatChunk001Sub000Block146Part004

theorem surrogateDiagonalTailChunk001Sub000Block146Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part004] using hcert

def TailChunk001Sub000Block146Part005SupportExplicit : Finset ℕ :=
  ([22514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block146Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22514
    = surrogateDiagTailX0RatChunk001Sub000Block146Part005

theorem surrogateDiagonalTailChunk001Sub000Block146Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part005] using hcert

def TailChunk001Sub000Block146Part006SupportExplicit : Finset ℕ :=
  ([22515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part006 : ℚ :=
  (1415225150525 : ℚ) / 19898724644657823744

def SurrogateDiagonalTailChunk001Sub000Block146Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22515
    = surrogateDiagTailX0RatChunk001Sub000Block146Part006

theorem surrogateDiagonalTailChunk001Sub000Block146Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part006] using hcert

def TailChunk001Sub000Block146Part007SupportExplicit : Finset ℕ :=
  ([22517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part007 : ℚ :=
  (2144079057 : ℚ) / 936735551329402880

def SurrogateDiagonalTailChunk001Sub000Block146Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22517
    = surrogateDiagTailX0RatChunk001Sub000Block146Part007

theorem surrogateDiagonalTailChunk001Sub000Block146Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part007] using hcert

def TailChunk001Sub000Block146Part008SupportExplicit : Finset ℕ :=
  ([22519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part008 : ℚ :=
  (648290910625 : ℚ) / 346653844260719689728

def SurrogateDiagonalTailChunk001Sub000Block146Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22519
    = surrogateDiagTailX0RatChunk001Sub000Block146Part008

theorem surrogateDiagonalTailChunk001Sub000Block146Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part008] using hcert

def TailChunk001Sub000Block146Part009SupportExplicit : Finset ℕ :=
  ([22521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part009 : ℚ :=
  (1760938624925 : ℚ) / 63496689928251845184

def SurrogateDiagonalTailChunk001Sub000Block146Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22521
    = surrogateDiagTailX0RatChunk001Sub000Block146Part009

theorem surrogateDiagonalTailChunk001Sub000Block146Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part009] using hcert

def TailChunk001Sub000Block146Part010SupportExplicit : Finset ℕ :=
  ([22522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block146Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22522
    = surrogateDiagTailX0RatChunk001Sub000Block146Part010

theorem surrogateDiagonalTailChunk001Sub000Block146Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part010] using hcert

def TailChunk001Sub000Block146Part011SupportExplicit : Finset ℕ :=
  ([22523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part011 : ℚ :=
  (990365269 : ℚ) / 6073496096328000000

def SurrogateDiagonalTailChunk001Sub000Block146Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22523
    = surrogateDiagTailX0RatChunk001Sub000Block146Part011

theorem surrogateDiagonalTailChunk001Sub000Block146Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part011] using hcert

def TailChunk001Sub000Block146Part012SupportExplicit : Finset ℕ :=
  ([22526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part012 : ℚ :=
  (9009124075 : ℚ) / 401219727153610752

def SurrogateDiagonalTailChunk001Sub000Block146Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22526
    = surrogateDiagTailX0RatChunk001Sub000Block146Part012

theorem surrogateDiagonalTailChunk001Sub000Block146Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part012] using hcert

def TailChunk001Sub000Block146Part013SupportExplicit : Finset ℕ :=
  ([22529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part013 : ℚ :=
  (282997583225 : ℚ) / 233299279808754499584

def SurrogateDiagonalTailChunk001Sub000Block146Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22529
    = surrogateDiagTailX0RatChunk001Sub000Block146Part013

theorem surrogateDiagonalTailChunk001Sub000Block146Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part013] using hcert

def TailChunk001Sub000Block146Part014SupportExplicit : Finset ℕ :=
  ([22530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part014 : ℚ :=
  (14562883577 : ℚ) / 43208640000000000

def SurrogateDiagonalTailChunk001Sub000Block146Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22530
    = surrogateDiagTailX0RatChunk001Sub000Block146Part014

theorem surrogateDiagonalTailChunk001Sub000Block146Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part014] using hcert

def TailChunk001Sub000Block146Part015SupportExplicit : Finset ℕ :=
  ([22531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block146Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22531
    = surrogateDiagTailX0RatChunk001Sub000Block146Part015

theorem surrogateDiagonalTailChunk001Sub000Block146Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part015] using hcert

def TailChunk001Sub000Block146Part016SupportExplicit : Finset ℕ :=
  ([22533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part016 : ℚ :=
  (1477381304975 : ℚ) / 26764798359622385664

def SurrogateDiagonalTailChunk001Sub000Block146Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22533
    = surrogateDiagTailX0RatChunk001Sub000Block146Part016

theorem surrogateDiagonalTailChunk001Sub000Block146Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part016] using hcert

def TailChunk001Sub000Block146Part017SupportExplicit : Finset ℕ :=
  ([22534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part017 : ℚ :=
  (60202900225 : ℚ) / 10746881284561698816

def SurrogateDiagonalTailChunk001Sub000Block146Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22534
    = surrogateDiagTailX0RatChunk001Sub000Block146Part017

theorem surrogateDiagonalTailChunk001Sub000Block146Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part017] using hcert

def TailChunk001Sub000Block146Part018SupportExplicit : Finset ℕ :=
  ([22535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part018 : ℚ :=
  (846248890675 : ℚ) / 87965083448506423296

def SurrogateDiagonalTailChunk001Sub000Block146Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22535
    = surrogateDiagTailX0RatChunk001Sub000Block146Part018

theorem surrogateDiagonalTailChunk001Sub000Block146Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part018] using hcert

def TailChunk001Sub000Block146Part019SupportExplicit : Finset ℕ :=
  ([22537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part019 : ℚ :=
  (266310667 : ℚ) / 625195511095399200

def SurrogateDiagonalTailChunk001Sub000Block146Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22537
    = surrogateDiagTailX0RatChunk001Sub000Block146Part019

theorem surrogateDiagonalTailChunk001Sub000Block146Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part019] using hcert

def TailChunk001Sub000Block146Part020SupportExplicit : Finset ℕ :=
  ([22538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part020 : ℚ :=
  (204119301 : ℚ) / 98338135375402880

def SurrogateDiagonalTailChunk001Sub000Block146Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22538
    = surrogateDiagTailX0RatChunk001Sub000Block146Part020

theorem surrogateDiagonalTailChunk001Sub000Block146Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part020] using hcert

def TailChunk001Sub000Block146Part021SupportExplicit : Finset ℕ :=
  ([22539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part021 : ℚ :=
  (130487614843 : ℚ) / 3462137655089203200

def SurrogateDiagonalTailChunk001Sub000Block146Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22539
    = surrogateDiagTailX0RatChunk001Sub000Block146Part021

theorem surrogateDiagonalTailChunk001Sub000Block146Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part021] using hcert

def TailChunk001Sub000Block146Part022SupportExplicit : Finset ℕ :=
  ([22541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block146Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22541
    = surrogateDiagTailX0RatChunk001Sub000Block146Part022

theorem surrogateDiagonalTailChunk001Sub000Block146Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part022] using hcert

def TailChunk001Sub000Block146Part023SupportExplicit : Finset ℕ :=
  ([22543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block146Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22543
    = surrogateDiagTailX0RatChunk001Sub000Block146Part023

theorem surrogateDiagonalTailChunk001Sub000Block146Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part023] using hcert

def TailChunk001Sub000Block146Part024SupportExplicit : Finset ℕ :=
  ([22546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block146Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block146Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22546
    = surrogateDiagTailX0RatChunk001Sub000Block146Part024

theorem surrogateDiagonalTailChunk001Sub000Block146Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block146Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block146Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block146Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block146Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block146Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block146Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block146HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block146Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block146Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block146Part000
    + surrogateDiagTailX0RatChunk001Sub000Block146Part001
    + surrogateDiagTailX0RatChunk001Sub000Block146Part002
    + surrogateDiagTailX0RatChunk001Sub000Block146Part003
    + surrogateDiagTailX0RatChunk001Sub000Block146Part004
    + surrogateDiagTailX0RatChunk001Sub000Block146Part005
    + surrogateDiagTailX0RatChunk001Sub000Block146Part006
    + surrogateDiagTailX0RatChunk001Sub000Block146Part007
    + surrogateDiagTailX0RatChunk001Sub000Block146Part008
    + surrogateDiagTailX0RatChunk001Sub000Block146Part009

def surrogateDiagonalTailChunk001Sub000Block146MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block146Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block146Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block146Part010
    + surrogateDiagTailX0RatChunk001Sub000Block146Part011
    + surrogateDiagTailX0RatChunk001Sub000Block146Part012
    + surrogateDiagTailX0RatChunk001Sub000Block146Part013
    + surrogateDiagTailX0RatChunk001Sub000Block146Part014
    + surrogateDiagTailX0RatChunk001Sub000Block146Part015
    + surrogateDiagTailX0RatChunk001Sub000Block146Part016
    + surrogateDiagTailX0RatChunk001Sub000Block146Part017
    + surrogateDiagTailX0RatChunk001Sub000Block146Part018
    + surrogateDiagTailX0RatChunk001Sub000Block146Part019

def surrogateDiagonalTailChunk001Sub000Block146TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block146Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block146Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block146Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block146Part020
    + surrogateDiagTailX0RatChunk001Sub000Block146Part021
    + surrogateDiagTailX0RatChunk001Sub000Block146Part022
    + surrogateDiagTailX0RatChunk001Sub000Block146Part023
    + surrogateDiagTailX0RatChunk001Sub000Block146Part024

def surrogateDiagonalTailChunk001Sub000Block146Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block146HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block146MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block146TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block146 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block146Part000
    + surrogateDiagTailX0RatChunk001Sub000Block146Part001
    + surrogateDiagTailX0RatChunk001Sub000Block146Part002
    + surrogateDiagTailX0RatChunk001Sub000Block146Part003
    + surrogateDiagTailX0RatChunk001Sub000Block146Part004
    + surrogateDiagTailX0RatChunk001Sub000Block146Part005
    + surrogateDiagTailX0RatChunk001Sub000Block146Part006
    + surrogateDiagTailX0RatChunk001Sub000Block146Part007
    + surrogateDiagTailX0RatChunk001Sub000Block146Part008
    + surrogateDiagTailX0RatChunk001Sub000Block146Part009
    + surrogateDiagTailX0RatChunk001Sub000Block146Part010
    + surrogateDiagTailX0RatChunk001Sub000Block146Part011
    + surrogateDiagTailX0RatChunk001Sub000Block146Part012
    + surrogateDiagTailX0RatChunk001Sub000Block146Part013
    + surrogateDiagTailX0RatChunk001Sub000Block146Part014
    + surrogateDiagTailX0RatChunk001Sub000Block146Part015
    + surrogateDiagTailX0RatChunk001Sub000Block146Part016
    + surrogateDiagTailX0RatChunk001Sub000Block146Part017
    + surrogateDiagTailX0RatChunk001Sub000Block146Part018
    + surrogateDiagTailX0RatChunk001Sub000Block146Part019
    + surrogateDiagTailX0RatChunk001Sub000Block146Part020
    + surrogateDiagTailX0RatChunk001Sub000Block146Part021
    + surrogateDiagTailX0RatChunk001Sub000Block146Part022
    + surrogateDiagTailX0RatChunk001Sub000Block146Part023
    + surrogateDiagTailX0RatChunk001Sub000Block146Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block146_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block146Head + surrogateDiagTailX0RatChunk001Sub000Block146Mid + surrogateDiagTailX0RatChunk001Sub000Block146Tail =
      surrogateDiagTailX0RatChunk001Sub000Block146 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block146Head surrogateDiagTailX0RatChunk001Sub000Block146Mid surrogateDiagTailX0RatChunk001Sub000Block146Tail surrogateDiagTailX0RatChunk001Sub000Block146
  ring

def SurrogateDiagonalTailChunk001Sub000Block146HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block146HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block146Head

def SurrogateDiagonalTailChunk001Sub000Block146MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block146MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block146Mid

def SurrogateDiagonalTailChunk001Sub000Block146TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block146TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block146Tail

theorem surrogateDiagonalTailChunk001Sub000Block146_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block146HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block146MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block146TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block146Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block146 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block146HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block146MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block146TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block146Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block146_eq_head_add_mid_add_tail

/-- Block 147 covers tail-support indices [13675,13700) and q from 22547 to 22586. -/

def TailChunk001Sub000Block147Part000SupportExplicit : Finset ℕ :=
  ([22547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part000 : ℚ :=
  (25995996433 : ℚ) / 13935268421761075200

def SurrogateDiagonalTailChunk001Sub000Block147Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22547
    = surrogateDiagTailX0RatChunk001Sub000Block147Part000

theorem surrogateDiagonalTailChunk001Sub000Block147Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part000] using hcert

def TailChunk001Sub000Block147Part001SupportExplicit : Finset ℕ :=
  ([22549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block147Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22549
    = surrogateDiagTailX0RatChunk001Sub000Block147Part001

theorem surrogateDiagonalTailChunk001Sub000Block147Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part001] using hcert

def TailChunk001Sub000Block147Part002SupportExplicit : Finset ℕ :=
  ([22551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part002 : ℚ :=
  (220704124975 : ℚ) / 7979468131875312768

def SurrogateDiagonalTailChunk001Sub000Block147Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22551
    = surrogateDiagTailX0RatChunk001Sub000Block147Part002

theorem surrogateDiagonalTailChunk001Sub000Block147Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part002] using hcert

def TailChunk001Sub000Block147Part003SupportExplicit : Finset ℕ :=
  ([22553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part003 : ℚ :=
  (357060759925 : ℚ) / 519344618059748193408

def SurrogateDiagonalTailChunk001Sub000Block147Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22553
    = surrogateDiagTailX0RatChunk001Sub000Block147Part003

theorem surrogateDiagonalTailChunk001Sub000Block147Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part003] using hcert

def TailChunk001Sub000Block147Part004SupportExplicit : Finset ℕ :=
  ([22555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part004 : ℚ :=
  (766975839575 : ℚ) / 95118766100531380224

def SurrogateDiagonalTailChunk001Sub000Block147Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22555
    = surrogateDiagTailX0RatChunk001Sub000Block147Part004

theorem surrogateDiagonalTailChunk001Sub000Block147Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part004] using hcert

def TailChunk001Sub000Block147Part005SupportExplicit : Finset ℕ :=
  ([22557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part005 : ℚ :=
  (869097080725 : ℚ) / 29094943822808481792

def SurrogateDiagonalTailChunk001Sub000Block147Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22557
    = surrogateDiagTailX0RatChunk001Sub000Block147Part005

theorem surrogateDiagonalTailChunk001Sub000Block147Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part005] using hcert

def TailChunk001Sub000Block147Part006SupportExplicit : Finset ℕ :=
  ([22558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block147Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22558
    = surrogateDiagTailX0RatChunk001Sub000Block147Part006

theorem surrogateDiagonalTailChunk001Sub000Block147Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part006] using hcert

def TailChunk001Sub000Block147Part007SupportExplicit : Finset ℕ :=
  ([22559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part007 : ℚ :=
  (444304063075 : ℚ) / 506618314600355463168

def SurrogateDiagonalTailChunk001Sub000Block147Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22559
    = surrogateDiagTailX0RatChunk001Sub000Block147Part007

theorem surrogateDiagonalTailChunk001Sub000Block147Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part007] using hcert

def TailChunk001Sub000Block147Part008SupportExplicit : Finset ℕ :=
  ([22561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part008 : ℚ :=
  (177253187 : ℚ) / 34902737692508160

def SurrogateDiagonalTailChunk001Sub000Block147Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22561
    = surrogateDiagTailX0RatChunk001Sub000Block147Part008

theorem surrogateDiagonalTailChunk001Sub000Block147Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part008] using hcert

def TailChunk001Sub000Block147Part009SupportExplicit : Finset ℕ :=
  ([22562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part009 : ℚ :=
  (16344273125 : ℚ) / 4354074940246757376

def SurrogateDiagonalTailChunk001Sub000Block147Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22562
    = surrogateDiagTailX0RatChunk001Sub000Block147Part009

theorem surrogateDiagonalTailChunk001Sub000Block147Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part009] using hcert

def TailChunk001Sub000Block147Part010SupportExplicit : Finset ℕ :=
  ([22565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part010 : ℚ :=
  (1273634623375 : ℚ) / 265303627475303006208

def SurrogateDiagonalTailChunk001Sub000Block147Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22565
    = surrogateDiagTailX0RatChunk001Sub000Block147Part010

theorem surrogateDiagonalTailChunk001Sub000Block147Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part010] using hcert

def TailChunk001Sub000Block147Part011SupportExplicit : Finset ℕ :=
  ([22566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part011 : ℚ :=
  (35349426179 : ℚ) / 159929366485401600

def SurrogateDiagonalTailChunk001Sub000Block147Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22566
    = surrogateDiagTailX0RatChunk001Sub000Block147Part011

theorem surrogateDiagonalTailChunk001Sub000Block147Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part011] using hcert

def TailChunk001Sub000Block147Part012SupportExplicit : Finset ℕ :=
  ([22567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block147Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22567
    = surrogateDiagTailX0RatChunk001Sub000Block147Part012

theorem surrogateDiagonalTailChunk001Sub000Block147Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part012] using hcert

def TailChunk001Sub000Block147Part013SupportExplicit : Finset ℕ :=
  ([22569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part013 : ℚ :=
  (1768452624725 : ℚ) / 64039828798163817024

def SurrogateDiagonalTailChunk001Sub000Block147Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22569
    = surrogateDiagTailX0RatChunk001Sub000Block147Part013

theorem surrogateDiagonalTailChunk001Sub000Block147Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part013] using hcert

def TailChunk001Sub000Block147Part014SupportExplicit : Finset ℕ :=
  ([22570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part014 : ℚ :=
  (2799498253 : ℚ) / 55736772927160320

def SurrogateDiagonalTailChunk001Sub000Block147Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22570
    = surrogateDiagTailX0RatChunk001Sub000Block147Part014

theorem surrogateDiagonalTailChunk001Sub000Block147Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part014] using hcert

def TailChunk001Sub000Block147Part015SupportExplicit : Finset ℕ :=
  ([22571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block147Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22571
    = surrogateDiagTailX0RatChunk001Sub000Block147Part015

theorem surrogateDiagonalTailChunk001Sub000Block147Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part015] using hcert

def TailChunk001Sub000Block147Part016SupportExplicit : Finset ℕ :=
  ([22573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block147Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22573
    = surrogateDiagTailX0RatChunk001Sub000Block147Part016

theorem surrogateDiagonalTailChunk001Sub000Block147Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part016] using hcert

def TailChunk001Sub000Block147Part017SupportExplicit : Finset ℕ :=
  ([22574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block147Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22574
    = surrogateDiagTailX0RatChunk001Sub000Block147Part017

theorem surrogateDiagonalTailChunk001Sub000Block147Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part017] using hcert

def TailChunk001Sub000Block147Part018SupportExplicit : Finset ℕ :=
  ([22577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part018 : ℚ :=
  (3966386479 : ℚ) / 24557688721409155200

def SurrogateDiagonalTailChunk001Sub000Block147Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22577
    = surrogateDiagTailX0RatChunk001Sub000Block147Part018

theorem surrogateDiagonalTailChunk001Sub000Block147Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part018] using hcert

def TailChunk001Sub000Block147Part019SupportExplicit : Finset ℕ :=
  ([22578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part019 : ℚ :=
  (69213735583 : ℚ) / 280939216864051200

def SurrogateDiagonalTailChunk001Sub000Block147Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22578
    = surrogateDiagTailX0RatChunk001Sub000Block147Part019

theorem surrogateDiagonalTailChunk001Sub000Block147Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part019] using hcert

def TailChunk001Sub000Block147Part020SupportExplicit : Finset ℕ :=
  ([22579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part020 : ℚ :=
  (425146625 : ℚ) / 2036119491121250304

def SurrogateDiagonalTailChunk001Sub000Block147Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22579
    = surrogateDiagTailX0RatChunk001Sub000Block147Part020

theorem surrogateDiagonalTailChunk001Sub000Block147Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part020] using hcert

def TailChunk001Sub000Block147Part021SupportExplicit : Finset ℕ :=
  ([22582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part021 : ℚ :=
  (651120619525 : ℚ) / 21882251755828758528

def SurrogateDiagonalTailChunk001Sub000Block147Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22582
    = surrogateDiagTailX0RatChunk001Sub000Block147Part021

theorem surrogateDiagonalTailChunk001Sub000Block147Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part021] using hcert

def TailChunk001Sub000Block147Part022SupportExplicit : Finset ℕ :=
  ([22583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part022 : ℚ :=
  (1764534973 : ℚ) / 1477797848437593600

def SurrogateDiagonalTailChunk001Sub000Block147Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22583
    = surrogateDiagTailX0RatChunk001Sub000Block147Part022

theorem surrogateDiagonalTailChunk001Sub000Block147Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part022] using hcert

def TailChunk001Sub000Block147Part023SupportExplicit : Finset ℕ :=
  ([22585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part023 : ℚ :=
  (425297207625 : ℚ) / 88748557424873537536

def SurrogateDiagonalTailChunk001Sub000Block147Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22585
    = surrogateDiagTailX0RatChunk001Sub000Block147Part023

theorem surrogateDiagonalTailChunk001Sub000Block147Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part023] using hcert

def TailChunk001Sub000Block147Part024SupportExplicit : Finset ℕ :=
  ([22586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block147Part024 : ℚ :=
  (895179343 : ℚ) / 192958472985801600

def SurrogateDiagonalTailChunk001Sub000Block147Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22586
    = surrogateDiagTailX0RatChunk001Sub000Block147Part024

theorem surrogateDiagonalTailChunk001Sub000Block147Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block147Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block147Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block147Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block147Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block147Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block147Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block147HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block147Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block147Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block147Part000
    + surrogateDiagTailX0RatChunk001Sub000Block147Part001
    + surrogateDiagTailX0RatChunk001Sub000Block147Part002
    + surrogateDiagTailX0RatChunk001Sub000Block147Part003
    + surrogateDiagTailX0RatChunk001Sub000Block147Part004
    + surrogateDiagTailX0RatChunk001Sub000Block147Part005
    + surrogateDiagTailX0RatChunk001Sub000Block147Part006
    + surrogateDiagTailX0RatChunk001Sub000Block147Part007
    + surrogateDiagTailX0RatChunk001Sub000Block147Part008
    + surrogateDiagTailX0RatChunk001Sub000Block147Part009

def surrogateDiagonalTailChunk001Sub000Block147MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block147Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block147Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block147Part010
    + surrogateDiagTailX0RatChunk001Sub000Block147Part011
    + surrogateDiagTailX0RatChunk001Sub000Block147Part012
    + surrogateDiagTailX0RatChunk001Sub000Block147Part013
    + surrogateDiagTailX0RatChunk001Sub000Block147Part014
    + surrogateDiagTailX0RatChunk001Sub000Block147Part015
    + surrogateDiagTailX0RatChunk001Sub000Block147Part016
    + surrogateDiagTailX0RatChunk001Sub000Block147Part017
    + surrogateDiagTailX0RatChunk001Sub000Block147Part018
    + surrogateDiagTailX0RatChunk001Sub000Block147Part019

def surrogateDiagonalTailChunk001Sub000Block147TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block147Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block147Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block147Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block147Part020
    + surrogateDiagTailX0RatChunk001Sub000Block147Part021
    + surrogateDiagTailX0RatChunk001Sub000Block147Part022
    + surrogateDiagTailX0RatChunk001Sub000Block147Part023
    + surrogateDiagTailX0RatChunk001Sub000Block147Part024

def surrogateDiagonalTailChunk001Sub000Block147Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block147HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block147MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block147TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block147 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block147Part000
    + surrogateDiagTailX0RatChunk001Sub000Block147Part001
    + surrogateDiagTailX0RatChunk001Sub000Block147Part002
    + surrogateDiagTailX0RatChunk001Sub000Block147Part003
    + surrogateDiagTailX0RatChunk001Sub000Block147Part004
    + surrogateDiagTailX0RatChunk001Sub000Block147Part005
    + surrogateDiagTailX0RatChunk001Sub000Block147Part006
    + surrogateDiagTailX0RatChunk001Sub000Block147Part007
    + surrogateDiagTailX0RatChunk001Sub000Block147Part008
    + surrogateDiagTailX0RatChunk001Sub000Block147Part009
    + surrogateDiagTailX0RatChunk001Sub000Block147Part010
    + surrogateDiagTailX0RatChunk001Sub000Block147Part011
    + surrogateDiagTailX0RatChunk001Sub000Block147Part012
    + surrogateDiagTailX0RatChunk001Sub000Block147Part013
    + surrogateDiagTailX0RatChunk001Sub000Block147Part014
    + surrogateDiagTailX0RatChunk001Sub000Block147Part015
    + surrogateDiagTailX0RatChunk001Sub000Block147Part016
    + surrogateDiagTailX0RatChunk001Sub000Block147Part017
    + surrogateDiagTailX0RatChunk001Sub000Block147Part018
    + surrogateDiagTailX0RatChunk001Sub000Block147Part019
    + surrogateDiagTailX0RatChunk001Sub000Block147Part020
    + surrogateDiagTailX0RatChunk001Sub000Block147Part021
    + surrogateDiagTailX0RatChunk001Sub000Block147Part022
    + surrogateDiagTailX0RatChunk001Sub000Block147Part023
    + surrogateDiagTailX0RatChunk001Sub000Block147Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block147_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block147Head + surrogateDiagTailX0RatChunk001Sub000Block147Mid + surrogateDiagTailX0RatChunk001Sub000Block147Tail =
      surrogateDiagTailX0RatChunk001Sub000Block147 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block147Head surrogateDiagTailX0RatChunk001Sub000Block147Mid surrogateDiagTailX0RatChunk001Sub000Block147Tail surrogateDiagTailX0RatChunk001Sub000Block147
  ring

def SurrogateDiagonalTailChunk001Sub000Block147HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block147HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block147Head

def SurrogateDiagonalTailChunk001Sub000Block147MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block147MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block147Mid

def SurrogateDiagonalTailChunk001Sub000Block147TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block147TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block147Tail

theorem surrogateDiagonalTailChunk001Sub000Block147_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block147HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block147MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block147TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block147Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block147 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block147HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block147MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block147TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block147Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block147_eq_head_add_mid_add_tail

/-- Block 148 covers tail-support indices [13700,13725) and q from 22587 to 22629. -/

def TailChunk001Sub000Block148Part000SupportExplicit : Finset ℕ :=
  ([22587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part000 : ℚ :=
  (885637249825 : ℚ) / 32122200747264909312

def SurrogateDiagonalTailChunk001Sub000Block148Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22587
    = surrogateDiagTailX0RatChunk001Sub000Block148Part000

theorem surrogateDiagonalTailChunk001Sub000Block148Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part000] using hcert

def TailChunk001Sub000Block148Part001SupportExplicit : Finset ℕ :=
  ([22591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part001 : ℚ :=
  (7072615771 : ℚ) / 4130370117225676800

def SurrogateDiagonalTailChunk001Sub000Block148Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22591
    = surrogateDiagTailX0RatChunk001Sub000Block148Part001

theorem surrogateDiagonalTailChunk001Sub000Block148Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part001] using hcert

def TailChunk001Sub000Block148Part002SupportExplicit : Finset ℕ :=
  ([22593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part002 : ℚ :=
  (1122639848925 : ℚ) / 33357584500434927616

def SurrogateDiagonalTailChunk001Sub000Block148Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22593
    = surrogateDiagTailX0RatChunk001Sub000Block148Part002

theorem surrogateDiagonalTailChunk001Sub000Block148Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part002] using hcert

def TailChunk001Sub000Block148Part003SupportExplicit : Finset ℕ :=
  ([22594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part003 : ℚ :=
  (5589061381 : ℚ) / 191924427514060800

def SurrogateDiagonalTailChunk001Sub000Block148Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22594
    = surrogateDiagTailX0RatChunk001Sub000Block148Part003

theorem surrogateDiagonalTailChunk001Sub000Block148Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part003] using hcert

def TailChunk001Sub000Block148Part004SupportExplicit : Finset ℕ :=
  ([22595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part004 : ℚ :=
  (1277020872625 : ℚ) / 266717634352123004928

def SurrogateDiagonalTailChunk001Sub000Block148Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22595
    = surrogateDiagTailX0RatChunk001Sub000Block148Part004

theorem surrogateDiagonalTailChunk001Sub000Block148Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part004] using hcert

def TailChunk001Sub000Block148Part005SupportExplicit : Finset ℕ :=
  ([22597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part005 : ℚ :=
  (136456660075 : ℚ) / 602548881731332664448

def SurrogateDiagonalTailChunk001Sub000Block148Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22597
    = surrogateDiagTailX0RatChunk001Sub000Block148Part005

theorem surrogateDiagonalTailChunk001Sub000Block148Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part005] using hcert

def TailChunk001Sub000Block148Part006SupportExplicit : Finset ℕ :=
  ([22598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block148Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22598
    = surrogateDiagTailX0RatChunk001Sub000Block148Part006

theorem surrogateDiagonalTailChunk001Sub000Block148Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part006] using hcert

def TailChunk001Sub000Block148Part007SupportExplicit : Finset ℕ :=
  ([22601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part007 : ℚ :=
  (34651603025 : ℚ) / 205089051183861989376

def SurrogateDiagonalTailChunk001Sub000Block148Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22601
    = surrogateDiagTailX0RatChunk001Sub000Block148Part007

theorem surrogateDiagonalTailChunk001Sub000Block148Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part007] using hcert

def TailChunk001Sub000Block148Part008SupportExplicit : Finset ℕ :=
  ([22602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part008 : ℚ :=
  (886557339725 : ℚ) / 4023815957381742144

def SurrogateDiagonalTailChunk001Sub000Block148Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22602
    = surrogateDiagTailX0RatChunk001Sub000Block148Part008

theorem surrogateDiagonalTailChunk001Sub000Block148Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part008] using hcert

def TailChunk001Sub000Block148Part009SupportExplicit : Finset ℕ :=
  ([22603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part009 : ℚ :=
  (652056174575 : ℚ) / 175928406473180242944

def SurrogateDiagonalTailChunk001Sub000Block148Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22603
    = surrogateDiagTailX0RatChunk001Sub000Block148Part009

theorem surrogateDiagonalTailChunk001Sub000Block148Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part009] using hcert

def TailChunk001Sub000Block148Part010SupportExplicit : Finset ℕ :=
  ([22605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part010 : ℚ :=
  (4591986241 : ℚ) / 56061204300300288

def SurrogateDiagonalTailChunk001Sub000Block148Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22605
    = surrogateDiagTailX0RatChunk001Sub000Block148Part010

theorem surrogateDiagonalTailChunk001Sub000Block148Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part010] using hcert

def TailChunk001Sub000Block148Part011SupportExplicit : Finset ℕ :=
  ([22606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part011 : ℚ :=
  (3682777675 : ℚ) / 2099748225218789376

def SurrogateDiagonalTailChunk001Sub000Block148Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22606
    = surrogateDiagTailX0RatChunk001Sub000Block148Part011

theorem surrogateDiagonalTailChunk001Sub000Block148Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part011] using hcert

def TailChunk001Sub000Block148Part012SupportExplicit : Finset ℕ :=
  ([22607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part012 : ℚ :=
  (404530518125 : ℚ) / 194967928408868388864

def SurrogateDiagonalTailChunk001Sub000Block148Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22607
    = surrogateDiagTailX0RatChunk001Sub000Block148Part012

theorem surrogateDiagonalTailChunk001Sub000Block148Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part012] using hcert

def TailChunk001Sub000Block148Part013SupportExplicit : Finset ℕ :=
  ([22609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part013 : ℚ :=
  (102658364175 : ℚ) / 181569241196330094976

def SurrogateDiagonalTailChunk001Sub000Block148Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22609
    = surrogateDiagTailX0RatChunk001Sub000Block148Part013

theorem surrogateDiagonalTailChunk001Sub000Block148Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part013] using hcert

def TailChunk001Sub000Block148Part014SupportExplicit : Finset ℕ :=
  ([22610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part014 : ℚ :=
  (461476622225 : ℚ) / 2853722773870608384

def SurrogateDiagonalTailChunk001Sub000Block148Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22610
    = surrogateDiagTailX0RatChunk001Sub000Block148Part014

theorem surrogateDiagonalTailChunk001Sub000Block148Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part014] using hcert

def TailChunk001Sub000Block148Part015SupportExplicit : Finset ℕ :=
  ([22611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part015 : ℚ :=
  (887520249775 : ℚ) / 32258963516198879232

def SurrogateDiagonalTailChunk001Sub000Block148Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22611
    = surrogateDiagTailX0RatChunk001Sub000Block148Part015

theorem surrogateDiagonalTailChunk001Sub000Block148Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part015] using hcert

def TailChunk001Sub000Block148Part016SupportExplicit : Finset ℕ :=
  ([22613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block148Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22613
    = surrogateDiagTailX0RatChunk001Sub000Block148Part016

theorem surrogateDiagonalTailChunk001Sub000Block148Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part016] using hcert

def TailChunk001Sub000Block148Part017SupportExplicit : Finset ℕ :=
  ([22614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part017 : ℚ :=
  (221997273325 : ℚ) / 2016185219762429952

def SurrogateDiagonalTailChunk001Sub000Block148Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22614
    = surrogateDiagTailX0RatChunk001Sub000Block148Part017

theorem surrogateDiagonalTailChunk001Sub000Block148Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part017] using hcert

def TailChunk001Sub000Block148Part018SupportExplicit : Finset ℕ :=
  ([22615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part018 : ℚ :=
  (426426957375 : ℚ) / 89221146879538272256

def SurrogateDiagonalTailChunk001Sub000Block148Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22615
    = surrogateDiagTailX0RatChunk001Sub000Block148Part018

theorem surrogateDiagonalTailChunk001Sub000Block148Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part018] using hcert

def TailChunk001Sub000Block148Part019SupportExplicit : Finset ℕ :=
  ([22618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part019 : ℚ :=
  (5901320125 : ℚ) / 2291443762553128008

def SurrogateDiagonalTailChunk001Sub000Block148Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22618
    = surrogateDiagTailX0RatChunk001Sub000Block148Part019

theorem surrogateDiagonalTailChunk001Sub000Block148Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part019] using hcert

def TailChunk001Sub000Block148Part020SupportExplicit : Finset ℕ :=
  ([22619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block148Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22619
    = surrogateDiagTailX0RatChunk001Sub000Block148Part020

theorem surrogateDiagonalTailChunk001Sub000Block148Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part020] using hcert

def TailChunk001Sub000Block148Part021SupportExplicit : Finset ℕ :=
  ([22621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block148Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22621
    = surrogateDiagTailX0RatChunk001Sub000Block148Part021

theorem surrogateDiagonalTailChunk001Sub000Block148Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part021] using hcert

def TailChunk001Sub000Block148Part022SupportExplicit : Finset ℕ :=
  ([22622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block148Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22622
    = surrogateDiagTailX0RatChunk001Sub000Block148Part022

theorem surrogateDiagonalTailChunk001Sub000Block148Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part022] using hcert

def TailChunk001Sub000Block148Part023SupportExplicit : Finset ℕ :=
  ([22623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part023 : ℚ :=
  (5001 : ℚ) / 1034273415219200

def SurrogateDiagonalTailChunk001Sub000Block148Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22623
    = surrogateDiagTailX0RatChunk001Sub000Block148Part023

theorem surrogateDiagonalTailChunk001Sub000Block148Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part023] using hcert

def TailChunk001Sub000Block148Part024SupportExplicit : Finset ℕ :=
  ([22629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block148Part024 : ℚ :=
  (10582928275 : ℚ) / 3825197308249473024

def SurrogateDiagonalTailChunk001Sub000Block148Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22629
    = surrogateDiagTailX0RatChunk001Sub000Block148Part024

theorem surrogateDiagonalTailChunk001Sub000Block148Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block148Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block148Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block148Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block148Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block148Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block148Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block148HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block148Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block148Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block148Part000
    + surrogateDiagTailX0RatChunk001Sub000Block148Part001
    + surrogateDiagTailX0RatChunk001Sub000Block148Part002
    + surrogateDiagTailX0RatChunk001Sub000Block148Part003
    + surrogateDiagTailX0RatChunk001Sub000Block148Part004
    + surrogateDiagTailX0RatChunk001Sub000Block148Part005
    + surrogateDiagTailX0RatChunk001Sub000Block148Part006
    + surrogateDiagTailX0RatChunk001Sub000Block148Part007
    + surrogateDiagTailX0RatChunk001Sub000Block148Part008
    + surrogateDiagTailX0RatChunk001Sub000Block148Part009

def surrogateDiagonalTailChunk001Sub000Block148MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block148Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block148Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block148Part010
    + surrogateDiagTailX0RatChunk001Sub000Block148Part011
    + surrogateDiagTailX0RatChunk001Sub000Block148Part012
    + surrogateDiagTailX0RatChunk001Sub000Block148Part013
    + surrogateDiagTailX0RatChunk001Sub000Block148Part014
    + surrogateDiagTailX0RatChunk001Sub000Block148Part015
    + surrogateDiagTailX0RatChunk001Sub000Block148Part016
    + surrogateDiagTailX0RatChunk001Sub000Block148Part017
    + surrogateDiagTailX0RatChunk001Sub000Block148Part018
    + surrogateDiagTailX0RatChunk001Sub000Block148Part019

def surrogateDiagonalTailChunk001Sub000Block148TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block148Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block148Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block148Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block148Part020
    + surrogateDiagTailX0RatChunk001Sub000Block148Part021
    + surrogateDiagTailX0RatChunk001Sub000Block148Part022
    + surrogateDiagTailX0RatChunk001Sub000Block148Part023
    + surrogateDiagTailX0RatChunk001Sub000Block148Part024

def surrogateDiagonalTailChunk001Sub000Block148Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block148HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block148MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block148TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block148 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block148Part000
    + surrogateDiagTailX0RatChunk001Sub000Block148Part001
    + surrogateDiagTailX0RatChunk001Sub000Block148Part002
    + surrogateDiagTailX0RatChunk001Sub000Block148Part003
    + surrogateDiagTailX0RatChunk001Sub000Block148Part004
    + surrogateDiagTailX0RatChunk001Sub000Block148Part005
    + surrogateDiagTailX0RatChunk001Sub000Block148Part006
    + surrogateDiagTailX0RatChunk001Sub000Block148Part007
    + surrogateDiagTailX0RatChunk001Sub000Block148Part008
    + surrogateDiagTailX0RatChunk001Sub000Block148Part009
    + surrogateDiagTailX0RatChunk001Sub000Block148Part010
    + surrogateDiagTailX0RatChunk001Sub000Block148Part011
    + surrogateDiagTailX0RatChunk001Sub000Block148Part012
    + surrogateDiagTailX0RatChunk001Sub000Block148Part013
    + surrogateDiagTailX0RatChunk001Sub000Block148Part014
    + surrogateDiagTailX0RatChunk001Sub000Block148Part015
    + surrogateDiagTailX0RatChunk001Sub000Block148Part016
    + surrogateDiagTailX0RatChunk001Sub000Block148Part017
    + surrogateDiagTailX0RatChunk001Sub000Block148Part018
    + surrogateDiagTailX0RatChunk001Sub000Block148Part019
    + surrogateDiagTailX0RatChunk001Sub000Block148Part020
    + surrogateDiagTailX0RatChunk001Sub000Block148Part021
    + surrogateDiagTailX0RatChunk001Sub000Block148Part022
    + surrogateDiagTailX0RatChunk001Sub000Block148Part023
    + surrogateDiagTailX0RatChunk001Sub000Block148Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block148_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block148Head + surrogateDiagTailX0RatChunk001Sub000Block148Mid + surrogateDiagTailX0RatChunk001Sub000Block148Tail =
      surrogateDiagTailX0RatChunk001Sub000Block148 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block148Head surrogateDiagTailX0RatChunk001Sub000Block148Mid surrogateDiagTailX0RatChunk001Sub000Block148Tail surrogateDiagTailX0RatChunk001Sub000Block148
  ring

def SurrogateDiagonalTailChunk001Sub000Block148HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block148HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block148Head

def SurrogateDiagonalTailChunk001Sub000Block148MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block148MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block148Mid

def SurrogateDiagonalTailChunk001Sub000Block148TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block148TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block148Tail

theorem surrogateDiagonalTailChunk001Sub000Block148_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block148HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block148MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block148TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block148Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block148 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block148HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block148MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block148TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block148Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block148_eq_head_add_mid_add_tail

/-- Block 149 covers tail-support indices [13725,13750) and q from 22630 to 22670. -/

def TailChunk001Sub000Block149Part000SupportExplicit : Finset ℕ :=
  ([22630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part000 : ℚ :=
  (2002804529 : ℚ) / 27868386463580160

def SurrogateDiagonalTailChunk001Sub000Block149Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22630
    = surrogateDiagTailX0RatChunk001Sub000Block149Part000

theorem surrogateDiagonalTailChunk001Sub000Block149Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part000] using hcert

def TailChunk001Sub000Block149Part001SupportExplicit : Finset ℕ :=
  ([22631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part001 : ℚ :=
  (1466000021 : ℚ) / 314952906689740800

def SurrogateDiagonalTailChunk001Sub000Block149Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22631
    = surrogateDiagTailX0RatChunk001Sub000Block149Part001

theorem surrogateDiagonalTailChunk001Sub000Block149Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part001] using hcert

def TailChunk001Sub000Block149Part002SupportExplicit : Finset ℕ :=
  ([22633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part002 : ℚ :=
  (11424021581 : ℚ) / 9505584609542553600

def SurrogateDiagonalTailChunk001Sub000Block149Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22633
    = surrogateDiagTailX0RatChunk001Sub000Block149Part002

theorem surrogateDiagonalTailChunk001Sub000Block149Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part002] using hcert

def TailChunk001Sub000Block149Part003SupportExplicit : Finset ℕ :=
  ([22634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block149Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22634
    = surrogateDiagTailX0RatChunk001Sub000Block149Part003

theorem surrogateDiagonalTailChunk001Sub000Block149Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part003] using hcert

def TailChunk001Sub000Block149Part004SupportExplicit : Finset ℕ :=
  ([22637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block149Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22637
    = surrogateDiagTailX0RatChunk001Sub000Block149Part004

theorem surrogateDiagonalTailChunk001Sub000Block149Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part004] using hcert

def TailChunk001Sub000Block149Part005SupportExplicit : Finset ℕ :=
  ([22639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block149Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22639
    = surrogateDiagTailX0RatChunk001Sub000Block149Part005

theorem surrogateDiagonalTailChunk001Sub000Block149Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part005] using hcert

def TailChunk001Sub000Block149Part006SupportExplicit : Finset ℕ :=
  ([22641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part006 : ℚ :=
  (125025 : ℚ) / 25939236596459648

def SurrogateDiagonalTailChunk001Sub000Block149Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22641
    = surrogateDiagTailX0RatChunk001Sub000Block149Part006

theorem surrogateDiagonalTailChunk001Sub000Block149Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part006] using hcert

def TailChunk001Sub000Block149Part007SupportExplicit : Finset ℕ :=
  ([22642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block149Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22642
    = surrogateDiagTailX0RatChunk001Sub000Block149Part007

theorem surrogateDiagonalTailChunk001Sub000Block149Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part007] using hcert

def TailChunk001Sub000Block149Part008SupportExplicit : Finset ℕ :=
  ([22643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block149Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22643
    = surrogateDiagTailX0RatChunk001Sub000Block149Part008

theorem surrogateDiagonalTailChunk001Sub000Block149Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part008] using hcert

def TailChunk001Sub000Block149Part009SupportExplicit : Finset ℕ :=
  ([22645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part009 : ℚ :=
  (17698729375 : ℚ) / 1337759803275042816

def SurrogateDiagonalTailChunk001Sub000Block149Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22645
    = surrogateDiagTailX0RatChunk001Sub000Block149Part009

theorem surrogateDiagonalTailChunk001Sub000Block149Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part009] using hcert

def TailChunk001Sub000Block149Part010SupportExplicit : Finset ℕ :=
  ([22647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part010 : ℚ :=
  (41675 : ℚ) / 8655582461515776

def SurrogateDiagonalTailChunk001Sub000Block149Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22647
    = surrogateDiagTailX0RatChunk001Sub000Block149Part010

theorem surrogateDiagonalTailChunk001Sub000Block149Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part010] using hcert

def TailChunk001Sub000Block149Part011SupportExplicit : Finset ℕ :=
  ([22649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part011 : ℚ :=
  (2528391583 : ℚ) / 922552633632000000

def SurrogateDiagonalTailChunk001Sub000Block149Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22649
    = surrogateDiagTailX0RatChunk001Sub000Block149Part011

theorem surrogateDiagonalTailChunk001Sub000Block149Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part011] using hcert

def TailChunk001Sub000Block149Part012SupportExplicit : Finset ℕ :=
  ([22651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block149Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22651
    = surrogateDiagTailX0RatChunk001Sub000Block149Part012

theorem surrogateDiagonalTailChunk001Sub000Block149Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part012] using hcert

def TailChunk001Sub000Block149Part013SupportExplicit : Finset ℕ :=
  ([22654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part013 : ℚ :=
  (3584933503 : ℚ) / 1485809544344371200

def SurrogateDiagonalTailChunk001Sub000Block149Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22654
    = surrogateDiagTailX0RatChunk001Sub000Block149Part013

theorem surrogateDiagonalTailChunk001Sub000Block149Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part013] using hcert

def TailChunk001Sub000Block149Part014SupportExplicit : Finset ℕ :=
  ([22655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part014 : ℚ :=
  (5407172175 : ℚ) / 838258384461955072

def SurrogateDiagonalTailChunk001Sub000Block149Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22655
    = surrogateDiagTailX0RatChunk001Sub000Block149Part014

theorem surrogateDiagonalTailChunk001Sub000Block149Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part014] using hcert

def TailChunk001Sub000Block149Part015SupportExplicit : Finset ℕ :=
  ([22657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part015 : ℚ :=
  (4074103775 : ℚ) / 27156601950802171776

def SurrogateDiagonalTailChunk001Sub000Block149Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22657
    = surrogateDiagTailX0RatChunk001Sub000Block149Part015

theorem surrogateDiagonalTailChunk001Sub000Block149Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part015] using hcert

def TailChunk001Sub000Block149Part016SupportExplicit : Finset ℕ :=
  ([22658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block149Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22658
    = surrogateDiagTailX0RatChunk001Sub000Block149Part016

theorem surrogateDiagonalTailChunk001Sub000Block149Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part016] using hcert

def TailChunk001Sub000Block149Part017SupportExplicit : Finset ℕ :=
  ([22659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part017 : ℚ :=
  (1021005575275 : ℚ) / 48610740494884405248

def SurrogateDiagonalTailChunk001Sub000Block149Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22659
    = surrogateDiagTailX0RatChunk001Sub000Block149Part017

theorem surrogateDiagonalTailChunk001Sub000Block149Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part017] using hcert

def TailChunk001Sub000Block149Part018SupportExplicit : Finset ℕ :=
  ([22661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part018 : ℚ :=
  (13279384877 : ℚ) / 8260740234451353600

def SurrogateDiagonalTailChunk001Sub000Block149Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22661
    = surrogateDiagTailX0RatChunk001Sub000Block149Part018

theorem surrogateDiagonalTailChunk001Sub000Block149Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part018] using hcert

def TailChunk001Sub000Block149Part019SupportExplicit : Finset ℕ :=
  ([22663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part019 : ℚ :=
  (3750957517 : ℚ) / 25001959484434483200

def SurrogateDiagonalTailChunk001Sub000Block149Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22663
    = surrogateDiagTailX0RatChunk001Sub000Block149Part019

theorem surrogateDiagonalTailChunk001Sub000Block149Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part019] using hcert

def TailChunk001Sub000Block149Part020SupportExplicit : Finset ℕ :=
  ([22665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part020 : ℚ :=
  (13336193709 : ℚ) / 709959103993446400

def SurrogateDiagonalTailChunk001Sub000Block149Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22665
    = surrogateDiagTailX0RatChunk001Sub000Block149Part020

theorem surrogateDiagonalTailChunk001Sub000Block149Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part020] using hcert

def TailChunk001Sub000Block149Part021SupportExplicit : Finset ℕ :=
  ([22666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part021 : ℚ :=
  (27363279475 : ℚ) / 1233881419498191936

def SurrogateDiagonalTailChunk001Sub000Block149Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22666
    = surrogateDiagTailX0RatChunk001Sub000Block149Part021

theorem surrogateDiagonalTailChunk001Sub000Block149Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part021] using hcert

def TailChunk001Sub000Block149Part022SupportExplicit : Finset ℕ :=
  ([22667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part022 : ℚ :=
  (360625619725 : ℚ) / 529934142320147202048

def SurrogateDiagonalTailChunk001Sub000Block149Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22667
    = surrogateDiagTailX0RatChunk001Sub000Block149Part022

theorem surrogateDiagonalTailChunk001Sub000Block149Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part022] using hcert

def TailChunk001Sub000Block149Part023SupportExplicit : Finset ℕ :=
  ([22669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block149Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22669
    = surrogateDiagTailX0RatChunk001Sub000Block149Part023

theorem surrogateDiagonalTailChunk001Sub000Block149Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part023] using hcert

def TailChunk001Sub000Block149Part024SupportExplicit : Finset ℕ :=
  ([22670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block149Part024 : ℚ :=
  (642966576025 : ℚ) / 16877435086958020608

def SurrogateDiagonalTailChunk001Sub000Block149Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22670
    = surrogateDiagTailX0RatChunk001Sub000Block149Part024

theorem surrogateDiagonalTailChunk001Sub000Block149Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block149Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block149Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block149Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block149Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block149Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block149Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block149HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block149Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block149Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block149Part000
    + surrogateDiagTailX0RatChunk001Sub000Block149Part001
    + surrogateDiagTailX0RatChunk001Sub000Block149Part002
    + surrogateDiagTailX0RatChunk001Sub000Block149Part003
    + surrogateDiagTailX0RatChunk001Sub000Block149Part004
    + surrogateDiagTailX0RatChunk001Sub000Block149Part005
    + surrogateDiagTailX0RatChunk001Sub000Block149Part006
    + surrogateDiagTailX0RatChunk001Sub000Block149Part007
    + surrogateDiagTailX0RatChunk001Sub000Block149Part008
    + surrogateDiagTailX0RatChunk001Sub000Block149Part009

def surrogateDiagonalTailChunk001Sub000Block149MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block149Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block149Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block149Part010
    + surrogateDiagTailX0RatChunk001Sub000Block149Part011
    + surrogateDiagTailX0RatChunk001Sub000Block149Part012
    + surrogateDiagTailX0RatChunk001Sub000Block149Part013
    + surrogateDiagTailX0RatChunk001Sub000Block149Part014
    + surrogateDiagTailX0RatChunk001Sub000Block149Part015
    + surrogateDiagTailX0RatChunk001Sub000Block149Part016
    + surrogateDiagTailX0RatChunk001Sub000Block149Part017
    + surrogateDiagTailX0RatChunk001Sub000Block149Part018
    + surrogateDiagTailX0RatChunk001Sub000Block149Part019

def surrogateDiagonalTailChunk001Sub000Block149TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block149Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block149Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block149Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block149Part020
    + surrogateDiagTailX0RatChunk001Sub000Block149Part021
    + surrogateDiagTailX0RatChunk001Sub000Block149Part022
    + surrogateDiagTailX0RatChunk001Sub000Block149Part023
    + surrogateDiagTailX0RatChunk001Sub000Block149Part024

def surrogateDiagonalTailChunk001Sub000Block149Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block149HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block149MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block149TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block149 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block149Part000
    + surrogateDiagTailX0RatChunk001Sub000Block149Part001
    + surrogateDiagTailX0RatChunk001Sub000Block149Part002
    + surrogateDiagTailX0RatChunk001Sub000Block149Part003
    + surrogateDiagTailX0RatChunk001Sub000Block149Part004
    + surrogateDiagTailX0RatChunk001Sub000Block149Part005
    + surrogateDiagTailX0RatChunk001Sub000Block149Part006
    + surrogateDiagTailX0RatChunk001Sub000Block149Part007
    + surrogateDiagTailX0RatChunk001Sub000Block149Part008
    + surrogateDiagTailX0RatChunk001Sub000Block149Part009
    + surrogateDiagTailX0RatChunk001Sub000Block149Part010
    + surrogateDiagTailX0RatChunk001Sub000Block149Part011
    + surrogateDiagTailX0RatChunk001Sub000Block149Part012
    + surrogateDiagTailX0RatChunk001Sub000Block149Part013
    + surrogateDiagTailX0RatChunk001Sub000Block149Part014
    + surrogateDiagTailX0RatChunk001Sub000Block149Part015
    + surrogateDiagTailX0RatChunk001Sub000Block149Part016
    + surrogateDiagTailX0RatChunk001Sub000Block149Part017
    + surrogateDiagTailX0RatChunk001Sub000Block149Part018
    + surrogateDiagTailX0RatChunk001Sub000Block149Part019
    + surrogateDiagTailX0RatChunk001Sub000Block149Part020
    + surrogateDiagTailX0RatChunk001Sub000Block149Part021
    + surrogateDiagTailX0RatChunk001Sub000Block149Part022
    + surrogateDiagTailX0RatChunk001Sub000Block149Part023
    + surrogateDiagTailX0RatChunk001Sub000Block149Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block149_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block149Head + surrogateDiagTailX0RatChunk001Sub000Block149Mid + surrogateDiagTailX0RatChunk001Sub000Block149Tail =
      surrogateDiagTailX0RatChunk001Sub000Block149 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block149Head surrogateDiagTailX0RatChunk001Sub000Block149Mid surrogateDiagTailX0RatChunk001Sub000Block149Tail surrogateDiagTailX0RatChunk001Sub000Block149
  ring

def SurrogateDiagonalTailChunk001Sub000Block149HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block149HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block149Head

def SurrogateDiagonalTailChunk001Sub000Block149MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block149MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block149Mid

def SurrogateDiagonalTailChunk001Sub000Block149TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block149TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block149Tail

theorem surrogateDiagonalTailChunk001Sub000Block149_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block149HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block149MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block149TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block149Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block149 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block149HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block149MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block149TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block149Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block149_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
