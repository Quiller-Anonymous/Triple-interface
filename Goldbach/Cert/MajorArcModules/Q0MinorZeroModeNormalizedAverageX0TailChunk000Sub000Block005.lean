import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [5,6). -/

/- Block 005 covers tail-support indices [125,150) and q from 255 to 295. -/

def TailChunk000Sub000Block005Part000SupportExplicit : Finset ℕ :=
  ([255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part000 : ℚ :=
  (20163881825 : ℚ) / 335611428864

def SurrogateDiagonalTailChunk000Sub000Block005Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 255
    = surrogateDiagTailX0RatChunk000Sub000Block005Part000

theorem surrogateDiagonalTailChunk000Sub000Block005Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part000] using hcert

def TailChunk000Sub000Block005Part001SupportExplicit : Finset ℕ :=
  ([257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part001 : ℚ :=
  (78150828025 : ℚ) / 10739565723648

def SurrogateDiagonalTailChunk000Sub000Block005Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 257
    = surrogateDiagTailX0RatChunk000Sub000Block005Part001

theorem surrogateDiagonalTailChunk000Sub000Block005Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part001] using hcert

def TailChunk000Sub000Block005Part002SupportExplicit : Finset ℕ :=
  ([258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part002 : ℚ :=
  (220075 : ℚ) / 1037232

def SurrogateDiagonalTailChunk000Sub000Block005Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 258
    = surrogateDiagTailX0RatChunk000Sub000Block005Part002

theorem surrogateDiagonalTailChunk000Sub000Block005Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part002] using hcert

def TailChunk000Sub000Block005Part003SupportExplicit : Finset ℕ :=
  ([259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part003 : ℚ :=
  (66637699375 : ℚ) / 5443044231168

def SurrogateDiagonalTailChunk000Sub000Block005Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 259
    = surrogateDiagTailX0RatChunk000Sub000Block005Part003

theorem surrogateDiagonalTailChunk000Sub000Block005Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part003] using hcert

def TailChunk000Sub000Block005Part004SupportExplicit : Finset ℕ :=
  ([262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part004 : ℚ :=
  (1618230817 : ℚ) / 28566712200

def SurrogateDiagonalTailChunk000Sub000Block005Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 262
    = surrogateDiagTailX0RatChunk000Sub000Block005Part004

theorem surrogateDiagonalTailChunk000Sub000Block005Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part004] using hcert

def TailChunk000Sub000Block005Part005SupportExplicit : Finset ℕ :=
  ([263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part005 : ℚ :=
  (81842490025 : ℚ) / 11782352839368

def SurrogateDiagonalTailChunk000Sub000Block005Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 263
    = surrogateDiagTailX0RatChunk000Sub000Block005Part005

theorem surrogateDiagonalTailChunk000Sub000Block005Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part005] using hcert

def TailChunk000Sub000Block005Part006SupportExplicit : Finset ℕ :=
  ([265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part006 : ℚ :=
  (32730169625 : ℚ) / 2340185063424

def SurrogateDiagonalTailChunk000Sub000Block005Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 265
    = surrogateDiagTailX0RatChunk000Sub000Block005Part006

theorem surrogateDiagonalTailChunk000Sub000Block005Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part006] using hcert

def TailChunk000Sub000Block005Part007SupportExplicit : Finset ℕ :=
  ([266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part007 : ℚ :=
  (2083322575 : ℚ) / 21261891528

def SurrogateDiagonalTailChunk000Sub000Block005Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 266
    = surrogateDiagTailX0RatChunk000Sub000Block005Part007

theorem surrogateDiagonalTailChunk000Sub000Block005Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part007] using hcert

def TailChunk000Sub000Block005Part008SupportExplicit : Finset ℕ :=
  ([267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part008 : ℚ :=
  (697425 : ℚ) / 29984768

def SurrogateDiagonalTailChunk000Sub000Block005Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 267
    = surrogateDiagTailX0RatChunk000Sub000Block005Part008

theorem surrogateDiagonalTailChunk000Sub000Block005Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part008] using hcert

def TailChunk000Sub000Block005Part009SupportExplicit : Finset ℕ :=
  ([269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part009 : ℚ :=
  (85619344225 : ℚ) / 12899296783488

def SurrogateDiagonalTailChunk000Sub000Block005Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 269
    = surrogateDiagTailX0RatChunk000Sub000Block005Part009

theorem surrogateDiagonalTailChunk000Sub000Block005Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part009] using hcert

def TailChunk000Sub000Block005Part010SupportExplicit : Finset ℕ :=
  ([271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part010 : ℚ :=
  (121985501 : ℚ) / 19686936600

def SurrogateDiagonalTailChunk000Sub000Block005Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 271
    = surrogateDiagTailX0RatChunk000Sub000Block005Part010

theorem surrogateDiagonalTailChunk000Sub000Block005Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part010] using hcert

def TailChunk000Sub000Block005Part011SupportExplicit : Finset ℕ :=
  ([273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part011 : ℚ :=
  (4969693625 : ℚ) / 119463247872

def SurrogateDiagonalTailChunk000Sub000Block005Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 273
    = surrogateDiagTailX0RatChunk000Sub000Block005Part011

theorem surrogateDiagonalTailChunk000Sub000Block005Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part011] using hcert

def TailChunk000Sub000Block005Part012SupportExplicit : Finset ℕ :=
  ([274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part012 : ℚ :=
  (1267376725 : ℚ) / 25159590912

def SurrogateDiagonalTailChunk000Sub000Block005Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 274
    = surrogateDiagTailX0RatChunk000Sub000Block005Part012

theorem surrogateDiagonalTailChunk000Sub000Block005Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part012] using hcert

def TailChunk000Sub000Block005Part013SupportExplicit : Finset ℕ :=
  ([277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part013 : ℚ :=
  (3186171725 : ℚ) / 537402178944

def SurrogateDiagonalTailChunk000Sub000Block005Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 277
    = surrogateDiagTailX0RatChunk000Sub000Block005Part013

theorem surrogateDiagonalTailChunk000Sub000Block005Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part013] using hcert

def TailChunk000Sub000Block005Part014SupportExplicit : Finset ℕ :=
  ([278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part014 : ℚ :=
  (799406375 : ℚ) / 16793818092

def SurrogateDiagonalTailChunk000Sub000Block005Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 278
    = surrogateDiagTailX0RatChunk000Sub000Block005Part014

theorem surrogateDiagonalTailChunk000Sub000Block005Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part014] using hcert

def TailChunk000Sub000Block005Part015SupportExplicit : Finset ℕ :=
  ([281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part015 : ℚ :=
  (1180387989 : ℚ) / 204926310400

def SurrogateDiagonalTailChunk000Sub000Block005Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 281
    = surrogateDiagTailX0RatChunk000Sub000Block005Part015

theorem surrogateDiagonalTailChunk000Sub000Block005Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part015] using hcert

def TailChunk000Sub000Block005Part016SupportExplicit : Finset ℕ :=
  ([282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part016 : ℚ :=
  (28522363225 : ℚ) / 179134059648

def SurrogateDiagonalTailChunk000Sub000Block005Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 282
    = surrogateDiagTailX0RatChunk000Sub000Block005Part016

theorem surrogateDiagonalTailChunk000Sub000Block005Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part016] using hcert

def TailChunk000Sub000Block005Part017SupportExplicit : Finset ℕ :=
  ([283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part017 : ℚ :=
  (3325695725 : ℚ) / 585678832344

def SurrogateDiagonalTailChunk000Sub000Block005Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 283
    = surrogateDiagTailX0RatChunk000Sub000Block005Part017

theorem surrogateDiagonalTailChunk000Sub000Block005Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part017] using hcert

def TailChunk000Sub000Block005Part018SupportExplicit : Finset ℕ :=
  ([285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part018 : ℚ :=
  (44337355525 : ℚ) / 1075169230848

def SurrogateDiagonalTailChunk000Sub000Block005Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 285
    = surrogateDiagTailX0RatChunk000Sub000Block005Part018

theorem surrogateDiagonalTailChunk000Sub000Block005Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part018] using hcert

def TailChunk000Sub000Block005Part019SupportExplicit : Finset ℕ :=
  ([286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part019 : ℚ :=
  (150179029 : ℚ) / 2074014720

def SurrogateDiagonalTailChunk000Sub000Block005Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 286
    = surrogateDiagTailX0RatChunk000Sub000Block005Part019

theorem surrogateDiagonalTailChunk000Sub000Block005Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part019] using hcert

def TailChunk000Sub000Block005Part020SupportExplicit : Finset ℕ :=
  ([287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part020 : ℚ :=
  (326862893 : ℚ) / 36871372800

def SurrogateDiagonalTailChunk000Sub000Block005Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 287
    = surrogateDiagTailX0RatChunk000Sub000Block005Part020

theorem surrogateDiagonalTailChunk000Sub000Block005Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part020] using hcert

def TailChunk000Sub000Block005Part021SupportExplicit : Finset ℕ :=
  ([290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part021 : ℚ :=
  (34633252225 : ℚ) / 393458515968

def SurrogateDiagonalTailChunk000Sub000Block005Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 290
    = surrogateDiagTailX0RatChunk000Sub000Block005Part021

theorem surrogateDiagonalTailChunk000Sub000Block005Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part021] using hcert

def TailChunk000Sub000Block005Part022SupportExplicit : Finset ℕ :=
  ([291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part022 : ℚ :=
  (59958559225 : ℚ) / 3398065717248

def SurrogateDiagonalTailChunk000Sub000Block005Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 291
    = surrogateDiagTailX0RatChunk000Sub000Block005Part022

theorem surrogateDiagonalTailChunk000Sub000Block005Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part022] using hcert

def TailChunk000Sub000Block005Part023SupportExplicit : Finset ℕ :=
  ([293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part023 : ℚ :=
  (22730668975 : ℚ) / 4544627303712

def SurrogateDiagonalTailChunk000Sub000Block005Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 293
    = surrogateDiagTailX0RatChunk000Sub000Block005Part023

theorem surrogateDiagonalTailChunk000Sub000Block005Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part023] using hcert

def TailChunk000Sub000Block005Part024SupportExplicit : Finset ℕ :=
  ([295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block005Part024 : ℚ :=
  (36364646375 : ℚ) / 3622002975744

def SurrogateDiagonalTailChunk000Sub000Block005Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 295
    = surrogateDiagTailX0RatChunk000Sub000Block005Part024

theorem surrogateDiagonalTailChunk000Sub000Block005Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block005Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block005Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block005Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block005Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block005Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block005HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block005Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block005Part000
    + surrogateDiagTailX0RatChunk000Sub000Block005Part001
    + surrogateDiagTailX0RatChunk000Sub000Block005Part002
    + surrogateDiagTailX0RatChunk000Sub000Block005Part003
    + surrogateDiagTailX0RatChunk000Sub000Block005Part004
    + surrogateDiagTailX0RatChunk000Sub000Block005Part005
    + surrogateDiagTailX0RatChunk000Sub000Block005Part006
    + surrogateDiagTailX0RatChunk000Sub000Block005Part007
    + surrogateDiagTailX0RatChunk000Sub000Block005Part008
    + surrogateDiagTailX0RatChunk000Sub000Block005Part009

def surrogateDiagonalTailChunk000Sub000Block005MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block005Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block005Part010
    + surrogateDiagTailX0RatChunk000Sub000Block005Part011
    + surrogateDiagTailX0RatChunk000Sub000Block005Part012
    + surrogateDiagTailX0RatChunk000Sub000Block005Part013
    + surrogateDiagTailX0RatChunk000Sub000Block005Part014
    + surrogateDiagTailX0RatChunk000Sub000Block005Part015
    + surrogateDiagTailX0RatChunk000Sub000Block005Part016
    + surrogateDiagTailX0RatChunk000Sub000Block005Part017
    + surrogateDiagTailX0RatChunk000Sub000Block005Part018
    + surrogateDiagTailX0RatChunk000Sub000Block005Part019

def surrogateDiagonalTailChunk000Sub000Block005TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block005Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block005Part020
    + surrogateDiagTailX0RatChunk000Sub000Block005Part021
    + surrogateDiagTailX0RatChunk000Sub000Block005Part022
    + surrogateDiagTailX0RatChunk000Sub000Block005Part023
    + surrogateDiagTailX0RatChunk000Sub000Block005Part024

def surrogateDiagonalTailChunk000Sub000Block005Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block005HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block005MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block005TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block005 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block005Part000
    + surrogateDiagTailX0RatChunk000Sub000Block005Part001
    + surrogateDiagTailX0RatChunk000Sub000Block005Part002
    + surrogateDiagTailX0RatChunk000Sub000Block005Part003
    + surrogateDiagTailX0RatChunk000Sub000Block005Part004
    + surrogateDiagTailX0RatChunk000Sub000Block005Part005
    + surrogateDiagTailX0RatChunk000Sub000Block005Part006
    + surrogateDiagTailX0RatChunk000Sub000Block005Part007
    + surrogateDiagTailX0RatChunk000Sub000Block005Part008
    + surrogateDiagTailX0RatChunk000Sub000Block005Part009
    + surrogateDiagTailX0RatChunk000Sub000Block005Part010
    + surrogateDiagTailX0RatChunk000Sub000Block005Part011
    + surrogateDiagTailX0RatChunk000Sub000Block005Part012
    + surrogateDiagTailX0RatChunk000Sub000Block005Part013
    + surrogateDiagTailX0RatChunk000Sub000Block005Part014
    + surrogateDiagTailX0RatChunk000Sub000Block005Part015
    + surrogateDiagTailX0RatChunk000Sub000Block005Part016
    + surrogateDiagTailX0RatChunk000Sub000Block005Part017
    + surrogateDiagTailX0RatChunk000Sub000Block005Part018
    + surrogateDiagTailX0RatChunk000Sub000Block005Part019
    + surrogateDiagTailX0RatChunk000Sub000Block005Part020
    + surrogateDiagTailX0RatChunk000Sub000Block005Part021
    + surrogateDiagTailX0RatChunk000Sub000Block005Part022
    + surrogateDiagTailX0RatChunk000Sub000Block005Part023
    + surrogateDiagTailX0RatChunk000Sub000Block005Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block005_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block005Head + surrogateDiagTailX0RatChunk000Sub000Block005Mid + surrogateDiagTailX0RatChunk000Sub000Block005Tail =
      surrogateDiagTailX0RatChunk000Sub000Block005 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block005Head surrogateDiagTailX0RatChunk000Sub000Block005Mid surrogateDiagTailX0RatChunk000Sub000Block005Tail surrogateDiagTailX0RatChunk000Sub000Block005
  ring

def SurrogateDiagonalTailChunk000Sub000Block005HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block005HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block005Head

def SurrogateDiagonalTailChunk000Sub000Block005MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block005MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block005Mid

def SurrogateDiagonalTailChunk000Sub000Block005TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block005TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block005Tail

theorem surrogateDiagonalTailChunk000Sub000Block005_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block005HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block005MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block005TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block005Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block005 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block005HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block005MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block005TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block005Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block005_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
