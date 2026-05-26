import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [110,120). -/

/-- Block 110 covers tail-support indices [17750,17775) and q from 29245 to 29285. -/

def TailChunk001Sub001Block110Part000SupportExplicit : Finset ℕ :=
  ([29245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part000 : ℚ :=
  (712898152125 : ℚ) / 249560027764415266816

def SurrogateDiagonalTailChunk001Sub001Block110Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29245
    = surrogateDiagTailX0RatChunk001Sub001Block110Part000

theorem surrogateDiagonalTailChunk001Sub001Block110Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part000] using hcert

def TailChunk001Sub001Block110Part001SupportExplicit : Finset ℕ :=
  ([29246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part001 : ℚ :=
  (273366899075 : ℚ) / 30798094134917873664

def SurrogateDiagonalTailChunk001Sub001Block110Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29246
    = surrogateDiagTailX0RatChunk001Sub001Block110Part001

theorem surrogateDiagonalTailChunk001Sub001Block110Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part001] using hcert

def TailChunk001Sub001Block110Part002SupportExplicit : Finset ℕ :=
  ([29247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part002 : ℚ :=
  (125025 : ℚ) / 72235730499504128

def SurrogateDiagonalTailChunk001Sub001Block110Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29247
    = surrogateDiagTailX0RatChunk001Sub001Block110Part002

theorem surrogateDiagonalTailChunk001Sub001Block110Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part002] using hcert

def TailChunk001Sub001Block110Part003SupportExplicit : Finset ℕ :=
  ([29249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part003 : ℚ :=
  (889376711 : ℚ) / 2496184953228012960

def SurrogateDiagonalTailChunk001Sub001Block110Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29249
    = surrogateDiagTailX0RatChunk001Sub001Block110Part003

theorem surrogateDiagonalTailChunk001Sub001Block110Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part003] using hcert

def TailChunk001Sub001Block110Part004SupportExplicit : Finset ℕ :=
  ([29251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block110Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29251
    = surrogateDiagTailX0RatChunk001Sub001Block110Part004

theorem surrogateDiagonalTailChunk001Sub001Block110Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part004] using hcert

def TailChunk001Sub001Block110Part005SupportExplicit : Finset ℕ :=
  ([29254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block110Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29254
    = surrogateDiagTailX0RatChunk001Sub001Block110Part005

theorem surrogateDiagonalTailChunk001Sub001Block110Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part005] using hcert

def TailChunk001Sub001Block110Part006SupportExplicit : Finset ℕ :=
  ([29255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part006 : ℚ :=
  (17121253649 : ℚ) / 5997638359814400000

def SurrogateDiagonalTailChunk001Sub001Block110Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29255
    = surrogateDiagTailX0RatChunk001Sub001Block110Part006

theorem surrogateDiagonalTailChunk001Sub001Block110Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part006] using hcert

def TailChunk001Sub001Block110Part007SupportExplicit : Finset ℕ :=
  ([29257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part007 : ℚ :=
  (466230933 : ℚ) / 1195196550637158400

def SurrogateDiagonalTailChunk001Sub001Block110Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29257
    = surrogateDiagTailX0RatChunk001Sub001Block110Part007

theorem surrogateDiagonalTailChunk001Sub001Block110Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part007] using hcert

def TailChunk001Sub001Block110Part008SupportExplicit : Finset ℕ :=
  ([29258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block110Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29258
    = surrogateDiagTailX0RatChunk001Sub001Block110Part008

theorem surrogateDiagonalTailChunk001Sub001Block110Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part008] using hcert

def TailChunk001Sub001Block110Part009SupportExplicit : Finset ℕ :=
  ([29261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part009 : ℚ :=
  (81499559275 : ℚ) / 396680746058353999872

def SurrogateDiagonalTailChunk001Sub001Block110Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29261
    = surrogateDiagTailX0RatChunk001Sub001Block110Part009

theorem surrogateDiagonalTailChunk001Sub001Block110Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part009] using hcert

def TailChunk001Sub001Block110Part010SupportExplicit : Finset ℕ :=
  ([29262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part010 : ℚ :=
  (23227907275 : ℚ) / 353363473526352672

def SurrogateDiagonalTailChunk001Sub001Block110Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29262
    = surrogateDiagTailX0RatChunk001Sub001Block110Part010

theorem surrogateDiagonalTailChunk001Sub001Block110Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part010] using hcert

def TailChunk001Sub001Block110Part011SupportExplicit : Finset ℕ :=
  ([29263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part011 : ℚ :=
  (942873167 : ℚ) / 1968693660000000000

def SurrogateDiagonalTailChunk001Sub001Block110Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29263
    = surrogateDiagTailX0RatChunk001Sub001Block110Part011

theorem surrogateDiagonalTailChunk001Sub001Block110Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part011] using hcert

def TailChunk001Sub001Block110Part012SupportExplicit : Finset ℕ :=
  ([29265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part012 : ℚ :=
  (76344367 : ℚ) / 9492938208000000

def SurrogateDiagonalTailChunk001Sub001Block110Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29265
    = surrogateDiagTailX0RatChunk001Sub001Block110Part012

theorem surrogateDiagonalTailChunk001Sub001Block110Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part012] using hcert

def TailChunk001Sub001Block110Part013SupportExplicit : Finset ℕ :=
  ([29266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block110Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29266
    = surrogateDiagTailX0RatChunk001Sub001Block110Part013

theorem surrogateDiagonalTailChunk001Sub001Block110Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part013] using hcert

def TailChunk001Sub001Block110Part014SupportExplicit : Finset ℕ :=
  ([29267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part014 : ℚ :=
  (106817179375 : ℚ) / 71372795625659695104

def SurrogateDiagonalTailChunk001Sub001Block110Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29267
    = surrogateDiagTailX0RatChunk001Sub001Block110Part014

theorem surrogateDiagonalTailChunk001Sub001Block110Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part014] using hcert

def TailChunk001Sub001Block110Part015SupportExplicit : Finset ℕ :=
  ([29269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block110Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29269
    = surrogateDiagTailX0RatChunk001Sub001Block110Part015

theorem surrogateDiagonalTailChunk001Sub001Block110Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part015] using hcert

def TailChunk001Sub001Block110Part016SupportExplicit : Finset ℕ :=
  ([29270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part016 : ℚ :=
  (1071220710025 : ℚ) / 46920659886614857728

def SurrogateDiagonalTailChunk001Sub001Block110Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29270
    = surrogateDiagTailX0RatChunk001Sub001Block110Part016

theorem surrogateDiagonalTailChunk001Sub001Block110Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part016] using hcert

def TailChunk001Sub001Block110Part017SupportExplicit : Finset ℕ :=
  ([29271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part017 : ℚ :=
  (4761017501 : ℚ) / 1972294284032010240

def SurrogateDiagonalTailChunk001Sub001Block110Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29271
    = surrogateDiagTailX0RatChunk001Sub001Block110Part017

theorem surrogateDiagonalTailChunk001Sub001Block110Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part017] using hcert

def TailChunk001Sub001Block110Part018SupportExplicit : Finset ℕ :=
  ([29273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part018 : ℚ :=
  (1520350807 : ℚ) / 17202707693568000000

def SurrogateDiagonalTailChunk001Sub001Block110Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29273
    = surrogateDiagTailX0RatChunk001Sub001Block110Part018

theorem surrogateDiagonalTailChunk001Sub001Block110Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part018] using hcert

def TailChunk001Sub001Block110Part019SupportExplicit : Finset ℕ :=
  ([29274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part019 : ℚ :=
  (2118291491 : ℚ) / 12887478868377600

def SurrogateDiagonalTailChunk001Sub001Block110Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29274
    = surrogateDiagTailX0RatChunk001Sub001Block110Part019

theorem surrogateDiagonalTailChunk001Sub001Block110Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part019] using hcert

def TailChunk001Sub001Block110Part020SupportExplicit : Finset ℕ :=
  ([29278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block110Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29278
    = surrogateDiagTailX0RatChunk001Sub001Block110Part020

theorem surrogateDiagonalTailChunk001Sub001Block110Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part020] using hcert

def TailChunk001Sub001Block110Part021SupportExplicit : Finset ℕ :=
  ([29279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part021 : ℚ :=
  (221457920125 : ℚ) / 291691217656669450752

def SurrogateDiagonalTailChunk001Sub001Block110Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29279
    = surrogateDiagTailX0RatChunk001Sub001Block110Part021

theorem surrogateDiagonalTailChunk001Sub001Block110Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part021] using hcert

def TailChunk001Sub001Block110Part022SupportExplicit : Finset ℕ :=
  ([29281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part022 : ℚ :=
  (70663824925 : ℚ) / 48341638974990974976

def SurrogateDiagonalTailChunk001Sub001Block110Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29281
    = surrogateDiagTailX0RatChunk001Sub001Block110Part022

theorem surrogateDiagonalTailChunk001Sub001Block110Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part022] using hcert

def TailChunk001Sub001Block110Part023SupportExplicit : Finset ℕ :=
  ([29283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part023 : ℚ :=
  (20463144125 : ℚ) / 40596423343877028096

def SurrogateDiagonalTailChunk001Sub001Block110Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29283
    = surrogateDiagTailX0RatChunk001Sub001Block110Part023

theorem surrogateDiagonalTailChunk001Sub001Block110Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part023] using hcert

def TailChunk001Sub001Block110Part024SupportExplicit : Finset ℕ :=
  ([29285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block110Part024 : ℚ :=
  (2144546455375 : ℚ) / 752785242057068249088

def SurrogateDiagonalTailChunk001Sub001Block110Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29285
    = surrogateDiagTailX0RatChunk001Sub001Block110Part024

theorem surrogateDiagonalTailChunk001Sub001Block110Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block110Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block110Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block110Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block110Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block110Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block110Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block110HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block110Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block110Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block110Part000
    + surrogateDiagTailX0RatChunk001Sub001Block110Part001
    + surrogateDiagTailX0RatChunk001Sub001Block110Part002
    + surrogateDiagTailX0RatChunk001Sub001Block110Part003
    + surrogateDiagTailX0RatChunk001Sub001Block110Part004
    + surrogateDiagTailX0RatChunk001Sub001Block110Part005
    + surrogateDiagTailX0RatChunk001Sub001Block110Part006
    + surrogateDiagTailX0RatChunk001Sub001Block110Part007
    + surrogateDiagTailX0RatChunk001Sub001Block110Part008
    + surrogateDiagTailX0RatChunk001Sub001Block110Part009

def surrogateDiagonalTailChunk001Sub001Block110MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block110Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block110Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block110Part010
    + surrogateDiagTailX0RatChunk001Sub001Block110Part011
    + surrogateDiagTailX0RatChunk001Sub001Block110Part012
    + surrogateDiagTailX0RatChunk001Sub001Block110Part013
    + surrogateDiagTailX0RatChunk001Sub001Block110Part014
    + surrogateDiagTailX0RatChunk001Sub001Block110Part015
    + surrogateDiagTailX0RatChunk001Sub001Block110Part016
    + surrogateDiagTailX0RatChunk001Sub001Block110Part017
    + surrogateDiagTailX0RatChunk001Sub001Block110Part018
    + surrogateDiagTailX0RatChunk001Sub001Block110Part019

def surrogateDiagonalTailChunk001Sub001Block110TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block110Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block110Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block110Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block110Part020
    + surrogateDiagTailX0RatChunk001Sub001Block110Part021
    + surrogateDiagTailX0RatChunk001Sub001Block110Part022
    + surrogateDiagTailX0RatChunk001Sub001Block110Part023
    + surrogateDiagTailX0RatChunk001Sub001Block110Part024

def surrogateDiagonalTailChunk001Sub001Block110Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block110HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block110MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block110TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block110 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block110Part000
    + surrogateDiagTailX0RatChunk001Sub001Block110Part001
    + surrogateDiagTailX0RatChunk001Sub001Block110Part002
    + surrogateDiagTailX0RatChunk001Sub001Block110Part003
    + surrogateDiagTailX0RatChunk001Sub001Block110Part004
    + surrogateDiagTailX0RatChunk001Sub001Block110Part005
    + surrogateDiagTailX0RatChunk001Sub001Block110Part006
    + surrogateDiagTailX0RatChunk001Sub001Block110Part007
    + surrogateDiagTailX0RatChunk001Sub001Block110Part008
    + surrogateDiagTailX0RatChunk001Sub001Block110Part009
    + surrogateDiagTailX0RatChunk001Sub001Block110Part010
    + surrogateDiagTailX0RatChunk001Sub001Block110Part011
    + surrogateDiagTailX0RatChunk001Sub001Block110Part012
    + surrogateDiagTailX0RatChunk001Sub001Block110Part013
    + surrogateDiagTailX0RatChunk001Sub001Block110Part014
    + surrogateDiagTailX0RatChunk001Sub001Block110Part015
    + surrogateDiagTailX0RatChunk001Sub001Block110Part016
    + surrogateDiagTailX0RatChunk001Sub001Block110Part017
    + surrogateDiagTailX0RatChunk001Sub001Block110Part018
    + surrogateDiagTailX0RatChunk001Sub001Block110Part019
    + surrogateDiagTailX0RatChunk001Sub001Block110Part020
    + surrogateDiagTailX0RatChunk001Sub001Block110Part021
    + surrogateDiagTailX0RatChunk001Sub001Block110Part022
    + surrogateDiagTailX0RatChunk001Sub001Block110Part023
    + surrogateDiagTailX0RatChunk001Sub001Block110Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block110_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block110Head + surrogateDiagTailX0RatChunk001Sub001Block110Mid + surrogateDiagTailX0RatChunk001Sub001Block110Tail =
      surrogateDiagTailX0RatChunk001Sub001Block110 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block110Head surrogateDiagTailX0RatChunk001Sub001Block110Mid surrogateDiagTailX0RatChunk001Sub001Block110Tail surrogateDiagTailX0RatChunk001Sub001Block110
  ring

def SurrogateDiagonalTailChunk001Sub001Block110HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block110HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block110Head

def SurrogateDiagonalTailChunk001Sub001Block110MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block110MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block110Mid

def SurrogateDiagonalTailChunk001Sub001Block110TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block110TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block110Tail

theorem surrogateDiagonalTailChunk001Sub001Block110_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block110HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block110MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block110TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block110Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block110 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block110HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block110MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block110TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block110Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block110_eq_head_add_mid_add_tail

/-- Block 111 covers tail-support indices [17775,17800) and q from 29287 to 29326. -/

def TailChunk001Sub001Block111Part000SupportExplicit : Finset ℕ :=
  ([29287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block111Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29287
    = surrogateDiagTailX0RatChunk001Sub001Block111Part000

theorem surrogateDiagonalTailChunk001Sub001Block111Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part000] using hcert

def TailChunk001Sub001Block111Part001SupportExplicit : Finset ℕ :=
  ([29289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part001 : ℚ :=
  (5700833479 : ℚ) / 2624924880000000000

def SurrogateDiagonalTailChunk001Sub001Block111Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29289
    = surrogateDiagTailX0RatChunk001Sub001Block111Part001

theorem surrogateDiagonalTailChunk001Sub001Block111Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part001] using hcert

def TailChunk001Sub001Block111Part002SupportExplicit : Finset ℕ :=
  ([29290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part002 : ℚ :=
  (379357911 : ℚ) / 13115283865600000

def SurrogateDiagonalTailChunk001Sub001Block111Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29290
    = surrogateDiagTailX0RatChunk001Sub001Block111Part002

theorem surrogateDiagonalTailChunk001Sub001Block111Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part002] using hcert

def TailChunk001Sub001Block111Part003SupportExplicit : Finset ℕ :=
  ([29291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part003 : ℚ :=
  (317895325 : ℚ) / 816847148233654272

def SurrogateDiagonalTailChunk001Sub001Block111Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29291
    = surrogateDiagTailX0RatChunk001Sub001Block111Part003

theorem surrogateDiagonalTailChunk001Sub001Block111Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part003] using hcert

def TailChunk001Sub001Block111Part004SupportExplicit : Finset ℕ :=
  ([29293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part004 : ℚ :=
  (2221827301 : ℚ) / 3139056062396344200

def SurrogateDiagonalTailChunk001Sub001Block111Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29293
    = surrogateDiagTailX0RatChunk001Sub001Block111Part004

theorem surrogateDiagonalTailChunk001Sub001Block111Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part004] using hcert

def TailChunk001Sub001Block111Part005SupportExplicit : Finset ℕ :=
  ([29294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part005 : ℚ :=
  (1527301493 : ℚ) / 2150338461696000000

def SurrogateDiagonalTailChunk001Sub001Block111Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29294
    = surrogateDiagTailX0RatChunk001Sub001Block111Part005

theorem surrogateDiagonalTailChunk001Sub001Block111Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part005] using hcert

def TailChunk001Sub001Block111Part006SupportExplicit : Finset ℕ :=
  ([29297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block111Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29297
    = surrogateDiagTailX0RatChunk001Sub001Block111Part006

theorem surrogateDiagonalTailChunk001Sub001Block111Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part006] using hcert

def TailChunk001Sub001Block111Part007SupportExplicit : Finset ℕ :=
  ([29298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part007 : ℚ :=
  (1485828897475 : ℚ) / 18038346422490759168

def SurrogateDiagonalTailChunk001Sub001Block111Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29298
    = surrogateDiagTailX0RatChunk001Sub001Block111Part007

theorem surrogateDiagonalTailChunk001Sub001Block111Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part007] using hcert

def TailChunk001Sub001Block111Part008SupportExplicit : Finset ℕ :=
  ([29299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part008 : ℚ :=
  (133663022275 : ℚ) / 1735613111624697643008

def SurrogateDiagonalTailChunk001Sub001Block111Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29299
    = surrogateDiagTailX0RatChunk001Sub001Block111Part008

theorem surrogateDiagonalTailChunk001Sub001Block111Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part008] using hcert

def TailChunk001Sub001Block111Part009SupportExplicit : Finset ℕ :=
  ([29301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part009 : ℚ :=
  (125025 : ℚ) / 72770752656476288

def SurrogateDiagonalTailChunk001Sub001Block111Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29301
    = surrogateDiagTailX0RatChunk001Sub001Block111Part009

theorem surrogateDiagonalTailChunk001Sub001Block111Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part009] using hcert

def TailChunk001Sub001Block111Part010SupportExplicit : Finset ℕ :=
  ([29303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block111Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29303
    = surrogateDiagTailX0RatChunk001Sub001Block111Part010

theorem surrogateDiagonalTailChunk001Sub001Block111Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part010] using hcert

def TailChunk001Sub001Block111Part011SupportExplicit : Finset ℕ :=
  ([29305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part011 : ℚ :=
  (5726601213 : ℚ) / 2012917708434145280

def SurrogateDiagonalTailChunk001Sub001Block111Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29305
    = surrogateDiagTailX0RatChunk001Sub001Block111Part011

theorem surrogateDiagonalTailChunk001Sub001Block111Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part011] using hcert

def TailChunk001Sub001Block111Part012SupportExplicit : Finset ℕ :=
  ([29306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block111Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29306
    = surrogateDiagTailX0RatChunk001Sub001Block111Part012

theorem surrogateDiagonalTailChunk001Sub001Block111Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part012] using hcert

def TailChunk001Sub001Block111Part013SupportExplicit : Finset ℕ :=
  ([29307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part013 : ℚ :=
  (41675 : ℚ) / 24276794160807936

def SurrogateDiagonalTailChunk001Sub001Block111Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29307
    = surrogateDiagTailX0RatChunk001Sub001Block111Part013

theorem surrogateDiagonalTailChunk001Sub001Block111Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part013] using hcert

def TailChunk001Sub001Block111Part014SupportExplicit : Finset ℕ :=
  ([29309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part014 : ℚ :=
  (318019638025 : ℚ) / 219262142969163620352

def SurrogateDiagonalTailChunk001Sub001Block111Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29309
    = surrogateDiagTailX0RatChunk001Sub001Block111Part014

theorem surrogateDiagonalTailChunk001Sub001Block111Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part014] using hcert

def TailChunk001Sub001Block111Part015SupportExplicit : Finset ℕ :=
  ([29310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part015 : ℚ :=
  (387579128275 : ℚ) / 2323411240916877312

def SurrogateDiagonalTailChunk001Sub001Block111Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29310
    = surrogateDiagTailX0RatChunk001Sub001Block111Part015

theorem surrogateDiagonalTailChunk001Sub001Block111Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part015] using hcert

def TailChunk001Sub001Block111Part016SupportExplicit : Finset ℕ :=
  ([29311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block111Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29311
    = surrogateDiagTailX0RatChunk001Sub001Block111Part016

theorem surrogateDiagonalTailChunk001Sub001Block111Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part016] using hcert

def TailChunk001Sub001Block111Part017SupportExplicit : Finset ℕ :=
  ([29314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block111Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29314
    = surrogateDiagTailX0RatChunk001Sub001Block111Part017

theorem surrogateDiagonalTailChunk001Sub001Block111Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part017] using hcert

def TailChunk001Sub001Block111Part018SupportExplicit : Finset ℕ :=
  ([29315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part018 : ℚ :=
  (2576193127 : ℚ) / 339806571724800000

def SurrogateDiagonalTailChunk001Sub001Block111Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29315
    = surrogateDiagTailX0RatChunk001Sub001Block111Part018

theorem surrogateDiagonalTailChunk001Sub001Block111Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part018] using hcert

def TailChunk001Sub001Block111Part019SupportExplicit : Finset ℕ :=
  ([29317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part019 : ℚ :=
  (451275345175 : ℚ) / 1484069959362762603648

def SurrogateDiagonalTailChunk001Sub001Block111Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29317
    = surrogateDiagTailX0RatChunk001Sub001Block111Part019

theorem surrogateDiagonalTailChunk001Sub001Block111Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part019] using hcert

def TailChunk001Sub001Block111Part020SupportExplicit : Finset ℕ :=
  ([29318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part020 : ℚ :=
  (6314628075 : ℚ) / 8999631090670526464

def SurrogateDiagonalTailChunk001Sub001Block111Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29318
    = surrogateDiagTailX0RatChunk001Sub001Block111Part020

theorem surrogateDiagonalTailChunk001Sub001Block111Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part020] using hcert

def TailChunk001Sub001Block111Part021SupportExplicit : Finset ℕ :=
  ([29319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part021 : ℚ :=
  (114567309875 : ℚ) / 156713381158855901184

def SurrogateDiagonalTailChunk001Sub001Block111Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29319
    = surrogateDiagTailX0RatChunk001Sub001Block111Part021

theorem surrogateDiagonalTailChunk001Sub001Block111Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part021] using hcert

def TailChunk001Sub001Block111Part022SupportExplicit : Finset ℕ :=
  ([29321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part022 : ℚ :=
  (9902427875 : ℚ) / 146244590547491119104

def SurrogateDiagonalTailChunk001Sub001Block111Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29321
    = surrogateDiagTailX0RatChunk001Sub001Block111Part022

theorem surrogateDiagonalTailChunk001Sub001Block111Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part022] using hcert

def TailChunk001Sub001Block111Part023SupportExplicit : Finset ℕ :=
  ([29323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part023 : ℚ :=
  (7236378181 : ℚ) / 5031505433754777600

def SurrogateDiagonalTailChunk001Sub001Block111Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29323
    = surrogateDiagTailX0RatChunk001Sub001Block111Part023

theorem surrogateDiagonalTailChunk001Sub001Block111Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part023] using hcert

def TailChunk001Sub001Block111Part024SupportExplicit : Finset ℕ :=
  ([29326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block111Part024 : ℚ :=
  (6788718787 : ℚ) / 840325951584000000

def SurrogateDiagonalTailChunk001Sub001Block111Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29326
    = surrogateDiagTailX0RatChunk001Sub001Block111Part024

theorem surrogateDiagonalTailChunk001Sub001Block111Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block111Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block111Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block111Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block111Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block111Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block111Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block111HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block111Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block111Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block111Part000
    + surrogateDiagTailX0RatChunk001Sub001Block111Part001
    + surrogateDiagTailX0RatChunk001Sub001Block111Part002
    + surrogateDiagTailX0RatChunk001Sub001Block111Part003
    + surrogateDiagTailX0RatChunk001Sub001Block111Part004
    + surrogateDiagTailX0RatChunk001Sub001Block111Part005
    + surrogateDiagTailX0RatChunk001Sub001Block111Part006
    + surrogateDiagTailX0RatChunk001Sub001Block111Part007
    + surrogateDiagTailX0RatChunk001Sub001Block111Part008
    + surrogateDiagTailX0RatChunk001Sub001Block111Part009

def surrogateDiagonalTailChunk001Sub001Block111MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block111Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block111Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block111Part010
    + surrogateDiagTailX0RatChunk001Sub001Block111Part011
    + surrogateDiagTailX0RatChunk001Sub001Block111Part012
    + surrogateDiagTailX0RatChunk001Sub001Block111Part013
    + surrogateDiagTailX0RatChunk001Sub001Block111Part014
    + surrogateDiagTailX0RatChunk001Sub001Block111Part015
    + surrogateDiagTailX0RatChunk001Sub001Block111Part016
    + surrogateDiagTailX0RatChunk001Sub001Block111Part017
    + surrogateDiagTailX0RatChunk001Sub001Block111Part018
    + surrogateDiagTailX0RatChunk001Sub001Block111Part019

def surrogateDiagonalTailChunk001Sub001Block111TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block111Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block111Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block111Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block111Part020
    + surrogateDiagTailX0RatChunk001Sub001Block111Part021
    + surrogateDiagTailX0RatChunk001Sub001Block111Part022
    + surrogateDiagTailX0RatChunk001Sub001Block111Part023
    + surrogateDiagTailX0RatChunk001Sub001Block111Part024

def surrogateDiagonalTailChunk001Sub001Block111Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block111HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block111MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block111TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block111 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block111Part000
    + surrogateDiagTailX0RatChunk001Sub001Block111Part001
    + surrogateDiagTailX0RatChunk001Sub001Block111Part002
    + surrogateDiagTailX0RatChunk001Sub001Block111Part003
    + surrogateDiagTailX0RatChunk001Sub001Block111Part004
    + surrogateDiagTailX0RatChunk001Sub001Block111Part005
    + surrogateDiagTailX0RatChunk001Sub001Block111Part006
    + surrogateDiagTailX0RatChunk001Sub001Block111Part007
    + surrogateDiagTailX0RatChunk001Sub001Block111Part008
    + surrogateDiagTailX0RatChunk001Sub001Block111Part009
    + surrogateDiagTailX0RatChunk001Sub001Block111Part010
    + surrogateDiagTailX0RatChunk001Sub001Block111Part011
    + surrogateDiagTailX0RatChunk001Sub001Block111Part012
    + surrogateDiagTailX0RatChunk001Sub001Block111Part013
    + surrogateDiagTailX0RatChunk001Sub001Block111Part014
    + surrogateDiagTailX0RatChunk001Sub001Block111Part015
    + surrogateDiagTailX0RatChunk001Sub001Block111Part016
    + surrogateDiagTailX0RatChunk001Sub001Block111Part017
    + surrogateDiagTailX0RatChunk001Sub001Block111Part018
    + surrogateDiagTailX0RatChunk001Sub001Block111Part019
    + surrogateDiagTailX0RatChunk001Sub001Block111Part020
    + surrogateDiagTailX0RatChunk001Sub001Block111Part021
    + surrogateDiagTailX0RatChunk001Sub001Block111Part022
    + surrogateDiagTailX0RatChunk001Sub001Block111Part023
    + surrogateDiagTailX0RatChunk001Sub001Block111Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block111_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block111Head + surrogateDiagTailX0RatChunk001Sub001Block111Mid + surrogateDiagTailX0RatChunk001Sub001Block111Tail =
      surrogateDiagTailX0RatChunk001Sub001Block111 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block111Head surrogateDiagTailX0RatChunk001Sub001Block111Mid surrogateDiagTailX0RatChunk001Sub001Block111Tail surrogateDiagTailX0RatChunk001Sub001Block111
  ring

def SurrogateDiagonalTailChunk001Sub001Block111HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block111HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block111Head

def SurrogateDiagonalTailChunk001Sub001Block111MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block111MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block111Mid

def SurrogateDiagonalTailChunk001Sub001Block111TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block111TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block111Tail

theorem surrogateDiagonalTailChunk001Sub001Block111_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block111HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block111MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block111TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block111Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block111 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block111HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block111MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block111TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block111Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block111_eq_head_add_mid_add_tail

/-- Block 112 covers tail-support indices [17800,17825) and q from 29327 to 29366. -/

def TailChunk001Sub001Block112Part000SupportExplicit : Finset ℕ :=
  ([29327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block112Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29327
    = surrogateDiagTailX0RatChunk001Sub001Block112Part000

theorem surrogateDiagonalTailChunk001Sub001Block112Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part000] using hcert

def TailChunk001Sub001Block112Part001SupportExplicit : Finset ℕ :=
  ([29329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part001 : ℚ :=
  (8971913 : ℚ) / 145159046060011200

def SurrogateDiagonalTailChunk001Sub001Block112Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29329
    = surrogateDiagTailX0RatChunk001Sub001Block112Part001

theorem surrogateDiagonalTailChunk001Sub001Block112Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part001] using hcert

def TailChunk001Sub001Block112Part002SupportExplicit : Finset ℕ :=
  ([29330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part002 : ℚ :=
  (126728454575 : ℚ) / 2302418507934302208

def SurrogateDiagonalTailChunk001Sub001Block112Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29330
    = surrogateDiagTailX0RatChunk001Sub001Block112Part002

theorem surrogateDiagonalTailChunk001Sub001Block112Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part002] using hcert

def TailChunk001Sub001Block112Part003SupportExplicit : Finset ℕ :=
  ([29333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block112Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29333
    = surrogateDiagTailX0RatChunk001Sub001Block112Part003

theorem surrogateDiagonalTailChunk001Sub001Block112Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part003] using hcert

def TailChunk001Sub001Block112Part004SupportExplicit : Finset ℕ :=
  ([29334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part004 : ℚ :=
  (373477266325 : ℚ) / 5709678295236943872

def SurrogateDiagonalTailChunk001Sub001Block112Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29334
    = surrogateDiagTailX0RatChunk001Sub001Block112Part004

theorem surrogateDiagonalTailChunk001Sub001Block112Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part004] using hcert

def TailChunk001Sub001Block112Part005SupportExplicit : Finset ℕ :=
  ([29335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part005 : ℚ :=
  (717290901375 : ℚ) / 252646801266415015936

def SurrogateDiagonalTailChunk001Sub001Block112Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29335
    = surrogateDiagTailX0RatChunk001Sub001Block112Part005

theorem surrogateDiagonalTailChunk001Sub001Block112Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part005] using hcert

def TailChunk001Sub001Block112Part006SupportExplicit : Finset ℕ :=
  ([29337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part006 : ℚ :=
  (1951475893 : ℚ) / 209099987184549888

def SurrogateDiagonalTailChunk001Sub001Block112Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29337
    = surrogateDiagTailX0RatChunk001Sub001Block112Part006

theorem surrogateDiagonalTailChunk001Sub001Block112Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part006] using hcert

def TailChunk001Sub001Block112Part007SupportExplicit : Finset ℕ :=
  ([29338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block112Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29338
    = surrogateDiagTailX0RatChunk001Sub001Block112Part007

theorem surrogateDiagonalTailChunk001Sub001Block112Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part007] using hcert

def TailChunk001Sub001Block112Part008SupportExplicit : Finset ℕ :=
  ([29339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block112Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29339
    = surrogateDiagTailX0RatChunk001Sub001Block112Part008

theorem surrogateDiagonalTailChunk001Sub001Block112Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part008] using hcert

def TailChunk001Sub001Block112Part009SupportExplicit : Finset ℕ :=
  ([29341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part009 : ℚ :=
  (1848853541 : ℚ) / 2257339303549992960

def SurrogateDiagonalTailChunk001Sub001Block112Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29341
    = surrogateDiagTailX0RatChunk001Sub001Block112Part009

theorem surrogateDiagonalTailChunk001Sub001Block112Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part009] using hcert

def TailChunk001Sub001Block112Part010SupportExplicit : Finset ℕ :=
  ([29342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part010 : ℚ :=
  (47226880425 : ℚ) / 15079418779325431808

def SurrogateDiagonalTailChunk001Sub001Block112Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29342
    = surrogateDiagTailX0RatChunk001Sub001Block112Part010

theorem surrogateDiagonalTailChunk001Sub001Block112Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part010] using hcert

def TailChunk001Sub001Block112Part011SupportExplicit : Finset ℕ :=
  ([29343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part011 : ℚ :=
  (1667 : ℚ) / 975852418406400

def SurrogateDiagonalTailChunk001Sub001Block112Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29343
    = surrogateDiagTailX0RatChunk001Sub001Block112Part011

theorem surrogateDiagonalTailChunk001Sub001Block112Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part011] using hcert

def TailChunk001Sub001Block112Part012SupportExplicit : Finset ℕ :=
  ([29345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part012 : ℚ :=
  (2153339453875 : ℚ) / 758974605120927203328

def SurrogateDiagonalTailChunk001Sub001Block112Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29345
    = surrogateDiagTailX0RatChunk001Sub001Block112Part012

theorem surrogateDiagonalTailChunk001Sub001Block112Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part012] using hcert

def TailChunk001Sub001Block112Part013SupportExplicit : Finset ℕ :=
  ([29346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part013 : ℚ :=
  (1495626371425 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk001Sub001Block112Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29346
    = surrogateDiagTailX0RatChunk001Sub001Block112Part013

theorem surrogateDiagonalTailChunk001Sub001Block112Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part013] using hcert

def TailChunk001Sub001Block112Part014SupportExplicit : Finset ℕ :=
  ([29347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block112Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29347
    = surrogateDiagTailX0RatChunk001Sub001Block112Part014

theorem surrogateDiagonalTailChunk001Sub001Block112Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part014] using hcert

def TailChunk001Sub001Block112Part015SupportExplicit : Finset ℕ :=
  ([29353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part015 : ℚ :=
  (106589999725 : ℚ) / 1770508458393991938048

def SurrogateDiagonalTailChunk001Sub001Block112Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29353
    = surrogateDiagTailX0RatChunk001Sub001Block112Part015

theorem surrogateDiagonalTailChunk001Sub001Block112Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part015] using hcert

def TailChunk001Sub001Block112Part016SupportExplicit : Finset ℕ :=
  ([29354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part016 : ℚ :=
  (44561619125 : ℚ) / 9327080653428621312

def SurrogateDiagonalTailChunk001Sub001Block112Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29354
    = surrogateDiagTailX0RatChunk001Sub001Block112Part016

theorem surrogateDiagonalTailChunk001Sub001Block112Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part016] using hcert

def TailChunk001Sub001Block112Part017SupportExplicit : Finset ℕ :=
  ([29355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part017 : ℚ :=
  (1552419070675 : ℚ) / 116379775291233927168

def SurrogateDiagonalTailChunk001Sub001Block112Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29355
    = surrogateDiagTailX0RatChunk001Sub001Block112Part017

theorem surrogateDiagonalTailChunk001Sub001Block112Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part017] using hcert

def TailChunk001Sub001Block112Part018SupportExplicit : Finset ℕ :=
  ([29357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part018 : ℚ :=
  (13784748823 : ℚ) / 64883820580818307200

def SurrogateDiagonalTailChunk001Sub001Block112Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29357
    = surrogateDiagTailX0RatChunk001Sub001Block112Part018

theorem surrogateDiagonalTailChunk001Sub001Block112Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part018] using hcert

def TailChunk001Sub001Block112Part019SupportExplicit : Finset ℕ :=
  ([29359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part019 : ℚ :=
  (26527247483 : ℚ) / 19410430990064025600

def SurrogateDiagonalTailChunk001Sub001Block112Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29359
    = surrogateDiagTailX0RatChunk001Sub001Block112Part019

theorem surrogateDiagonalTailChunk001Sub001Block112Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part019] using hcert

def TailChunk001Sub001Block112Part020SupportExplicit : Finset ℕ :=
  ([29361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part020 : ℚ :=
  (41675 : ℚ) / 24456233822702976

def SurrogateDiagonalTailChunk001Sub001Block112Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29361
    = surrogateDiagTailX0RatChunk001Sub001Block112Part020

theorem surrogateDiagonalTailChunk001Sub001Block112Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part020] using hcert

def TailChunk001Sub001Block112Part021SupportExplicit : Finset ℕ :=
  ([29362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part021 : ℚ :=
  (25440976675 : ℚ) / 26522628997512241152

def SurrogateDiagonalTailChunk001Sub001Block112Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29362
    = surrogateDiagTailX0RatChunk001Sub001Block112Part021

theorem surrogateDiagonalTailChunk001Sub001Block112Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part021] using hcert

def TailChunk001Sub001Block112Part022SupportExplicit : Finset ℕ :=
  ([29363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block112Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29363
    = surrogateDiagTailX0RatChunk001Sub001Block112Part022

theorem surrogateDiagonalTailChunk001Sub001Block112Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part022] using hcert

def TailChunk001Sub001Block112Part023SupportExplicit : Finset ℕ :=
  ([29365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part023 : ℚ :=
  (58086006475 : ℚ) / 25569834530503477248

def SurrogateDiagonalTailChunk001Sub001Block112Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29365
    = surrogateDiagTailX0RatChunk001Sub001Block112Part023

theorem surrogateDiagonalTailChunk001Sub001Block112Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part023] using hcert

def TailChunk001Sub001Block112Part024SupportExplicit : Finset ℕ :=
  ([29366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block112Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block112Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29366
    = surrogateDiagTailX0RatChunk001Sub001Block112Part024

theorem surrogateDiagonalTailChunk001Sub001Block112Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block112Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block112Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block112Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block112Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block112Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block112Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block112HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block112Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block112Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block112Part000
    + surrogateDiagTailX0RatChunk001Sub001Block112Part001
    + surrogateDiagTailX0RatChunk001Sub001Block112Part002
    + surrogateDiagTailX0RatChunk001Sub001Block112Part003
    + surrogateDiagTailX0RatChunk001Sub001Block112Part004
    + surrogateDiagTailX0RatChunk001Sub001Block112Part005
    + surrogateDiagTailX0RatChunk001Sub001Block112Part006
    + surrogateDiagTailX0RatChunk001Sub001Block112Part007
    + surrogateDiagTailX0RatChunk001Sub001Block112Part008
    + surrogateDiagTailX0RatChunk001Sub001Block112Part009

def surrogateDiagonalTailChunk001Sub001Block112MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block112Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block112Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block112Part010
    + surrogateDiagTailX0RatChunk001Sub001Block112Part011
    + surrogateDiagTailX0RatChunk001Sub001Block112Part012
    + surrogateDiagTailX0RatChunk001Sub001Block112Part013
    + surrogateDiagTailX0RatChunk001Sub001Block112Part014
    + surrogateDiagTailX0RatChunk001Sub001Block112Part015
    + surrogateDiagTailX0RatChunk001Sub001Block112Part016
    + surrogateDiagTailX0RatChunk001Sub001Block112Part017
    + surrogateDiagTailX0RatChunk001Sub001Block112Part018
    + surrogateDiagTailX0RatChunk001Sub001Block112Part019

def surrogateDiagonalTailChunk001Sub001Block112TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block112Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block112Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block112Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block112Part020
    + surrogateDiagTailX0RatChunk001Sub001Block112Part021
    + surrogateDiagTailX0RatChunk001Sub001Block112Part022
    + surrogateDiagTailX0RatChunk001Sub001Block112Part023
    + surrogateDiagTailX0RatChunk001Sub001Block112Part024

def surrogateDiagonalTailChunk001Sub001Block112Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block112HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block112MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block112TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block112 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block112Part000
    + surrogateDiagTailX0RatChunk001Sub001Block112Part001
    + surrogateDiagTailX0RatChunk001Sub001Block112Part002
    + surrogateDiagTailX0RatChunk001Sub001Block112Part003
    + surrogateDiagTailX0RatChunk001Sub001Block112Part004
    + surrogateDiagTailX0RatChunk001Sub001Block112Part005
    + surrogateDiagTailX0RatChunk001Sub001Block112Part006
    + surrogateDiagTailX0RatChunk001Sub001Block112Part007
    + surrogateDiagTailX0RatChunk001Sub001Block112Part008
    + surrogateDiagTailX0RatChunk001Sub001Block112Part009
    + surrogateDiagTailX0RatChunk001Sub001Block112Part010
    + surrogateDiagTailX0RatChunk001Sub001Block112Part011
    + surrogateDiagTailX0RatChunk001Sub001Block112Part012
    + surrogateDiagTailX0RatChunk001Sub001Block112Part013
    + surrogateDiagTailX0RatChunk001Sub001Block112Part014
    + surrogateDiagTailX0RatChunk001Sub001Block112Part015
    + surrogateDiagTailX0RatChunk001Sub001Block112Part016
    + surrogateDiagTailX0RatChunk001Sub001Block112Part017
    + surrogateDiagTailX0RatChunk001Sub001Block112Part018
    + surrogateDiagTailX0RatChunk001Sub001Block112Part019
    + surrogateDiagTailX0RatChunk001Sub001Block112Part020
    + surrogateDiagTailX0RatChunk001Sub001Block112Part021
    + surrogateDiagTailX0RatChunk001Sub001Block112Part022
    + surrogateDiagTailX0RatChunk001Sub001Block112Part023
    + surrogateDiagTailX0RatChunk001Sub001Block112Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block112_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block112Head + surrogateDiagTailX0RatChunk001Sub001Block112Mid + surrogateDiagTailX0RatChunk001Sub001Block112Tail =
      surrogateDiagTailX0RatChunk001Sub001Block112 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block112Head surrogateDiagTailX0RatChunk001Sub001Block112Mid surrogateDiagTailX0RatChunk001Sub001Block112Tail surrogateDiagTailX0RatChunk001Sub001Block112
  ring

def SurrogateDiagonalTailChunk001Sub001Block112HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block112HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block112Head

def SurrogateDiagonalTailChunk001Sub001Block112MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block112MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block112Mid

def SurrogateDiagonalTailChunk001Sub001Block112TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block112TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block112Tail

theorem surrogateDiagonalTailChunk001Sub001Block112_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block112HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block112MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block112TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block112Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block112 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block112HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block112MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block112TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block112Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block112_eq_head_add_mid_add_tail

/-- Block 113 covers tail-support indices [17825,17850) and q from 29369 to 29407. -/

def TailChunk001Sub001Block113Part000SupportExplicit : Finset ℕ :=
  ([29369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part000 : ℚ :=
  (108224915075 : ℚ) / 841649991624254159424

def SurrogateDiagonalTailChunk001Sub001Block113Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29369
    = surrogateDiagTailX0RatChunk001Sub001Block113Part000

theorem surrogateDiagonalTailChunk001Sub001Block113Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part000] using hcert

def TailChunk001Sub001Block113Part001SupportExplicit : Finset ℕ :=
  ([29370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part001 : ℚ :=
  (26982410387 : ℚ) / 122842173249945600

def SurrogateDiagonalTailChunk001Sub001Block113Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29370
    = surrogateDiagTailX0RatChunk001Sub001Block113Part001

theorem surrogateDiagonalTailChunk001Sub001Block113Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part001] using hcert

def TailChunk001Sub001Block113Part002SupportExplicit : Finset ℕ :=
  ([29371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part002 : ℚ :=
  (206832455675 : ℚ) / 776408504859153982464

def SurrogateDiagonalTailChunk001Sub001Block113Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29371
    = surrogateDiagTailX0RatChunk001Sub001Block113Part002

theorem surrogateDiagonalTailChunk001Sub001Block113Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part002] using hcert

def TailChunk001Sub001Block113Part003SupportExplicit : Finset ℕ :=
  ([29373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part003 : ℚ :=
  (5001 : ℚ) / 2939549281539200

def SurrogateDiagonalTailChunk001Sub001Block113Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29373
    = surrogateDiagTailX0RatChunk001Sub001Block113Part003

theorem surrogateDiagonalTailChunk001Sub001Block113Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part003] using hcert

def TailChunk001Sub001Block113Part004SupportExplicit : Finset ℕ :=
  ([29374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part004 : ℚ :=
  (266052264775 : ℚ) / 93236525427874940928

def SurrogateDiagonalTailChunk001Sub001Block113Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29374
    = surrogateDiagTailX0RatChunk001Sub001Block113Part004

theorem surrogateDiagonalTailChunk001Sub001Block113Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part004] using hcert

def TailChunk001Sub001Block113Part005SupportExplicit : Finset ℕ :=
  ([29377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part005 : ℚ :=
  (27376768425 : ℚ) / 134338281457121910784

def SurrogateDiagonalTailChunk001Sub001Block113Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29377
    = surrogateDiagTailX0RatChunk001Sub001Block113Part005

theorem surrogateDiagonalTailChunk001Sub001Block113Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part005] using hcert

def TailChunk001Sub001Block113Part006SupportExplicit : Finset ℕ :=
  ([29378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part006 : ℚ :=
  (6288493975 : ℚ) / 4694560332851625984

def SurrogateDiagonalTailChunk001Sub001Block113Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29378
    = surrogateDiagTailX0RatChunk001Sub001Block113Part006

theorem surrogateDiagonalTailChunk001Sub001Block113Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part006] using hcert

def TailChunk001Sub001Block113Part007SupportExplicit : Finset ℕ :=
  ([29379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part007 : ℚ :=
  (1023125 : ℚ) / 275018039655552

def SurrogateDiagonalTailChunk001Sub001Block113Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29379
    = surrogateDiagTailX0RatChunk001Sub001Block113Part007

theorem surrogateDiagonalTailChunk001Sub001Block113Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part007] using hcert

def TailChunk001Sub001Block113Part008SupportExplicit : Finset ℕ :=
  ([29381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part008 : ℚ :=
  (745051543 : ℚ) / 1058987071938375000

def SurrogateDiagonalTailChunk001Sub001Block113Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29381
    = surrogateDiagTailX0RatChunk001Sub001Block113Part008

theorem surrogateDiagonalTailChunk001Sub001Block113Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part008] using hcert

def TailChunk001Sub001Block113Part009SupportExplicit : Finset ℕ :=
  ([29382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part009 : ℚ :=
  (1500276117775 : ℚ) / 20469829501482682368

def SurrogateDiagonalTailChunk001Sub001Block113Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29382
    = surrogateDiagTailX0RatChunk001Sub001Block113Part009

theorem surrogateDiagonalTailChunk001Sub001Block113Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part009] using hcert

def TailChunk001Sub001Block113Part010SupportExplicit : Finset ℕ :=
  ([29383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block113Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29383
    = surrogateDiagTailX0RatChunk001Sub001Block113Part010

theorem surrogateDiagonalTailChunk001Sub001Block113Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part010] using hcert

def TailChunk001Sub001Block113Part011SupportExplicit : Finset ℕ :=
  ([29386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part011 : ℚ :=
  (275982626075 : ℚ) / 31392348006120312384

def SurrogateDiagonalTailChunk001Sub001Block113Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29386
    = surrogateDiagTailX0RatChunk001Sub001Block113Part011

theorem surrogateDiagonalTailChunk001Sub001Block113Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part011] using hcert

def TailChunk001Sub001Block113Part012SupportExplicit : Finset ℕ :=
  ([29387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block113Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29387
    = surrogateDiagTailX0RatChunk001Sub001Block113Part012

theorem surrogateDiagonalTailChunk001Sub001Block113Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part012] using hcert

def TailChunk001Sub001Block113Part013SupportExplicit : Finset ℕ :=
  ([29389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block113Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29389
    = surrogateDiagTailX0RatChunk001Sub001Block113Part013

theorem surrogateDiagonalTailChunk001Sub001Block113Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part013] using hcert

def TailChunk001Sub001Block113Part014SupportExplicit : Finset ℕ :=
  ([29390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part014 : ℚ :=
  (180247023375 : ℚ) / 15898374951787534336

def SurrogateDiagonalTailChunk001Sub001Block113Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29390
    = surrogateDiagTailX0RatChunk001Sub001Block113Part014

theorem surrogateDiagonalTailChunk001Sub001Block113Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part014] using hcert

def TailChunk001Sub001Block113Part015SupportExplicit : Finset ℕ :=
  ([29391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part015 : ℚ :=
  (1212136831 : ℚ) / 3398065717248000000

def SurrogateDiagonalTailChunk001Sub001Block113Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29391
    = surrogateDiagTailX0RatChunk001Sub001Block113Part015

theorem surrogateDiagonalTailChunk001Sub001Block113Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part015] using hcert

def TailChunk001Sub001Block113Part016SupportExplicit : Finset ℕ :=
  ([29393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part016 : ℚ :=
  (29902220575 : ℚ) / 7223485771359977472

def SurrogateDiagonalTailChunk001Sub001Block113Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29393
    = surrogateDiagTailX0RatChunk001Sub001Block113Part016

theorem surrogateDiagonalTailChunk001Sub001Block113Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part016] using hcert

def TailChunk001Sub001Block113Part017SupportExplicit : Finset ℕ :=
  ([29395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part017 : ℚ :=
  (78203125 : ℚ) / 47760093515939691648

def SurrogateDiagonalTailChunk001Sub001Block113Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29395
    = surrogateDiagTailX0RatChunk001Sub001Block113Part017

theorem surrogateDiagonalTailChunk001Sub001Block113Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part017] using hcert

def TailChunk001Sub001Block113Part018SupportExplicit : Finset ℕ :=
  ([29397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part018 : ℚ :=
  (6799654837 : ℚ) / 13144819484865331200

def SurrogateDiagonalTailChunk001Sub001Block113Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29397
    = surrogateDiagTailX0RatChunk001Sub001Block113Part018

theorem surrogateDiagonalTailChunk001Sub001Block113Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part018] using hcert

def TailChunk001Sub001Block113Part019SupportExplicit : Finset ℕ :=
  ([29398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block113Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29398
    = surrogateDiagTailX0RatChunk001Sub001Block113Part019

theorem surrogateDiagonalTailChunk001Sub001Block113Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part019] using hcert

def TailChunk001Sub001Block113Part020SupportExplicit : Finset ℕ :=
  ([29399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block113Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29399
    = surrogateDiagTailX0RatChunk001Sub001Block113Part020

theorem surrogateDiagonalTailChunk001Sub001Block113Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part020] using hcert

def TailChunk001Sub001Block113Part021SupportExplicit : Finset ℕ :=
  ([29401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block113Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29401
    = surrogateDiagTailX0RatChunk001Sub001Block113Part021

theorem surrogateDiagonalTailChunk001Sub001Block113Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part021] using hcert

def TailChunk001Sub001Block113Part022SupportExplicit : Finset ℕ :=
  ([29402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part022 : ℚ :=
  (3762187927 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub001Block113Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29402
    = surrogateDiagTailX0RatChunk001Sub001Block113Part022

theorem surrogateDiagonalTailChunk001Sub001Block113Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part022] using hcert

def TailChunk001Sub001Block113Part023SupportExplicit : Finset ℕ :=
  ([29405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part023 : ℚ :=
  (17875 : ℚ) / 10931457949138944

def SurrogateDiagonalTailChunk001Sub001Block113Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29405
    = surrogateDiagTailX0RatChunk001Sub001Block113Part023

theorem surrogateDiagonalTailChunk001Sub001Block113Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part023] using hcert

def TailChunk001Sub001Block113Part024SupportExplicit : Finset ℕ :=
  ([29407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block113Part024 : ℚ :=
  (44174998393 : ℚ) / 40335645676032000000

def SurrogateDiagonalTailChunk001Sub001Block113Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29407
    = surrogateDiagTailX0RatChunk001Sub001Block113Part024

theorem surrogateDiagonalTailChunk001Sub001Block113Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block113Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block113Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block113Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block113Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block113Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block113Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block113HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block113Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block113Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block113Part000
    + surrogateDiagTailX0RatChunk001Sub001Block113Part001
    + surrogateDiagTailX0RatChunk001Sub001Block113Part002
    + surrogateDiagTailX0RatChunk001Sub001Block113Part003
    + surrogateDiagTailX0RatChunk001Sub001Block113Part004
    + surrogateDiagTailX0RatChunk001Sub001Block113Part005
    + surrogateDiagTailX0RatChunk001Sub001Block113Part006
    + surrogateDiagTailX0RatChunk001Sub001Block113Part007
    + surrogateDiagTailX0RatChunk001Sub001Block113Part008
    + surrogateDiagTailX0RatChunk001Sub001Block113Part009

def surrogateDiagonalTailChunk001Sub001Block113MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block113Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block113Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block113Part010
    + surrogateDiagTailX0RatChunk001Sub001Block113Part011
    + surrogateDiagTailX0RatChunk001Sub001Block113Part012
    + surrogateDiagTailX0RatChunk001Sub001Block113Part013
    + surrogateDiagTailX0RatChunk001Sub001Block113Part014
    + surrogateDiagTailX0RatChunk001Sub001Block113Part015
    + surrogateDiagTailX0RatChunk001Sub001Block113Part016
    + surrogateDiagTailX0RatChunk001Sub001Block113Part017
    + surrogateDiagTailX0RatChunk001Sub001Block113Part018
    + surrogateDiagTailX0RatChunk001Sub001Block113Part019

def surrogateDiagonalTailChunk001Sub001Block113TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block113Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block113Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block113Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block113Part020
    + surrogateDiagTailX0RatChunk001Sub001Block113Part021
    + surrogateDiagTailX0RatChunk001Sub001Block113Part022
    + surrogateDiagTailX0RatChunk001Sub001Block113Part023
    + surrogateDiagTailX0RatChunk001Sub001Block113Part024

def surrogateDiagonalTailChunk001Sub001Block113Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block113HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block113MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block113TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block113 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block113Part000
    + surrogateDiagTailX0RatChunk001Sub001Block113Part001
    + surrogateDiagTailX0RatChunk001Sub001Block113Part002
    + surrogateDiagTailX0RatChunk001Sub001Block113Part003
    + surrogateDiagTailX0RatChunk001Sub001Block113Part004
    + surrogateDiagTailX0RatChunk001Sub001Block113Part005
    + surrogateDiagTailX0RatChunk001Sub001Block113Part006
    + surrogateDiagTailX0RatChunk001Sub001Block113Part007
    + surrogateDiagTailX0RatChunk001Sub001Block113Part008
    + surrogateDiagTailX0RatChunk001Sub001Block113Part009
    + surrogateDiagTailX0RatChunk001Sub001Block113Part010
    + surrogateDiagTailX0RatChunk001Sub001Block113Part011
    + surrogateDiagTailX0RatChunk001Sub001Block113Part012
    + surrogateDiagTailX0RatChunk001Sub001Block113Part013
    + surrogateDiagTailX0RatChunk001Sub001Block113Part014
    + surrogateDiagTailX0RatChunk001Sub001Block113Part015
    + surrogateDiagTailX0RatChunk001Sub001Block113Part016
    + surrogateDiagTailX0RatChunk001Sub001Block113Part017
    + surrogateDiagTailX0RatChunk001Sub001Block113Part018
    + surrogateDiagTailX0RatChunk001Sub001Block113Part019
    + surrogateDiagTailX0RatChunk001Sub001Block113Part020
    + surrogateDiagTailX0RatChunk001Sub001Block113Part021
    + surrogateDiagTailX0RatChunk001Sub001Block113Part022
    + surrogateDiagTailX0RatChunk001Sub001Block113Part023
    + surrogateDiagTailX0RatChunk001Sub001Block113Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block113_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block113Head + surrogateDiagTailX0RatChunk001Sub001Block113Mid + surrogateDiagTailX0RatChunk001Sub001Block113Tail =
      surrogateDiagTailX0RatChunk001Sub001Block113 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block113Head surrogateDiagTailX0RatChunk001Sub001Block113Mid surrogateDiagTailX0RatChunk001Sub001Block113Tail surrogateDiagTailX0RatChunk001Sub001Block113
  ring

def SurrogateDiagonalTailChunk001Sub001Block113HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block113HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block113Head

def SurrogateDiagonalTailChunk001Sub001Block113MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block113MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block113Mid

def SurrogateDiagonalTailChunk001Sub001Block113TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block113TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block113Tail

theorem surrogateDiagonalTailChunk001Sub001Block113_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block113HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block113MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block113TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block113Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block113 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block113HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block113MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block113TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block113Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block113_eq_head_add_mid_add_tail

/-- Block 114 covers tail-support indices [17850,17875) and q from 29409 to 29447. -/

def TailChunk001Sub001Block114Part000SupportExplicit : Finset ℕ :=
  ([29409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part000 : ℚ :=
  (125025 : ℚ) / 73849707530188928

def SurrogateDiagonalTailChunk001Sub001Block114Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29409
    = surrogateDiagTailX0RatChunk001Sub001Block114Part000

theorem surrogateDiagonalTailChunk001Sub001Block114Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part000] using hcert

def TailChunk001Sub001Block114Part001SupportExplicit : Finset ℕ :=
  ([29410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part001 : ℚ :=
  (227960892975 : ℚ) / 12238812678524502016

def SurrogateDiagonalTailChunk001Sub001Block114Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29410
    = surrogateDiagTailX0RatChunk001Sub001Block114Part001

theorem surrogateDiagonalTailChunk001Sub001Block114Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part001] using hcert

def TailChunk001Sub001Block114Part002SupportExplicit : Finset ℕ :=
  ([29411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block114Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29411
    = surrogateDiagTailX0RatChunk001Sub001Block114Part002

theorem surrogateDiagonalTailChunk001Sub001Block114Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part002] using hcert

def TailChunk001Sub001Block114Part003SupportExplicit : Finset ℕ :=
  ([29413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part003 : ℚ :=
  (52385079029575 : ℚ) / 1746220341953122155648

def SurrogateDiagonalTailChunk001Sub001Block114Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29413
    = surrogateDiagTailX0RatChunk001Sub001Block114Part003

theorem surrogateDiagonalTailChunk001Sub001Block114Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part003] using hcert

def TailChunk001Sub001Block114Part004SupportExplicit : Finset ℕ :=
  ([29414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part004 : ℚ :=
  (19737873827 : ℚ) / 93849886224000000

def SurrogateDiagonalTailChunk001Sub001Block114Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29414
    = surrogateDiagTailX0RatChunk001Sub001Block114Part004

theorem surrogateDiagonalTailChunk001Sub001Block114Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part004] using hcert

def TailChunk001Sub001Block114Part005SupportExplicit : Finset ℕ :=
  ([29415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part005 : ℚ :=
  (7330495862225 : ℚ) / 62889796407807442944

def SurrogateDiagonalTailChunk001Sub001Block114Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29415
    = surrogateDiagTailX0RatChunk001Sub001Block114Part005

theorem surrogateDiagonalTailChunk001Sub001Block114Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part005] using hcert

def TailChunk001Sub001Block114Part006SupportExplicit : Finset ℕ :=
  ([29417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part006 : ℚ :=
  (282514038275 : ℚ) / 8878269617406548568

def SurrogateDiagonalTailChunk001Sub001Block114Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29417
    = surrogateDiagTailX0RatChunk001Sub001Block114Part006

theorem surrogateDiagonalTailChunk001Sub001Block114Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part006] using hcert

def TailChunk001Sub001Block114Part007SupportExplicit : Finset ℕ :=
  ([29418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part007 : ℚ :=
  (6008025509725 : ℚ) / 23101494110819814528

def SurrogateDiagonalTailChunk001Sub001Block114Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29418
    = surrogateDiagTailX0RatChunk001Sub001Block114Part007

theorem surrogateDiagonalTailChunk001Sub001Block114Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part007] using hcert

def TailChunk001Sub001Block114Part008SupportExplicit : Finset ℕ :=
  ([29419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part008 : ℚ :=
  (42938035783 : ℚ) / 1128669651774996480

def SurrogateDiagonalTailChunk001Sub001Block114Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29419
    = surrogateDiagTailX0RatChunk001Sub001Block114Part008

theorem surrogateDiagonalTailChunk001Sub001Block114Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part008] using hcert

def TailChunk001Sub001Block114Part009SupportExplicit : Finset ℕ :=
  ([29422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part009 : ℚ :=
  (1622576202875 : ℚ) / 13261314498756120576

def SurrogateDiagonalTailChunk001Sub001Block114Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29422
    = surrogateDiagTailX0RatChunk001Sub001Block114Part009

theorem surrogateDiagonalTailChunk001Sub001Block114Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part009] using hcert

def TailChunk001Sub001Block114Part010SupportExplicit : Finset ℕ :=
  ([29423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part010 : ℚ :=
  (13526764515625 : ℚ) / 468441790340317644882

def SurrogateDiagonalTailChunk001Sub001Block114Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29423
    = surrogateDiagTailX0RatChunk001Sub001Block114Part010

theorem surrogateDiagonalTailChunk001Sub001Block114Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part010] using hcert

def TailChunk001Sub001Block114Part011SupportExplicit : Finset ℕ :=
  ([29426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part011 : ℚ :=
  (3382380765625 : ℚ) / 29285573448117883392

def SurrogateDiagonalTailChunk001Sub001Block114Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29426
    = surrogateDiagTailX0RatChunk001Sub001Block114Part011

theorem surrogateDiagonalTailChunk001Sub001Block114Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part011] using hcert

def TailChunk001Sub001Block114Part012SupportExplicit : Finset ℕ :=
  ([29427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part012 : ℚ :=
  (10766697727925 : ℚ) / 144306771379926073344

def SurrogateDiagonalTailChunk001Sub001Block114Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29427
    = surrogateDiagTailX0RatChunk001Sub001Block114Part012

theorem surrogateDiagonalTailChunk001Sub001Block114Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part012] using hcert

def TailChunk001Sub001Block114Part013SupportExplicit : Finset ℕ :=
  ([29429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part013 : ℚ :=
  (13532281890625 : ℚ) / 468824022767598611232

def SurrogateDiagonalTailChunk001Sub001Block114Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29429
    = surrogateDiagTailX0RatChunk001Sub001Block114Part013

theorem surrogateDiagonalTailChunk001Sub001Block114Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part013] using hcert

def TailChunk001Sub001Block114Part014SupportExplicit : Finset ℕ :=
  ([29431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part014 : ℚ :=
  (48983109811375 : ℚ) / 1507303489905472555008

def SurrogateDiagonalTailChunk001Sub001Block114Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29431
    = surrogateDiagTailX0RatChunk001Sub001Block114Part014

theorem surrogateDiagonalTailChunk001Sub001Block114Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part014] using hcert

def TailChunk001Sub001Block114Part015SupportExplicit : Finset ℕ :=
  ([29433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part015 : ℚ :=
  (962385960757 : ℚ) / 14821182752957827200

def SurrogateDiagonalTailChunk001Sub001Block114Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29433
    = surrogateDiagTailX0RatChunk001Sub001Block114Part015

theorem surrogateDiagonalTailChunk001Sub001Block114Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part015] using hcert

def TailChunk001Sub001Block114Part016SupportExplicit : Finset ℕ :=
  ([29434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part016 : ℚ :=
  (3384220140625 : ℚ) / 29317435894184853792

def SurrogateDiagonalTailChunk001Sub001Block114Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29434
    = surrogateDiagTailX0RatChunk001Sub001Block114Part016

theorem surrogateDiagonalTailChunk001Sub001Block114Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part016] using hcert

def TailChunk001Sub001Block114Part017SupportExplicit : Finset ℕ :=
  ([29437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part017 : ℚ :=
  (13539640140625 : ℚ) / 469334029816221733152

def SurrogateDiagonalTailChunk001Sub001Block114Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29437
    = surrogateDiagTailX0RatChunk001Sub001Block114Part017

theorem surrogateDiagonalTailChunk001Sub001Block114Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part017] using hcert

def TailChunk001Sub001Block114Part018SupportExplicit : Finset ℕ :=
  ([29438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part018 : ℚ :=
  (517373991067 : ℚ) / 4205899801133875200

def SurrogateDiagonalTailChunk001Sub001Block114Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29438
    = surrogateDiagTailX0RatChunk001Sub001Block114Part018

theorem surrogateDiagonalTailChunk001Sub001Block114Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part018] using hcert

def TailChunk001Sub001Block114Part019SupportExplicit : Finset ℕ :=
  ([29441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part019 : ℚ :=
  (52303306412575 : ℚ) / 1740428571343866403968

def SurrogateDiagonalTailChunk001Sub001Block114Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29441
    = surrogateDiagTailX0RatChunk001Sub001Block114Part019

theorem surrogateDiagonalTailChunk001Sub001Block114Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part019] using hcert

def TailChunk001Sub001Block114Part020SupportExplicit : Finset ℕ :=
  ([29442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part020 : ℚ :=
  (2361141161 : ℚ) / 6147789312000000

def SurrogateDiagonalTailChunk001Sub001Block114Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29442
    = surrogateDiagTailX0RatChunk001Sub001Block114Part020

theorem surrogateDiagonalTailChunk001Sub001Block114Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part020] using hcert

def TailChunk001Sub001Block114Part021SupportExplicit : Finset ℕ :=
  ([29443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part021 : ℚ :=
  (13545160140625 : ℚ) / 469716808085514572562

def SurrogateDiagonalTailChunk001Sub001Block114Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29443
    = surrogateDiagTailX0RatChunk001Sub001Block114Part021

theorem surrogateDiagonalTailChunk001Sub001Block114Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part021] using hcert

def TailChunk001Sub001Block114Part022SupportExplicit : Finset ℕ :=
  ([29445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part022 : ℚ :=
  (90967536013 : ℚ) / 716779487232000000

def SurrogateDiagonalTailChunk001Sub001Block114Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29445
    = surrogateDiagTailX0RatChunk001Sub001Block114Part022

theorem surrogateDiagonalTailChunk001Sub001Block114Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part022] using hcert

def TailChunk001Sub001Block114Part023SupportExplicit : Finset ℕ :=
  ([29446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part023 : ℚ :=
  (3386980140625 : ℚ) / 29365278303594872082

def SurrogateDiagonalTailChunk001Sub001Block114Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29446
    = surrogateDiagTailX0RatChunk001Sub001Block114Part023

theorem surrogateDiagonalTailChunk001Sub001Block114Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part023] using hcert

def TailChunk001Sub001Block114Part024SupportExplicit : Finset ℕ :=
  ([29447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block114Part024 : ℚ :=
  (2260428521 : ℚ) / 64112291485038144

def SurrogateDiagonalTailChunk001Sub001Block114Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29447
    = surrogateDiagTailX0RatChunk001Sub001Block114Part024

theorem surrogateDiagonalTailChunk001Sub001Block114Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block114Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block114Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block114Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block114Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block114Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block114Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block114HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block114Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block114Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block114Part000
    + surrogateDiagTailX0RatChunk001Sub001Block114Part001
    + surrogateDiagTailX0RatChunk001Sub001Block114Part002
    + surrogateDiagTailX0RatChunk001Sub001Block114Part003
    + surrogateDiagTailX0RatChunk001Sub001Block114Part004
    + surrogateDiagTailX0RatChunk001Sub001Block114Part005
    + surrogateDiagTailX0RatChunk001Sub001Block114Part006
    + surrogateDiagTailX0RatChunk001Sub001Block114Part007
    + surrogateDiagTailX0RatChunk001Sub001Block114Part008
    + surrogateDiagTailX0RatChunk001Sub001Block114Part009

def surrogateDiagonalTailChunk001Sub001Block114MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block114Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block114Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block114Part010
    + surrogateDiagTailX0RatChunk001Sub001Block114Part011
    + surrogateDiagTailX0RatChunk001Sub001Block114Part012
    + surrogateDiagTailX0RatChunk001Sub001Block114Part013
    + surrogateDiagTailX0RatChunk001Sub001Block114Part014
    + surrogateDiagTailX0RatChunk001Sub001Block114Part015
    + surrogateDiagTailX0RatChunk001Sub001Block114Part016
    + surrogateDiagTailX0RatChunk001Sub001Block114Part017
    + surrogateDiagTailX0RatChunk001Sub001Block114Part018
    + surrogateDiagTailX0RatChunk001Sub001Block114Part019

def surrogateDiagonalTailChunk001Sub001Block114TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block114Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block114Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block114Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block114Part020
    + surrogateDiagTailX0RatChunk001Sub001Block114Part021
    + surrogateDiagTailX0RatChunk001Sub001Block114Part022
    + surrogateDiagTailX0RatChunk001Sub001Block114Part023
    + surrogateDiagTailX0RatChunk001Sub001Block114Part024

def surrogateDiagonalTailChunk001Sub001Block114Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block114HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block114MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block114TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block114 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block114Part000
    + surrogateDiagTailX0RatChunk001Sub001Block114Part001
    + surrogateDiagTailX0RatChunk001Sub001Block114Part002
    + surrogateDiagTailX0RatChunk001Sub001Block114Part003
    + surrogateDiagTailX0RatChunk001Sub001Block114Part004
    + surrogateDiagTailX0RatChunk001Sub001Block114Part005
    + surrogateDiagTailX0RatChunk001Sub001Block114Part006
    + surrogateDiagTailX0RatChunk001Sub001Block114Part007
    + surrogateDiagTailX0RatChunk001Sub001Block114Part008
    + surrogateDiagTailX0RatChunk001Sub001Block114Part009
    + surrogateDiagTailX0RatChunk001Sub001Block114Part010
    + surrogateDiagTailX0RatChunk001Sub001Block114Part011
    + surrogateDiagTailX0RatChunk001Sub001Block114Part012
    + surrogateDiagTailX0RatChunk001Sub001Block114Part013
    + surrogateDiagTailX0RatChunk001Sub001Block114Part014
    + surrogateDiagTailX0RatChunk001Sub001Block114Part015
    + surrogateDiagTailX0RatChunk001Sub001Block114Part016
    + surrogateDiagTailX0RatChunk001Sub001Block114Part017
    + surrogateDiagTailX0RatChunk001Sub001Block114Part018
    + surrogateDiagTailX0RatChunk001Sub001Block114Part019
    + surrogateDiagTailX0RatChunk001Sub001Block114Part020
    + surrogateDiagTailX0RatChunk001Sub001Block114Part021
    + surrogateDiagTailX0RatChunk001Sub001Block114Part022
    + surrogateDiagTailX0RatChunk001Sub001Block114Part023
    + surrogateDiagTailX0RatChunk001Sub001Block114Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block114_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block114Head + surrogateDiagTailX0RatChunk001Sub001Block114Mid + surrogateDiagTailX0RatChunk001Sub001Block114Tail =
      surrogateDiagTailX0RatChunk001Sub001Block114 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block114Head surrogateDiagTailX0RatChunk001Sub001Block114Mid surrogateDiagTailX0RatChunk001Sub001Block114Tail surrogateDiagTailX0RatChunk001Sub001Block114
  ring

def SurrogateDiagonalTailChunk001Sub001Block114HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block114HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block114Head

def SurrogateDiagonalTailChunk001Sub001Block114MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block114MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block114Mid

def SurrogateDiagonalTailChunk001Sub001Block114TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block114TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block114Tail

theorem surrogateDiagonalTailChunk001Sub001Block114_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block114HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block114MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block114TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block114Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block114 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block114HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block114MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block114TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block114Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block114_eq_head_add_mid_add_tail

/-- Block 115 covers tail-support indices [17875,17900) and q from 29451 to 29489. -/

def TailChunk001Sub001Block115Part000SupportExplicit : Finset ℕ :=
  ([29451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part000 : ℚ :=
  (24089088018325 : ℚ) / 371436895167277989888

def SurrogateDiagonalTailChunk001Sub001Block115Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29451
    = surrogateDiagTailX0RatChunk001Sub001Block115Part000

theorem surrogateDiagonalTailChunk001Sub001Block115Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part000] using hcert

def TailChunk001Sub001Block115Part001SupportExplicit : Finset ℕ :=
  ([29453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part001 : ℚ :=
  (13554362640625 : ℚ) / 470355292117631691552

def SurrogateDiagonalTailChunk001Sub001Block115Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29453
    = surrogateDiagTailX0RatChunk001Sub001Block115Part001

theorem surrogateDiagonalTailChunk001Sub001Block115Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part001] using hcert

def TailChunk001Sub001Block115Part002SupportExplicit : Finset ℕ :=
  ([29454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part002 : ℚ :=
  (6022740509125 : ℚ) / 23214805947954874368

def SurrogateDiagonalTailChunk001Sub001Block115Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29454
    = surrogateDiagTailX0RatChunk001Sub001Block115Part002

theorem surrogateDiagonalTailChunk001Sub001Block115Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part002] using hcert

def TailChunk001Sub001Block115Part003SupportExplicit : Finset ℕ :=
  ([29455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part003 : ℚ :=
  (16420069957175 : ℚ) / 340713721047709384704

def SurrogateDiagonalTailChunk001Sub001Block115Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29455
    = surrogateDiagTailX0RatChunk001Sub001Block115Part003

theorem surrogateDiagonalTailChunk001Sub001Block115Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part003] using hcert

def TailChunk001Sub001Block115Part004SupportExplicit : Finset ℕ :=
  ([29458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part004 : ℚ :=
  (44016066433 : ℚ) / 249442248137932800

def SurrogateDiagonalTailChunk001Sub001Block115Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29458
    = surrogateDiagTailX0RatChunk001Sub001Block115Part004

theorem surrogateDiagonalTailChunk001Sub001Block115Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part004] using hcert

def TailChunk001Sub001Block115Part005SupportExplicit : Finset ℕ :=
  ([29459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part005 : ℚ :=
  (422667282071 : ℚ) / 14226671185815306240

def SurrogateDiagonalTailChunk001Sub001Block115Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29459
    = surrogateDiagTailX0RatChunk001Sub001Block115Part005

theorem surrogateDiagonalTailChunk001Sub001Block115Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part005] using hcert

def TailChunk001Sub001Block115Part006SupportExplicit : Finset ℕ :=
  ([29461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part006 : ℚ :=
  (12094864903375 : ℚ) / 368670466858278715392

def SurrogateDiagonalTailChunk001Sub001Block115Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29461
    = surrogateDiagTailX0RatChunk001Sub001Block115Part006

theorem surrogateDiagonalTailChunk001Sub001Block115Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part006] using hcert

def TailChunk001Sub001Block115Part007SupportExplicit : Finset ℕ :=
  ([29462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part007 : ℚ :=
  (5425059025 : ℚ) / 47086654782276882

def SurrogateDiagonalTailChunk001Sub001Block115Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29462
    = surrogateDiagTailX0RatChunk001Sub001Block115Part007

theorem surrogateDiagonalTailChunk001Sub001Block115Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part007] using hcert

def TailChunk001Sub001Block115Part008SupportExplicit : Finset ℕ :=
  ([29463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part008 : ℚ :=
  (107782657537 : ℚ) / 1049436847256371200

def SurrogateDiagonalTailChunk001Sub001Block115Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29463
    = surrogateDiagTailX0RatChunk001Sub001Block115Part008

theorem surrogateDiagonalTailChunk001Sub001Block115Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part008] using hcert

def TailChunk001Sub001Block115Part009SupportExplicit : Finset ℕ :=
  ([29465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part009 : ℚ :=
  (331234824139 : ℚ) / 6948873309626572800

def SurrogateDiagonalTailChunk001Sub001Block115Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29465
    = surrogateDiagTailX0RatChunk001Sub001Block115Part009

theorem surrogateDiagonalTailChunk001Sub001Block115Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part009] using hcert

def TailChunk001Sub001Block115Part010SupportExplicit : Finset ℕ :=
  ([29467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part010 : ℚ :=
  (5861238517825 : ℚ) / 196940265802458826752

def SurrogateDiagonalTailChunk001Sub001Block115Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29467
    = surrogateDiagTailX0RatChunk001Sub001Block115Part010

theorem surrogateDiagonalTailChunk001Sub001Block115Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part010] using hcert

def TailChunk001Sub001Block115Part011SupportExplicit : Finset ℕ :=
  ([29469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part011 : ℚ :=
  (237269626837 : ℚ) / 2507303606081126400

def SurrogateDiagonalTailChunk001Sub001Block115Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29469
    = surrogateDiagTailX0RatChunk001Sub001Block115Part011

theorem surrogateDiagonalTailChunk001Sub001Block115Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part011] using hcert

def TailChunk001Sub001Block115Part012SupportExplicit : Finset ℕ :=
  ([29470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part012 : ℚ :=
  (140612500961 : ℚ) / 516296264653209600

def SurrogateDiagonalTailChunk001Sub001Block115Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29470
    = surrogateDiagTailX0RatChunk001Sub001Block115Part012

theorem surrogateDiagonalTailChunk001Sub001Block115Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part012] using hcert

def TailChunk001Sub001Block115Part013SupportExplicit : Finset ℕ :=
  ([29471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part013 : ℚ :=
  (15513002500175 : ℚ) / 455690747347866556416

def SurrogateDiagonalTailChunk001Sub001Block115Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29471
    = surrogateDiagTailX0RatChunk001Sub001Block115Part013

theorem surrogateDiagonalTailChunk001Sub001Block115Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part013] using hcert

def TailChunk001Sub001Block115Part014SupportExplicit : Finset ℕ :=
  ([29473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part014 : ℚ :=
  (13572777015625 : ℚ) / 471634212709869944832

def SurrogateDiagonalTailChunk001Sub001Block115Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29473
    = surrogateDiagTailX0RatChunk001Sub001Block115Part014

theorem surrogateDiagonalTailChunk001Sub001Block115Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part014] using hcert

def TailChunk001Sub001Block115Part015SupportExplicit : Finset ℕ :=
  ([29474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part015 : ℚ :=
  (3393424515625 : ℚ) / 29477138294366871552

def SurrogateDiagonalTailChunk001Sub001Block115Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29474
    = surrogateDiagTailX0RatChunk001Sub001Block115Part015

theorem surrogateDiagonalTailChunk001Sub001Block115Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part015] using hcert

def TailChunk001Sub001Block115Part016SupportExplicit : Finset ℕ :=
  ([29477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part016 : ℚ :=
  (177249297233 : ℚ) / 4524574313579932800

def SurrogateDiagonalTailChunk001Sub001Block115Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29477
    = surrogateDiagTailX0RatChunk001Sub001Block115Part016

theorem surrogateDiagonalTailChunk001Sub001Block115Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part016] using hcert

def TailChunk001Sub001Block115Part017SupportExplicit : Finset ℕ :=
  ([29479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part017 : ℚ :=
  (129402520531 : ℚ) / 4253090361198643200

def SurrogateDiagonalTailChunk001Sub001Block115Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29479
    = surrogateDiagTailX0RatChunk001Sub001Block115Part017

theorem surrogateDiagonalTailChunk001Sub001Block115Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part017] using hcert

def TailChunk001Sub001Block115Part018SupportExplicit : Finset ℕ :=
  ([29481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part018 : ℚ :=
  (453468084227 : ℚ) / 6462643307135385600

def SurrogateDiagonalTailChunk001Sub001Block115Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29481
    = surrogateDiagTailX0RatChunk001Sub001Block115Part018

theorem surrogateDiagonalTailChunk001Sub001Block115Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part018] using hcert

def TailChunk001Sub001Block115Part019SupportExplicit : Finset ℕ :=
  ([29482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part019 : ℚ :=
  (5432427025 : ℚ) / 47214651051761952

def SurrogateDiagonalTailChunk001Sub001Block115Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29482
    = surrogateDiagTailX0RatChunk001Sub001Block115Part019

theorem surrogateDiagonalTailChunk001Sub001Block115Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part019] using hcert

def TailChunk001Sub001Block115Part020SupportExplicit : Finset ℕ :=
  ([29483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part020 : ℚ :=
  (13581988890625 : ℚ) / 472274650154027851122

def SurrogateDiagonalTailChunk001Sub001Block115Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29483
    = surrogateDiagTailX0RatChunk001Sub001Block115Part020

theorem surrogateDiagonalTailChunk001Sub001Block115Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part020] using hcert

def TailChunk001Sub001Block115Part021SupportExplicit : Finset ℕ :=
  ([29485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part021 : ℚ :=
  (2172754140625 : ℚ) / 48347802677004238848

def SurrogateDiagonalTailChunk001Sub001Block115Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29485
    = surrogateDiagTailX0RatChunk001Sub001Block115Part021

theorem surrogateDiagonalTailChunk001Sub001Block115Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part021] using hcert

def TailChunk001Sub001Block115Part022SupportExplicit : Finset ℕ :=
  ([29486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part022 : ℚ :=
  (15214576251 : ℚ) / 119119683151462400

def SurrogateDiagonalTailChunk001Sub001Block115Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29486
    = surrogateDiagTailX0RatChunk001Sub001Block115Part022

theorem surrogateDiagonalTailChunk001Sub001Block115Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part022] using hcert

def TailChunk001Sub001Block115Part023SupportExplicit : Finset ℕ :=
  ([29487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part023 : ℚ :=
  (24148020017125 : ℚ) / 373256545873620584448

def SurrogateDiagonalTailChunk001Sub001Block115Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29487
    = surrogateDiagTailX0RatChunk001Sub001Block115Part023

theorem surrogateDiagonalTailChunk001Sub001Block115Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part023] using hcert

def TailChunk001Sub001Block115Part024SupportExplicit : Finset ℕ :=
  ([29489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block115Part024 : ℚ :=
  (25767365534825 : ℚ) / 843061267762426036224

def SurrogateDiagonalTailChunk001Sub001Block115Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29489
    = surrogateDiagTailX0RatChunk001Sub001Block115Part024

theorem surrogateDiagonalTailChunk001Sub001Block115Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block115Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block115Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block115Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block115Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block115Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block115Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block115HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block115Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block115Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block115Part000
    + surrogateDiagTailX0RatChunk001Sub001Block115Part001
    + surrogateDiagTailX0RatChunk001Sub001Block115Part002
    + surrogateDiagTailX0RatChunk001Sub001Block115Part003
    + surrogateDiagTailX0RatChunk001Sub001Block115Part004
    + surrogateDiagTailX0RatChunk001Sub001Block115Part005
    + surrogateDiagTailX0RatChunk001Sub001Block115Part006
    + surrogateDiagTailX0RatChunk001Sub001Block115Part007
    + surrogateDiagTailX0RatChunk001Sub001Block115Part008
    + surrogateDiagTailX0RatChunk001Sub001Block115Part009

def surrogateDiagonalTailChunk001Sub001Block115MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block115Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block115Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block115Part010
    + surrogateDiagTailX0RatChunk001Sub001Block115Part011
    + surrogateDiagTailX0RatChunk001Sub001Block115Part012
    + surrogateDiagTailX0RatChunk001Sub001Block115Part013
    + surrogateDiagTailX0RatChunk001Sub001Block115Part014
    + surrogateDiagTailX0RatChunk001Sub001Block115Part015
    + surrogateDiagTailX0RatChunk001Sub001Block115Part016
    + surrogateDiagTailX0RatChunk001Sub001Block115Part017
    + surrogateDiagTailX0RatChunk001Sub001Block115Part018
    + surrogateDiagTailX0RatChunk001Sub001Block115Part019

def surrogateDiagonalTailChunk001Sub001Block115TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block115Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block115Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block115Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block115Part020
    + surrogateDiagTailX0RatChunk001Sub001Block115Part021
    + surrogateDiagTailX0RatChunk001Sub001Block115Part022
    + surrogateDiagTailX0RatChunk001Sub001Block115Part023
    + surrogateDiagTailX0RatChunk001Sub001Block115Part024

def surrogateDiagonalTailChunk001Sub001Block115Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block115HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block115MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block115TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block115 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block115Part000
    + surrogateDiagTailX0RatChunk001Sub001Block115Part001
    + surrogateDiagTailX0RatChunk001Sub001Block115Part002
    + surrogateDiagTailX0RatChunk001Sub001Block115Part003
    + surrogateDiagTailX0RatChunk001Sub001Block115Part004
    + surrogateDiagTailX0RatChunk001Sub001Block115Part005
    + surrogateDiagTailX0RatChunk001Sub001Block115Part006
    + surrogateDiagTailX0RatChunk001Sub001Block115Part007
    + surrogateDiagTailX0RatChunk001Sub001Block115Part008
    + surrogateDiagTailX0RatChunk001Sub001Block115Part009
    + surrogateDiagTailX0RatChunk001Sub001Block115Part010
    + surrogateDiagTailX0RatChunk001Sub001Block115Part011
    + surrogateDiagTailX0RatChunk001Sub001Block115Part012
    + surrogateDiagTailX0RatChunk001Sub001Block115Part013
    + surrogateDiagTailX0RatChunk001Sub001Block115Part014
    + surrogateDiagTailX0RatChunk001Sub001Block115Part015
    + surrogateDiagTailX0RatChunk001Sub001Block115Part016
    + surrogateDiagTailX0RatChunk001Sub001Block115Part017
    + surrogateDiagTailX0RatChunk001Sub001Block115Part018
    + surrogateDiagTailX0RatChunk001Sub001Block115Part019
    + surrogateDiagTailX0RatChunk001Sub001Block115Part020
    + surrogateDiagTailX0RatChunk001Sub001Block115Part021
    + surrogateDiagTailX0RatChunk001Sub001Block115Part022
    + surrogateDiagTailX0RatChunk001Sub001Block115Part023
    + surrogateDiagTailX0RatChunk001Sub001Block115Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block115_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block115Head + surrogateDiagTailX0RatChunk001Sub001Block115Mid + surrogateDiagTailX0RatChunk001Sub001Block115Tail =
      surrogateDiagTailX0RatChunk001Sub001Block115 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block115Head surrogateDiagTailX0RatChunk001Sub001Block115Mid surrogateDiagTailX0RatChunk001Sub001Block115Tail surrogateDiagTailX0RatChunk001Sub001Block115
  ring

def SurrogateDiagonalTailChunk001Sub001Block115HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block115HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block115Head

def SurrogateDiagonalTailChunk001Sub001Block115MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block115MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block115Mid

def SurrogateDiagonalTailChunk001Sub001Block115TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block115TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block115Tail

theorem surrogateDiagonalTailChunk001Sub001Block115_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block115HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block115MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block115TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block115Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block115 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block115HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block115MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block115TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block115Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block115_eq_head_add_mid_add_tail

/-- Block 116 covers tail-support indices [17900,17925) and q from 29490 to 29530. -/

def TailChunk001Sub001Block116Part000SupportExplicit : Finset ℕ :=
  ([29490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part000 : ℚ :=
  (4281559193575 : ℚ) / 9524293233985486848

def SurrogateDiagonalTailChunk001Sub001Block116Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29490
    = surrogateDiagTailX0RatChunk001Sub001Block116Part000

theorem surrogateDiagonalTailChunk001Sub001Block116Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part000] using hcert

def TailChunk001Sub001Block116Part001SupportExplicit : Finset ℕ :=
  ([29491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part001 : ℚ :=
  (1331160039889 : ℚ) / 27602302010226739200

def SurrogateDiagonalTailChunk001Sub001Block116Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29491
    = surrogateDiagTailX0RatChunk001Sub001Block116Part001

theorem surrogateDiagonalTailChunk001Sub001Block116Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part001] using hcert

def TailChunk001Sub001Block116Part002SupportExplicit : Finset ℕ :=
  ([29494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part002 : ℚ :=
  (3398031390625 : ℚ) / 29557233726238719282

def SurrogateDiagonalTailChunk001Sub001Block116Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29494
    = surrogateDiagTailX0RatChunk001Sub001Block116Part002

theorem surrogateDiagonalTailChunk001Sub001Block116Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part002] using hcert

def TailChunk001Sub001Block116Part003SupportExplicit : Finset ℕ :=
  ([29495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part003 : ℚ :=
  (645740517675 : ℚ) / 12525928046160510976

def SurrogateDiagonalTailChunk001Sub001Block116Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29495
    = surrogateDiagTailX0RatChunk001Sub001Block116Part003

theorem surrogateDiagonalTailChunk001Sub001Block116Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part003] using hcert

def TailChunk001Sub001Block116Part004SupportExplicit : Finset ℕ :=
  ([29497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part004 : ℚ :=
  (46621188967075 : ℚ) / 1371905015917831815168

def SurrogateDiagonalTailChunk001Sub001Block116Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29497
    = surrogateDiagTailX0RatChunk001Sub001Block116Part004

theorem surrogateDiagonalTailChunk001Sub001Block116Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part004] using hcert

def TailChunk001Sub001Block116Part005SupportExplicit : Finset ℕ :=
  ([29499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part005 : ℚ :=
  (24167680016725 : ℚ) / 373864579216817553408

def SurrogateDiagonalTailChunk001Sub001Block116Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29499
    = surrogateDiagTailX0RatChunk001Sub001Block116Part005

theorem surrogateDiagonalTailChunk001Sub001Block116Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part005] using hcert

def TailChunk001Sub001Block116Part006SupportExplicit : Finset ℕ :=
  ([29501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part006 : ℚ :=
  (870309001 : ℚ) / 30299461180500000

def SurrogateDiagonalTailChunk001Sub001Block116Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29501
    = surrogateDiagTailX0RatChunk001Sub001Block116Part006

theorem surrogateDiagonalTailChunk001Sub001Block116Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part006] using hcert

def TailChunk001Sub001Block116Part007SupportExplicit : Finset ℕ :=
  ([29503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part007 : ℚ :=
  (2130060378487 : ℚ) / 72316421731403827200

def SurrogateDiagonalTailChunk001Sub001Block116Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29503
    = surrogateDiagTailX0RatChunk001Sub001Block116Part007

theorem surrogateDiagonalTailChunk001Sub001Block116Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part007] using hcert

def TailChunk001Sub001Block116Part008SupportExplicit : Finset ℕ :=
  ([29505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part008 : ℚ :=
  (118511182459 : ℚ) / 815875578711244800

def SurrogateDiagonalTailChunk001Sub001Block116Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29505
    = surrogateDiagTailX0RatChunk001Sub001Block116Part008

theorem surrogateDiagonalTailChunk001Sub001Block116Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part008] using hcert

def TailChunk001Sub001Block116Part009SupportExplicit : Finset ℕ :=
  ([29506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part009 : ℚ :=
  (3400797015625 : ℚ) / 29605369266889162752

def SurrogateDiagonalTailChunk001Sub001Block116Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29506
    = surrogateDiagTailX0RatChunk001Sub001Block116Part009

theorem surrogateDiagonalTailChunk001Sub001Block116Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part009] using hcert

def TailChunk001Sub001Block116Part010SupportExplicit : Finset ℕ :=
  ([29507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part010 : ℚ :=
  (49236550592875 : ℚ) / 1522943343364743364608

def SurrogateDiagonalTailChunk001Sub001Block116Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29507
    = surrogateDiagTailX0RatChunk001Sub001Block116Part010

theorem surrogateDiagonalTailChunk001Sub001Block116Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part010] using hcert

def TailChunk001Sub001Block116Part011SupportExplicit : Finset ℕ :=
  ([29509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part011 : ℚ :=
  (4169513900775 : ℚ) / 131852520697397314144

def SurrogateDiagonalTailChunk001Sub001Block116Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29509
    = surrogateDiagTailX0RatChunk001Sub001Block116Part011

theorem surrogateDiagonalTailChunk001Sub001Block116Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part011] using hcert

def TailChunk001Sub001Block116Part012SupportExplicit : Finset ℕ :=
  ([29510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part012 : ℚ :=
  (8037505649875 : ℚ) / 34627852981366161408

def SurrogateDiagonalTailChunk001Sub001Block116Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29510
    = surrogateDiagTailX0RatChunk001Sub001Block116Part012

theorem surrogateDiagonalTailChunk001Sub001Block116Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part012] using hcert

def TailChunk001Sub001Block116Part013SupportExplicit : Finset ℕ :=
  ([29513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part013 : ℚ :=
  (181646050801 : ℚ) / 5175138108595187520

def SurrogateDiagonalTailChunk001Sub001Block116Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29513
    = surrogateDiagTailX0RatChunk001Sub001Block116Part013

theorem surrogateDiagonalTailChunk001Sub001Block116Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part013] using hcert

def TailChunk001Sub001Block116Part014SupportExplicit : Finset ℕ :=
  ([29514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part014 : ℚ :=
  (6047305508125 : ℚ) / 23404584695029857408

def SurrogateDiagonalTailChunk001Sub001Block116Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29514
    = surrogateDiagTailX0RatChunk001Sub001Block116Part014

theorem surrogateDiagonalTailChunk001Sub001Block116Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part014] using hcert

def TailChunk001Sub001Block116Part015SupportExplicit : Finset ℕ :=
  ([29515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part015 : ℚ :=
  (2177178390625 : ℚ) / 48544905744893670528

def SurrogateDiagonalTailChunk001Sub001Block116Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29515
    = surrogateDiagTailX0RatChunk001Sub001Block116Part015

theorem surrogateDiagonalTailChunk001Sub001Block116Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part015] using hcert

def TailChunk001Sub001Block116Part016SupportExplicit : Finset ℕ :=
  ([29517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part016 : ℚ :=
  (24197185016125 : ℚ) / 374778021721322460288

def SurrogateDiagonalTailChunk001Sub001Block116Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29517
    = surrogateDiagTailX0RatChunk001Sub001Block116Part016

theorem surrogateDiagonalTailChunk001Sub001Block116Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part016] using hcert

def TailChunk001Sub001Block116Part017SupportExplicit : Finset ℕ :=
  ([29518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part017 : ℚ :=
  (3403563765625 : ℚ) / 29653563577098867762

def SurrogateDiagonalTailChunk001Sub001Block116Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29518
    = surrogateDiagTailX0RatChunk001Sub001Block116Part017

theorem surrogateDiagonalTailChunk001Sub001Block116Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part017] using hcert

def TailChunk001Sub001Block116Part018SupportExplicit : Finset ℕ :=
  ([29519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part018 : ℚ :=
  (4443871429925 : ℚ) / 113760570095107080192

def SurrogateDiagonalTailChunk001Sub001Block116Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29519
    = surrogateDiagTailX0RatChunk001Sub001Block116Part018

theorem surrogateDiagonalTailChunk001Sub001Block116Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part018] using hcert

def TailChunk001Sub001Block116Part019SupportExplicit : Finset ℕ :=
  ([29521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part019 : ℚ :=
  (17472579955125 : ℚ) / 582395680205886816256

def SurrogateDiagonalTailChunk001Sub001Block116Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29521
    = surrogateDiagTailX0RatChunk001Sub001Block116Part019

theorem surrogateDiagonalTailChunk001Sub001Block116Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part019] using hcert

def TailChunk001Sub001Block116Part020SupportExplicit : Finset ℕ :=
  ([29522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part020 : ℚ :=
  (2133394132875 : ℚ) / 17059354064148021248

def SurrogateDiagonalTailChunk001Sub001Block116Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29522
    = surrogateDiagTailX0RatChunk001Sub001Block116Part020

theorem surrogateDiagonalTailChunk001Sub001Block116Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part020] using hcert

def TailChunk001Sub001Block116Part021SupportExplicit : Finset ℕ :=
  ([29523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part021 : ℚ :=
  (746542814125 : ℚ) / 9678342263970594816

def SurrogateDiagonalTailChunk001Sub001Block116Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29523
    = surrogateDiagTailX0RatChunk001Sub001Block116Part021

theorem surrogateDiagonalTailChunk001Sub001Block116Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part021] using hcert

def TailChunk001Sub001Block116Part022SupportExplicit : Finset ℕ :=
  ([29526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part022 : ℚ :=
  (232879017925 : ℚ) / 507901343298748416

def SurrogateDiagonalTailChunk001Sub001Block116Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29526
    = surrogateDiagTailX0RatChunk001Sub001Block116Part022

theorem surrogateDiagonalTailChunk001Sub001Block116Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part022] using hcert

def TailChunk001Sub001Block116Part023SupportExplicit : Finset ℕ :=
  ([29527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part023 : ℚ :=
  (13622558265625 : ℚ) / 475100326882929163122

def SurrogateDiagonalTailChunk001Sub001Block116Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29527
    = surrogateDiagTailX0RatChunk001Sub001Block116Part023

theorem surrogateDiagonalTailChunk001Sub001Block116Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part023] using hcert

def TailChunk001Sub001Block116Part024SupportExplicit : Finset ℕ :=
  ([29530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block116Part024 : ℚ :=
  (9261069839275 : ℚ) / 48610740494884405248

def SurrogateDiagonalTailChunk001Sub001Block116Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29530
    = surrogateDiagTailX0RatChunk001Sub001Block116Part024

theorem surrogateDiagonalTailChunk001Sub001Block116Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block116Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block116Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block116Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block116Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block116Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block116Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block116HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block116Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block116Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block116Part000
    + surrogateDiagTailX0RatChunk001Sub001Block116Part001
    + surrogateDiagTailX0RatChunk001Sub001Block116Part002
    + surrogateDiagTailX0RatChunk001Sub001Block116Part003
    + surrogateDiagTailX0RatChunk001Sub001Block116Part004
    + surrogateDiagTailX0RatChunk001Sub001Block116Part005
    + surrogateDiagTailX0RatChunk001Sub001Block116Part006
    + surrogateDiagTailX0RatChunk001Sub001Block116Part007
    + surrogateDiagTailX0RatChunk001Sub001Block116Part008
    + surrogateDiagTailX0RatChunk001Sub001Block116Part009

def surrogateDiagonalTailChunk001Sub001Block116MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block116Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block116Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block116Part010
    + surrogateDiagTailX0RatChunk001Sub001Block116Part011
    + surrogateDiagTailX0RatChunk001Sub001Block116Part012
    + surrogateDiagTailX0RatChunk001Sub001Block116Part013
    + surrogateDiagTailX0RatChunk001Sub001Block116Part014
    + surrogateDiagTailX0RatChunk001Sub001Block116Part015
    + surrogateDiagTailX0RatChunk001Sub001Block116Part016
    + surrogateDiagTailX0RatChunk001Sub001Block116Part017
    + surrogateDiagTailX0RatChunk001Sub001Block116Part018
    + surrogateDiagTailX0RatChunk001Sub001Block116Part019

def surrogateDiagonalTailChunk001Sub001Block116TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block116Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block116Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block116Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block116Part020
    + surrogateDiagTailX0RatChunk001Sub001Block116Part021
    + surrogateDiagTailX0RatChunk001Sub001Block116Part022
    + surrogateDiagTailX0RatChunk001Sub001Block116Part023
    + surrogateDiagTailX0RatChunk001Sub001Block116Part024

def surrogateDiagonalTailChunk001Sub001Block116Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block116HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block116MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block116TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block116 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block116Part000
    + surrogateDiagTailX0RatChunk001Sub001Block116Part001
    + surrogateDiagTailX0RatChunk001Sub001Block116Part002
    + surrogateDiagTailX0RatChunk001Sub001Block116Part003
    + surrogateDiagTailX0RatChunk001Sub001Block116Part004
    + surrogateDiagTailX0RatChunk001Sub001Block116Part005
    + surrogateDiagTailX0RatChunk001Sub001Block116Part006
    + surrogateDiagTailX0RatChunk001Sub001Block116Part007
    + surrogateDiagTailX0RatChunk001Sub001Block116Part008
    + surrogateDiagTailX0RatChunk001Sub001Block116Part009
    + surrogateDiagTailX0RatChunk001Sub001Block116Part010
    + surrogateDiagTailX0RatChunk001Sub001Block116Part011
    + surrogateDiagTailX0RatChunk001Sub001Block116Part012
    + surrogateDiagTailX0RatChunk001Sub001Block116Part013
    + surrogateDiagTailX0RatChunk001Sub001Block116Part014
    + surrogateDiagTailX0RatChunk001Sub001Block116Part015
    + surrogateDiagTailX0RatChunk001Sub001Block116Part016
    + surrogateDiagTailX0RatChunk001Sub001Block116Part017
    + surrogateDiagTailX0RatChunk001Sub001Block116Part018
    + surrogateDiagTailX0RatChunk001Sub001Block116Part019
    + surrogateDiagTailX0RatChunk001Sub001Block116Part020
    + surrogateDiagTailX0RatChunk001Sub001Block116Part021
    + surrogateDiagTailX0RatChunk001Sub001Block116Part022
    + surrogateDiagTailX0RatChunk001Sub001Block116Part023
    + surrogateDiagTailX0RatChunk001Sub001Block116Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block116_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block116Head + surrogateDiagTailX0RatChunk001Sub001Block116Mid + surrogateDiagTailX0RatChunk001Sub001Block116Tail =
      surrogateDiagTailX0RatChunk001Sub001Block116 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block116Head surrogateDiagTailX0RatChunk001Sub001Block116Mid surrogateDiagTailX0RatChunk001Sub001Block116Tail surrogateDiagTailX0RatChunk001Sub001Block116
  ring

def SurrogateDiagonalTailChunk001Sub001Block116HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block116HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block116Head

def SurrogateDiagonalTailChunk001Sub001Block116MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block116MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block116Mid

def SurrogateDiagonalTailChunk001Sub001Block116TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block116TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block116Tail

theorem surrogateDiagonalTailChunk001Sub001Block116_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block116HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block116MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block116TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block116Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block116 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block116HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block116MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block116TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block116Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block116_eq_head_add_mid_add_tail

/-- Block 117 covers tail-support indices [17925,17950) and q from 29531 to 29569. -/

def TailChunk001Sub001Block117Part000SupportExplicit : Finset ℕ :=
  ([29531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part000 : ℚ :=
  (21801999025 : ℚ) / 760572534126817362

def SurrogateDiagonalTailChunk001Sub001Block117Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29531
    = surrogateDiagTailX0RatChunk001Sub001Block117Part000

theorem surrogateDiagonalTailChunk001Sub001Block117Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part000] using hcert

def TailChunk001Sub001Block117Part001SupportExplicit : Finset ℕ :=
  ([29533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part001 : ℚ :=
  (4448088429625 : ℚ) / 113976588206816825472

def SurrogateDiagonalTailChunk001Sub001Block117Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29533
    = surrogateDiagTailX0RatChunk001Sub001Block117Part001

theorem surrogateDiagonalTailChunk001Sub001Block117Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part001] using hcert

def TailChunk001Sub001Block117Part002SupportExplicit : Finset ℕ :=
  ([29534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part002 : ℚ :=
  (3407254515625 : ℚ) / 29717914159340207442

def SurrogateDiagonalTailChunk001Sub001Block117Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29534
    = surrogateDiagTailX0RatChunk001Sub001Block117Part002

theorem surrogateDiagonalTailChunk001Sub001Block117Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part002] using hcert

def TailChunk001Sub001Block117Part003SupportExplicit : Finset ℕ :=
  ([29535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part003 : ℚ :=
  (537069004357 : ℚ) / 4112697881277235200

def SurrogateDiagonalTailChunk001Sub001Block117Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29535
    = surrogateDiagTailX0RatChunk001Sub001Block117Part003

theorem surrogateDiagonalTailChunk001Sub001Block117Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part003] using hcert

def TailChunk001Sub001Block117Part004SupportExplicit : Finset ℕ :=
  ([29537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part004 : ℚ :=
  (13631787015625 : ℚ) / 475744290501563645952

def SurrogateDiagonalTailChunk001Sub001Block117Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29537
    = surrogateDiagTailX0RatChunk001Sub001Block117Part004

theorem surrogateDiagonalTailChunk001Sub001Block117Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part004] using hcert

def TailChunk001Sub001Block117Part005SupportExplicit : Finset ℕ :=
  ([29539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part005 : ℚ :=
  (78900335941 : ℚ) / 2678385990051993600

def SurrogateDiagonalTailChunk001Sub001Block117Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29539
    = surrogateDiagTailX0RatChunk001Sub001Block117Part005

theorem surrogateDiagonalTailChunk001Sub001Block117Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part005] using hcert

def TailChunk001Sub001Block117Part006SupportExplicit : Finset ℕ :=
  ([29541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part006 : ℚ :=
  (285029130275 : ℚ) / 4153348488016723968

def SurrogateDiagonalTailChunk001Sub001Block117Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29541
    = surrogateDiagTailX0RatChunk001Sub001Block117Part006

theorem surrogateDiagonalTailChunk001Sub001Block117Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part006] using hcert

def TailChunk001Sub001Block117Part007SupportExplicit : Finset ℕ :=
  ([29542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part007 : ℚ :=
  (5454561025 : ℚ) / 47600205915965682

def SurrogateDiagonalTailChunk001Sub001Block117Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29542
    = surrogateDiagTailX0RatChunk001Sub001Block117Part007

theorem surrogateDiagonalTailChunk001Sub001Block117Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part007] using hcert

def TailChunk001Sub001Block117Part008SupportExplicit : Finset ℕ :=
  ([29543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part008 : ℚ :=
  (1024360815677 : ℚ) / 33272824321065369600

def SurrogateDiagonalTailChunk001Sub001Block117Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29543
    = surrogateDiagTailX0RatChunk001Sub001Block117Part008

theorem surrogateDiagonalTailChunk001Sub001Block117Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part008] using hcert

def TailChunk001Sub001Block117Part009SupportExplicit : Finset ℕ :=
  ([29545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part009 : ℚ :=
  (157138709657 : ℚ) / 3102941760131174400

def SurrogateDiagonalTailChunk001Sub001Block117Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29545
    = surrogateDiagTailX0RatChunk001Sub001Block117Part009

theorem surrogateDiagonalTailChunk001Sub001Block117Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part009] using hcert

def TailChunk001Sub001Block117Part010SupportExplicit : Finset ℕ :=
  ([29546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part010 : ℚ :=
  (22859645513 : ℚ) / 134794659653222400

def SurrogateDiagonalTailChunk001Sub001Block117Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29546
    = surrogateDiagTailX0RatChunk001Sub001Block117Part010

theorem surrogateDiagonalTailChunk001Sub001Block117Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part010] using hcert

def TailChunk001Sub001Block117Part011SupportExplicit : Finset ℕ :=
  ([29549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part011 : ℚ :=
  (47109813856225 : ℚ) / 1381608992379877982208

def SurrogateDiagonalTailChunk001Sub001Block117Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29549
    = surrogateDiagTailX0RatChunk001Sub001Block117Part011

theorem surrogateDiagonalTailChunk001Sub001Block117Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part011] using hcert

def TailChunk001Sub001Block117Part012SupportExplicit : Finset ℕ :=
  ([29551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part012 : ℚ :=
  (1823227247875 : ℚ) / 58951120588267224576

def SurrogateDiagonalTailChunk001Sub001Block117Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29551
    = surrogateDiagTailX0RatChunk001Sub001Block117Part012

theorem surrogateDiagonalTailChunk001Sub001Block117Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part012] using hcert

def TailChunk001Sub001Block117Part013SupportExplicit : Finset ℕ :=
  ([29553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part013 : ℚ :=
  (970249960597 : ℚ) / 15064397086962000000

def SurrogateDiagonalTailChunk001Sub001Block117Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29553
    = surrogateDiagTailX0RatChunk001Sub001Block117Part013

theorem surrogateDiagonalTailChunk001Sub001Block117Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part013] using hcert

def TailChunk001Sub001Block117Part014SupportExplicit : Finset ℕ :=
  ([29554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part014 : ℚ :=
  (26442081967 : ℚ) / 160583785055944200

def SurrogateDiagonalTailChunk001Sub001Block117Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29554
    = surrogateDiagTailX0RatChunk001Sub001Block117Part014

theorem surrogateDiagonalTailChunk001Sub001Block117Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part014] using hcert

def TailChunk001Sub001Block117Part015SupportExplicit : Finset ℕ :=
  ([29555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part015 : ℚ :=
  (31942090285975 : ℚ) / 644046773288674787328

def SurrogateDiagonalTailChunk001Sub001Block117Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29555
    = surrogateDiagTailX0RatChunk001Sub001Block117Part015

theorem surrogateDiagonalTailChunk001Sub001Block117Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part015] using hcert

def TailChunk001Sub001Block117Part016SupportExplicit : Finset ℕ :=
  ([29557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part016 : ℚ :=
  (360754745759 : ℚ) / 10412161104460928640

def SurrogateDiagonalTailChunk001Sub001Block117Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29557
    = surrogateDiagTailX0RatChunk001Sub001Block117Part016

theorem surrogateDiagonalTailChunk001Sub001Block117Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part016] using hcert

def TailChunk001Sub001Block117Part017SupportExplicit : Finset ℕ :=
  ([29558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part017 : ℚ :=
  (3412794390625 : ℚ) / 29814636338691164082

def SurrogateDiagonalTailChunk001Sub001Block117Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29558
    = surrogateDiagTailX0RatChunk001Sub001Block117Part017

theorem surrogateDiagonalTailChunk001Sub001Block117Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part017] using hcert

def TailChunk001Sub001Block117Part018SupportExplicit : Finset ℕ :=
  ([29559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part018 : ℚ :=
  (23299785066175 : ℚ) / 343788359771627931648

def SurrogateDiagonalTailChunk001Sub001Block117Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29559
    = surrogateDiagTailX0RatChunk001Sub001Block117Part018

theorem surrogateDiagonalTailChunk001Sub001Block117Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part018] using hcert

def TailChunk001Sub001Block117Part019SupportExplicit : Finset ℕ :=
  ([29561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part019 : ℚ :=
  (150763720591 : ℚ) / 3591968373186232320

def SurrogateDiagonalTailChunk001Sub001Block117Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29561
    = surrogateDiagTailX0RatChunk001Sub001Block117Part019

theorem surrogateDiagonalTailChunk001Sub001Block117Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part019] using hcert

def TailChunk001Sub001Block117Part020SupportExplicit : Finset ℕ :=
  ([29562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part020 : ℚ :=
  (1341411627775 : ℚ) / 4234274740487135232

def SurrogateDiagonalTailChunk001Sub001Block117Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29562
    = surrogateDiagTailX0RatChunk001Sub001Block117Part020

theorem surrogateDiagonalTailChunk001Sub001Block117Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part020] using hcert

def TailChunk001Sub001Block117Part021SupportExplicit : Finset ℕ :=
  ([29563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part021 : ℚ :=
  (44598070508575 : ℚ) / 1232389868460995248128

def SurrogateDiagonalTailChunk001Sub001Block117Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29563
    = surrogateDiagTailX0RatChunk001Sub001Block117Part021

theorem surrogateDiagonalTailChunk001Sub001Block117Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part021] using hcert

def TailChunk001Sub001Block117Part022SupportExplicit : Finset ℕ :=
  ([29566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part022 : ℚ :=
  (3414642015625 : ℚ) / 29846929470137186322

def SurrogateDiagonalTailChunk001Sub001Block117Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29566
    = surrogateDiagTailX0RatChunk001Sub001Block117Part022

theorem surrogateDiagonalTailChunk001Sub001Block117Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part022] using hcert

def TailChunk001Sub001Block117Part023SupportExplicit : Finset ℕ :=
  ([29567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part023 : ℚ :=
  (13659492015625 : ℚ) / 477680109604476397842

def SurrogateDiagonalTailChunk001Sub001Block117Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29567
    = surrogateDiagTailX0RatChunk001Sub001Block117Part023

theorem surrogateDiagonalTailChunk001Sub001Block117Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part023] using hcert

def TailChunk001Sub001Block117Part024SupportExplicit : Finset ℕ :=
  ([29569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block117Part024 : ℚ :=
  (13661340015625 : ℚ) / 477809373916453404672

def SurrogateDiagonalTailChunk001Sub001Block117Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29569
    = surrogateDiagTailX0RatChunk001Sub001Block117Part024

theorem surrogateDiagonalTailChunk001Sub001Block117Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block117Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block117Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block117Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block117Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block117Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block117Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block117HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block117Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block117Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block117Part000
    + surrogateDiagTailX0RatChunk001Sub001Block117Part001
    + surrogateDiagTailX0RatChunk001Sub001Block117Part002
    + surrogateDiagTailX0RatChunk001Sub001Block117Part003
    + surrogateDiagTailX0RatChunk001Sub001Block117Part004
    + surrogateDiagTailX0RatChunk001Sub001Block117Part005
    + surrogateDiagTailX0RatChunk001Sub001Block117Part006
    + surrogateDiagTailX0RatChunk001Sub001Block117Part007
    + surrogateDiagTailX0RatChunk001Sub001Block117Part008
    + surrogateDiagTailX0RatChunk001Sub001Block117Part009

def surrogateDiagonalTailChunk001Sub001Block117MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block117Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block117Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block117Part010
    + surrogateDiagTailX0RatChunk001Sub001Block117Part011
    + surrogateDiagTailX0RatChunk001Sub001Block117Part012
    + surrogateDiagTailX0RatChunk001Sub001Block117Part013
    + surrogateDiagTailX0RatChunk001Sub001Block117Part014
    + surrogateDiagTailX0RatChunk001Sub001Block117Part015
    + surrogateDiagTailX0RatChunk001Sub001Block117Part016
    + surrogateDiagTailX0RatChunk001Sub001Block117Part017
    + surrogateDiagTailX0RatChunk001Sub001Block117Part018
    + surrogateDiagTailX0RatChunk001Sub001Block117Part019

def surrogateDiagonalTailChunk001Sub001Block117TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block117Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block117Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block117Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block117Part020
    + surrogateDiagTailX0RatChunk001Sub001Block117Part021
    + surrogateDiagTailX0RatChunk001Sub001Block117Part022
    + surrogateDiagTailX0RatChunk001Sub001Block117Part023
    + surrogateDiagTailX0RatChunk001Sub001Block117Part024

def surrogateDiagonalTailChunk001Sub001Block117Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block117HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block117MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block117TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block117 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block117Part000
    + surrogateDiagTailX0RatChunk001Sub001Block117Part001
    + surrogateDiagTailX0RatChunk001Sub001Block117Part002
    + surrogateDiagTailX0RatChunk001Sub001Block117Part003
    + surrogateDiagTailX0RatChunk001Sub001Block117Part004
    + surrogateDiagTailX0RatChunk001Sub001Block117Part005
    + surrogateDiagTailX0RatChunk001Sub001Block117Part006
    + surrogateDiagTailX0RatChunk001Sub001Block117Part007
    + surrogateDiagTailX0RatChunk001Sub001Block117Part008
    + surrogateDiagTailX0RatChunk001Sub001Block117Part009
    + surrogateDiagTailX0RatChunk001Sub001Block117Part010
    + surrogateDiagTailX0RatChunk001Sub001Block117Part011
    + surrogateDiagTailX0RatChunk001Sub001Block117Part012
    + surrogateDiagTailX0RatChunk001Sub001Block117Part013
    + surrogateDiagTailX0RatChunk001Sub001Block117Part014
    + surrogateDiagTailX0RatChunk001Sub001Block117Part015
    + surrogateDiagTailX0RatChunk001Sub001Block117Part016
    + surrogateDiagTailX0RatChunk001Sub001Block117Part017
    + surrogateDiagTailX0RatChunk001Sub001Block117Part018
    + surrogateDiagTailX0RatChunk001Sub001Block117Part019
    + surrogateDiagTailX0RatChunk001Sub001Block117Part020
    + surrogateDiagTailX0RatChunk001Sub001Block117Part021
    + surrogateDiagTailX0RatChunk001Sub001Block117Part022
    + surrogateDiagTailX0RatChunk001Sub001Block117Part023
    + surrogateDiagTailX0RatChunk001Sub001Block117Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block117_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block117Head + surrogateDiagTailX0RatChunk001Sub001Block117Mid + surrogateDiagTailX0RatChunk001Sub001Block117Tail =
      surrogateDiagTailX0RatChunk001Sub001Block117 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block117Head surrogateDiagTailX0RatChunk001Sub001Block117Mid surrogateDiagTailX0RatChunk001Sub001Block117Tail surrogateDiagTailX0RatChunk001Sub001Block117
  ring

def SurrogateDiagonalTailChunk001Sub001Block117HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block117HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block117Head

def SurrogateDiagonalTailChunk001Sub001Block117MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block117MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block117Mid

def SurrogateDiagonalTailChunk001Sub001Block117TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block117TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block117Tail

theorem surrogateDiagonalTailChunk001Sub001Block117_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block117HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block117MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block117TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block117Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block117 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block117HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block117MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block117TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block117Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block117_eq_head_add_mid_add_tail

/-- Block 118 covers tail-support indices [17950,17975) and q from 29570 to 29609. -/

def TailChunk001Sub001Block118Part000SupportExplicit : Finset ℕ :=
  ([29570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part000 : ℚ :=
  (546199140625 : ℚ) / 3054671833808160768

def SurrogateDiagonalTailChunk001Sub001Block118Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29570
    = surrogateDiagTailX0RatChunk001Sub001Block118Part000

theorem surrogateDiagonalTailChunk001Sub001Block118Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part000] using hcert

def TailChunk001Sub001Block118Part001SupportExplicit : Finset ℕ :=
  ([29571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part001 : ℚ :=
  (2207800728575 : ℚ) / 34320763109599346688

def SurrogateDiagonalTailChunk001Sub001Block118Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29571
    = surrogateDiagTailX0RatChunk001Sub001Block118Part001

theorem surrogateDiagonalTailChunk001Sub001Block118Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part001] using hcert

def TailChunk001Sub001Block118Part002SupportExplicit : Finset ℕ :=
  ([29573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part002 : ℚ :=
  (13665036390625 : ℚ) / 478067981243689427232

def SurrogateDiagonalTailChunk001Sub001Block118Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29573
    = surrogateDiagTailX0RatChunk001Sub001Block118Part002

theorem surrogateDiagonalTailChunk001Sub001Block118Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part002] using hcert

def TailChunk001Sub001Block118Part003SupportExplicit : Finset ℕ :=
  ([29577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part003 : ℚ :=
  (24295665014125 : ℚ) / 377834922876876375168

def SurrogateDiagonalTailChunk001Sub001Block118Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29577
    = surrogateDiagTailX0RatChunk001Sub001Block118Part003

theorem surrogateDiagonalTailChunk001Sub001Block118Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part003] using hcert

def TailChunk001Sub001Block118Part004SupportExplicit : Finset ℕ :=
  ([29578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part004 : ℚ :=
  (6328240548875 : ℚ) / 49753965282502561344

def SurrogateDiagonalTailChunk001Sub001Block118Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29578
    = surrogateDiagTailX0RatChunk001Sub001Block118Part004

theorem surrogateDiagonalTailChunk001Sub001Block118Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part004] using hcert

def TailChunk001Sub001Block118Part005SupportExplicit : Finset ℕ :=
  ([29579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part005 : ℚ :=
  (91229818997 : ℚ) / 2610801851875983360

def SurrogateDiagonalTailChunk001Sub001Block118Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29579
    = surrogateDiagTailX0RatChunk001Sub001Block118Part005

theorem surrogateDiagonalTailChunk001Sub001Block118Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part005] using hcert

def TailChunk001Sub001Block118Part006SupportExplicit : Finset ℕ :=
  ([29581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part006 : ℚ :=
  (21875889025 : ℚ) / 765736817297071392

def SurrogateDiagonalTailChunk001Sub001Block118Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29581
    = surrogateDiagTailX0RatChunk001Sub001Block118Part006

theorem surrogateDiagonalTailChunk001Sub001Block118Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part006] using hcert

def TailChunk001Sub001Block118Part007SupportExplicit : Finset ℕ :=
  ([29582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part007 : ℚ :=
  (10317547468225 : ℚ) / 64477399895431446528

def SurrogateDiagonalTailChunk001Sub001Block118Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29582
    = surrogateDiagTailX0RatChunk001Sub001Block118Part007

theorem surrogateDiagonalTailChunk001Sub001Block118Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part007] using hcert

def TailChunk001Sub001Block118Part008SupportExplicit : Finset ℕ :=
  ([29585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part008 : ℚ :=
  (26690569691 : ℚ) / 563698325702836224

def SurrogateDiagonalTailChunk001Sub001Block118Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29585
    = surrogateDiagTailX0RatChunk001Sub001Block118Part008

theorem surrogateDiagonalTailChunk001Sub001Block118Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part008] using hcert

def TailChunk001Sub001Block118Part009SupportExplicit : Finset ℕ :=
  ([29586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part009 : ℚ :=
  (243073980277 : ℚ) / 945354095428483200

def SurrogateDiagonalTailChunk001Sub001Block118Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29586
    = surrogateDiagTailX0RatChunk001Sub001Block118Part009

theorem surrogateDiagonalTailChunk001Sub001Block118Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part009] using hcert

def TailChunk001Sub001Block118Part010SupportExplicit : Finset ℕ :=
  ([29587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part010 : ℚ :=
  (13677977640625 : ℚ) / 478973933646170923602

def SurrogateDiagonalTailChunk001Sub001Block118Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29587
    = surrogateDiagTailX0RatChunk001Sub001Block118Part010

theorem surrogateDiagonalTailChunk001Sub001Block118Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part010] using hcert

def TailChunk001Sub001Block118Part011SupportExplicit : Finset ℕ :=
  ([29589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part011 : ℚ :=
  (224885032225 : ℚ) / 2515807708158885888

def SurrogateDiagonalTailChunk001Sub001Block118Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29589
    = surrogateDiagTailX0RatChunk001Sub001Block118Part011

theorem surrogateDiagonalTailChunk001Sub001Block118Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part011] using hcert

def TailChunk001Sub001Block118Part012SupportExplicit : Finset ℕ :=
  ([29590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part012 : ℚ :=
  (316907097889 : ℚ) / 1320887990629171200

def SurrogateDiagonalTailChunk001Sub001Block118Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29590
    = surrogateDiagTailX0RatChunk001Sub001Block118Part012

theorem surrogateDiagonalTailChunk001Sub001Block118Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part012] using hcert

def TailChunk001Sub001Block118Part013SupportExplicit : Finset ℕ :=
  ([29591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part013 : ℚ :=
  (2973261907075 : ℚ) / 101435149544496316416

def SurrogateDiagonalTailChunk001Sub001Block118Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29591
    = surrogateDiagTailX0RatChunk001Sub001Block118Part013

theorem surrogateDiagonalTailChunk001Sub001Block118Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part013] using hcert

def TailChunk001Sub001Block118Part014SupportExplicit : Finset ℕ :=
  ([29593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part014 : ℚ :=
  (427274695319 : ℚ) / 14542807371878400000

def SurrogateDiagonalTailChunk001Sub001Block118Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29593
    = surrogateDiagTailX0RatChunk001Sub001Block118Part014

theorem surrogateDiagonalTailChunk001Sub001Block118Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part014] using hcert

def TailChunk001Sub001Block118Part015SupportExplicit : Finset ℕ :=
  ([29594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part015 : ℚ :=
  (3421112640625 : ℚ) / 29960162054276166432

def SurrogateDiagonalTailChunk001Sub001Block118Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29594
    = surrogateDiagTailX0RatChunk001Sub001Block118Part015

theorem surrogateDiagonalTailChunk001Sub001Block118Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part015] using hcert

def TailChunk001Sub001Block118Part016SupportExplicit : Finset ℕ :=
  ([29595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part016 : ℚ :=
  (3949973842525 : ℚ) / 38721703748750671872

def SurrogateDiagonalTailChunk001Sub001Block118Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29595
    = surrogateDiagTailX0RatChunk001Sub001Block118Part016

theorem surrogateDiagonalTailChunk001Sub001Block118Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part016] using hcert

def TailChunk001Sub001Block118Part017SupportExplicit : Finset ℕ :=
  ([29597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part017 : ℚ :=
  (488273690923 : ℚ) / 15021170741005516800

def SurrogateDiagonalTailChunk001Sub001Block118Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29597
    = surrogateDiagTailX0RatChunk001Sub001Block118Part017

theorem surrogateDiagonalTailChunk001Sub001Block118Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part017] using hcert

def TailChunk001Sub001Block118Part018SupportExplicit : Finset ℕ :=
  ([29598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part018 : ℚ :=
  (6081780506725 : ℚ) / 23672226808316971008

def SurrogateDiagonalTailChunk001Sub001Block118Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29598
    = surrogateDiagTailX0RatChunk001Sub001Block118Part018

theorem surrogateDiagonalTailChunk001Sub001Block118Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part018] using hcert

def TailChunk001Sub001Block118Part019SupportExplicit : Finset ℕ :=
  ([29599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part019 : ℚ :=
  (13689075015625 : ℚ) / 479751488573300371602

def SurrogateDiagonalTailChunk001Sub001Block118Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29599
    = surrogateDiagTailX0RatChunk001Sub001Block118Part019

theorem surrogateDiagonalTailChunk001Sub001Block118Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part019] using hcert

def TailChunk001Sub001Block118Part020SupportExplicit : Finset ℕ :=
  ([29603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part020 : ℚ :=
  (4469203428125 : ℚ) / 115061297086457874432

def SurrogateDiagonalTailChunk001Sub001Block118Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29603
    = surrogateDiagTailX0RatChunk001Sub001Block118Part020

theorem surrogateDiagonalTailChunk001Sub001Block118Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part020] using hcert

def TailChunk001Sub001Block118Part021SupportExplicit : Finset ℕ :=
  ([29605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part021 : ℚ :=
  (2093982463 : ℚ) / 43246027572019200

def SurrogateDiagonalTailChunk001Sub001Block118Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29605
    = surrogateDiagTailX0RatChunk001Sub001Block118Part021

theorem surrogateDiagonalTailChunk001Sub001Block118Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part021] using hcert

def TailChunk001Sub001Block118Part022SupportExplicit : Finset ℕ :=
  ([29606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part022 : ℚ :=
  (177666177279 : ℚ) / 1498342489941606400

def SurrogateDiagonalTailChunk001Sub001Block118Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29606
    = surrogateDiagTailX0RatChunk001Sub001Block118Part022

theorem surrogateDiagonalTailChunk001Sub001Block118Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part022] using hcert

def TailChunk001Sub001Block118Part023SupportExplicit : Finset ℕ :=
  ([29607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part023 : ℚ :=
  (104229237067 : ℚ) / 1548363157973452800

def SurrogateDiagonalTailChunk001Sub001Block118Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29607
    = surrogateDiagTailX0RatChunk001Sub001Block118Part023

theorem surrogateDiagonalTailChunk001Sub001Block118Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part023] using hcert

def TailChunk001Sub001Block118Part024SupportExplicit : Finset ℕ :=
  ([29609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block118Part024 : ℚ :=
  (20500446679 : ℚ) / 665456486421307392

def SurrogateDiagonalTailChunk001Sub001Block118Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29609
    = surrogateDiagTailX0RatChunk001Sub001Block118Part024

theorem surrogateDiagonalTailChunk001Sub001Block118Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block118Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block118Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block118Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block118Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block118Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block118Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block118HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block118Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block118Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block118Part000
    + surrogateDiagTailX0RatChunk001Sub001Block118Part001
    + surrogateDiagTailX0RatChunk001Sub001Block118Part002
    + surrogateDiagTailX0RatChunk001Sub001Block118Part003
    + surrogateDiagTailX0RatChunk001Sub001Block118Part004
    + surrogateDiagTailX0RatChunk001Sub001Block118Part005
    + surrogateDiagTailX0RatChunk001Sub001Block118Part006
    + surrogateDiagTailX0RatChunk001Sub001Block118Part007
    + surrogateDiagTailX0RatChunk001Sub001Block118Part008
    + surrogateDiagTailX0RatChunk001Sub001Block118Part009

def surrogateDiagonalTailChunk001Sub001Block118MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block118Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block118Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block118Part010
    + surrogateDiagTailX0RatChunk001Sub001Block118Part011
    + surrogateDiagTailX0RatChunk001Sub001Block118Part012
    + surrogateDiagTailX0RatChunk001Sub001Block118Part013
    + surrogateDiagTailX0RatChunk001Sub001Block118Part014
    + surrogateDiagTailX0RatChunk001Sub001Block118Part015
    + surrogateDiagTailX0RatChunk001Sub001Block118Part016
    + surrogateDiagTailX0RatChunk001Sub001Block118Part017
    + surrogateDiagTailX0RatChunk001Sub001Block118Part018
    + surrogateDiagTailX0RatChunk001Sub001Block118Part019

def surrogateDiagonalTailChunk001Sub001Block118TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block118Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block118Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block118Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block118Part020
    + surrogateDiagTailX0RatChunk001Sub001Block118Part021
    + surrogateDiagTailX0RatChunk001Sub001Block118Part022
    + surrogateDiagTailX0RatChunk001Sub001Block118Part023
    + surrogateDiagTailX0RatChunk001Sub001Block118Part024

def surrogateDiagonalTailChunk001Sub001Block118Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block118HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block118MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block118TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block118 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block118Part000
    + surrogateDiagTailX0RatChunk001Sub001Block118Part001
    + surrogateDiagTailX0RatChunk001Sub001Block118Part002
    + surrogateDiagTailX0RatChunk001Sub001Block118Part003
    + surrogateDiagTailX0RatChunk001Sub001Block118Part004
    + surrogateDiagTailX0RatChunk001Sub001Block118Part005
    + surrogateDiagTailX0RatChunk001Sub001Block118Part006
    + surrogateDiagTailX0RatChunk001Sub001Block118Part007
    + surrogateDiagTailX0RatChunk001Sub001Block118Part008
    + surrogateDiagTailX0RatChunk001Sub001Block118Part009
    + surrogateDiagTailX0RatChunk001Sub001Block118Part010
    + surrogateDiagTailX0RatChunk001Sub001Block118Part011
    + surrogateDiagTailX0RatChunk001Sub001Block118Part012
    + surrogateDiagTailX0RatChunk001Sub001Block118Part013
    + surrogateDiagTailX0RatChunk001Sub001Block118Part014
    + surrogateDiagTailX0RatChunk001Sub001Block118Part015
    + surrogateDiagTailX0RatChunk001Sub001Block118Part016
    + surrogateDiagTailX0RatChunk001Sub001Block118Part017
    + surrogateDiagTailX0RatChunk001Sub001Block118Part018
    + surrogateDiagTailX0RatChunk001Sub001Block118Part019
    + surrogateDiagTailX0RatChunk001Sub001Block118Part020
    + surrogateDiagTailX0RatChunk001Sub001Block118Part021
    + surrogateDiagTailX0RatChunk001Sub001Block118Part022
    + surrogateDiagTailX0RatChunk001Sub001Block118Part023
    + surrogateDiagTailX0RatChunk001Sub001Block118Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block118_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block118Head + surrogateDiagTailX0RatChunk001Sub001Block118Mid + surrogateDiagTailX0RatChunk001Sub001Block118Tail =
      surrogateDiagTailX0RatChunk001Sub001Block118 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block118Head surrogateDiagTailX0RatChunk001Sub001Block118Mid surrogateDiagTailX0RatChunk001Sub001Block118Tail surrogateDiagTailX0RatChunk001Sub001Block118
  ring

def SurrogateDiagonalTailChunk001Sub001Block118HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block118HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block118Head

def SurrogateDiagonalTailChunk001Sub001Block118MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block118MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block118Mid

def SurrogateDiagonalTailChunk001Sub001Block118TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block118TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block118Tail

theorem surrogateDiagonalTailChunk001Sub001Block118_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block118HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block118MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block118TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block118Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block118 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block118HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block118MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block118TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block118Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block118_eq_head_add_mid_add_tail

/-- Block 119 covers tail-support indices [17975,18000) and q from 29611 to 29651. -/

def TailChunk001Sub001Block119Part000SupportExplicit : Finset ℕ :=
  ([29611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part000 : ℚ :=
  (21920283025 : ℚ) / 768847983703380882

def SurrogateDiagonalTailChunk001Sub001Block119Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29611
    = surrogateDiagTailX0RatChunk001Sub001Block119Part000

theorem surrogateDiagonalTailChunk001Sub001Block119Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part000] using hcert

def TailChunk001Sub001Block119Part001SupportExplicit : Finset ℕ :=
  ([29613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part001 : ℚ :=
  (974193960517 : ℚ) / 15187120665745795200

def SurrogateDiagonalTailChunk001Sub001Block119Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29613
    = surrogateDiagTailX0RatChunk001Sub001Block119Part001

theorem surrogateDiagonalTailChunk001Sub001Block119Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part001] using hcert

def TailChunk001Sub001Block119Part002SupportExplicit : Finset ℕ :=
  ([29614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part002 : ℚ :=
  (10549175218375 : ℚ) / 64477399895431446528

def SurrogateDiagonalTailChunk001Sub001Block119Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29614
    = surrogateDiagTailX0RatChunk001Sub001Block119Part002

theorem surrogateDiagonalTailChunk001Sub001Block119Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part002] using hcert

def TailChunk001Sub001Block119Part003SupportExplicit : Finset ℕ :=
  ([29615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part003 : ℚ :=
  (730652796875 : ℚ) / 16402090319005458816

def SurrogateDiagonalTailChunk001Sub001Block119Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29615
    = surrogateDiagTailX0RatChunk001Sub001Block119Part003

theorem surrogateDiagonalTailChunk001Sub001Block119Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part003] using hcert

def TailChunk001Sub001Block119Part004SupportExplicit : Finset ℕ :=
  ([29617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part004 : ℚ :=
  (178937297113 : ℚ) / 4611166582810780800

def SurrogateDiagonalTailChunk001Sub001Block119Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29617
    = surrogateDiagTailX0RatChunk001Sub001Block119Part004

theorem surrogateDiagonalTailChunk001Sub001Block119Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part004] using hcert

def TailChunk001Sub001Block119Part005SupportExplicit : Finset ℕ :=
  ([29618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part005 : ℚ :=
  (176403918633 : ℚ) / 1473796783750000000

def SurrogateDiagonalTailChunk001Sub001Block119Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29618
    = surrogateDiagTailX0RatChunk001Sub001Block119Part005

theorem surrogateDiagonalTailChunk001Sub001Block119Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part005] using hcert

def TailChunk001Sub001Block119Part006SupportExplicit : Finset ℕ :=
  ([29621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part006 : ℚ :=
  (1030526158225 : ℚ) / 32221477824065300376

def SurrogateDiagonalTailChunk001Sub001Block119Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29621
    = surrogateDiagTailX0RatChunk001Sub001Block119Part006

theorem surrogateDiagonalTailChunk001Sub001Block119Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part006] using hcert

def TailChunk001Sub001Block119Part007SupportExplicit : Finset ℕ :=
  ([29622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part007 : ℚ :=
  (6091648506325 : ℚ) / 23749115829279817728

def SurrogateDiagonalTailChunk001Sub001Block119Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29622
    = surrogateDiagTailX0RatChunk001Sub001Block119Part007

theorem surrogateDiagonalTailChunk001Sub001Block119Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part007] using hcert

def TailChunk001Sub001Block119Part008SupportExplicit : Finset ℕ :=
  ([29623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part008 : ℚ :=
  (22875379937 : ℚ) / 656594265525786240

def SurrogateDiagonalTailChunk001Sub001Block119Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29623
    = surrogateDiagTailX0RatChunk001Sub001Block119Part008

theorem surrogateDiagonalTailChunk001Sub001Block119Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part008] using hcert

def TailChunk001Sub001Block119Part009SupportExplicit : Finset ℕ :=
  ([29626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part009 : ℚ :=
  (3428515140625 : ℚ) / 30089964895170069792

def SurrogateDiagonalTailChunk001Sub001Block119Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29626
    = surrogateDiagTailX0RatChunk001Sub001Block119Part009

theorem surrogateDiagonalTailChunk001Sub001Block119Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part009] using hcert

def TailChunk001Sub001Block119Part010SupportExplicit : Finset ℕ :=
  ([29627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part010 : ℚ :=
  (777333293075 : ℚ) / 21065625163943313408

def SurrogateDiagonalTailChunk001Sub001Block119Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29627
    = surrogateDiagTailX0RatChunk001Sub001Block119Part010

theorem surrogateDiagonalTailChunk001Sub001Block119Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part010] using hcert

def TailChunk001Sub001Block119Part011SupportExplicit : Finset ℕ :=
  ([29629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part011 : ℚ :=
  (13716838140625 : ℚ) / 481699517694643206432

def SurrogateDiagonalTailChunk001Sub001Block119Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29629
    = surrogateDiagTailX0RatChunk001Sub001Block119Part011

theorem surrogateDiagonalTailChunk001Sub001Block119Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part011] using hcert

def TailChunk001Sub001Block119Part012SupportExplicit : Finset ℕ :=
  ([29630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part012 : ℚ :=
  (9323912004025 : ℚ) / 49272777142438545408

def SurrogateDiagonalTailChunk001Sub001Block119Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29630
    = surrogateDiagTailX0RatChunk001Sub001Block119Part012

theorem surrogateDiagonalTailChunk001Sub001Block119Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part012] using hcert

def TailChunk001Sub001Block119Part013SupportExplicit : Finset ℕ :=
  ([29631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part013 : ℚ :=
  (16017023608075 : ℚ) / 153633945267782811648

def SurrogateDiagonalTailChunk001Sub001Block119Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29631
    = surrogateDiagTailX0RatChunk001Sub001Block119Part013

theorem surrogateDiagonalTailChunk001Sub001Block119Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part013] using hcert

def TailChunk001Sub001Block119Part014SupportExplicit : Finset ℕ :=
  ([29633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part014 : ℚ :=
  (13720542015625 : ℚ) / 481959702425839337472

def SurrogateDiagonalTailChunk001Sub001Block119Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29633
    = surrogateDiagTailX0RatChunk001Sub001Block119Part014

theorem surrogateDiagonalTailChunk001Sub001Block119Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part014] using hcert

def TailChunk001Sub001Block119Part015SupportExplicit : Finset ℕ :=
  ([29634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part015 : ℚ :=
  (208965451207 : ℚ) / 644642432561971200

def SurrogateDiagonalTailChunk001Sub001Block119Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29634
    = surrogateDiagTailX0RatChunk001Sub001Block119Part015

theorem surrogateDiagonalTailChunk001Sub001Block119Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part015] using hcert

def TailChunk001Sub001Block119Part016SupportExplicit : Finset ℕ :=
  ([29635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part016 : ℚ :=
  (2194920390625 : ℚ) / 49339350721387924608

def SurrogateDiagonalTailChunk001Sub001Block119Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29635
    = surrogateDiagTailX0RatChunk001Sub001Block119Part016

theorem surrogateDiagonalTailChunk001Sub001Block119Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part016] using hcert

def TailChunk001Sub001Block119Part017SupportExplicit : Finset ℕ :=
  ([29638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part017 : ℚ :=
  (9572120885875 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk001Sub001Block119Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29638
    = surrogateDiagTailX0RatChunk001Sub001Block119Part017

theorem surrogateDiagonalTailChunk001Sub001Block119Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part017] using hcert

def TailChunk001Sub001Block119Part018SupportExplicit : Finset ℕ :=
  ([29639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part018 : ℚ :=
  (13402821702175 : ℚ) / 457959061690153062912

def SurrogateDiagonalTailChunk001Sub001Block119Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29639
    = surrogateDiagTailX0RatChunk001Sub001Block119Part018

theorem surrogateDiagonalTailChunk001Sub001Block119Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part018] using hcert

def TailChunk001Sub001Block119Part019SupportExplicit : Finset ℕ :=
  ([29641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part019 : ℚ :=
  (21964722025 : ℚ) / 771968620927775232

def SurrogateDiagonalTailChunk001Sub001Block119Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29641
    = surrogateDiagTailX0RatChunk001Sub001Block119Part019

theorem surrogateDiagonalTailChunk001Sub001Block119Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part019] using hcert

def TailChunk001Sub001Block119Part020SupportExplicit : Finset ℕ :=
  ([29642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part020 : ℚ :=
  (5491551025 : ℚ) / 48248038807985952

def SurrogateDiagonalTailChunk001Sub001Block119Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29642
    = surrogateDiagTailX0RatChunk001Sub001Block119Part020

theorem surrogateDiagonalTailChunk001Sub001Block119Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part020] using hcert

def TailChunk001Sub001Block119Part021SupportExplicit : Finset ℕ :=
  ([29643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part021 : ℚ :=
  (928037022493 : ℚ) / 13592262868992000000

def SurrogateDiagonalTailChunk001Sub001Block119Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29643
    = surrogateDiagTailX0RatChunk001Sub001Block119Part021

theorem surrogateDiagonalTailChunk001Sub001Block119Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part021] using hcert

def TailChunk001Sub001Block119Part022SupportExplicit : Finset ℕ :=
  ([29647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part022 : ℚ :=
  (8417256210525 : ℚ) / 268676562914243821568

def SurrogateDiagonalTailChunk001Sub001Block119Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29647
    = surrogateDiagTailX0RatChunk001Sub001Block119Part022

theorem surrogateDiagonalTailChunk001Sub001Block119Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part022] using hcert

def TailChunk001Sub001Block119Part023SupportExplicit : Finset ℕ :=
  ([29649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part023 : ℚ :=
  (24414105011725 : ℚ) / 381527845214891822208

def SurrogateDiagonalTailChunk001Sub001Block119Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29649
    = surrogateDiagTailX0RatChunk001Sub001Block119Part023

theorem surrogateDiagonalTailChunk001Sub001Block119Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part023] using hcert

def TailChunk001Sub001Block119Part024SupportExplicit : Finset ℕ :=
  ([29651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block119Part024 : ℚ :=
  (53777751584575 : ℚ) / 1843887760397669910528

def SurrogateDiagonalTailChunk001Sub001Block119Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29651
    = surrogateDiagTailX0RatChunk001Sub001Block119Part024

theorem surrogateDiagonalTailChunk001Sub001Block119Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block119Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block119Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block119Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block119Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block119Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block119Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block119HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block119Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block119Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block119Part000
    + surrogateDiagTailX0RatChunk001Sub001Block119Part001
    + surrogateDiagTailX0RatChunk001Sub001Block119Part002
    + surrogateDiagTailX0RatChunk001Sub001Block119Part003
    + surrogateDiagTailX0RatChunk001Sub001Block119Part004
    + surrogateDiagTailX0RatChunk001Sub001Block119Part005
    + surrogateDiagTailX0RatChunk001Sub001Block119Part006
    + surrogateDiagTailX0RatChunk001Sub001Block119Part007
    + surrogateDiagTailX0RatChunk001Sub001Block119Part008
    + surrogateDiagTailX0RatChunk001Sub001Block119Part009

def surrogateDiagonalTailChunk001Sub001Block119MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block119Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block119Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block119Part010
    + surrogateDiagTailX0RatChunk001Sub001Block119Part011
    + surrogateDiagTailX0RatChunk001Sub001Block119Part012
    + surrogateDiagTailX0RatChunk001Sub001Block119Part013
    + surrogateDiagTailX0RatChunk001Sub001Block119Part014
    + surrogateDiagTailX0RatChunk001Sub001Block119Part015
    + surrogateDiagTailX0RatChunk001Sub001Block119Part016
    + surrogateDiagTailX0RatChunk001Sub001Block119Part017
    + surrogateDiagTailX0RatChunk001Sub001Block119Part018
    + surrogateDiagTailX0RatChunk001Sub001Block119Part019

def surrogateDiagonalTailChunk001Sub001Block119TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block119Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block119Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block119Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block119Part020
    + surrogateDiagTailX0RatChunk001Sub001Block119Part021
    + surrogateDiagTailX0RatChunk001Sub001Block119Part022
    + surrogateDiagTailX0RatChunk001Sub001Block119Part023
    + surrogateDiagTailX0RatChunk001Sub001Block119Part024

def surrogateDiagonalTailChunk001Sub001Block119Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block119HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block119MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block119TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block119 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block119Part000
    + surrogateDiagTailX0RatChunk001Sub001Block119Part001
    + surrogateDiagTailX0RatChunk001Sub001Block119Part002
    + surrogateDiagTailX0RatChunk001Sub001Block119Part003
    + surrogateDiagTailX0RatChunk001Sub001Block119Part004
    + surrogateDiagTailX0RatChunk001Sub001Block119Part005
    + surrogateDiagTailX0RatChunk001Sub001Block119Part006
    + surrogateDiagTailX0RatChunk001Sub001Block119Part007
    + surrogateDiagTailX0RatChunk001Sub001Block119Part008
    + surrogateDiagTailX0RatChunk001Sub001Block119Part009
    + surrogateDiagTailX0RatChunk001Sub001Block119Part010
    + surrogateDiagTailX0RatChunk001Sub001Block119Part011
    + surrogateDiagTailX0RatChunk001Sub001Block119Part012
    + surrogateDiagTailX0RatChunk001Sub001Block119Part013
    + surrogateDiagTailX0RatChunk001Sub001Block119Part014
    + surrogateDiagTailX0RatChunk001Sub001Block119Part015
    + surrogateDiagTailX0RatChunk001Sub001Block119Part016
    + surrogateDiagTailX0RatChunk001Sub001Block119Part017
    + surrogateDiagTailX0RatChunk001Sub001Block119Part018
    + surrogateDiagTailX0RatChunk001Sub001Block119Part019
    + surrogateDiagTailX0RatChunk001Sub001Block119Part020
    + surrogateDiagTailX0RatChunk001Sub001Block119Part021
    + surrogateDiagTailX0RatChunk001Sub001Block119Part022
    + surrogateDiagTailX0RatChunk001Sub001Block119Part023
    + surrogateDiagTailX0RatChunk001Sub001Block119Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block119_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block119Head + surrogateDiagTailX0RatChunk001Sub001Block119Mid + surrogateDiagTailX0RatChunk001Sub001Block119Tail =
      surrogateDiagTailX0RatChunk001Sub001Block119 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block119Head surrogateDiagTailX0RatChunk001Sub001Block119Mid surrogateDiagTailX0RatChunk001Sub001Block119Tail surrogateDiagTailX0RatChunk001Sub001Block119
  ring

def SurrogateDiagonalTailChunk001Sub001Block119HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block119HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block119Head

def SurrogateDiagonalTailChunk001Sub001Block119MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block119MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block119Mid

def SurrogateDiagonalTailChunk001Sub001Block119TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block119TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block119Tail

theorem surrogateDiagonalTailChunk001Sub001Block119_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block119HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block119MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block119TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block119Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block119 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block119HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block119MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block119TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block119Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block119_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
