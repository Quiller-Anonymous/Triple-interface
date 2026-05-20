import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [127,128). -/

/- Block 127 covers tail-support indices [3175,3200) and q from 5277 to 5314. -/

def TailChunk000Sub000Block127Part000SupportExplicit : Finset ℕ :=
  ([5277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part000 : ℚ :=
  (38652875 : ℚ) / 12735447784128

def SurrogateDiagonalTailChunk000Sub000Block127Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5277
    = surrogateDiagTailX0RatChunk000Sub000Block127Part000

theorem surrogateDiagonalTailChunk000Sub000Block127Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part000] using hcert

def TailChunk000Sub000Block127Part001SupportExplicit : Finset ℕ :=
  ([5278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part001 : ℚ :=
  (326505787775 : ℚ) / 20651850586128384

def SurrogateDiagonalTailChunk000Sub000Block127Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5278
    = surrogateDiagTailX0RatChunk000Sub000Block127Part001

theorem surrogateDiagonalTailChunk000Sub000Block127Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part001] using hcert

def TailChunk000Sub000Block127Part002SupportExplicit : Finset ℕ :=
  ([5279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part002 : ℚ :=
  (435435015625 : ℚ) / 485114673444392082

def SurrogateDiagonalTailChunk000Sub000Block127Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5279
    = surrogateDiagTailX0RatChunk000Sub000Block127Part002

theorem surrogateDiagonalTailChunk000Sub000Block127Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part002] using hcert

def TailChunk000Sub000Block127Part003SupportExplicit : Finset ℕ :=
  ([5281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part003 : ℚ :=
  (697224025 : ℚ) / 777360627597312

def SurrogateDiagonalTailChunk000Sub000Block127Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5281
    = surrogateDiagTailX0RatChunk000Sub000Block127Part003

theorem surrogateDiagonalTailChunk000Sub000Block127Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part003] using hcert

def TailChunk000Sub000Block127Part004SupportExplicit : Finset ℕ :=
  ([5282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part004 : ℚ :=
  (7569372425 : ℚ) / 881473924012896

def SurrogateDiagonalTailChunk000Sub000Block127Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5282
    = surrogateDiagTailX0RatChunk000Sub000Block127Part004

theorem surrogateDiagonalTailChunk000Sub000Block127Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part004] using hcert

def TailChunk000Sub000Block127Part005SupportExplicit : Finset ℕ :=
  ([5285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part005 : ℚ :=
  (22315510811 : ℚ) / 8399759616000000

def SurrogateDiagonalTailChunk000Sub000Block127Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5285
    = surrogateDiagTailX0RatChunk000Sub000Block127Part005

theorem surrogateDiagonalTailChunk000Sub000Block127Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part005] using hcert

def TailChunk000Sub000Block127Part006SupportExplicit : Finset ℕ :=
  ([5286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part006 : ℚ :=
  (930279 : ℚ) / 38380503040

def SurrogateDiagonalTailChunk000Sub000Block127Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5286
    = surrogateDiagTailX0RatChunk000Sub000Block127Part006

theorem surrogateDiagonalTailChunk000Sub000Block127Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part006] using hcert

def TailChunk000Sub000Block127Part007SupportExplicit : Finset ℕ :=
  ([5287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part007 : ℚ :=
  (32660006051 : ℚ) / 30267988515225600

def SurrogateDiagonalTailChunk000Sub000Block127Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5287
    = surrogateDiagTailX0RatChunk000Sub000Block127Part007

theorem surrogateDiagonalTailChunk000Sub000Block127Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part007] using hcert

def TailChunk000Sub000Block127Part008SupportExplicit : Finset ℕ :=
  ([5289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part008 : ℚ :=
  (443181685 : ℚ) / 127480559173632

def SurrogateDiagonalTailChunk000Sub000Block127Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5289
    = surrogateDiagTailX0RatChunk000Sub000Block127Part008

theorem surrogateDiagonalTailChunk000Sub000Block127Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part008] using hcert

def TailChunk000Sub000Block127Part009SupportExplicit : Finset ℕ :=
  ([5291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part009 : ℚ :=
  (11251737383 : ℚ) / 6967096615895040

def SurrogateDiagonalTailChunk000Sub000Block127Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5291
    = surrogateDiagTailX0RatChunk000Sub000Block127Part009

theorem surrogateDiagonalTailChunk000Sub000Block127Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part009] using hcert

def TailChunk000Sub000Block127Part010SupportExplicit : Finset ℕ :=
  ([5293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part010 : ℚ :=
  (106295875825 : ℚ) / 109764279032553288

def SurrogateDiagonalTailChunk000Sub000Block127Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5293
    = surrogateDiagTailX0RatChunk000Sub000Block127Part010

theorem surrogateDiagonalTailChunk000Sub000Block127Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part010] using hcert

def TailChunk000Sub000Block127Part011SupportExplicit : Finset ℕ :=
  ([5294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part011 : ℚ :=
  (875650959775 : ℚ) / 122570573542505928

def SurrogateDiagonalTailChunk000Sub000Block127Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5294
    = surrogateDiagTailX0RatChunk000Sub000Block127Part011

theorem surrogateDiagonalTailChunk000Sub000Block127Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part011] using hcert

def TailChunk000Sub000Block127Part012SupportExplicit : Finset ℕ :=
  ([5295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part012 : ℚ :=
  (900970626175 : ℚ) / 157237981759930368

def SurrogateDiagonalTailChunk000Sub000Block127Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5295
    = surrogateDiagTailX0RatChunk000Sub000Block127Part012

theorem surrogateDiagonalTailChunk000Sub000Block127Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part012] using hcert

def TailChunk000Sub000Block127Part013SupportExplicit : Finset ℕ :=
  ([5297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part013 : ℚ :=
  (438409515625 : ℚ) / 491766310647570432

def SurrogateDiagonalTailChunk000Sub000Block127Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5297
    = surrogateDiagTailX0RatChunk000Sub000Block127Part013

theorem surrogateDiagonalTailChunk000Sub000Block127Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part013] using hcert

def TailChunk000Sub000Block127Part014SupportExplicit : Finset ℕ :=
  ([5298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part014 : ℚ :=
  (535544530825 : ℚ) / 24211471317038208

def SurrogateDiagonalTailChunk000Sub000Block127Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5298
    = surrogateDiagTailX0RatChunk000Sub000Block127Part014

theorem surrogateDiagonalTailChunk000Sub000Block127Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part014] using hcert

def TailChunk000Sub000Block127Part015SupportExplicit : Finset ℕ :=
  ([5299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part015 : ℚ :=
  (3974746675 : ℚ) / 2800446256935936

def SurrogateDiagonalTailChunk000Sub000Block127Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5299
    = surrogateDiagTailX0RatChunk000Sub000Block127Part015

theorem surrogateDiagonalTailChunk000Sub000Block127Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part015] using hcert

def TailChunk000Sub000Block127Part016SupportExplicit : Finset ℕ :=
  ([5302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part016 : ℚ :=
  (3518541281 : ℚ) / 368713728000000

def SurrogateDiagonalTailChunk000Sub000Block127Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5302
    = surrogateDiagTailX0RatChunk000Sub000Block127Part016

theorem surrogateDiagonalTailChunk000Sub000Block127Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part016] using hcert

def TailChunk000Sub000Block127Part017SupportExplicit : Finset ℕ :=
  ([5303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part017 : ℚ :=
  (439403265625 : ℚ) / 493998648929801202

def SurrogateDiagonalTailChunk000Sub000Block127Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5303
    = surrogateDiagTailX0RatChunk000Sub000Block127Part017

theorem surrogateDiagonalTailChunk000Sub000Block127Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part017] using hcert

def TailChunk000Sub000Block127Part018SupportExplicit : Finset ℕ :=
  ([5305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part018 : ℚ :=
  (26715559037 : ℚ) / 16162937029017600

def SurrogateDiagonalTailChunk000Sub000Block127Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5305
    = surrogateDiagTailX0RatChunk000Sub000Block127Part018

theorem surrogateDiagonalTailChunk000Sub000Block127Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part018] using hcert

def TailChunk000Sub000Block127Part019SupportExplicit : Finset ℕ :=
  ([5306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part019 : ℚ :=
  (371613395975 : ℚ) / 33080271410055744

def SurrogateDiagonalTailChunk000Sub000Block127Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5306
    = surrogateDiagTailX0RatChunk000Sub000Block127Part019

theorem surrogateDiagonalTailChunk000Sub000Block127Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part019] using hcert

def TailChunk000Sub000Block127Part020SupportExplicit : Finset ℕ :=
  ([5307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part020 : ℚ :=
  (2962810507 : ℚ) / 849870394490880

def SurrogateDiagonalTailChunk000Sub000Block127Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5307
    = surrogateDiagTailX0RatChunk000Sub000Block127Part020

theorem surrogateDiagonalTailChunk000Sub000Block127Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part020] using hcert

def TailChunk000Sub000Block127Part021SupportExplicit : Finset ℕ :=
  ([5309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part021 : ℚ :=
  (440398140625 : ℚ) / 496238578756737312

def SurrogateDiagonalTailChunk000Sub000Block127Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5309
    = surrogateDiagTailX0RatChunk000Sub000Block127Part021

theorem surrogateDiagonalTailChunk000Sub000Block127Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part021] using hcert

def TailChunk000Sub000Block127Part022SupportExplicit : Finset ℕ :=
  ([5311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part022 : ℚ :=
  (243995744725 : ℚ) / 251670456153145344

def SurrogateDiagonalTailChunk000Sub000Block127Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5311
    = surrogateDiagTailX0RatChunk000Sub000Block127Part022

theorem surrogateDiagonalTailChunk000Sub000Block127Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part022] using hcert

def TailChunk000Sub000Block127Part023SupportExplicit : Finset ℕ :=
  ([5313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part023 : ℚ :=
  (4327893671 : ℚ) / 607312990310400

def SurrogateDiagonalTailChunk000Sub000Block127Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5313
    = surrogateDiagTailX0RatChunk000Sub000Block127Part023

theorem surrogateDiagonalTailChunk000Sub000Block127Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part023] using hcert

def TailChunk000Sub000Block127Part024SupportExplicit : Finset ℕ :=
  ([5314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block127Part024 : ℚ :=
  (882279633775 : ℚ) / 124434022830440448

def SurrogateDiagonalTailChunk000Sub000Block127Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5314
    = surrogateDiagTailX0RatChunk000Sub000Block127Part024

theorem surrogateDiagonalTailChunk000Sub000Block127Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block127Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block127Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block127Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block127Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block127Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block127Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block127HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block127Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block127Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block127Part000
    + surrogateDiagTailX0RatChunk000Sub000Block127Part001
    + surrogateDiagTailX0RatChunk000Sub000Block127Part002
    + surrogateDiagTailX0RatChunk000Sub000Block127Part003
    + surrogateDiagTailX0RatChunk000Sub000Block127Part004
    + surrogateDiagTailX0RatChunk000Sub000Block127Part005
    + surrogateDiagTailX0RatChunk000Sub000Block127Part006
    + surrogateDiagTailX0RatChunk000Sub000Block127Part007
    + surrogateDiagTailX0RatChunk000Sub000Block127Part008
    + surrogateDiagTailX0RatChunk000Sub000Block127Part009

def surrogateDiagonalTailChunk000Sub000Block127MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block127Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block127Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block127Part010
    + surrogateDiagTailX0RatChunk000Sub000Block127Part011
    + surrogateDiagTailX0RatChunk000Sub000Block127Part012
    + surrogateDiagTailX0RatChunk000Sub000Block127Part013
    + surrogateDiagTailX0RatChunk000Sub000Block127Part014
    + surrogateDiagTailX0RatChunk000Sub000Block127Part015
    + surrogateDiagTailX0RatChunk000Sub000Block127Part016
    + surrogateDiagTailX0RatChunk000Sub000Block127Part017
    + surrogateDiagTailX0RatChunk000Sub000Block127Part018
    + surrogateDiagTailX0RatChunk000Sub000Block127Part019

def surrogateDiagonalTailChunk000Sub000Block127TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block127Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block127Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block127Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block127Part020
    + surrogateDiagTailX0RatChunk000Sub000Block127Part021
    + surrogateDiagTailX0RatChunk000Sub000Block127Part022
    + surrogateDiagTailX0RatChunk000Sub000Block127Part023
    + surrogateDiagTailX0RatChunk000Sub000Block127Part024

def surrogateDiagonalTailChunk000Sub000Block127Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block127HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block127MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block127TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block127 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block127Part000
    + surrogateDiagTailX0RatChunk000Sub000Block127Part001
    + surrogateDiagTailX0RatChunk000Sub000Block127Part002
    + surrogateDiagTailX0RatChunk000Sub000Block127Part003
    + surrogateDiagTailX0RatChunk000Sub000Block127Part004
    + surrogateDiagTailX0RatChunk000Sub000Block127Part005
    + surrogateDiagTailX0RatChunk000Sub000Block127Part006
    + surrogateDiagTailX0RatChunk000Sub000Block127Part007
    + surrogateDiagTailX0RatChunk000Sub000Block127Part008
    + surrogateDiagTailX0RatChunk000Sub000Block127Part009
    + surrogateDiagTailX0RatChunk000Sub000Block127Part010
    + surrogateDiagTailX0RatChunk000Sub000Block127Part011
    + surrogateDiagTailX0RatChunk000Sub000Block127Part012
    + surrogateDiagTailX0RatChunk000Sub000Block127Part013
    + surrogateDiagTailX0RatChunk000Sub000Block127Part014
    + surrogateDiagTailX0RatChunk000Sub000Block127Part015
    + surrogateDiagTailX0RatChunk000Sub000Block127Part016
    + surrogateDiagTailX0RatChunk000Sub000Block127Part017
    + surrogateDiagTailX0RatChunk000Sub000Block127Part018
    + surrogateDiagTailX0RatChunk000Sub000Block127Part019
    + surrogateDiagTailX0RatChunk000Sub000Block127Part020
    + surrogateDiagTailX0RatChunk000Sub000Block127Part021
    + surrogateDiagTailX0RatChunk000Sub000Block127Part022
    + surrogateDiagTailX0RatChunk000Sub000Block127Part023
    + surrogateDiagTailX0RatChunk000Sub000Block127Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block127_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block127Head + surrogateDiagTailX0RatChunk000Sub000Block127Mid + surrogateDiagTailX0RatChunk000Sub000Block127Tail =
      surrogateDiagTailX0RatChunk000Sub000Block127 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block127Head surrogateDiagTailX0RatChunk000Sub000Block127Mid surrogateDiagTailX0RatChunk000Sub000Block127Tail surrogateDiagTailX0RatChunk000Sub000Block127
  ring

def SurrogateDiagonalTailChunk000Sub000Block127HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block127HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block127Head

def SurrogateDiagonalTailChunk000Sub000Block127MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block127MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block127Mid

def SurrogateDiagonalTailChunk000Sub000Block127TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block127TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block127Tail

theorem surrogateDiagonalTailChunk000Sub000Block127_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block127HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block127MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block127TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block127Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block127 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block127HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block127MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block127TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block127Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block127_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
