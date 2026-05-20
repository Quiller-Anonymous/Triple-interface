import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [6,7). -/

/-- Block 006 covers tail-support indices [5150,5175) and q from 8519 to 8558. -/

def TailChunk000Sub001Block006Part000SupportExplicit : Finset ℕ :=
  ([8519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part000 : ℚ :=
  (200369462375 : ℚ) / 393634953188868096

def SurrogateDiagonalTailChunk000Sub001Block006Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8519
    = surrogateDiagTailX0RatChunk000Sub001Block006Part000

theorem surrogateDiagonalTailChunk000Sub001Block006Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part000] using hcert

def TailChunk000Sub001Block006Part001SupportExplicit : Finset ℕ :=
  ([8521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part001 : ℚ :=
  (1815186025 : ℚ) / 5270420045394432

def SurrogateDiagonalTailChunk000Sub001Block006Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8521
    = surrogateDiagTailX0RatChunk000Sub001Block006Part001

theorem surrogateDiagonalTailChunk000Sub001Block006Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part001] using hcert

def TailChunk000Sub001Block006Part002SupportExplicit : Finset ℕ :=
  ([8522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part002 : ℚ :=
  (453903025 : ℚ) / 329401252837152

def SurrogateDiagonalTailChunk000Sub001Block006Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8522
    = surrogateDiagTailX0RatChunk000Sub001Block006Part002

theorem surrogateDiagonalTailChunk000Sub001Block006Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part002] using hcert

def TailChunk000Sub001Block006Part003SupportExplicit : Finset ℕ :=
  ([8527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part003 : ℚ :=
  (1136089515625 : ℚ) / 3303301243168615122

def SurrogateDiagonalTailChunk000Sub001Block006Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8527
    = surrogateDiagTailX0RatChunk000Sub001Block006Part003

theorem surrogateDiagonalTailChunk000Sub001Block006Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part003] using hcert

def TailChunk000Sub001Block006Part004SupportExplicit : Finset ℕ :=
  ([8529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part004 : ℚ :=
  (315634995575 : ℚ) / 326251974633937296

def SurrogateDiagonalTailChunk000Sub001Block006Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8529
    = surrogateDiagTailX0RatChunk000Sub001Block006Part004

theorem surrogateDiagonalTailChunk000Sub001Block006Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part004] using hcert

def TailChunk000Sub001Block006Part005SupportExplicit : Finset ℕ :=
  ([8530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part005 : ℚ :=
  (954180306625 : ℚ) / 337306882905243648

def SurrogateDiagonalTailChunk000Sub001Block006Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8530
    = surrogateDiagTailX0RatChunk000Sub001Block006Part005

theorem surrogateDiagonalTailChunk000Sub001Block006Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part005] using hcert

def TailChunk000Sub001Block006Part006SupportExplicit : Finset ℕ :=
  ([8531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part006 : ℚ :=
  (16390525075 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub001Block006Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8531
    = surrogateDiagTailX0RatChunk000Sub001Block006Part006

theorem surrogateDiagonalTailChunk000Sub001Block006Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part006] using hcert

def TailChunk000Sub001Block006Part007SupportExplicit : Finset ℕ :=
  ([8533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part007 : ℚ :=
  (369199384025 : ℚ) / 616727691244634112

def SurrogateDiagonalTailChunk000Sub001Block006Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8533
    = surrogateDiagTailX0RatChunk000Sub001Block006Part007

theorem surrogateDiagonalTailChunk000Sub001Block006Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part007] using hcert

def TailChunk000Sub001Block006Part008SupportExplicit : Finset ℕ :=
  ([8534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part008 : ℚ :=
  (10755055087 : ℚ) / 6401280000000000

def SurrogateDiagonalTailChunk000Sub001Block006Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8534
    = surrogateDiagTailX0RatChunk000Sub001Block006Part008

theorem surrogateDiagonalTailChunk000Sub001Block006Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part008] using hcert

def TailChunk000Sub001Block006Part009SupportExplicit : Finset ℕ :=
  ([8535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part009 : ℚ :=
  (939009986975 : ℚ) / 533028160640385024

def SurrogateDiagonalTailChunk000Sub001Block006Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8535
    = surrogateDiagTailX0RatChunk000Sub001Block006Part009

theorem surrogateDiagonalTailChunk000Sub001Block006Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part009] using hcert

def TailChunk000Sub001Block006Part010SupportExplicit : Finset ℕ :=
  ([8537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part010 : ℚ :=
  (1138755765625 : ℚ) / 3318826072477757952

def SurrogateDiagonalTailChunk000Sub001Block006Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8537
    = surrogateDiagTailX0RatChunk000Sub001Block006Part010

theorem surrogateDiagonalTailChunk000Sub001Block006Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part010] using hcert

def TailChunk000Sub001Block006Part011SupportExplicit : Finset ℕ :=
  ([8538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part011 : ℚ :=
  (25296875 : ℚ) / 5451764937408

def SurrogateDiagonalTailChunk000Sub001Block006Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8538
    = surrogateDiagTailX0RatChunk000Sub001Block006Part011

theorem surrogateDiagonalTailChunk000Sub001Block006Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part011] using hcert

def TailChunk000Sub001Block006Part012SupportExplicit : Finset ℕ :=
  ([8539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part012 : ℚ :=
  (1139289390625 : ℚ) / 3321937593250926642

def SurrogateDiagonalTailChunk000Sub001Block006Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8539
    = surrogateDiagTailX0RatChunk000Sub001Block006Part012

theorem surrogateDiagonalTailChunk000Sub001Block006Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part012] using hcert

def TailChunk000Sub001Block006Part013SupportExplicit : Finset ℕ :=
  ([8542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part013 : ℚ :=
  (456036025 : ℚ) / 332505130138482

def SurrogateDiagonalTailChunk000Sub001Block006Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8542
    = surrogateDiagTailX0RatChunk000Sub001Block006Part013

theorem surrogateDiagonalTailChunk000Sub001Block006Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part013] using hcert

def TailChunk000Sub001Block006Part014SupportExplicit : Finset ℕ :=
  ([8543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part014 : ℚ :=
  (1140357015625 : ℚ) / 3328167197904322962

def SurrogateDiagonalTailChunk000Sub001Block006Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8543
    = surrogateDiagTailX0RatChunk000Sub001Block006Part014

theorem surrogateDiagonalTailChunk000Sub001Block006Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part014] using hcert

def TailChunk000Sub001Block006Part015SupportExplicit : Finset ℕ :=
  ([8545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part015 : ℚ :=
  (156365848425 : ℚ) / 259417335818518528

def SurrogateDiagonalTailChunk000Sub001Block006Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8545
    = surrogateDiagTailX0RatChunk000Sub001Block006Part015

theorem surrogateDiagonalTailChunk000Sub001Block006Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part015] using hcert

def TailChunk000Sub001Block006Part016SupportExplicit : Finset ℕ :=
  ([8546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part016 : ℚ :=
  (285289515625 : ℚ) / 208205330239660032

def SurrogateDiagonalTailChunk000Sub001Block006Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8546
    = surrogateDiagTailX0RatChunk000Sub001Block006Part016

theorem surrogateDiagonalTailChunk000Sub001Block006Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part016] using hcert

def TailChunk000Sub001Block006Part017SupportExplicit : Finset ℕ :=
  ([8547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part017 : ℚ :=
  (1466006977 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub001Block006Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8547
    = surrogateDiagTailX0RatChunk000Sub001Block006Part017

theorem surrogateDiagonalTailChunk000Sub001Block006Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part017] using hcert

def TailChunk000Sub001Block006Part018SupportExplicit : Finset ℕ :=
  ([8549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part018 : ℚ :=
  (4428664615225 : ℚ) / 12237225287161339008

def SurrogateDiagonalTailChunk000Sub001Block006Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8549
    = surrogateDiagTailX0RatChunk000Sub001Block006Part018

theorem surrogateDiagonalTailChunk000Sub001Block006Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part018] using hcert

def TailChunk000Sub001Block006Part019SupportExplicit : Finset ℕ :=
  ([8551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part019 : ℚ :=
  (4163677587925 : ℚ) / 10406906629194252288

def SurrogateDiagonalTailChunk000Sub001Block006Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8551
    = surrogateDiagTailX0RatChunk000Sub001Block006Part019

theorem surrogateDiagonalTailChunk000Sub001Block006Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part019] using hcert

def TailChunk000Sub001Block006Part020SupportExplicit : Finset ℕ :=
  ([8553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part020 : ℚ :=
  (6348280603 : ℚ) / 6598820125125000

def SurrogateDiagonalTailChunk000Sub001Block006Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8553
    = surrogateDiagTailX0RatChunk000Sub001Block006Part020

theorem surrogateDiagonalTailChunk000Sub001Block006Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part020] using hcert

def TailChunk000Sub001Block006Part021SupportExplicit : Finset ℕ :=
  ([8554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part021 : ℚ :=
  (395123442175 : ℚ) / 75219108182433792

def SurrogateDiagonalTailChunk000Sub001Block006Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8554
    = surrogateDiagTailX0RatChunk000Sub001Block006Part021

theorem surrogateDiagonalTailChunk000Sub001Block006Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part021] using hcert

def TailChunk000Sub001Block006Part022SupportExplicit : Finset ℕ :=
  ([8555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part022 : ℚ :=
  (1534467358175 : ℚ) / 2226285861058904064

def SurrogateDiagonalTailChunk000Sub001Block006Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8555
    = surrogateDiagTailX0RatChunk000Sub001Block006Part022

theorem surrogateDiagonalTailChunk000Sub001Block006Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part022] using hcert

def TailChunk000Sub001Block006Part023SupportExplicit : Finset ℕ :=
  ([8557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part023 : ℚ :=
  (244158937175 : ℚ) / 664373461885632576

def SurrogateDiagonalTailChunk000Sub001Block006Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8557
    = surrogateDiagTailX0RatChunk000Sub001Block006Part023

theorem surrogateDiagonalTailChunk000Sub001Block006Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part023] using hcert

def TailChunk000Sub001Block006Part024SupportExplicit : Finset ℕ :=
  ([8558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block006Part024 : ℚ :=
  (15909268061 : ℚ) / 4533605727037440

def SurrogateDiagonalTailChunk000Sub001Block006Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8558
    = surrogateDiagTailX0RatChunk000Sub001Block006Part024

theorem surrogateDiagonalTailChunk000Sub001Block006Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block006Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block006Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block006Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block006Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block006Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block006HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block006Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block006Part000
    + surrogateDiagTailX0RatChunk000Sub001Block006Part001
    + surrogateDiagTailX0RatChunk000Sub001Block006Part002
    + surrogateDiagTailX0RatChunk000Sub001Block006Part003
    + surrogateDiagTailX0RatChunk000Sub001Block006Part004
    + surrogateDiagTailX0RatChunk000Sub001Block006Part005
    + surrogateDiagTailX0RatChunk000Sub001Block006Part006
    + surrogateDiagTailX0RatChunk000Sub001Block006Part007
    + surrogateDiagTailX0RatChunk000Sub001Block006Part008
    + surrogateDiagTailX0RatChunk000Sub001Block006Part009

def surrogateDiagonalTailChunk000Sub001Block006MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block006Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block006Part010
    + surrogateDiagTailX0RatChunk000Sub001Block006Part011
    + surrogateDiagTailX0RatChunk000Sub001Block006Part012
    + surrogateDiagTailX0RatChunk000Sub001Block006Part013
    + surrogateDiagTailX0RatChunk000Sub001Block006Part014
    + surrogateDiagTailX0RatChunk000Sub001Block006Part015
    + surrogateDiagTailX0RatChunk000Sub001Block006Part016
    + surrogateDiagTailX0RatChunk000Sub001Block006Part017
    + surrogateDiagTailX0RatChunk000Sub001Block006Part018
    + surrogateDiagTailX0RatChunk000Sub001Block006Part019

def surrogateDiagonalTailChunk000Sub001Block006TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block006Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block006Part020
    + surrogateDiagTailX0RatChunk000Sub001Block006Part021
    + surrogateDiagTailX0RatChunk000Sub001Block006Part022
    + surrogateDiagTailX0RatChunk000Sub001Block006Part023
    + surrogateDiagTailX0RatChunk000Sub001Block006Part024

def surrogateDiagonalTailChunk000Sub001Block006Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block006HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block006MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block006TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block006 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block006Part000
    + surrogateDiagTailX0RatChunk000Sub001Block006Part001
    + surrogateDiagTailX0RatChunk000Sub001Block006Part002
    + surrogateDiagTailX0RatChunk000Sub001Block006Part003
    + surrogateDiagTailX0RatChunk000Sub001Block006Part004
    + surrogateDiagTailX0RatChunk000Sub001Block006Part005
    + surrogateDiagTailX0RatChunk000Sub001Block006Part006
    + surrogateDiagTailX0RatChunk000Sub001Block006Part007
    + surrogateDiagTailX0RatChunk000Sub001Block006Part008
    + surrogateDiagTailX0RatChunk000Sub001Block006Part009
    + surrogateDiagTailX0RatChunk000Sub001Block006Part010
    + surrogateDiagTailX0RatChunk000Sub001Block006Part011
    + surrogateDiagTailX0RatChunk000Sub001Block006Part012
    + surrogateDiagTailX0RatChunk000Sub001Block006Part013
    + surrogateDiagTailX0RatChunk000Sub001Block006Part014
    + surrogateDiagTailX0RatChunk000Sub001Block006Part015
    + surrogateDiagTailX0RatChunk000Sub001Block006Part016
    + surrogateDiagTailX0RatChunk000Sub001Block006Part017
    + surrogateDiagTailX0RatChunk000Sub001Block006Part018
    + surrogateDiagTailX0RatChunk000Sub001Block006Part019
    + surrogateDiagTailX0RatChunk000Sub001Block006Part020
    + surrogateDiagTailX0RatChunk000Sub001Block006Part021
    + surrogateDiagTailX0RatChunk000Sub001Block006Part022
    + surrogateDiagTailX0RatChunk000Sub001Block006Part023
    + surrogateDiagTailX0RatChunk000Sub001Block006Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block006_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block006Head + surrogateDiagTailX0RatChunk000Sub001Block006Mid + surrogateDiagTailX0RatChunk000Sub001Block006Tail =
      surrogateDiagTailX0RatChunk000Sub001Block006 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block006Head surrogateDiagTailX0RatChunk000Sub001Block006Mid surrogateDiagTailX0RatChunk000Sub001Block006Tail surrogateDiagTailX0RatChunk000Sub001Block006
  ring

def SurrogateDiagonalTailChunk000Sub001Block006HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block006HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block006Head

def SurrogateDiagonalTailChunk000Sub001Block006MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block006MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block006Mid

def SurrogateDiagonalTailChunk000Sub001Block006TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block006TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block006Tail

theorem surrogateDiagonalTailChunk000Sub001Block006_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block006HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block006MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block006TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block006Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block006 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block006HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block006MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block006TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block006Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block006_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
