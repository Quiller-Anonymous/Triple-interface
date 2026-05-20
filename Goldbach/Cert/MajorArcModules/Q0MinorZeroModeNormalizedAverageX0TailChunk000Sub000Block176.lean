import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [176,177). -/

/-- Block 176 covers tail-support indices [4400,4425) and q from 7291 to 7330. -/

def TailChunk000Sub000Block176Part000SupportExplicit : Finset ℕ :=
  ([7291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part000 : ℚ :=
  (32517220575 : ℚ) / 60840766885139648

def SurrogateDiagonalTailChunk000Sub000Block176Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7291
    = surrogateDiagTailX0RatChunk000Sub000Block176Part000

theorem surrogateDiagonalTailChunk000Sub000Block176Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part000] using hcert

def TailChunk000Sub000Block176Part001SupportExplicit : Finset ℕ :=
  ([7293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part001 : ℚ :=
  (55965245563 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub000Block176Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7293
    = surrogateDiagTailX0RatChunk000Sub000Block176Part001

theorem surrogateDiagonalTailChunk000Sub000Block176Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part001] using hcert

def TailChunk000Sub000Block176Part002SupportExplicit : Finset ℕ :=
  ([7294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part002 : ℚ :=
  (3388860797 : ℚ) / 1053083278540800

def SurrogateDiagonalTailChunk000Sub000Block176Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7294
    = surrogateDiagTailX0RatChunk000Sub000Block176Part002

theorem surrogateDiagonalTailChunk000Sub000Block176Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part002] using hcert

def TailChunk000Sub000Block176Part003SupportExplicit : Finset ℕ :=
  ([7295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part003 : ℚ :=
  (105253050775 : ℚ) / 120527369552339712

def SurrogateDiagonalTailChunk000Sub000Block176Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7295
    = surrogateDiagTailX0RatChunk000Sub000Block176Part003

theorem surrogateDiagonalTailChunk000Sub000Block176Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part003] using hcert

def TailChunk000Sub000Block176Part004SupportExplicit : Finset ℕ :=
  ([7297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part004 : ℚ :=
  (831972015625 : ℚ) / 1771357289349906432

def SurrogateDiagonalTailChunk000Sub000Block176Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7297
    = surrogateDiagTailX0RatChunk000Sub000Block176Part004

theorem surrogateDiagonalTailChunk000Sub000Block176Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part004] using hcert

def TailChunk000Sub000Block176Part005SupportExplicit : Finset ℕ :=
  ([7298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part005 : ℚ :=
  (10853904477 : ℚ) / 5118423885414400

def SurrogateDiagonalTailChunk000Sub000Block176Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7298
    = surrogateDiagTailX0RatChunk000Sub000Block176Part005

theorem surrogateDiagonalTailChunk000Sub000Block176Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part005] using hcert

def TailChunk000Sub000Block176Part006SupportExplicit : Finset ℕ :=
  ([7302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part006 : ℚ :=
  (462447701225 : ℚ) / 43737217020985344

def SurrogateDiagonalTailChunk000Sub000Block176Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7302
    = surrogateDiagTailX0RatChunk000Sub000Block176Part006

theorem surrogateDiagonalTailChunk000Sub000Block176Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part006] using hcert

def TailChunk000Sub000Block176Part007SupportExplicit : Finset ℕ :=
  ([7303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part007 : ℚ :=
  (22426126325 : ℚ) / 44826530956048512

def SurrogateDiagonalTailChunk000Sub000Block176Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7303
    = surrogateDiagTailX0RatChunk000Sub000Block176Part007

theorem surrogateDiagonalTailChunk000Sub000Block176Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part007] using hcert

def TailChunk000Sub000Block176Part008SupportExplicit : Finset ℕ :=
  ([7305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part008 : ℚ :=
  (695158160675 : ℚ) / 285694505605545984

def SurrogateDiagonalTailChunk000Sub000Block176Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7305
    = surrogateDiagTailX0RatChunk000Sub000Block176Part008

theorem surrogateDiagonalTailChunk000Sub000Block176Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part008] using hcert

def TailChunk000Sub000Block176Part009SupportExplicit : Finset ℕ :=
  ([7306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part009 : ℚ :=
  (4978567409 : ℚ) / 1062337993113600

def SurrogateDiagonalTailChunk000Sub000Block176Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7306
    = surrogateDiagTailX0RatChunk000Sub000Block176Part009

theorem surrogateDiagonalTailChunk000Sub000Block176Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part009] using hcert

def TailChunk000Sub000Block176Part010SupportExplicit : Finset ℕ :=
  ([7307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part010 : ℚ :=
  (834253890625 : ℚ) / 1781088662095928562

def SurrogateDiagonalTailChunk000Sub000Block176Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7307
    = surrogateDiagTailX0RatChunk000Sub000Block176Part010

theorem surrogateDiagonalTailChunk000Sub000Block176Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part010] using hcert

def TailChunk000Sub000Block176Part011SupportExplicit : Finset ℕ :=
  ([7309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part011 : ℚ :=
  (834710640625 : ℚ) / 1783039738086849312

def SurrogateDiagonalTailChunk000Sub000Block176Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7309
    = surrogateDiagTailX0RatChunk000Sub000Block176Part011

theorem surrogateDiagonalTailChunk000Sub000Block176Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part011] using hcert

def TailChunk000Sub000Block176Part012SupportExplicit : Finset ℕ :=
  ([7310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part012 : ℚ :=
  (79337494925 : ℚ) / 9324292328128512

def SurrogateDiagonalTailChunk000Sub000Block176Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7310
    = surrogateDiagTailX0RatChunk000Sub000Block176Part012

theorem surrogateDiagonalTailChunk000Sub000Block176Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part012] using hcert

def TailChunk000Sub000Block176Part013SupportExplicit : Finset ℕ :=
  ([7311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part013 : ℚ :=
  (927663290675 : ℚ) / 704410760725668864

def SurrogateDiagonalTailChunk000Sub000Block176Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7311
    = surrogateDiagTailX0RatChunk000Sub000Block176Part013

theorem surrogateDiagonalTailChunk000Sub000Block176Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part013] using hcert

def TailChunk000Sub000Block176Part014SupportExplicit : Finset ℕ :=
  ([7313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part014 : ℚ :=
  (7197330877 : ℚ) / 14441330000462400

def SurrogateDiagonalTailChunk000Sub000Block176Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7313
    = surrogateDiagTailX0RatChunk000Sub000Block176Part014

theorem surrogateDiagonalTailChunk000Sub000Block176Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part014] using hcert

def TailChunk000Sub000Block176Part015SupportExplicit : Finset ℕ :=
  ([7314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part015 : ℚ :=
  (215507851375 : ℚ) / 17131324756795392

def SurrogateDiagonalTailChunk000Sub000Block176Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7314
    = surrogateDiagTailX0RatChunk000Sub000Block176Part015

theorem surrogateDiagonalTailChunk000Sub000Block176Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part015] using hcert

def TailChunk000Sub000Block176Part016SupportExplicit : Finset ℕ :=
  ([7315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part016 : ℚ :=
  (23123986127 : ℚ) / 11611827693158400

def SurrogateDiagonalTailChunk000Sub000Block176Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7315
    = surrogateDiagTailX0RatChunk000Sub000Block176Part016

theorem surrogateDiagonalTailChunk000Sub000Block176Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part016] using hcert

def TailChunk000Sub000Block176Part017SupportExplicit : Finset ℕ :=
  ([7318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part017 : ℚ :=
  (1673200417975 : ℚ) / 447715019022024648

def SurrogateDiagonalTailChunk000Sub000Block176Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7318
    = surrogateDiagTailX0RatChunk000Sub000Block176Part017

theorem surrogateDiagonalTailChunk000Sub000Block176Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part017] using hcert

def TailChunk000Sub000Block176Part018SupportExplicit : Finset ℕ :=
  ([7319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part018 : ℚ :=
  (10090831825 : ℚ) / 323278723584793728

def SurrogateDiagonalTailChunk000Sub000Block176Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7319
    = surrogateDiagTailX0RatChunk000Sub000Block176Part018

theorem surrogateDiagonalTailChunk000Sub000Block176Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part018] using hcert

def TailChunk000Sub000Block176Part019SupportExplicit : Finset ℕ :=
  ([7321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block176Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7321
    = surrogateDiagTailX0RatChunk000Sub000Block176Part019

theorem surrogateDiagonalTailChunk000Sub000Block176Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part019] using hcert

def TailChunk000Sub000Block176Part020SupportExplicit : Finset ℕ :=
  ([7322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part020 : ℚ :=
  (751339329925 : ℚ) / 240610110429045888

def SurrogateDiagonalTailChunk000Sub000Block176Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7322
    = surrogateDiagTailX0RatChunk000Sub000Block176Part020

theorem surrogateDiagonalTailChunk000Sub000Block176Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part020] using hcert

def TailChunk000Sub000Block176Part021SupportExplicit : Finset ℕ :=
  ([7323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part021 : ℚ :=
  (244156079 : ℚ) / 464950059417600

def SurrogateDiagonalTailChunk000Sub000Block176Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7323
    = surrogateDiagTailX0RatChunk000Sub000Block176Part021

theorem surrogateDiagonalTailChunk000Sub000Block176Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part021] using hcert

def TailChunk000Sub000Block176Part022SupportExplicit : Finset ℕ :=
  ([7327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part022 : ℚ :=
  (329655163 : ℚ) / 14006209577779200

def SurrogateDiagonalTailChunk000Sub000Block176Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7327
    = surrogateDiagTailX0RatChunk000Sub000Block176Part022

theorem surrogateDiagonalTailChunk000Sub000Block176Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part022] using hcert

def TailChunk000Sub000Block176Part023SupportExplicit : Finset ℕ :=
  ([7329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part023 : ℚ :=
  (27884508775 : ℚ) / 28164695139385344

def SurrogateDiagonalTailChunk000Sub000Block176Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7329
    = surrogateDiagTailX0RatChunk000Sub000Block176Part023

theorem surrogateDiagonalTailChunk000Sub000Block176Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part023] using hcert

def TailChunk000Sub000Block176Part024SupportExplicit : Finset ℕ :=
  ([7330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block176Part024 : ℚ :=
  (704652801625 : ℚ) / 183785459486588928

def SurrogateDiagonalTailChunk000Sub000Block176Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7330
    = surrogateDiagTailX0RatChunk000Sub000Block176Part024

theorem surrogateDiagonalTailChunk000Sub000Block176Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block176Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block176Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block176Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block176Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block176Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block176Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block176HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block176Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block176Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block176Part000
    + surrogateDiagTailX0RatChunk000Sub000Block176Part001
    + surrogateDiagTailX0RatChunk000Sub000Block176Part002
    + surrogateDiagTailX0RatChunk000Sub000Block176Part003
    + surrogateDiagTailX0RatChunk000Sub000Block176Part004
    + surrogateDiagTailX0RatChunk000Sub000Block176Part005
    + surrogateDiagTailX0RatChunk000Sub000Block176Part006
    + surrogateDiagTailX0RatChunk000Sub000Block176Part007
    + surrogateDiagTailX0RatChunk000Sub000Block176Part008
    + surrogateDiagTailX0RatChunk000Sub000Block176Part009

def surrogateDiagonalTailChunk000Sub000Block176MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block176Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block176Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block176Part010
    + surrogateDiagTailX0RatChunk000Sub000Block176Part011
    + surrogateDiagTailX0RatChunk000Sub000Block176Part012
    + surrogateDiagTailX0RatChunk000Sub000Block176Part013
    + surrogateDiagTailX0RatChunk000Sub000Block176Part014
    + surrogateDiagTailX0RatChunk000Sub000Block176Part015
    + surrogateDiagTailX0RatChunk000Sub000Block176Part016
    + surrogateDiagTailX0RatChunk000Sub000Block176Part017
    + surrogateDiagTailX0RatChunk000Sub000Block176Part018
    + surrogateDiagTailX0RatChunk000Sub000Block176Part019

def surrogateDiagonalTailChunk000Sub000Block176TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block176Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block176Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block176Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block176Part020
    + surrogateDiagTailX0RatChunk000Sub000Block176Part021
    + surrogateDiagTailX0RatChunk000Sub000Block176Part022
    + surrogateDiagTailX0RatChunk000Sub000Block176Part023
    + surrogateDiagTailX0RatChunk000Sub000Block176Part024

def surrogateDiagonalTailChunk000Sub000Block176Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block176HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block176MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block176TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block176 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block176Part000
    + surrogateDiagTailX0RatChunk000Sub000Block176Part001
    + surrogateDiagTailX0RatChunk000Sub000Block176Part002
    + surrogateDiagTailX0RatChunk000Sub000Block176Part003
    + surrogateDiagTailX0RatChunk000Sub000Block176Part004
    + surrogateDiagTailX0RatChunk000Sub000Block176Part005
    + surrogateDiagTailX0RatChunk000Sub000Block176Part006
    + surrogateDiagTailX0RatChunk000Sub000Block176Part007
    + surrogateDiagTailX0RatChunk000Sub000Block176Part008
    + surrogateDiagTailX0RatChunk000Sub000Block176Part009
    + surrogateDiagTailX0RatChunk000Sub000Block176Part010
    + surrogateDiagTailX0RatChunk000Sub000Block176Part011
    + surrogateDiagTailX0RatChunk000Sub000Block176Part012
    + surrogateDiagTailX0RatChunk000Sub000Block176Part013
    + surrogateDiagTailX0RatChunk000Sub000Block176Part014
    + surrogateDiagTailX0RatChunk000Sub000Block176Part015
    + surrogateDiagTailX0RatChunk000Sub000Block176Part016
    + surrogateDiagTailX0RatChunk000Sub000Block176Part017
    + surrogateDiagTailX0RatChunk000Sub000Block176Part018
    + surrogateDiagTailX0RatChunk000Sub000Block176Part019
    + surrogateDiagTailX0RatChunk000Sub000Block176Part020
    + surrogateDiagTailX0RatChunk000Sub000Block176Part021
    + surrogateDiagTailX0RatChunk000Sub000Block176Part022
    + surrogateDiagTailX0RatChunk000Sub000Block176Part023
    + surrogateDiagTailX0RatChunk000Sub000Block176Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block176_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block176Head + surrogateDiagTailX0RatChunk000Sub000Block176Mid + surrogateDiagTailX0RatChunk000Sub000Block176Tail =
      surrogateDiagTailX0RatChunk000Sub000Block176 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block176Head surrogateDiagTailX0RatChunk000Sub000Block176Mid surrogateDiagTailX0RatChunk000Sub000Block176Tail surrogateDiagTailX0RatChunk000Sub000Block176
  ring

def SurrogateDiagonalTailChunk000Sub000Block176HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block176HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block176Head

def SurrogateDiagonalTailChunk000Sub000Block176MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block176MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block176Mid

def SurrogateDiagonalTailChunk000Sub000Block176TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block176TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block176Tail

theorem surrogateDiagonalTailChunk000Sub000Block176_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block176HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block176MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block176TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block176Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block176 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block176HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block176MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block176TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block176Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block176_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
