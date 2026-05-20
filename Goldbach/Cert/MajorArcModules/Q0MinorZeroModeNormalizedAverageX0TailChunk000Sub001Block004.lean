import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [4,5). -/

/-- Block 004 covers tail-support indices [5100,5125) and q from 8438 to 8481. -/

def TailChunk000Sub001Block004Part000SupportExplicit : Finset ℕ :=
  ([8438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part000 : ℚ :=
  (278124390625 : ℚ) / 197876021192390322

def SurrogateDiagonalTailChunk000Sub001Block004Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8438
    = surrogateDiagTailX0RatChunk000Sub001Block004Part000

theorem surrogateDiagonalTailChunk000Sub001Block004Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part000] using hcert

def TailChunk000Sub001Block004Part001SupportExplicit : Finset ℕ :=
  ([8439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part001 : ℚ :=
  (978467980075 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk000Sub001Block004Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8439
    = surrogateDiagTailX0RatChunk000Sub001Block004Part001

theorem surrogateDiagonalTailChunk000Sub001Block004Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part001] using hcert

def TailChunk000Sub001Block004Part002SupportExplicit : Finset ℕ :=
  ([8441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part002 : ℚ :=
  (123769984975 : ℚ) / 10510948876340423808

def SurrogateDiagonalTailChunk000Sub001Block004Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8441
    = surrogateDiagTailX0RatChunk000Sub001Block004Part002

theorem surrogateDiagonalTailChunk000Sub001Block004Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part002] using hcert

def TailChunk000Sub001Block004Part003SupportExplicit : Finset ℕ :=
  ([8443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block004Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8443
    = surrogateDiagTailX0RatChunk000Sub001Block004Part003

theorem surrogateDiagonalTailChunk000Sub001Block004Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part003] using hcert

def TailChunk000Sub001Block004Part004SupportExplicit : Finset ℕ :=
  ([8445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part004 : ℚ :=
  (290330046075 : ℚ) / 340573470114021376

def SurrogateDiagonalTailChunk000Sub001Block004Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8445
    = surrogateDiagTailX0RatChunk000Sub001Block004Part004

theorem surrogateDiagonalTailChunk000Sub001Block004Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part004] using hcert

def TailChunk000Sub001Block004Part005SupportExplicit : Finset ℕ :=
  ([8446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part005 : ℚ :=
  (10835739067 : ℚ) / 6928951337164800

def SurrogateDiagonalTailChunk000Sub001Block004Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8446
    = surrogateDiagTailX0RatChunk000Sub001Block004Part005

theorem surrogateDiagonalTailChunk000Sub001Block004Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part005] using hcert

def TailChunk000Sub001Block004Part006SupportExplicit : Finset ℕ :=
  ([8447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block004Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8447
    = surrogateDiagTailX0RatChunk000Sub001Block004Part006

theorem surrogateDiagonalTailChunk000Sub001Block004Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part006] using hcert

def TailChunk000Sub001Block004Part007SupportExplicit : Finset ℕ :=
  ([8449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part007 : ℚ :=
  (537943583 : ℚ) / 5827682705080320

def SurrogateDiagonalTailChunk000Sub001Block004Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8449
    = surrogateDiagTailX0RatChunk000Sub001Block004Part007

theorem surrogateDiagonalTailChunk000Sub001Block004Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part007] using hcert

def TailChunk000Sub001Block004Part008SupportExplicit : Finset ℕ :=
  ([8453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part008 : ℚ :=
  (56965515625 : ℚ) / 11685000376046095488

def SurrogateDiagonalTailChunk000Sub001Block004Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8453
    = surrogateDiagTailX0RatChunk000Sub001Block004Part008

theorem surrogateDiagonalTailChunk000Sub001Block004Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part008] using hcert

def TailChunk000Sub001Block004Part009SupportExplicit : Finset ℕ :=
  ([8454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part009 : ℚ :=
  (868101462025 : ℚ) / 157237981759930368

def SurrogateDiagonalTailChunk000Sub001Block004Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8454
    = surrogateDiagTailX0RatChunk000Sub001Block004Part009

theorem surrogateDiagonalTailChunk000Sub001Block004Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part009] using hcert

def TailChunk000Sub001Block004Part010SupportExplicit : Finset ℕ :=
  ([8455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part010 : ℚ :=
  (598503765775 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk000Sub001Block004Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8455
    = surrogateDiagTailX0RatChunk000Sub001Block004Part010

theorem surrogateDiagonalTailChunk000Sub001Block004Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part010] using hcert

def TailChunk000Sub001Block004Part011SupportExplicit : Finset ℕ :=
  ([8457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part011 : ℚ :=
  (496533407525 : ℚ) / 1261481253469053504

def SurrogateDiagonalTailChunk000Sub001Block004Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8457
    = surrogateDiagTailX0RatChunk000Sub001Block004Part011

theorem surrogateDiagonalTailChunk000Sub001Block004Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part011] using hcert

def TailChunk000Sub001Block004Part012SupportExplicit : Finset ℕ :=
  ([8458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part012 : ℚ :=
  (279444390625 : ℚ) / 199759196330656032

def SurrogateDiagonalTailChunk000Sub001Block004Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8458
    = surrogateDiagTailX0RatChunk000Sub001Block004Part012

theorem surrogateDiagonalTailChunk000Sub001Block004Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part012] using hcert

def TailChunk000Sub001Block004Part013SupportExplicit : Finset ℕ :=
  ([8459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part013 : ℚ :=
  (896359153 : ℚ) / 34796192944619520

def SurrogateDiagonalTailChunk000Sub001Block004Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8459
    = surrogateDiagTailX0RatChunk000Sub001Block004Part013

theorem surrogateDiagonalTailChunk000Sub001Block004Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part013] using hcert

def TailChunk000Sub001Block004Part014SupportExplicit : Finset ℕ :=
  ([8461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block004Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8461
    = surrogateDiagTailX0RatChunk000Sub001Block004Part014

theorem surrogateDiagonalTailChunk000Sub001Block004Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part014] using hcert

def TailChunk000Sub001Block004Part015SupportExplicit : Finset ℕ :=
  ([8462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part015 : ℚ :=
  (447534025 : ℚ) / 320219901584082

def SurrogateDiagonalTailChunk000Sub001Block004Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8462
    = surrogateDiagTailX0RatChunk000Sub001Block004Part015

theorem surrogateDiagonalTailChunk000Sub001Block004Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part015] using hcert

def TailChunk000Sub001Block004Part016SupportExplicit : Finset ℕ :=
  ([8463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part016 : ℚ :=
  (7300878083 : ℚ) / 6967096615895040

def SurrogateDiagonalTailChunk000Sub001Block004Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8463
    = surrogateDiagTailX0RatChunk000Sub001Block004Part016

theorem surrogateDiagonalTailChunk000Sub001Block004Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part016] using hcert

def TailChunk000Sub001Block004Part017SupportExplicit : Finset ℕ :=
  ([8465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part017 : ℚ :=
  (268911229475 : ℚ) / 2623241433776799744

def SurrogateDiagonalTailChunk000Sub001Block004Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8465
    = surrogateDiagTailX0RatChunk000Sub001Block004Part017

theorem surrogateDiagonalTailChunk000Sub001Block004Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part017] using hcert

def TailChunk000Sub001Block004Part018SupportExplicit : Finset ℕ :=
  ([8466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part018 : ℚ :=
  (70330575 : ℚ) / 11852100665344

def SurrogateDiagonalTailChunk000Sub001Block004Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8466
    = surrogateDiagTailX0RatChunk000Sub001Block004Part018

theorem surrogateDiagonalTailChunk000Sub001Block004Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part018] using hcert

def TailChunk000Sub001Block004Part019SupportExplicit : Finset ℕ :=
  ([8467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block004Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8467
    = surrogateDiagTailX0RatChunk000Sub001Block004Part019

theorem surrogateDiagonalTailChunk000Sub001Block004Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part019] using hcert

def TailChunk000Sub001Block004Part020SupportExplicit : Finset ℕ :=
  ([8471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part020 : ℚ :=
  (72935682775 : ℚ) / 11482813359448639488

def SurrogateDiagonalTailChunk000Sub001Block004Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8471
    = surrogateDiagTailX0RatChunk000Sub001Block004Part020

theorem surrogateDiagonalTailChunk000Sub001Block004Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part020] using hcert

def TailChunk000Sub001Block004Part021SupportExplicit : Finset ℕ :=
  ([8473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part021 : ℚ :=
  (2168836325 : ℚ) / 298670723052650496

def SurrogateDiagonalTailChunk000Sub001Block004Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8473
    = surrogateDiagTailX0RatChunk000Sub001Block004Part021

theorem surrogateDiagonalTailChunk000Sub001Block004Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part021] using hcert

def TailChunk000Sub001Block004Part022SupportExplicit : Finset ℕ :=
  ([8474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part022 : ℚ :=
  (33390459125 : ℚ) / 19924103944004004

def SurrogateDiagonalTailChunk000Sub001Block004Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8474
    = surrogateDiagTailX0RatChunk000Sub001Block004Part022

theorem surrogateDiagonalTailChunk000Sub001Block004Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part022] using hcert

def TailChunk000Sub001Block004Part023SupportExplicit : Finset ℕ :=
  ([8479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part023 : ℚ :=
  (9657349243 : ℚ) / 26117745896678400

def SurrogateDiagonalTailChunk000Sub001Block004Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8479
    = surrogateDiagTailX0RatChunk000Sub001Block004Part023

theorem surrogateDiagonalTailChunk000Sub001Block004Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part023] using hcert

def TailChunk000Sub001Block004Part024SupportExplicit : Finset ℕ :=
  ([8481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block004Part024 : ℚ :=
  (87424788241 : ℚ) / 68733220631347200

def SurrogateDiagonalTailChunk000Sub001Block004Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8481
    = surrogateDiagTailX0RatChunk000Sub001Block004Part024

theorem surrogateDiagonalTailChunk000Sub001Block004Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block004Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block004Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block004Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block004Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block004Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block004HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block004Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block004Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block004Part000
    + surrogateDiagTailX0RatChunk000Sub001Block004Part001
    + surrogateDiagTailX0RatChunk000Sub001Block004Part002
    + surrogateDiagTailX0RatChunk000Sub001Block004Part003
    + surrogateDiagTailX0RatChunk000Sub001Block004Part004
    + surrogateDiagTailX0RatChunk000Sub001Block004Part005
    + surrogateDiagTailX0RatChunk000Sub001Block004Part006
    + surrogateDiagTailX0RatChunk000Sub001Block004Part007
    + surrogateDiagTailX0RatChunk000Sub001Block004Part008
    + surrogateDiagTailX0RatChunk000Sub001Block004Part009

def surrogateDiagonalTailChunk000Sub001Block004MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block004Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block004Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block004Part010
    + surrogateDiagTailX0RatChunk000Sub001Block004Part011
    + surrogateDiagTailX0RatChunk000Sub001Block004Part012
    + surrogateDiagTailX0RatChunk000Sub001Block004Part013
    + surrogateDiagTailX0RatChunk000Sub001Block004Part014
    + surrogateDiagTailX0RatChunk000Sub001Block004Part015
    + surrogateDiagTailX0RatChunk000Sub001Block004Part016
    + surrogateDiagTailX0RatChunk000Sub001Block004Part017
    + surrogateDiagTailX0RatChunk000Sub001Block004Part018
    + surrogateDiagTailX0RatChunk000Sub001Block004Part019

def surrogateDiagonalTailChunk000Sub001Block004TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block004Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block004Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block004Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block004Part020
    + surrogateDiagTailX0RatChunk000Sub001Block004Part021
    + surrogateDiagTailX0RatChunk000Sub001Block004Part022
    + surrogateDiagTailX0RatChunk000Sub001Block004Part023
    + surrogateDiagTailX0RatChunk000Sub001Block004Part024

def surrogateDiagonalTailChunk000Sub001Block004Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block004HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block004MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block004TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block004 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block004Part000
    + surrogateDiagTailX0RatChunk000Sub001Block004Part001
    + surrogateDiagTailX0RatChunk000Sub001Block004Part002
    + surrogateDiagTailX0RatChunk000Sub001Block004Part003
    + surrogateDiagTailX0RatChunk000Sub001Block004Part004
    + surrogateDiagTailX0RatChunk000Sub001Block004Part005
    + surrogateDiagTailX0RatChunk000Sub001Block004Part006
    + surrogateDiagTailX0RatChunk000Sub001Block004Part007
    + surrogateDiagTailX0RatChunk000Sub001Block004Part008
    + surrogateDiagTailX0RatChunk000Sub001Block004Part009
    + surrogateDiagTailX0RatChunk000Sub001Block004Part010
    + surrogateDiagTailX0RatChunk000Sub001Block004Part011
    + surrogateDiagTailX0RatChunk000Sub001Block004Part012
    + surrogateDiagTailX0RatChunk000Sub001Block004Part013
    + surrogateDiagTailX0RatChunk000Sub001Block004Part014
    + surrogateDiagTailX0RatChunk000Sub001Block004Part015
    + surrogateDiagTailX0RatChunk000Sub001Block004Part016
    + surrogateDiagTailX0RatChunk000Sub001Block004Part017
    + surrogateDiagTailX0RatChunk000Sub001Block004Part018
    + surrogateDiagTailX0RatChunk000Sub001Block004Part019
    + surrogateDiagTailX0RatChunk000Sub001Block004Part020
    + surrogateDiagTailX0RatChunk000Sub001Block004Part021
    + surrogateDiagTailX0RatChunk000Sub001Block004Part022
    + surrogateDiagTailX0RatChunk000Sub001Block004Part023
    + surrogateDiagTailX0RatChunk000Sub001Block004Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block004_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block004Head + surrogateDiagTailX0RatChunk000Sub001Block004Mid + surrogateDiagTailX0RatChunk000Sub001Block004Tail =
      surrogateDiagTailX0RatChunk000Sub001Block004 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block004Head surrogateDiagTailX0RatChunk000Sub001Block004Mid surrogateDiagTailX0RatChunk000Sub001Block004Tail surrogateDiagTailX0RatChunk000Sub001Block004
  ring

def SurrogateDiagonalTailChunk000Sub001Block004HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block004HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block004Head

def SurrogateDiagonalTailChunk000Sub001Block004MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block004MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block004Mid

def SurrogateDiagonalTailChunk000Sub001Block004TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block004TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block004Tail

theorem surrogateDiagonalTailChunk000Sub001Block004_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block004HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block004MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block004TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block004Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block004 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block004HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block004MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block004TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block004Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block004_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
