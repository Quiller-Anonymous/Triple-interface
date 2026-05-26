import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [90,100). -/

/-- Block 090 covers tail-support indices [17250,17275) and q from 28421 to 28462. -/

def TailChunk001Sub001Block090Part000SupportExplicit : Finset ℕ :=
  ([28421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part000 : ℚ :=
  (60280956725 : ℚ) / 771992713377972486144

def SurrogateDiagonalTailChunk001Sub001Block090Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28421
    = surrogateDiagTailX0RatChunk001Sub001Block090Part000

theorem surrogateDiagonalTailChunk001Sub001Block090Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part000] using hcert

def TailChunk001Sub001Block090Part001SupportExplicit : Finset ℕ :=
  ([28423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part001 : ℚ :=
  (2035487227 : ℚ) / 14763854708569612800

def SurrogateDiagonalTailChunk001Sub001Block090Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28423
    = surrogateDiagTailX0RatChunk001Sub001Block090Part001

theorem surrogateDiagonalTailChunk001Sub001Block090Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part001] using hcert

def TailChunk001Sub001Block090Part002SupportExplicit : Finset ℕ :=
  ([28426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part002 : ℚ :=
  (10626901 : ℚ) / 10791070934630400

def SurrogateDiagonalTailChunk001Sub001Block090Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28426
    = surrogateDiagTailX0RatChunk001Sub001Block090Part002

theorem surrogateDiagonalTailChunk001Sub001Block090Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part002] using hcert

def TailChunk001Sub001Block090Part003SupportExplicit : Finset ℕ :=
  ([28427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part003 : ℚ :=
  (12307097359 : ℚ) / 7497047949768000000

def SurrogateDiagonalTailChunk001Sub001Block090Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28427
    = surrogateDiagTailX0RatChunk001Sub001Block090Part003

theorem surrogateDiagonalTailChunk001Sub001Block090Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part003] using hcert

def TailChunk001Sub001Block090Part004SupportExplicit : Finset ℕ :=
  ([28429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block090Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28429
    = surrogateDiagTailX0RatChunk001Sub001Block090Part004

theorem surrogateDiagonalTailChunk001Sub001Block090Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part004] using hcert

def TailChunk001Sub001Block090Part005SupportExplicit : Finset ℕ :=
  ([28430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part005 : ℚ :=
  (1010668848025 : ℚ) / 41760252753143973888

def SurrogateDiagonalTailChunk001Sub001Block090Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28430
    = surrogateDiagTailX0RatChunk001Sub001Block090Part005

theorem surrogateDiagonalTailChunk001Sub001Block090Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part005] using hcert

def TailChunk001Sub001Block090Part006SupportExplicit : Finset ℕ :=
  ([28433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block090Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28433
    = surrogateDiagTailX0RatChunk001Sub001Block090Part006

theorem surrogateDiagonalTailChunk001Sub001Block090Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part006] using hcert

def TailChunk001Sub001Block090Part007SupportExplicit : Finset ℕ :=
  ([28434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part007 : ℚ :=
  (3916645475 : ℚ) / 30848319506055168

def SurrogateDiagonalTailChunk001Sub001Block090Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28434
    = surrogateDiagTailX0RatChunk001Sub001Block090Part007

theorem surrogateDiagonalTailChunk001Sub001Block090Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part007] using hcert

def TailChunk001Sub001Block090Part008SupportExplicit : Finset ℕ :=
  ([28437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part008 : ℚ :=
  (401082514325 : ℚ) / 23061397590418794432

def SurrogateDiagonalTailChunk001Sub001Block090Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28437
    = surrogateDiagTailX0RatChunk001Sub001Block090Part008

theorem surrogateDiagonalTailChunk001Sub001Block090Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part008] using hcert

def TailChunk001Sub001Block090Part009SupportExplicit : Finset ℕ :=
  ([28438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part009 : ℚ :=
  (747791981 : ℚ) / 751058537050275840

def SurrogateDiagonalTailChunk001Sub001Block090Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28438
    = surrogateDiagTailX0RatChunk001Sub001Block090Part009

theorem surrogateDiagonalTailChunk001Sub001Block090Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part009] using hcert

def TailChunk001Sub001Block090Part010SupportExplicit : Finset ℕ :=
  ([28439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block090Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28439
    = surrogateDiagTailX0RatChunk001Sub001Block090Part010

theorem surrogateDiagonalTailChunk001Sub001Block090Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part010] using hcert

def TailChunk001Sub001Block090Part011SupportExplicit : Finset ℕ :=
  ([28441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part011 : ℚ :=
  (50937141725 : ℚ) / 25238053410941435904

def SurrogateDiagonalTailChunk001Sub001Block090Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28441
    = surrogateDiagTailX0RatChunk001Sub001Block090Part011

theorem surrogateDiagonalTailChunk001Sub001Block090Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part011] using hcert

def TailChunk001Sub001Block090Part012SupportExplicit : Finset ℕ :=
  ([28442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block090Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28442
    = surrogateDiagTailX0RatChunk001Sub001Block090Part012

theorem surrogateDiagonalTailChunk001Sub001Block090Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part012] using hcert

def TailChunk001Sub001Block090Part013SupportExplicit : Finset ℕ :=
  ([28443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part013 : ℚ :=
  (1328094450775 : ℚ) / 64579435084992287232

def SurrogateDiagonalTailChunk001Sub001Block090Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28443
    = surrogateDiagTailX0RatChunk001Sub001Block090Part013

theorem surrogateDiagonalTailChunk001Sub001Block090Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part013] using hcert

def TailChunk001Sub001Block090Part014SupportExplicit : Finset ℕ :=
  ([28445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part014 : ℚ :=
  (2023334476375 : ℚ) / 670046858083796779008

def SurrogateDiagonalTailChunk001Sub001Block090Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28445
    = surrogateDiagTailX0RatChunk001Sub001Block090Part014

theorem surrogateDiagonalTailChunk001Sub001Block090Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part014] using hcert

def TailChunk001Sub001Block090Part015SupportExplicit : Finset ℕ :=
  ([28446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part015 : ℚ :=
  (5664256969 : ℚ) / 54711756163200000

def SurrogateDiagonalTailChunk001Sub001Block090Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28446
    = surrogateDiagTailX0RatChunk001Sub001Block090Part015

theorem surrogateDiagonalTailChunk001Sub001Block090Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part015] using hcert

def TailChunk001Sub001Block090Part016SupportExplicit : Finset ℕ :=
  ([28447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block090Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28447
    = surrogateDiagTailX0RatChunk001Sub001Block090Part016

theorem surrogateDiagonalTailChunk001Sub001Block090Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part016] using hcert

def TailChunk001Sub001Block090Part017SupportExplicit : Finset ℕ :=
  ([28451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part017 : ℚ :=
  (64759993225 : ℚ) / 227845373673933278208

def SurrogateDiagonalTailChunk001Sub001Block090Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28451
    = surrogateDiagTailX0RatChunk001Sub001Block090Part017

theorem surrogateDiagonalTailChunk001Sub001Block090Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part017] using hcert

def TailChunk001Sub001Block090Part018SupportExplicit : Finset ℕ :=
  ([28453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part018 : ℚ :=
  (159261875 : ℚ) / 1002130356805042176

def SurrogateDiagonalTailChunk001Sub001Block090Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28453
    = surrogateDiagTailX0RatChunk001Sub001Block090Part018

theorem surrogateDiagonalTailChunk001Sub001Block090Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part018] using hcert

def TailChunk001Sub001Block090Part019SupportExplicit : Finset ℕ :=
  ([28454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part019 : ℚ :=
  (1244239171 : ℚ) / 917426370568396800

def SurrogateDiagonalTailChunk001Sub001Block090Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28454
    = surrogateDiagTailX0RatChunk001Sub001Block090Part019

theorem surrogateDiagonalTailChunk001Sub001Block090Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part019] using hcert

def TailChunk001Sub001Block090Part020SupportExplicit : Finset ℕ :=
  ([28455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part020 : ℚ :=
  (78751416449 : ℚ) / 1410837064718745600

def SurrogateDiagonalTailChunk001Sub001Block090Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28455
    = surrogateDiagTailX0RatChunk001Sub001Block090Part020

theorem surrogateDiagonalTailChunk001Sub001Block090Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part020] using hcert

def TailChunk001Sub001Block090Part021SupportExplicit : Finset ℕ :=
  ([28457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part021 : ℚ :=
  (51387128797 : ℚ) / 31876644235412275200

def SurrogateDiagonalTailChunk001Sub001Block090Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28457
    = surrogateDiagTailX0RatChunk001Sub001Block090Part021

theorem surrogateDiagonalTailChunk001Sub001Block090Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part021] using hcert

def TailChunk001Sub001Block090Part022SupportExplicit : Finset ℕ :=
  ([28459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part022 : ℚ :=
  (701480193 : ℚ) / 10423099058693811200

def SurrogateDiagonalTailChunk001Sub001Block090Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28459
    = surrogateDiagTailX0RatChunk001Sub001Block090Part022

theorem surrogateDiagonalTailChunk001Sub001Block090Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part022] using hcert

def TailChunk001Sub001Block090Part023SupportExplicit : Finset ℕ :=
  ([28461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part023 : ℚ :=
  (2747126404175 : ℚ) / 146828455233948893184

def SurrogateDiagonalTailChunk001Sub001Block090Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28461
    = surrogateDiagTailX0RatChunk001Sub001Block090Part023

theorem surrogateDiagonalTailChunk001Sub001Block090Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part023] using hcert

def TailChunk001Sub001Block090Part024SupportExplicit : Finset ℕ :=
  ([28462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block090Part024 : ℚ :=
  (38270084875 : ℚ) / 1789509878674612992

def SurrogateDiagonalTailChunk001Sub001Block090Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28462
    = surrogateDiagTailX0RatChunk001Sub001Block090Part024

theorem surrogateDiagonalTailChunk001Sub001Block090Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block090Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block090Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block090Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block090Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block090Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block090Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block090HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block090Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block090Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block090Part000
    + surrogateDiagTailX0RatChunk001Sub001Block090Part001
    + surrogateDiagTailX0RatChunk001Sub001Block090Part002
    + surrogateDiagTailX0RatChunk001Sub001Block090Part003
    + surrogateDiagTailX0RatChunk001Sub001Block090Part004
    + surrogateDiagTailX0RatChunk001Sub001Block090Part005
    + surrogateDiagTailX0RatChunk001Sub001Block090Part006
    + surrogateDiagTailX0RatChunk001Sub001Block090Part007
    + surrogateDiagTailX0RatChunk001Sub001Block090Part008
    + surrogateDiagTailX0RatChunk001Sub001Block090Part009

def surrogateDiagonalTailChunk001Sub001Block090MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block090Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block090Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block090Part010
    + surrogateDiagTailX0RatChunk001Sub001Block090Part011
    + surrogateDiagTailX0RatChunk001Sub001Block090Part012
    + surrogateDiagTailX0RatChunk001Sub001Block090Part013
    + surrogateDiagTailX0RatChunk001Sub001Block090Part014
    + surrogateDiagTailX0RatChunk001Sub001Block090Part015
    + surrogateDiagTailX0RatChunk001Sub001Block090Part016
    + surrogateDiagTailX0RatChunk001Sub001Block090Part017
    + surrogateDiagTailX0RatChunk001Sub001Block090Part018
    + surrogateDiagTailX0RatChunk001Sub001Block090Part019

def surrogateDiagonalTailChunk001Sub001Block090TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block090Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block090Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block090Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block090Part020
    + surrogateDiagTailX0RatChunk001Sub001Block090Part021
    + surrogateDiagTailX0RatChunk001Sub001Block090Part022
    + surrogateDiagTailX0RatChunk001Sub001Block090Part023
    + surrogateDiagTailX0RatChunk001Sub001Block090Part024

def surrogateDiagonalTailChunk001Sub001Block090Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block090HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block090MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block090TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block090 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block090Part000
    + surrogateDiagTailX0RatChunk001Sub001Block090Part001
    + surrogateDiagTailX0RatChunk001Sub001Block090Part002
    + surrogateDiagTailX0RatChunk001Sub001Block090Part003
    + surrogateDiagTailX0RatChunk001Sub001Block090Part004
    + surrogateDiagTailX0RatChunk001Sub001Block090Part005
    + surrogateDiagTailX0RatChunk001Sub001Block090Part006
    + surrogateDiagTailX0RatChunk001Sub001Block090Part007
    + surrogateDiagTailX0RatChunk001Sub001Block090Part008
    + surrogateDiagTailX0RatChunk001Sub001Block090Part009
    + surrogateDiagTailX0RatChunk001Sub001Block090Part010
    + surrogateDiagTailX0RatChunk001Sub001Block090Part011
    + surrogateDiagTailX0RatChunk001Sub001Block090Part012
    + surrogateDiagTailX0RatChunk001Sub001Block090Part013
    + surrogateDiagTailX0RatChunk001Sub001Block090Part014
    + surrogateDiagTailX0RatChunk001Sub001Block090Part015
    + surrogateDiagTailX0RatChunk001Sub001Block090Part016
    + surrogateDiagTailX0RatChunk001Sub001Block090Part017
    + surrogateDiagTailX0RatChunk001Sub001Block090Part018
    + surrogateDiagTailX0RatChunk001Sub001Block090Part019
    + surrogateDiagTailX0RatChunk001Sub001Block090Part020
    + surrogateDiagTailX0RatChunk001Sub001Block090Part021
    + surrogateDiagTailX0RatChunk001Sub001Block090Part022
    + surrogateDiagTailX0RatChunk001Sub001Block090Part023
    + surrogateDiagTailX0RatChunk001Sub001Block090Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block090_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block090Head + surrogateDiagTailX0RatChunk001Sub001Block090Mid + surrogateDiagTailX0RatChunk001Sub001Block090Tail =
      surrogateDiagTailX0RatChunk001Sub001Block090 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block090Head surrogateDiagTailX0RatChunk001Sub001Block090Mid surrogateDiagTailX0RatChunk001Sub001Block090Tail surrogateDiagTailX0RatChunk001Sub001Block090
  ring

def SurrogateDiagonalTailChunk001Sub001Block090HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block090HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block090Head

def SurrogateDiagonalTailChunk001Sub001Block090MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block090MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block090Mid

def SurrogateDiagonalTailChunk001Sub001Block090TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block090TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block090Tail

theorem surrogateDiagonalTailChunk001Sub001Block090_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block090HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block090MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block090TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block090Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block090 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block090HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block090MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block090TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block090Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block090_eq_head_add_mid_add_tail

/-- Block 091 covers tail-support indices [17275,17300) and q from 28463 to 28502. -/

def TailChunk001Sub001Block091Part000SupportExplicit : Finset ℕ :=
  ([28463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block091Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28463
    = surrogateDiagTailX0RatChunk001Sub001Block091Part000

theorem surrogateDiagonalTailChunk001Sub001Block091Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part000] using hcert

def TailChunk001Sub001Block091Part001SupportExplicit : Finset ℕ :=
  ([28465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part001 : ℚ :=
  (675393158625 : ℚ) / 223977882830548074496

def SurrogateDiagonalTailChunk001Sub001Block091Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28465
    = surrogateDiagTailX0RatChunk001Sub001Block091Part001

theorem surrogateDiagonalTailChunk001Sub001Block091Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part001] using hcert

def TailChunk001Sub001Block091Part002SupportExplicit : Finset ℕ :=
  ([28466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part002 : ℚ :=
  (85191479 : ℚ) / 68351179206340800

def SurrogateDiagonalTailChunk001Sub001Block091Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28466
    = surrogateDiagTailX0RatChunk001Sub001Block091Part002

theorem surrogateDiagonalTailChunk001Sub001Block091Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part002] using hcert

def TailChunk001Sub001Block091Part003SupportExplicit : Finset ℕ :=
  ([28470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part003 : ℚ :=
  (1464755243725 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk001Sub001Block091Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28470
    = surrogateDiagTailX0RatChunk001Sub001Block091Part003

theorem surrogateDiagonalTailChunk001Sub001Block091Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part003] using hcert

def TailChunk001Sub001Block091Part004SupportExplicit : Finset ℕ :=
  ([28471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part004 : ℚ :=
  (6057582397 : ℚ) / 61477893120000000000

def SurrogateDiagonalTailChunk001Sub001Block091Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28471
    = surrogateDiagTailX0RatChunk001Sub001Block091Part004

theorem surrogateDiagonalTailChunk001Sub001Block091Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part004] using hcert

def TailChunk001Sub001Block091Part005SupportExplicit : Finset ℕ :=
  ([28473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part005 : ℚ :=
  (22517524801 : ℚ) / 1297991004213184320

def SurrogateDiagonalTailChunk001Sub001Block091Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28473
    = surrogateDiagTailX0RatChunk001Sub001Block091Part005

theorem surrogateDiagonalTailChunk001Sub001Block091Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part005] using hcert

def TailChunk001Sub001Block091Part006SupportExplicit : Finset ℕ :=
  ([28474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part006 : ℚ :=
  (49389755725 : ℚ) / 21360503781931244832

def SurrogateDiagonalTailChunk001Sub001Block091Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28474
    = surrogateDiagTailX0RatChunk001Sub001Block091Part006

theorem surrogateDiagonalTailChunk001Sub001Block091Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part006] using hcert

def TailChunk001Sub001Block091Part007SupportExplicit : Finset ℕ :=
  ([28477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block091Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28477
    = surrogateDiagTailX0RatChunk001Sub001Block091Part007

theorem surrogateDiagonalTailChunk001Sub001Block091Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part007] using hcert

def TailChunk001Sub001Block091Part008SupportExplicit : Finset ℕ :=
  ([28478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part008 : ℚ :=
  (905849647 : ℚ) / 506296885337241600

def SurrogateDiagonalTailChunk001Sub001Block091Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28478
    = surrogateDiagTailX0RatChunk001Sub001Block091Part008

theorem surrogateDiagonalTailChunk001Sub001Block091Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part008] using hcert

def TailChunk001Sub001Block091Part009SupportExplicit : Finset ℕ :=
  ([28479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part009 : ℚ :=
  (34406839329 : ℚ) / 1472599490168499200

def SurrogateDiagonalTailChunk001Sub001Block091Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28479
    = surrogateDiagTailX0RatChunk001Sub001Block091Part009

theorem surrogateDiagonalTailChunk001Sub001Block091Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part009] using hcert

def TailChunk001Sub001Block091Part010SupportExplicit : Finset ℕ :=
  ([28481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part010 : ℚ :=
  (426205373875 : ℚ) / 1321795085322912455808

def SurrogateDiagonalTailChunk001Sub001Block091Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28481
    = surrogateDiagTailX0RatChunk001Sub001Block091Part010

theorem surrogateDiagonalTailChunk001Sub001Block091Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part010] using hcert

def TailChunk001Sub001Block091Part011SupportExplicit : Finset ℕ :=
  ([28482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part011 : ℚ :=
  (2258452441 : ℚ) / 28661449543680000

def SurrogateDiagonalTailChunk001Sub001Block091Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28482
    = surrogateDiagTailX0RatChunk001Sub001Block091Part011

theorem surrogateDiagonalTailChunk001Sub001Block091Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part011] using hcert

def TailChunk001Sub001Block091Part012SupportExplicit : Finset ℕ :=
  ([28483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part012 : ℚ :=
  (126972001175 : ℚ) / 35375510479391686656

def SurrogateDiagonalTailChunk001Sub001Block091Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28483
    = surrogateDiagTailX0RatChunk001Sub001Block091Part012

theorem surrogateDiagonalTailChunk001Sub001Block091Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part012] using hcert

def TailChunk001Sub001Block091Part013SupportExplicit : Finset ℕ :=
  ([28486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block091Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28486
    = surrogateDiagTailX0RatChunk001Sub001Block091Part013

theorem surrogateDiagonalTailChunk001Sub001Block091Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part013] using hcert

def TailChunk001Sub001Block091Part014SupportExplicit : Finset ℕ :=
  ([28487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part014 : ℚ :=
  (671020489 : ℚ) / 6112734294744069120

def SurrogateDiagonalTailChunk001Sub001Block091Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28487
    = surrogateDiagTailX0RatChunk001Sub001Block091Part014

theorem surrogateDiagonalTailChunk001Sub001Block091Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part014] using hcert

def TailChunk001Sub001Block091Part015SupportExplicit : Finset ℕ :=
  ([28489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part015 : ℚ :=
  (2180011613 : ℚ) / 11507277586169370240

def SurrogateDiagonalTailChunk001Sub001Block091Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28489
    = surrogateDiagTailX0RatChunk001Sub001Block091Part015

theorem surrogateDiagonalTailChunk001Sub001Block091Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part015] using hcert

def TailChunk001Sub001Block091Part016SupportExplicit : Finset ℕ :=
  ([28490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part016 : ℚ :=
  (1097947801 : ℚ) / 11611827693158400

def SurrogateDiagonalTailChunk001Sub001Block091Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28490
    = surrogateDiagTailX0RatChunk001Sub001Block091Part016

theorem surrogateDiagonalTailChunk001Sub001Block091Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part016] using hcert

def TailChunk001Sub001Block091Part017SupportExplicit : Finset ℕ :=
  ([28491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part017 : ℚ :=
  (1409125237525 : ℚ) / 81329794322005696512

def SurrogateDiagonalTailChunk001Sub001Block091Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28491
    = surrogateDiagTailX0RatChunk001Sub001Block091Part017

theorem surrogateDiagonalTailChunk001Sub001Block091Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part017] using hcert

def TailChunk001Sub001Block091Part018SupportExplicit : Finset ℕ :=
  ([28493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block091Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28493
    = surrogateDiagTailX0RatChunk001Sub001Block091Part018

theorem surrogateDiagonalTailChunk001Sub001Block091Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part018] using hcert

def TailChunk001Sub001Block091Part019SupportExplicit : Finset ℕ :=
  ([28495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part019 : ℚ :=
  (84815865439 : ℚ) / 23772952709509939200

def SurrogateDiagonalTailChunk001Sub001Block091Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28495
    = surrogateDiagTailX0RatChunk001Sub001Block091Part019

theorem surrogateDiagonalTailChunk001Sub001Block091Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part019] using hcert

def TailChunk001Sub001Block091Part020SupportExplicit : Finset ℕ :=
  ([28497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part020 : ℚ :=
  (4861590795475 : ℚ) / 137453100511913607168

def SurrogateDiagonalTailChunk001Sub001Block091Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28497
    = surrogateDiagTailX0RatChunk001Sub001Block091Part020

theorem surrogateDiagonalTailChunk001Sub001Block091Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part020] using hcert

def TailChunk001Sub001Block091Part021SupportExplicit : Finset ℕ :=
  ([28498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block091Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28498
    = surrogateDiagTailX0RatChunk001Sub001Block091Part021

theorem surrogateDiagonalTailChunk001Sub001Block091Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part021] using hcert

def TailChunk001Sub001Block091Part022SupportExplicit : Finset ℕ :=
  ([28499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block091Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28499
    = surrogateDiagTailX0RatChunk001Sub001Block091Part022

theorem surrogateDiagonalTailChunk001Sub001Block091Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part022] using hcert

def TailChunk001Sub001Block091Part023SupportExplicit : Finset ℕ :=
  ([28501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part023 : ℚ :=
  (2103680989 : ℚ) / 2812975333195125000

def SurrogateDiagonalTailChunk001Sub001Block091Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28501
    = surrogateDiagTailX0RatChunk001Sub001Block091Part023

theorem surrogateDiagonalTailChunk001Sub001Block091Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part023] using hcert

def TailChunk001Sub001Block091Part024SupportExplicit : Finset ℕ :=
  ([28502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block091Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block091Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28502
    = surrogateDiagTailX0RatChunk001Sub001Block091Part024

theorem surrogateDiagonalTailChunk001Sub001Block091Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block091Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block091Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block091Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block091Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block091Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block091Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block091HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block091Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block091Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block091Part000
    + surrogateDiagTailX0RatChunk001Sub001Block091Part001
    + surrogateDiagTailX0RatChunk001Sub001Block091Part002
    + surrogateDiagTailX0RatChunk001Sub001Block091Part003
    + surrogateDiagTailX0RatChunk001Sub001Block091Part004
    + surrogateDiagTailX0RatChunk001Sub001Block091Part005
    + surrogateDiagTailX0RatChunk001Sub001Block091Part006
    + surrogateDiagTailX0RatChunk001Sub001Block091Part007
    + surrogateDiagTailX0RatChunk001Sub001Block091Part008
    + surrogateDiagTailX0RatChunk001Sub001Block091Part009

def surrogateDiagonalTailChunk001Sub001Block091MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block091Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block091Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block091Part010
    + surrogateDiagTailX0RatChunk001Sub001Block091Part011
    + surrogateDiagTailX0RatChunk001Sub001Block091Part012
    + surrogateDiagTailX0RatChunk001Sub001Block091Part013
    + surrogateDiagTailX0RatChunk001Sub001Block091Part014
    + surrogateDiagTailX0RatChunk001Sub001Block091Part015
    + surrogateDiagTailX0RatChunk001Sub001Block091Part016
    + surrogateDiagTailX0RatChunk001Sub001Block091Part017
    + surrogateDiagTailX0RatChunk001Sub001Block091Part018
    + surrogateDiagTailX0RatChunk001Sub001Block091Part019

def surrogateDiagonalTailChunk001Sub001Block091TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block091Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block091Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block091Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block091Part020
    + surrogateDiagTailX0RatChunk001Sub001Block091Part021
    + surrogateDiagTailX0RatChunk001Sub001Block091Part022
    + surrogateDiagTailX0RatChunk001Sub001Block091Part023
    + surrogateDiagTailX0RatChunk001Sub001Block091Part024

def surrogateDiagonalTailChunk001Sub001Block091Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block091HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block091MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block091TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block091 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block091Part000
    + surrogateDiagTailX0RatChunk001Sub001Block091Part001
    + surrogateDiagTailX0RatChunk001Sub001Block091Part002
    + surrogateDiagTailX0RatChunk001Sub001Block091Part003
    + surrogateDiagTailX0RatChunk001Sub001Block091Part004
    + surrogateDiagTailX0RatChunk001Sub001Block091Part005
    + surrogateDiagTailX0RatChunk001Sub001Block091Part006
    + surrogateDiagTailX0RatChunk001Sub001Block091Part007
    + surrogateDiagTailX0RatChunk001Sub001Block091Part008
    + surrogateDiagTailX0RatChunk001Sub001Block091Part009
    + surrogateDiagTailX0RatChunk001Sub001Block091Part010
    + surrogateDiagTailX0RatChunk001Sub001Block091Part011
    + surrogateDiagTailX0RatChunk001Sub001Block091Part012
    + surrogateDiagTailX0RatChunk001Sub001Block091Part013
    + surrogateDiagTailX0RatChunk001Sub001Block091Part014
    + surrogateDiagTailX0RatChunk001Sub001Block091Part015
    + surrogateDiagTailX0RatChunk001Sub001Block091Part016
    + surrogateDiagTailX0RatChunk001Sub001Block091Part017
    + surrogateDiagTailX0RatChunk001Sub001Block091Part018
    + surrogateDiagTailX0RatChunk001Sub001Block091Part019
    + surrogateDiagTailX0RatChunk001Sub001Block091Part020
    + surrogateDiagTailX0RatChunk001Sub001Block091Part021
    + surrogateDiagTailX0RatChunk001Sub001Block091Part022
    + surrogateDiagTailX0RatChunk001Sub001Block091Part023
    + surrogateDiagTailX0RatChunk001Sub001Block091Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block091_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block091Head + surrogateDiagTailX0RatChunk001Sub001Block091Mid + surrogateDiagTailX0RatChunk001Sub001Block091Tail =
      surrogateDiagTailX0RatChunk001Sub001Block091 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block091Head surrogateDiagTailX0RatChunk001Sub001Block091Mid surrogateDiagTailX0RatChunk001Sub001Block091Tail surrogateDiagTailX0RatChunk001Sub001Block091
  ring

def SurrogateDiagonalTailChunk001Sub001Block091HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block091HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block091Head

def SurrogateDiagonalTailChunk001Sub001Block091MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block091MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block091Mid

def SurrogateDiagonalTailChunk001Sub001Block091TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block091TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block091Tail

theorem surrogateDiagonalTailChunk001Sub001Block091_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block091HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block091MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block091TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block091Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block091 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block091HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block091MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block091TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block091Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block091_eq_head_add_mid_add_tail

/-- Block 092 covers tail-support indices [17300,17325) and q from 28505 to 28545. -/

def TailChunk001Sub001Block092Part000SupportExplicit : Finset ℕ :=
  ([28505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part000 : ℚ :=
  (16255003799 : ℚ) / 5405753446502400000

def SurrogateDiagonalTailChunk001Sub001Block092Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28505
    = surrogateDiagTailX0RatChunk001Sub001Block092Part000

theorem surrogateDiagonalTailChunk001Sub001Block092Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part000] using hcert

def TailChunk001Sub001Block092Part001SupportExplicit : Finset ℕ :=
  ([28506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part001 : ℚ :=
  (225725011 : ℚ) / 3258676605000000

def SurrogateDiagonalTailChunk001Sub001Block092Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28506
    = surrogateDiagTailX0RatChunk001Sub001Block092Part001

theorem surrogateDiagonalTailChunk001Sub001Block092Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part001] using hcert

def TailChunk001Sub001Block092Part002SupportExplicit : Finset ℕ :=
  ([28507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part002 : ℚ :=
  (25820199675 : ℚ) / 119103271118745593344

def SurrogateDiagonalTailChunk001Sub001Block092Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28507
    = surrogateDiagTailX0RatChunk001Sub001Block092Part002

theorem surrogateDiagonalTailChunk001Sub001Block092Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part002] using hcert

def TailChunk001Sub001Block092Part003SupportExplicit : Finset ℕ :=
  ([28509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part003 : ℚ :=
  (2377890175 : ℚ) / 82206005831663616

def SurrogateDiagonalTailChunk001Sub001Block092Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28509
    = surrogateDiagTailX0RatChunk001Sub001Block092Part003

theorem surrogateDiagonalTailChunk001Sub001Block092Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part003] using hcert

def TailChunk001Sub001Block092Part004SupportExplicit : Finset ℕ :=
  ([28510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part004 : ℚ :=
  (13551462763 : ℚ) / 563099317344000000

def SurrogateDiagonalTailChunk001Sub001Block092Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28510
    = surrogateDiagTailX0RatChunk001Sub001Block092Part004

theorem surrogateDiagonalTailChunk001Sub001Block092Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part004] using hcert

def TailChunk001Sub001Block092Part005SupportExplicit : Finset ℕ :=
  ([28511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part005 : ℚ :=
  (1038198953425 : ℚ) / 890969705917134962688

def SurrogateDiagonalTailChunk001Sub001Block092Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28511
    = surrogateDiagTailX0RatChunk001Sub001Block092Part005

theorem surrogateDiagonalTailChunk001Sub001Block092Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part005] using hcert

def TailChunk001Sub001Block092Part006SupportExplicit : Finset ℕ :=
  ([28513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block092Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28513
    = surrogateDiagTailX0RatChunk001Sub001Block092Part006

theorem surrogateDiagonalTailChunk001Sub001Block092Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part006] using hcert

def TailChunk001Sub001Block092Part007SupportExplicit : Finset ℕ :=
  ([28514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part007 : ℚ :=
  (33780293325 : ℚ) / 31438234916966465536

def SurrogateDiagonalTailChunk001Sub001Block092Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28514
    = surrogateDiagTailX0RatChunk001Sub001Block092Part007

theorem surrogateDiagonalTailChunk001Sub001Block092Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part007] using hcert

def TailChunk001Sub001Block092Part008SupportExplicit : Finset ℕ :=
  ([28515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part008 : ℚ :=
  (180571140583 : ℚ) / 5339015749632000000

def SurrogateDiagonalTailChunk001Sub001Block092Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28515
    = surrogateDiagTailX0RatChunk001Sub001Block092Part008

theorem surrogateDiagonalTailChunk001Sub001Block092Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part008] using hcert

def TailChunk001Sub001Block092Part009SupportExplicit : Finset ℕ :=
  ([28517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block092Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28517
    = surrogateDiagTailX0RatChunk001Sub001Block092Part009

theorem surrogateDiagonalTailChunk001Sub001Block092Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part009] using hcert

def TailChunk001Sub001Block092Part010SupportExplicit : Finset ℕ :=
  ([28522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part010 : ℚ :=
  (378832400125 : ℚ) / 74815926702828945408

def SurrogateDiagonalTailChunk001Sub001Block092Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28522
    = surrogateDiagTailX0RatChunk001Sub001Block092Part010

theorem surrogateDiagonalTailChunk001Sub001Block092Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part010] using hcert

def TailChunk001Sub001Block092Part011SupportExplicit : Finset ℕ :=
  ([28523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part011 : ℚ :=
  (2809225453 : ℚ) / 3762232172583321600

def SurrogateDiagonalTailChunk001Sub001Block092Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28523
    = surrogateDiagTailX0RatChunk001Sub001Block092Part011

theorem surrogateDiagonalTailChunk001Sub001Block092Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part011] using hcert

def TailChunk001Sub001Block092Part012SupportExplicit : Finset ℕ :=
  ([28526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part012 : ℚ :=
  (44679432225 : ℚ) / 13468884032528580608

def SurrogateDiagonalTailChunk001Sub001Block092Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28526
    = surrogateDiagTailX0RatChunk001Sub001Block092Part012

theorem surrogateDiagonalTailChunk001Sub001Block092Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part012] using hcert

def TailChunk001Sub001Block092Part013SupportExplicit : Finset ℕ :=
  ([28527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part013 : ℚ :=
  (38043699025 : ℚ) / 2004260713610084352

def SurrogateDiagonalTailChunk001Sub001Block092Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28527
    = surrogateDiagTailX0RatChunk001Sub001Block092Part013

theorem surrogateDiagonalTailChunk001Sub001Block092Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part013] using hcert

def TailChunk001Sub001Block092Part014SupportExplicit : Finset ℕ :=
  ([28529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part014 : ℚ :=
  (197689068775 : ℚ) / 1509901728458032706688

def SurrogateDiagonalTailChunk001Sub001Block092Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28529
    = surrogateDiagTailX0RatChunk001Sub001Block092Part014

theorem surrogateDiagonalTailChunk001Sub001Block092Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part014] using hcert

def TailChunk001Sub001Block092Part015SupportExplicit : Finset ℕ :=
  ([28531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part015 : ℚ :=
  (12993132575 : ℚ) / 174510420402918131712

def SurrogateDiagonalTailChunk001Sub001Block092Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28531
    = surrogateDiagTailX0RatChunk001Sub001Block092Part015

theorem surrogateDiagonalTailChunk001Sub001Block092Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part015] using hcert

def TailChunk001Sub001Block092Part016SupportExplicit : Finset ℕ :=
  ([28533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part016 : ℚ :=
  (22612524799 : ℚ) / 1308967611255616320

def SurrogateDiagonalTailChunk001Sub001Block092Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28533
    = surrogateDiagTailX0RatChunk001Sub001Block092Part016

theorem surrogateDiagonalTailChunk001Sub001Block092Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part016] using hcert

def TailChunk001Sub001Block092Part017SupportExplicit : Finset ℕ :=
  ([28534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part017 : ℚ :=
  (16911170821 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk001Sub001Block092Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28534
    = surrogateDiagTailX0RatChunk001Sub001Block092Part017

theorem surrogateDiagonalTailChunk001Sub001Block092Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part017] using hcert

def TailChunk001Sub001Block092Part018SupportExplicit : Finset ℕ :=
  ([28535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part018 : ℚ :=
  (134051047525 : ℚ) / 27140368829694345216

def SurrogateDiagonalTailChunk001Sub001Block092Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28535
    = surrogateDiagTailX0RatChunk001Sub001Block092Part018

theorem surrogateDiagonalTailChunk001Sub001Block092Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part018] using hcert

def TailChunk001Sub001Block092Part019SupportExplicit : Finset ℕ :=
  ([28537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block092Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28537
    = surrogateDiagTailX0RatChunk001Sub001Block092Part019

theorem surrogateDiagonalTailChunk001Sub001Block092Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part019] using hcert

def TailChunk001Sub001Block092Part020SupportExplicit : Finset ℕ :=
  ([28538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part020 : ℚ :=
  (372474971 : ℚ) / 123043353750000000

def SurrogateDiagonalTailChunk001Sub001Block092Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28538
    = surrogateDiagTailX0RatChunk001Sub001Block092Part020

theorem surrogateDiagonalTailChunk001Sub001Block092Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part020] using hcert

def TailChunk001Sub001Block092Part021SupportExplicit : Finset ℕ :=
  ([28541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block092Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28541
    = surrogateDiagTailX0RatChunk001Sub001Block092Part021

theorem surrogateDiagonalTailChunk001Sub001Block092Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part021] using hcert

def TailChunk001Sub001Block092Part022SupportExplicit : Finset ℕ :=
  ([28542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part022 : ℚ :=
  (2099953903 : ℚ) / 27002934995097600

def SurrogateDiagonalTailChunk001Sub001Block092Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28542
    = surrogateDiagTailX0RatChunk001Sub001Block092Part022

theorem surrogateDiagonalTailChunk001Sub001Block092Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part022] using hcert

def TailChunk001Sub001Block092Part023SupportExplicit : Finset ℕ :=
  ([28543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part023 : ℚ :=
  (933307347175 : ℚ) / 1031638398326903144448

def SurrogateDiagonalTailChunk001Sub001Block092Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28543
    = surrogateDiagTailX0RatChunk001Sub001Block092Part023

theorem surrogateDiagonalTailChunk001Sub001Block092Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part023] using hcert

def TailChunk001Sub001Block092Part024SupportExplicit : Finset ℕ :=
  ([28545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block092Part024 : ℚ :=
  (42826076353 : ℚ) / 896397412977868800

def SurrogateDiagonalTailChunk001Sub001Block092Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28545
    = surrogateDiagTailX0RatChunk001Sub001Block092Part024

theorem surrogateDiagonalTailChunk001Sub001Block092Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block092Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block092Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block092Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block092Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block092Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block092Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block092HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block092Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block092Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block092Part000
    + surrogateDiagTailX0RatChunk001Sub001Block092Part001
    + surrogateDiagTailX0RatChunk001Sub001Block092Part002
    + surrogateDiagTailX0RatChunk001Sub001Block092Part003
    + surrogateDiagTailX0RatChunk001Sub001Block092Part004
    + surrogateDiagTailX0RatChunk001Sub001Block092Part005
    + surrogateDiagTailX0RatChunk001Sub001Block092Part006
    + surrogateDiagTailX0RatChunk001Sub001Block092Part007
    + surrogateDiagTailX0RatChunk001Sub001Block092Part008
    + surrogateDiagTailX0RatChunk001Sub001Block092Part009

def surrogateDiagonalTailChunk001Sub001Block092MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block092Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block092Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block092Part010
    + surrogateDiagTailX0RatChunk001Sub001Block092Part011
    + surrogateDiagTailX0RatChunk001Sub001Block092Part012
    + surrogateDiagTailX0RatChunk001Sub001Block092Part013
    + surrogateDiagTailX0RatChunk001Sub001Block092Part014
    + surrogateDiagTailX0RatChunk001Sub001Block092Part015
    + surrogateDiagTailX0RatChunk001Sub001Block092Part016
    + surrogateDiagTailX0RatChunk001Sub001Block092Part017
    + surrogateDiagTailX0RatChunk001Sub001Block092Part018
    + surrogateDiagTailX0RatChunk001Sub001Block092Part019

def surrogateDiagonalTailChunk001Sub001Block092TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block092Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block092Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block092Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block092Part020
    + surrogateDiagTailX0RatChunk001Sub001Block092Part021
    + surrogateDiagTailX0RatChunk001Sub001Block092Part022
    + surrogateDiagTailX0RatChunk001Sub001Block092Part023
    + surrogateDiagTailX0RatChunk001Sub001Block092Part024

def surrogateDiagonalTailChunk001Sub001Block092Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block092HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block092MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block092TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block092 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block092Part000
    + surrogateDiagTailX0RatChunk001Sub001Block092Part001
    + surrogateDiagTailX0RatChunk001Sub001Block092Part002
    + surrogateDiagTailX0RatChunk001Sub001Block092Part003
    + surrogateDiagTailX0RatChunk001Sub001Block092Part004
    + surrogateDiagTailX0RatChunk001Sub001Block092Part005
    + surrogateDiagTailX0RatChunk001Sub001Block092Part006
    + surrogateDiagTailX0RatChunk001Sub001Block092Part007
    + surrogateDiagTailX0RatChunk001Sub001Block092Part008
    + surrogateDiagTailX0RatChunk001Sub001Block092Part009
    + surrogateDiagTailX0RatChunk001Sub001Block092Part010
    + surrogateDiagTailX0RatChunk001Sub001Block092Part011
    + surrogateDiagTailX0RatChunk001Sub001Block092Part012
    + surrogateDiagTailX0RatChunk001Sub001Block092Part013
    + surrogateDiagTailX0RatChunk001Sub001Block092Part014
    + surrogateDiagTailX0RatChunk001Sub001Block092Part015
    + surrogateDiagTailX0RatChunk001Sub001Block092Part016
    + surrogateDiagTailX0RatChunk001Sub001Block092Part017
    + surrogateDiagTailX0RatChunk001Sub001Block092Part018
    + surrogateDiagTailX0RatChunk001Sub001Block092Part019
    + surrogateDiagTailX0RatChunk001Sub001Block092Part020
    + surrogateDiagTailX0RatChunk001Sub001Block092Part021
    + surrogateDiagTailX0RatChunk001Sub001Block092Part022
    + surrogateDiagTailX0RatChunk001Sub001Block092Part023
    + surrogateDiagTailX0RatChunk001Sub001Block092Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block092_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block092Head + surrogateDiagTailX0RatChunk001Sub001Block092Mid + surrogateDiagTailX0RatChunk001Sub001Block092Tail =
      surrogateDiagTailX0RatChunk001Sub001Block092 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block092Head surrogateDiagTailX0RatChunk001Sub001Block092Mid surrogateDiagTailX0RatChunk001Sub001Block092Tail surrogateDiagTailX0RatChunk001Sub001Block092
  ring

def SurrogateDiagonalTailChunk001Sub001Block092HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block092HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block092Head

def SurrogateDiagonalTailChunk001Sub001Block092MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block092MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block092Mid

def SurrogateDiagonalTailChunk001Sub001Block092TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block092TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block092Tail

theorem surrogateDiagonalTailChunk001Sub001Block092_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block092HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block092MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block092TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block092Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block092 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block092HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block092MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block092TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block092Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block092_eq_head_add_mid_add_tail

/-- Block 093 covers tail-support indices [17325,17350) and q from 28546 to 28587. -/

def TailChunk001Sub001Block093Part000SupportExplicit : Finset ℕ :=
  ([28546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part000 : ℚ :=
  (260475726575 : ℚ) / 27952366594488128064

def SurrogateDiagonalTailChunk001Sub001Block093Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28546
    = surrogateDiagTailX0RatChunk001Sub001Block093Part000

theorem surrogateDiagonalTailChunk001Sub001Block093Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part000] using hcert

def TailChunk001Sub001Block093Part001SupportExplicit : Finset ℕ :=
  ([28547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block093Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28547
    = surrogateDiagTailX0RatChunk001Sub001Block093Part001

theorem surrogateDiagonalTailChunk001Sub001Block093Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part001] using hcert

def TailChunk001Sub001Block093Part002SupportExplicit : Finset ℕ :=
  ([28549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block093Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28549
    = surrogateDiagTailX0RatChunk001Sub001Block093Part002

theorem surrogateDiagonalTailChunk001Sub001Block093Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part002] using hcert

def TailChunk001Sub001Block093Part003SupportExplicit : Finset ℕ :=
  ([28551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part003 : ℚ :=
  (43829356559 : ℚ) / 2273042486156912640

def SurrogateDiagonalTailChunk001Sub001Block093Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28551
    = surrogateDiagTailX0RatChunk001Sub001Block093Part003

theorem surrogateDiagonalTailChunk001Sub001Block093Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part003] using hcert

def TailChunk001Sub001Block093Part004SupportExplicit : Finset ℕ :=
  ([28553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part004 : ℚ :=
  (1041255203725 : ℚ) / 896232618746074332288

def SurrogateDiagonalTailChunk001Sub001Block093Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28553
    = surrogateDiagTailX0RatChunk001Sub001Block093Part004

theorem surrogateDiagonalTailChunk001Sub001Block093Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part004] using hcert

def TailChunk001Sub001Block093Part005SupportExplicit : Finset ℕ :=
  ([28554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part005 : ℚ :=
  (707767659275 : ℚ) / 10252141617961848384

def SurrogateDiagonalTailChunk001Sub001Block093Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28554
    = surrogateDiagTailX0RatChunk001Sub001Block093Part005

theorem surrogateDiagonalTailChunk001Sub001Block093Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part005] using hcert

def TailChunk001Sub001Block093Part006SupportExplicit : Finset ℕ :=
  ([28555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part006 : ℚ :=
  (5437351263 : ℚ) / 1814596168153364480

def SurrogateDiagonalTailChunk001Sub001Block093Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28555
    = surrogateDiagTailX0RatChunk001Sub001Block093Part006

theorem surrogateDiagonalTailChunk001Sub001Block093Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part006] using hcert

def TailChunk001Sub001Block093Part007SupportExplicit : Finset ℕ :=
  ([28558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part007 : ℚ :=
  (294728929 : ℚ) / 388646965715973120

def SurrogateDiagonalTailChunk001Sub001Block093Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28558
    = surrogateDiagTailX0RatChunk001Sub001Block093Part007

theorem surrogateDiagonalTailChunk001Sub001Block093Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part007] using hcert

def TailChunk001Sub001Block093Part008SupportExplicit : Finset ℕ :=
  ([28559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block093Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28559
    = surrogateDiagTailX0RatChunk001Sub001Block093Part008

theorem surrogateDiagonalTailChunk001Sub001Block093Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part008] using hcert

def TailChunk001Sub001Block093Part009SupportExplicit : Finset ℕ :=
  ([28562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block093Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28562
    = surrogateDiagTailX0RatChunk001Sub001Block093Part009

theorem surrogateDiagonalTailChunk001Sub001Block093Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part009] using hcert

def TailChunk001Sub001Block093Part010SupportExplicit : Finset ℕ :=
  ([28563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part010 : ℚ :=
  (1618578557 : ℚ) / 93891567749038080

def SurrogateDiagonalTailChunk001Sub001Block093Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28563
    = surrogateDiagTailX0RatChunk001Sub001Block093Part010

theorem surrogateDiagonalTailChunk001Sub001Block093Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part010] using hcert

def TailChunk001Sub001Block093Part011SupportExplicit : Finset ℕ :=
  ([28565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part011 : ℚ :=
  (307812277975 : ℚ) / 82951681693653663744

def SurrogateDiagonalTailChunk001Sub001Block093Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28565
    = surrogateDiagTailX0RatChunk001Sub001Block093Part011

theorem surrogateDiagonalTailChunk001Sub001Block093Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part011] using hcert

def TailChunk001Sub001Block093Part012SupportExplicit : Finset ℕ :=
  ([28569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part012 : ℚ :=
  (1853164107225 : ℚ) / 100967066044521250816

def SurrogateDiagonalTailChunk001Sub001Block093Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28569
    = surrogateDiagTailX0RatChunk001Sub001Block093Part012

theorem surrogateDiagonalTailChunk001Sub001Block093Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part012] using hcert

def TailChunk001Sub001Block093Part013SupportExplicit : Finset ℕ :=
  ([28570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part013 : ℚ :=
  (511046830375 : ℚ) / 42589215130963673088

def SurrogateDiagonalTailChunk001Sub001Block093Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28570
    = surrogateDiagTailX0RatChunk001Sub001Block093Part013

theorem surrogateDiagonalTailChunk001Sub001Block093Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part013] using hcert

def TailChunk001Sub001Block093Part014SupportExplicit : Finset ℕ :=
  ([28571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block093Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28571
    = surrogateDiagTailX0RatChunk001Sub001Block093Part014

theorem surrogateDiagonalTailChunk001Sub001Block093Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part014] using hcert

def TailChunk001Sub001Block093Part015SupportExplicit : Finset ℕ :=
  ([28573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block093Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28573
    = surrogateDiagTailX0RatChunk001Sub001Block093Part015

theorem surrogateDiagonalTailChunk001Sub001Block093Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part015] using hcert

def TailChunk001Sub001Block093Part016SupportExplicit : Finset ℕ :=
  ([28574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part016 : ℚ :=
  (4301554862225 : ℚ) / 19898724644657823744

def SurrogateDiagonalTailChunk001Sub001Block093Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28574
    = surrogateDiagTailX0RatChunk001Sub001Block093Part016

theorem surrogateDiagonalTailChunk001Sub001Block093Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part016] using hcert

def TailChunk001Sub001Block093Part017SupportExplicit : Finset ℕ :=
  ([28578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part017 : ℚ :=
  (6734194667 : ℚ) / 15482436924211200

def SurrogateDiagonalTailChunk001Sub001Block093Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28578
    = surrogateDiagTailX0RatChunk001Sub001Block093Part017

theorem surrogateDiagonalTailChunk001Sub001Block093Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part017] using hcert

def TailChunk001Sub001Block093Part018SupportExplicit : Finset ℕ :=
  ([28579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block093Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28579
    = surrogateDiagTailX0RatChunk001Sub001Block093Part018

theorem surrogateDiagonalTailChunk001Sub001Block093Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part018] using hcert

def TailChunk001Sub001Block093Part019SupportExplicit : Finset ℕ :=
  ([28581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part019 : ℚ :=
  (449915231 : ℚ) / 16424180947353600

def SurrogateDiagonalTailChunk001Sub001Block093Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28581
    = surrogateDiagTailX0RatChunk001Sub001Block093Part019

theorem surrogateDiagonalTailChunk001Sub001Block093Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part019] using hcert

def TailChunk001Sub001Block093Part020SupportExplicit : Finset ℕ :=
  ([28582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part020 : ℚ :=
  (96363166193 : ℚ) / 725492941574400000

def SurrogateDiagonalTailChunk001Sub001Block093Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28582
    = surrogateDiagTailX0RatChunk001Sub001Block093Part020

theorem surrogateDiagonalTailChunk001Sub001Block093Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part020] using hcert

def TailChunk001Sub001Block093Part021SupportExplicit : Finset ℕ :=
  ([28583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part021 : ℚ :=
  (2414327729 : ℚ) / 31626656946576000000

def SurrogateDiagonalTailChunk001Sub001Block093Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28583
    = surrogateDiagTailX0RatChunk001Sub001Block093Part021

theorem surrogateDiagonalTailChunk001Sub001Block093Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part021] using hcert

def TailChunk001Sub001Block093Part022SupportExplicit : Finset ℕ :=
  ([28585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part022 : ℚ :=
  (681097157625 : ℚ) / 227779402791329038336

def SurrogateDiagonalTailChunk001Sub001Block093Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28585
    = surrogateDiagTailX0RatChunk001Sub001Block093Part022

theorem surrogateDiagonalTailChunk001Sub001Block093Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part022] using hcert

def TailChunk001Sub001Block093Part023SupportExplicit : Finset ℕ :=
  ([28586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part023 : ℚ :=
  (3192028890625 : ℚ) / 26081880314794919712

def SurrogateDiagonalTailChunk001Sub001Block093Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28586
    = surrogateDiagTailX0RatChunk001Sub001Block093Part023

theorem surrogateDiagonalTailChunk001Sub001Block093Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part023] using hcert

def TailChunk001Sub001Block093Part024SupportExplicit : Finset ℕ :=
  ([28587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block093Part024 : ℚ :=
  (204723591725 : ℚ) / 119092977747309625344

def SurrogateDiagonalTailChunk001Sub001Block093Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28587
    = surrogateDiagTailX0RatChunk001Sub001Block093Part024

theorem surrogateDiagonalTailChunk001Sub001Block093Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block093Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block093Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block093Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block093Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block093Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block093Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block093HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block093Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block093Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block093Part000
    + surrogateDiagTailX0RatChunk001Sub001Block093Part001
    + surrogateDiagTailX0RatChunk001Sub001Block093Part002
    + surrogateDiagTailX0RatChunk001Sub001Block093Part003
    + surrogateDiagTailX0RatChunk001Sub001Block093Part004
    + surrogateDiagTailX0RatChunk001Sub001Block093Part005
    + surrogateDiagTailX0RatChunk001Sub001Block093Part006
    + surrogateDiagTailX0RatChunk001Sub001Block093Part007
    + surrogateDiagTailX0RatChunk001Sub001Block093Part008
    + surrogateDiagTailX0RatChunk001Sub001Block093Part009

def surrogateDiagonalTailChunk001Sub001Block093MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block093Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block093Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block093Part010
    + surrogateDiagTailX0RatChunk001Sub001Block093Part011
    + surrogateDiagTailX0RatChunk001Sub001Block093Part012
    + surrogateDiagTailX0RatChunk001Sub001Block093Part013
    + surrogateDiagTailX0RatChunk001Sub001Block093Part014
    + surrogateDiagTailX0RatChunk001Sub001Block093Part015
    + surrogateDiagTailX0RatChunk001Sub001Block093Part016
    + surrogateDiagTailX0RatChunk001Sub001Block093Part017
    + surrogateDiagTailX0RatChunk001Sub001Block093Part018
    + surrogateDiagTailX0RatChunk001Sub001Block093Part019

def surrogateDiagonalTailChunk001Sub001Block093TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block093Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block093Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block093Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block093Part020
    + surrogateDiagTailX0RatChunk001Sub001Block093Part021
    + surrogateDiagTailX0RatChunk001Sub001Block093Part022
    + surrogateDiagTailX0RatChunk001Sub001Block093Part023
    + surrogateDiagTailX0RatChunk001Sub001Block093Part024

def surrogateDiagonalTailChunk001Sub001Block093Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block093HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block093MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block093TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block093 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block093Part000
    + surrogateDiagTailX0RatChunk001Sub001Block093Part001
    + surrogateDiagTailX0RatChunk001Sub001Block093Part002
    + surrogateDiagTailX0RatChunk001Sub001Block093Part003
    + surrogateDiagTailX0RatChunk001Sub001Block093Part004
    + surrogateDiagTailX0RatChunk001Sub001Block093Part005
    + surrogateDiagTailX0RatChunk001Sub001Block093Part006
    + surrogateDiagTailX0RatChunk001Sub001Block093Part007
    + surrogateDiagTailX0RatChunk001Sub001Block093Part008
    + surrogateDiagTailX0RatChunk001Sub001Block093Part009
    + surrogateDiagTailX0RatChunk001Sub001Block093Part010
    + surrogateDiagTailX0RatChunk001Sub001Block093Part011
    + surrogateDiagTailX0RatChunk001Sub001Block093Part012
    + surrogateDiagTailX0RatChunk001Sub001Block093Part013
    + surrogateDiagTailX0RatChunk001Sub001Block093Part014
    + surrogateDiagTailX0RatChunk001Sub001Block093Part015
    + surrogateDiagTailX0RatChunk001Sub001Block093Part016
    + surrogateDiagTailX0RatChunk001Sub001Block093Part017
    + surrogateDiagTailX0RatChunk001Sub001Block093Part018
    + surrogateDiagTailX0RatChunk001Sub001Block093Part019
    + surrogateDiagTailX0RatChunk001Sub001Block093Part020
    + surrogateDiagTailX0RatChunk001Sub001Block093Part021
    + surrogateDiagTailX0RatChunk001Sub001Block093Part022
    + surrogateDiagTailX0RatChunk001Sub001Block093Part023
    + surrogateDiagTailX0RatChunk001Sub001Block093Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block093_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block093Head + surrogateDiagTailX0RatChunk001Sub001Block093Mid + surrogateDiagTailX0RatChunk001Sub001Block093Tail =
      surrogateDiagTailX0RatChunk001Sub001Block093 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block093Head surrogateDiagTailX0RatChunk001Sub001Block093Mid surrogateDiagTailX0RatChunk001Sub001Block093Tail surrogateDiagTailX0RatChunk001Sub001Block093
  ring

def SurrogateDiagonalTailChunk001Sub001Block093HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block093HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block093Head

def SurrogateDiagonalTailChunk001Sub001Block093MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block093MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block093Mid

def SurrogateDiagonalTailChunk001Sub001Block093TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block093TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block093Tail

theorem surrogateDiagonalTailChunk001Sub001Block093_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block093HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block093MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block093TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block093Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block093 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block093HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block093MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block093TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block093Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block093_eq_head_add_mid_add_tail

/-- Block 094 covers tail-support indices [17350,17375) and q from 28589 to 28627. -/

def TailChunk001Sub001Block094Part000SupportExplicit : Finset ℕ :=
  ([28589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part000 : ℚ :=
  (46894113349 : ℚ) / 36868007246639923200

def SurrogateDiagonalTailChunk001Sub001Block094Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28589
    = surrogateDiagTailX0RatChunk001Sub001Block094Part000

theorem surrogateDiagonalTailChunk001Sub001Block094Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part000] using hcert

def TailChunk001Sub001Block094Part001SupportExplicit : Finset ℕ :=
  ([28590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part001 : ℚ :=
  (4024102824325 : ℚ) / 8412684470313811968

def SurrogateDiagonalTailChunk001Sub001Block094Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28590
    = surrogateDiagTailX0RatChunk001Sub001Block094Part001

theorem surrogateDiagonalTailChunk001Sub001Block094Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part001] using hcert

def TailChunk001Sub001Block094Part002SupportExplicit : Finset ℕ :=
  ([28591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block094Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28591
    = surrogateDiagTailX0RatChunk001Sub001Block094Part002

theorem surrogateDiagonalTailChunk001Sub001Block094Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part002] using hcert

def TailChunk001Sub001Block094Part003SupportExplicit : Finset ℕ :=
  ([28595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part003 : ℚ :=
  (90909896125 : ℚ) / 10036799384858394624

def SurrogateDiagonalTailChunk001Sub001Block094Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28595
    = surrogateDiagTailX0RatChunk001Sub001Block094Part003

theorem surrogateDiagonalTailChunk001Sub001Block094Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part003] using hcert

def TailChunk001Sub001Block094Part004SupportExplicit : Finset ℕ :=
  ([28597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block094Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28597
    = surrogateDiagTailX0RatChunk001Sub001Block094Part004

theorem surrogateDiagonalTailChunk001Sub001Block094Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part004] using hcert

def TailChunk001Sub001Block094Part005SupportExplicit : Finset ℕ :=
  ([28598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part005 : ℚ :=
  (18370468861 : ℚ) / 143943320635545600

def SurrogateDiagonalTailChunk001Sub001Block094Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28598
    = surrogateDiagTailX0RatChunk001Sub001Block094Part005

theorem surrogateDiagonalTailChunk001Sub001Block094Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part005] using hcert

def TailChunk001Sub001Block094Part006SupportExplicit : Finset ℕ :=
  ([28599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part006 : ℚ :=
  (125025 : ℚ) / 66042897937860608

def SurrogateDiagonalTailChunk001Sub001Block094Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28599
    = surrogateDiagTailX0RatChunk001Sub001Block094Part006

theorem surrogateDiagonalTailChunk001Sub001Block094Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part006] using hcert

def TailChunk001Sub001Block094Part007SupportExplicit : Finset ℕ :=
  ([28601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part007 : ℚ :=
  (271670908525 : ℚ) / 1491784406845999054848

def SurrogateDiagonalTailChunk001Sub001Block094Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28601
    = surrogateDiagTailX0RatChunk001Sub001Block094Part007

theorem surrogateDiagonalTailChunk001Sub001Block094Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part007] using hcert

def TailChunk001Sub001Block094Part008SupportExplicit : Finset ℕ :=
  ([28603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block094Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28603
    = surrogateDiagTailX0RatChunk001Sub001Block094Part008

theorem surrogateDiagonalTailChunk001Sub001Block094Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part008] using hcert

def TailChunk001Sub001Block094Part009SupportExplicit : Finset ℕ :=
  ([28605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part009 : ℚ :=
  (284485908025 : ℚ) / 33792350470084042752

def SurrogateDiagonalTailChunk001Sub001Block094Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28605
    = surrogateDiagTailX0RatChunk001Sub001Block094Part009

theorem surrogateDiagonalTailChunk001Sub001Block094Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part009] using hcert

def TailChunk001Sub001Block094Part010SupportExplicit : Finset ℕ :=
  ([28606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part010 : ℚ :=
  (3196497015625 : ℚ) / 26154954109969037202

def SurrogateDiagonalTailChunk001Sub001Block094Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28606
    = surrogateDiagTailX0RatChunk001Sub001Block094Part010

theorem surrogateDiagonalTailChunk001Sub001Block094Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part010] using hcert

def TailChunk001Sub001Block094Part011SupportExplicit : Finset ℕ :=
  ([28607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block094Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28607
    = surrogateDiagTailX0RatChunk001Sub001Block094Part011

theorem surrogateDiagonalTailChunk001Sub001Block094Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part011] using hcert

def TailChunk001Sub001Block094Part012SupportExplicit : Finset ℕ :=
  ([28609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part012 : ℚ :=
  (2420259377 : ℚ) / 1593832211770613760

def SurrogateDiagonalTailChunk001Sub001Block094Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28609
    = surrogateDiagTailX0RatChunk001Sub001Block094Part012

theorem surrogateDiagonalTailChunk001Sub001Block094Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part012] using hcert

def TailChunk001Sub001Block094Part013SupportExplicit : Finset ℕ :=
  ([28610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part013 : ℚ :=
  (347715734479 : ℚ) / 1713132475679539200

def SurrogateDiagonalTailChunk001Sub001Block094Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28610
    = surrogateDiagTailX0RatChunk001Sub001Block094Part013

theorem surrogateDiagonalTailChunk001Sub001Block094Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part013] using hcert

def TailChunk001Sub001Block094Part014SupportExplicit : Finset ℕ :=
  ([28613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part014 : ℚ :=
  (1812895117 : ℚ) / 1920745032192000000

def SurrogateDiagonalTailChunk001Sub001Block094Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28613
    = surrogateDiagTailX0RatChunk001Sub001Block094Part014

theorem surrogateDiagonalTailChunk001Sub001Block094Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part014] using hcert

def TailChunk001Sub001Block094Part015SupportExplicit : Finset ℕ :=
  ([28614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part015 : ℚ :=
  (208097379247 : ℚ) / 656231220000000000

def SurrogateDiagonalTailChunk001Sub001Block094Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28614
    = surrogateDiagTailX0RatChunk001Sub001Block094Part015

theorem surrogateDiagonalTailChunk001Sub001Block094Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part015] using hcert

def TailChunk001Sub001Block094Part016SupportExplicit : Finset ℕ :=
  ([28615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part016 : ℚ :=
  (1067273206475 : ℚ) / 307633576775792984064

def SurrogateDiagonalTailChunk001Sub001Block094Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28615
    = surrogateDiagTailX0RatChunk001Sub001Block094Part016

theorem surrogateDiagonalTailChunk001Sub001Block094Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part016] using hcert

def TailChunk001Sub001Block094Part017SupportExplicit : Finset ℕ :=
  ([28617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part017 : ℚ :=
  (125025 : ℚ) / 66209340105769088

def SurrogateDiagonalTailChunk001Sub001Block094Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28617
    = surrogateDiagTailX0RatChunk001Sub001Block094Part017

theorem surrogateDiagonalTailChunk001Sub001Block094Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part017] using hcert

def TailChunk001Sub001Block094Part018SupportExplicit : Finset ℕ :=
  ([28618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part018 : ℚ :=
  (488901427567 : ℚ) / 3755292685251379200

def SurrogateDiagonalTailChunk001Sub001Block094Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28618
    = surrogateDiagTailX0RatChunk001Sub001Block094Part018

theorem surrogateDiagonalTailChunk001Sub001Block094Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part018] using hcert

def TailChunk001Sub001Block094Part019SupportExplicit : Finset ℕ :=
  ([28619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block094Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28619
    = surrogateDiagTailX0RatChunk001Sub001Block094Part019

theorem surrogateDiagonalTailChunk001Sub001Block094Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part019] using hcert

def TailChunk001Sub001Block094Part020SupportExplicit : Finset ℕ :=
  ([28621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block094Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28621
    = surrogateDiagTailX0RatChunk001Sub001Block094Part020

theorem surrogateDiagonalTailChunk001Sub001Block094Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part020] using hcert

def TailChunk001Sub001Block094Part021SupportExplicit : Finset ℕ :=
  ([28622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part021 : ℚ :=
  (435345485167 : ℚ) / 2856671220000000000

def SurrogateDiagonalTailChunk001Sub001Block094Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28622
    = surrogateDiagTailX0RatChunk001Sub001Block094Part021

theorem surrogateDiagonalTailChunk001Sub001Block094Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part021] using hcert

def TailChunk001Sub001Block094Part022SupportExplicit : Finset ℕ :=
  ([28623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part022 : ℚ :=
  (13807439575 : ℚ) / 1981904842206019584

def SurrogateDiagonalTailChunk001Sub001Block094Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28623
    = surrogateDiagTailX0RatChunk001Sub001Block094Part022

theorem surrogateDiagonalTailChunk001Sub001Block094Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part022] using hcert

def TailChunk001Sub001Block094Part023SupportExplicit : Finset ℕ :=
  ([28626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part023 : ℚ :=
  (5013745706725 : ℚ) / 14886622218413703168

def SurrogateDiagonalTailChunk001Sub001Block094Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28626
    = surrogateDiagTailX0RatChunk001Sub001Block094Part023

theorem surrogateDiagonalTailChunk001Sub001Block094Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part023] using hcert

def TailChunk001Sub001Block094Part024SupportExplicit : Finset ℕ :=
  ([28627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block094Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block094Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28627
    = surrogateDiagTailX0RatChunk001Sub001Block094Part024

theorem surrogateDiagonalTailChunk001Sub001Block094Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block094Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block094Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block094Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block094Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block094Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block094Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block094HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block094Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block094Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block094Part000
    + surrogateDiagTailX0RatChunk001Sub001Block094Part001
    + surrogateDiagTailX0RatChunk001Sub001Block094Part002
    + surrogateDiagTailX0RatChunk001Sub001Block094Part003
    + surrogateDiagTailX0RatChunk001Sub001Block094Part004
    + surrogateDiagTailX0RatChunk001Sub001Block094Part005
    + surrogateDiagTailX0RatChunk001Sub001Block094Part006
    + surrogateDiagTailX0RatChunk001Sub001Block094Part007
    + surrogateDiagTailX0RatChunk001Sub001Block094Part008
    + surrogateDiagTailX0RatChunk001Sub001Block094Part009

def surrogateDiagonalTailChunk001Sub001Block094MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block094Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block094Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block094Part010
    + surrogateDiagTailX0RatChunk001Sub001Block094Part011
    + surrogateDiagTailX0RatChunk001Sub001Block094Part012
    + surrogateDiagTailX0RatChunk001Sub001Block094Part013
    + surrogateDiagTailX0RatChunk001Sub001Block094Part014
    + surrogateDiagTailX0RatChunk001Sub001Block094Part015
    + surrogateDiagTailX0RatChunk001Sub001Block094Part016
    + surrogateDiagTailX0RatChunk001Sub001Block094Part017
    + surrogateDiagTailX0RatChunk001Sub001Block094Part018
    + surrogateDiagTailX0RatChunk001Sub001Block094Part019

def surrogateDiagonalTailChunk001Sub001Block094TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block094Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block094Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block094Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block094Part020
    + surrogateDiagTailX0RatChunk001Sub001Block094Part021
    + surrogateDiagTailX0RatChunk001Sub001Block094Part022
    + surrogateDiagTailX0RatChunk001Sub001Block094Part023
    + surrogateDiagTailX0RatChunk001Sub001Block094Part024

def surrogateDiagonalTailChunk001Sub001Block094Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block094HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block094MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block094TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block094 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block094Part000
    + surrogateDiagTailX0RatChunk001Sub001Block094Part001
    + surrogateDiagTailX0RatChunk001Sub001Block094Part002
    + surrogateDiagTailX0RatChunk001Sub001Block094Part003
    + surrogateDiagTailX0RatChunk001Sub001Block094Part004
    + surrogateDiagTailX0RatChunk001Sub001Block094Part005
    + surrogateDiagTailX0RatChunk001Sub001Block094Part006
    + surrogateDiagTailX0RatChunk001Sub001Block094Part007
    + surrogateDiagTailX0RatChunk001Sub001Block094Part008
    + surrogateDiagTailX0RatChunk001Sub001Block094Part009
    + surrogateDiagTailX0RatChunk001Sub001Block094Part010
    + surrogateDiagTailX0RatChunk001Sub001Block094Part011
    + surrogateDiagTailX0RatChunk001Sub001Block094Part012
    + surrogateDiagTailX0RatChunk001Sub001Block094Part013
    + surrogateDiagTailX0RatChunk001Sub001Block094Part014
    + surrogateDiagTailX0RatChunk001Sub001Block094Part015
    + surrogateDiagTailX0RatChunk001Sub001Block094Part016
    + surrogateDiagTailX0RatChunk001Sub001Block094Part017
    + surrogateDiagTailX0RatChunk001Sub001Block094Part018
    + surrogateDiagTailX0RatChunk001Sub001Block094Part019
    + surrogateDiagTailX0RatChunk001Sub001Block094Part020
    + surrogateDiagTailX0RatChunk001Sub001Block094Part021
    + surrogateDiagTailX0RatChunk001Sub001Block094Part022
    + surrogateDiagTailX0RatChunk001Sub001Block094Part023
    + surrogateDiagTailX0RatChunk001Sub001Block094Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block094_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block094Head + surrogateDiagTailX0RatChunk001Sub001Block094Mid + surrogateDiagTailX0RatChunk001Sub001Block094Tail =
      surrogateDiagTailX0RatChunk001Sub001Block094 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block094Head surrogateDiagTailX0RatChunk001Sub001Block094Mid surrogateDiagTailX0RatChunk001Sub001Block094Tail surrogateDiagTailX0RatChunk001Sub001Block094
  ring

def SurrogateDiagonalTailChunk001Sub001Block094HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block094HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block094Head

def SurrogateDiagonalTailChunk001Sub001Block094MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block094MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block094Mid

def SurrogateDiagonalTailChunk001Sub001Block094TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block094TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block094Tail

theorem surrogateDiagonalTailChunk001Sub001Block094_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block094HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block094MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block094TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block094Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block094 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block094HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block094MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block094TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block094Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block094_eq_head_add_mid_add_tail

/-- Block 095 covers tail-support indices [17375,17400) and q from 28630 to 28667. -/

def TailChunk001Sub001Block095Part000SupportExplicit : Finset ℕ :=
  ([28630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part000 : ℚ :=
  (3317517386225 : ℚ) / 11494298794195943424

def SurrogateDiagonalTailChunk001Sub001Block095Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28630
    = surrogateDiagTailX0RatChunk001Sub001Block095Part000

theorem surrogateDiagonalTailChunk001Sub001Block095Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part000] using hcert

def TailChunk001Sub001Block095Part001SupportExplicit : Finset ℕ :=
  ([28631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block095Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28631
    = surrogateDiagTailX0RatChunk001Sub001Block095Part001

theorem surrogateDiagonalTailChunk001Sub001Block095Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part001] using hcert

def TailChunk001Sub001Block095Part002SupportExplicit : Finset ℕ :=
  ([28633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part002 : ℚ :=
  (8689617179 : ℚ) / 5986613955310387200

def SurrogateDiagonalTailChunk001Sub001Block095Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28633
    = surrogateDiagTailX0RatChunk001Sub001Block095Part002

theorem surrogateDiagonalTailChunk001Sub001Block095Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part002] using hcert

def TailChunk001Sub001Block095Part003SupportExplicit : Finset ℕ :=
  ([28634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part003 : ℚ :=
  (12457282591525 : ℚ) / 98162111476641449088

def SurrogateDiagonalTailChunk001Sub001Block095Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28634
    = surrogateDiagTailX0RatChunk001Sub001Block095Part003

theorem surrogateDiagonalTailChunk001Sub001Block095Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part003] using hcert

def TailChunk001Sub001Block095Part004SupportExplicit : Finset ℕ :=
  ([28635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part004 : ℚ :=
  (368550214675 : ℚ) / 27118954869135900672

def SurrogateDiagonalTailChunk001Sub001Block095Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28635
    = surrogateDiagTailX0RatChunk001Sub001Block095Part004

theorem surrogateDiagonalTailChunk001Sub001Block095Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part004] using hcert

def TailChunk001Sub001Block095Part005SupportExplicit : Finset ℕ :=
  ([28637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part005 : ℚ :=
  (41895248173 : ℚ) / 36273134293679491200

def SurrogateDiagonalTailChunk001Sub001Block095Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28637
    = surrogateDiagTailX0RatChunk001Sub001Block095Part005

theorem surrogateDiagonalTailChunk001Sub001Block095Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part005] using hcert

def TailChunk001Sub001Block095Part006SupportExplicit : Finset ℕ :=
  ([28639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part006 : ℚ :=
  (114067499525 : ℚ) / 152381103619794299136

def SurrogateDiagonalTailChunk001Sub001Block095Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28639
    = surrogateDiagTailX0RatChunk001Sub001Block095Part006

theorem surrogateDiagonalTailChunk001Sub001Block095Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part006] using hcert

def TailChunk001Sub001Block095Part007SupportExplicit : Finset ℕ :=
  ([28641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part007 : ℚ :=
  (41675 : ℚ) / 22143917379321216

def SurrogateDiagonalTailChunk001Sub001Block095Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28641
    = surrogateDiagTailX0RatChunk001Sub001Block095Part007

theorem surrogateDiagonalTailChunk001Sub001Block095Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part007] using hcert

def TailChunk001Sub001Block095Part008SupportExplicit : Finset ℕ :=
  ([28642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part008 : ℚ :=
  (5127276025 : ℚ) / 42058998011338752

def SurrogateDiagonalTailChunk001Sub001Block095Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28642
    = surrogateDiagTailX0RatChunk001Sub001Block095Part008

theorem surrogateDiagonalTailChunk001Sub001Block095Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part008] using hcert

def TailChunk001Sub001Block095Part009SupportExplicit : Finset ℕ :=
  ([28643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block095Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28643
    = surrogateDiagTailX0RatChunk001Sub001Block095Part009

theorem surrogateDiagonalTailChunk001Sub001Block095Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part009] using hcert

def TailChunk001Sub001Block095Part010SupportExplicit : Finset ℕ :=
  ([28645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part010 : ℚ :=
  (83062889825 : ℚ) / 19803415528303755264

def SurrogateDiagonalTailChunk001Sub001Block095Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28645
    = surrogateDiagTailX0RatChunk001Sub001Block095Part010

theorem surrogateDiagonalTailChunk001Sub001Block095Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part010] using hcert

def TailChunk001Sub001Block095Part011SupportExplicit : Finset ℕ :=
  ([28646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part011 : ℚ :=
  (3205442640625 : ℚ) / 26301562238257942482

def SurrogateDiagonalTailChunk001Sub001Block095Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28646
    = surrogateDiagTailX0RatChunk001Sub001Block095Part011

theorem surrogateDiagonalTailChunk001Sub001Block095Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part011] using hcert

def TailChunk001Sub001Block095Part012SupportExplicit : Finset ℕ :=
  ([28649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block095Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28649
    = surrogateDiagTailX0RatChunk001Sub001Block095Part012

theorem surrogateDiagonalTailChunk001Sub001Block095Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part012] using hcert

def TailChunk001Sub001Block095Part013SupportExplicit : Finset ℕ :=
  ([28651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part013 : ℚ :=
  (1048403954425 : ℚ) / 908603406201610487808

def SurrogateDiagonalTailChunk001Sub001Block095Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28651
    = surrogateDiagTailX0RatChunk001Sub001Block095Part013

theorem surrogateDiagonalTailChunk001Sub001Block095Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part013] using hcert

def TailChunk001Sub001Block095Part014SupportExplicit : Finset ℕ :=
  ([28653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part014 : ℚ :=
  (5001 : ℚ) / 2661726722000000

def SurrogateDiagonalTailChunk001Sub001Block095Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28653
    = surrogateDiagTailX0RatChunk001Sub001Block095Part014

theorem surrogateDiagonalTailChunk001Sub001Block095Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part014] using hcert

def TailChunk001Sub001Block095Part015SupportExplicit : Finset ℕ :=
  ([28654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part015 : ℚ :=
  (3207233265625 : ℚ) / 26330957666783265522

def SurrogateDiagonalTailChunk001Sub001Block095Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28654
    = surrogateDiagTailX0RatChunk001Sub001Block095Part015

theorem surrogateDiagonalTailChunk001Sub001Block095Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part015] using hcert

def TailChunk001Sub001Block095Part016SupportExplicit : Finset ℕ :=
  ([28655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part016 : ℚ :=
  (984027459 : ℚ) / 195015421952000000

def SurrogateDiagonalTailChunk001Sub001Block095Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28655
    = surrogateDiagTailX0RatChunk001Sub001Block095Part016

theorem surrogateDiagonalTailChunk001Sub001Block095Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part016] using hcert

def TailChunk001Sub001Block095Part017SupportExplicit : Finset ℕ :=
  ([28657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block095Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28657
    = surrogateDiagTailX0RatChunk001Sub001Block095Part017

theorem surrogateDiagonalTailChunk001Sub001Block095Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part017] using hcert

def TailChunk001Sub001Block095Part018SupportExplicit : Finset ℕ :=
  ([28658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part018 : ℚ :=
  (1106643945875 : ℚ) / 5690668474326122496

def SurrogateDiagonalTailChunk001Sub001Block095Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28658
    = surrogateDiagTailX0RatChunk001Sub001Block095Part018

theorem surrogateDiagonalTailChunk001Sub001Block095Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part018] using hcert

def TailChunk001Sub001Block095Part019SupportExplicit : Finset ℕ :=
  ([28659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part019 : ℚ :=
  (1129946427 : ℚ) / 1978096558486323200

def SurrogateDiagonalTailChunk001Sub001Block095Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28659
    = surrogateDiagTailX0RatChunk001Sub001Block095Part019

theorem surrogateDiagonalTailChunk001Sub001Block095Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part019] using hcert

def TailChunk001Sub001Block095Part020SupportExplicit : Finset ℕ :=
  ([28661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block095Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28661
    = surrogateDiagTailX0RatChunk001Sub001Block095Part020

theorem surrogateDiagonalTailChunk001Sub001Block095Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part020] using hcert

def TailChunk001Sub001Block095Part021SupportExplicit : Finset ℕ :=
  ([28662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part021 : ℚ :=
  (41473810037 : ℚ) / 128928486512394240

def SurrogateDiagonalTailChunk001Sub001Block095Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28662
    = surrogateDiagTailX0RatChunk001Sub001Block095Part021

theorem surrogateDiagonalTailChunk001Sub001Block095Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part021] using hcert

def TailChunk001Sub001Block095Part022SupportExplicit : Finset ℕ :=
  ([28663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block095Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28663
    = surrogateDiagTailX0RatChunk001Sub001Block095Part022

theorem surrogateDiagonalTailChunk001Sub001Block095Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part022] using hcert

def TailChunk001Sub001Block095Part023SupportExplicit : Finset ℕ :=
  ([28666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part023 : ℚ :=
  (145561885211 : ℚ) / 958097114978774400

def SurrogateDiagonalTailChunk001Sub001Block095Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28666
    = surrogateDiagTailX0RatChunk001Sub001Block095Part023

theorem surrogateDiagonalTailChunk001Sub001Block095Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part023] using hcert

def TailChunk001Sub001Block095Part024SupportExplicit : Finset ℕ :=
  ([28667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block095Part024 : ℚ :=
  (4794440425 : ℚ) / 66790670669936739072

def SurrogateDiagonalTailChunk001Sub001Block095Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28667
    = surrogateDiagTailX0RatChunk001Sub001Block095Part024

theorem surrogateDiagonalTailChunk001Sub001Block095Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block095Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block095Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block095Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block095Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block095Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block095Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block095HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block095Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block095Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block095Part000
    + surrogateDiagTailX0RatChunk001Sub001Block095Part001
    + surrogateDiagTailX0RatChunk001Sub001Block095Part002
    + surrogateDiagTailX0RatChunk001Sub001Block095Part003
    + surrogateDiagTailX0RatChunk001Sub001Block095Part004
    + surrogateDiagTailX0RatChunk001Sub001Block095Part005
    + surrogateDiagTailX0RatChunk001Sub001Block095Part006
    + surrogateDiagTailX0RatChunk001Sub001Block095Part007
    + surrogateDiagTailX0RatChunk001Sub001Block095Part008
    + surrogateDiagTailX0RatChunk001Sub001Block095Part009

def surrogateDiagonalTailChunk001Sub001Block095MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block095Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block095Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block095Part010
    + surrogateDiagTailX0RatChunk001Sub001Block095Part011
    + surrogateDiagTailX0RatChunk001Sub001Block095Part012
    + surrogateDiagTailX0RatChunk001Sub001Block095Part013
    + surrogateDiagTailX0RatChunk001Sub001Block095Part014
    + surrogateDiagTailX0RatChunk001Sub001Block095Part015
    + surrogateDiagTailX0RatChunk001Sub001Block095Part016
    + surrogateDiagTailX0RatChunk001Sub001Block095Part017
    + surrogateDiagTailX0RatChunk001Sub001Block095Part018
    + surrogateDiagTailX0RatChunk001Sub001Block095Part019

def surrogateDiagonalTailChunk001Sub001Block095TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block095Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block095Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block095Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block095Part020
    + surrogateDiagTailX0RatChunk001Sub001Block095Part021
    + surrogateDiagTailX0RatChunk001Sub001Block095Part022
    + surrogateDiagTailX0RatChunk001Sub001Block095Part023
    + surrogateDiagTailX0RatChunk001Sub001Block095Part024

def surrogateDiagonalTailChunk001Sub001Block095Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block095HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block095MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block095TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block095 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block095Part000
    + surrogateDiagTailX0RatChunk001Sub001Block095Part001
    + surrogateDiagTailX0RatChunk001Sub001Block095Part002
    + surrogateDiagTailX0RatChunk001Sub001Block095Part003
    + surrogateDiagTailX0RatChunk001Sub001Block095Part004
    + surrogateDiagTailX0RatChunk001Sub001Block095Part005
    + surrogateDiagTailX0RatChunk001Sub001Block095Part006
    + surrogateDiagTailX0RatChunk001Sub001Block095Part007
    + surrogateDiagTailX0RatChunk001Sub001Block095Part008
    + surrogateDiagTailX0RatChunk001Sub001Block095Part009
    + surrogateDiagTailX0RatChunk001Sub001Block095Part010
    + surrogateDiagTailX0RatChunk001Sub001Block095Part011
    + surrogateDiagTailX0RatChunk001Sub001Block095Part012
    + surrogateDiagTailX0RatChunk001Sub001Block095Part013
    + surrogateDiagTailX0RatChunk001Sub001Block095Part014
    + surrogateDiagTailX0RatChunk001Sub001Block095Part015
    + surrogateDiagTailX0RatChunk001Sub001Block095Part016
    + surrogateDiagTailX0RatChunk001Sub001Block095Part017
    + surrogateDiagTailX0RatChunk001Sub001Block095Part018
    + surrogateDiagTailX0RatChunk001Sub001Block095Part019
    + surrogateDiagTailX0RatChunk001Sub001Block095Part020
    + surrogateDiagTailX0RatChunk001Sub001Block095Part021
    + surrogateDiagTailX0RatChunk001Sub001Block095Part022
    + surrogateDiagTailX0RatChunk001Sub001Block095Part023
    + surrogateDiagTailX0RatChunk001Sub001Block095Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block095_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block095Head + surrogateDiagTailX0RatChunk001Sub001Block095Mid + surrogateDiagTailX0RatChunk001Sub001Block095Tail =
      surrogateDiagTailX0RatChunk001Sub001Block095 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block095Head surrogateDiagTailX0RatChunk001Sub001Block095Mid surrogateDiagTailX0RatChunk001Sub001Block095Tail surrogateDiagTailX0RatChunk001Sub001Block095
  ring

def SurrogateDiagonalTailChunk001Sub001Block095HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block095HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block095Head

def SurrogateDiagonalTailChunk001Sub001Block095MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block095MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block095Mid

def SurrogateDiagonalTailChunk001Sub001Block095TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block095TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block095Tail

theorem surrogateDiagonalTailChunk001Sub001Block095_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block095HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block095MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block095TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block095Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block095 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block095HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block095MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block095TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block095Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block095_eq_head_add_mid_add_tail

/-- Block 096 covers tail-support indices [17400,17425) and q from 28669 to 28707. -/

def TailChunk001Sub001Block096Part000SupportExplicit : Finset ℕ :=
  ([28669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block096Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28669
    = surrogateDiagTailX0RatChunk001Sub001Block096Part000

theorem surrogateDiagonalTailChunk001Sub001Block096Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part000] using hcert

def TailChunk001Sub001Block096Part001SupportExplicit : Finset ℕ :=
  ([28670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part001 : ℚ :=
  (14291549093 : ℚ) / 64600414971494400

def SurrogateDiagonalTailChunk001Sub001Block096Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28670
    = surrogateDiagTailX0RatChunk001Sub001Block096Part001

theorem surrogateDiagonalTailChunk001Sub001Block096Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part001] using hcert

def TailChunk001Sub001Block096Part002SupportExplicit : Finset ℕ :=
  ([28671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part002 : ℚ :=
  (147413130725 : ℚ) / 133358817176061502464

def SurrogateDiagonalTailChunk001Sub001Block096Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28671
    = surrogateDiagTailX0RatChunk001Sub001Block096Part002

theorem surrogateDiagonalTailChunk001Sub001Block096Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part002] using hcert

def TailChunk001Sub001Block096Part003SupportExplicit : Finset ℕ :=
  ([28673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part003 : ℚ :=
  (1801216471 : ℚ) / 15545878628638924800

def SurrogateDiagonalTailChunk001Sub001Block096Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28673
    = surrogateDiagTailX0RatChunk001Sub001Block096Part003

theorem surrogateDiagonalTailChunk001Sub001Block096Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part003] using hcert

def TailChunk001Sub001Block096Part004SupportExplicit : Finset ℕ :=
  ([28678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part004 : ℚ :=
  (1395260306825 : ℚ) / 9558466758489159936

def SurrogateDiagonalTailChunk001Sub001Block096Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28678
    = surrogateDiagTailX0RatChunk001Sub001Block096Part004

theorem surrogateDiagonalTailChunk001Sub001Block096Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part004] using hcert

def TailChunk001Sub001Block096Part005SupportExplicit : Finset ℕ :=
  ([28679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part005 : ℚ :=
  (11213076503 : ℚ) / 5636983257028362240

def SurrogateDiagonalTailChunk001Sub001Block096Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28679
    = surrogateDiagTailX0RatChunk001Sub001Block096Part005

theorem surrogateDiagonalTailChunk001Sub001Block096Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part005] using hcert

def TailChunk001Sub001Block096Part006SupportExplicit : Finset ℕ :=
  ([28681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part006 : ℚ :=
  (25884276575 : ℚ) / 35010385338543842304

def SurrogateDiagonalTailChunk001Sub001Block096Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28681
    = surrogateDiagTailX0RatChunk001Sub001Block096Part006

theorem surrogateDiagonalTailChunk001Sub001Block096Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part006] using hcert

def TailChunk001Sub001Block096Part007SupportExplicit : Finset ℕ :=
  ([28682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part007 : ℚ :=
  (5141607025 : ℚ) / 42294457187357472

def SurrogateDiagonalTailChunk001Sub001Block096Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28682
    = surrogateDiagTailX0RatChunk001Sub001Block096Part007

theorem surrogateDiagonalTailChunk001Sub001Block096Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part007] using hcert

def TailChunk001Sub001Block096Part008SupportExplicit : Finset ℕ :=
  ([28685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part008 : ℚ :=
  (2057606470375 : ℚ) / 692952386557664821248

def SurrogateDiagonalTailChunk001Sub001Block096Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28685
    = surrogateDiagTailX0RatChunk001Sub001Block096Part008

theorem surrogateDiagonalTailChunk001Sub001Block096Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part008] using hcert

def TailChunk001Sub001Block096Part009SupportExplicit : Finset ℕ :=
  ([28686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part009 : ℚ :=
  (41213572775 : ℚ) / 103864129652676096

def SurrogateDiagonalTailChunk001Sub001Block096Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28686
    = surrogateDiagTailX0RatChunk001Sub001Block096Part009

theorem surrogateDiagonalTailChunk001Sub001Block096Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part009] using hcert

def TailChunk001Sub001Block096Part010SupportExplicit : Finset ℕ :=
  ([28687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block096Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28687
    = surrogateDiagTailX0RatChunk001Sub001Block096Part010

theorem surrogateDiagonalTailChunk001Sub001Block096Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part010] using hcert

def TailChunk001Sub001Block096Part011SupportExplicit : Finset ℕ :=
  ([28689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part011 : ℚ :=
  (1629506431 : ℚ) / 4094387786966630400

def SurrogateDiagonalTailChunk001Sub001Block096Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28689
    = surrogateDiagTailX0RatChunk001Sub001Block096Part011

theorem surrogateDiagonalTailChunk001Sub001Block096Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part011] using hcert

def TailChunk001Sub001Block096Part012SupportExplicit : Finset ℕ :=
  ([28690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part012 : ℚ :=
  (12667498573 : ℚ) / 54430442311680000

def SurrogateDiagonalTailChunk001Sub001Block096Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28690
    = surrogateDiagTailX0RatChunk001Sub001Block096Part012

theorem surrogateDiagonalTailChunk001Sub001Block096Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part012] using hcert

def TailChunk001Sub001Block096Part013SupportExplicit : Finset ℕ :=
  ([28691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part013 : ℚ :=
  (611936302525 : ℚ) / 1227930750937035491328

def SurrogateDiagonalTailChunk001Sub001Block096Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28691
    = surrogateDiagTailX0RatChunk001Sub001Block096Part013

theorem surrogateDiagonalTailChunk001Sub001Block096Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part013] using hcert

def TailChunk001Sub001Block096Part014SupportExplicit : Finset ℕ :=
  ([28693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part014 : ℚ :=
  (1050327776075 : ℚ) / 456972095344121976384

def SurrogateDiagonalTailChunk001Sub001Block096Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28693
    = surrogateDiagTailX0RatChunk001Sub001Block096Part014

theorem surrogateDiagonalTailChunk001Sub001Block096Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part014] using hcert

def TailChunk001Sub001Block096Part015SupportExplicit : Finset ℕ :=
  ([28694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part015 : ℚ :=
  (3216193890625 : ℚ) / 26478304580206052082

def SurrogateDiagonalTailChunk001Sub001Block096Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28694
    = surrogateDiagTailX0RatChunk001Sub001Block096Part015

theorem surrogateDiagonalTailChunk001Sub001Block096Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part015] using hcert

def TailChunk001Sub001Block096Part016SupportExplicit : Finset ℕ :=
  ([28695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part016 : ℚ :=
  (57421994675 : ℚ) / 17109935470559625216

def SurrogateDiagonalTailChunk001Sub001Block096Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28695
    = surrogateDiagTailX0RatChunk001Sub001Block096Part016

theorem surrogateDiagonalTailChunk001Sub001Block096Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part016] using hcert

def TailChunk001Sub001Block096Part017SupportExplicit : Finset ℕ :=
  ([28697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block096Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28697
    = surrogateDiagTailX0RatChunk001Sub001Block096Part017

theorem surrogateDiagonalTailChunk001Sub001Block096Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part017] using hcert

def TailChunk001Sub001Block096Part018SupportExplicit : Finset ℕ :=
  ([28698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part018 : ℚ :=
  (5717505521725 : ℚ) / 20921129544854164608

def SurrogateDiagonalTailChunk001Sub001Block096Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28698
    = surrogateDiagTailX0RatChunk001Sub001Block096Part018

theorem surrogateDiagonalTailChunk001Sub001Block096Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part018] using hcert

def TailChunk001Sub001Block096Part019SupportExplicit : Finset ℕ :=
  ([28699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part019 : ℚ :=
  (8531655511 : ℚ) / 11567971423882444800

def SurrogateDiagonalTailChunk001Sub001Block096Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28699
    = surrogateDiagTailX0RatChunk001Sub001Block096Part019

theorem surrogateDiagonalTailChunk001Sub001Block096Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part019] using hcert

def TailChunk001Sub001Block096Part020SupportExplicit : Finset ℕ :=
  ([28702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part020 : ℚ :=
  (12520712351125 : ℚ) / 99170186514588499968

def SurrogateDiagonalTailChunk001Sub001Block096Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28702
    = surrogateDiagTailX0RatChunk001Sub001Block096Part020

theorem surrogateDiagonalTailChunk001Sub001Block096Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part020] using hcert

def TailChunk001Sub001Block096Part021SupportExplicit : Finset ℕ :=
  ([28703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block096Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28703
    = surrogateDiagTailX0RatChunk001Sub001Block096Part021

theorem surrogateDiagonalTailChunk001Sub001Block096Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part021] using hcert

def TailChunk001Sub001Block096Part022SupportExplicit : Finset ℕ :=
  ([28705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part022 : ℚ :=
  (17875 : ℚ) / 9926961870895104

def SurrogateDiagonalTailChunk001Sub001Block096Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28705
    = surrogateDiagTailX0RatChunk001Sub001Block096Part022

theorem surrogateDiagonalTailChunk001Sub001Block096Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part022] using hcert

def TailChunk001Sub001Block096Part023SupportExplicit : Finset ℕ :=
  ([28706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part023 : ℚ :=
  (10800253333 : ℚ) / 82021415047608960

def SurrogateDiagonalTailChunk001Sub001Block096Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28706
    = surrogateDiagTailX0RatChunk001Sub001Block096Part023

theorem surrogateDiagonalTailChunk001Sub001Block096Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part023] using hcert

def TailChunk001Sub001Block096Part024SupportExplicit : Finset ℕ :=
  ([28707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block096Part024 : ℚ :=
  (292527827425 : ℚ) / 45133046453740442112

def SurrogateDiagonalTailChunk001Sub001Block096Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28707
    = surrogateDiagTailX0RatChunk001Sub001Block096Part024

theorem surrogateDiagonalTailChunk001Sub001Block096Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block096Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block096Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block096Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block096Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block096Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block096Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block096HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block096Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block096Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block096Part000
    + surrogateDiagTailX0RatChunk001Sub001Block096Part001
    + surrogateDiagTailX0RatChunk001Sub001Block096Part002
    + surrogateDiagTailX0RatChunk001Sub001Block096Part003
    + surrogateDiagTailX0RatChunk001Sub001Block096Part004
    + surrogateDiagTailX0RatChunk001Sub001Block096Part005
    + surrogateDiagTailX0RatChunk001Sub001Block096Part006
    + surrogateDiagTailX0RatChunk001Sub001Block096Part007
    + surrogateDiagTailX0RatChunk001Sub001Block096Part008
    + surrogateDiagTailX0RatChunk001Sub001Block096Part009

def surrogateDiagonalTailChunk001Sub001Block096MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block096Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block096Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block096Part010
    + surrogateDiagTailX0RatChunk001Sub001Block096Part011
    + surrogateDiagTailX0RatChunk001Sub001Block096Part012
    + surrogateDiagTailX0RatChunk001Sub001Block096Part013
    + surrogateDiagTailX0RatChunk001Sub001Block096Part014
    + surrogateDiagTailX0RatChunk001Sub001Block096Part015
    + surrogateDiagTailX0RatChunk001Sub001Block096Part016
    + surrogateDiagTailX0RatChunk001Sub001Block096Part017
    + surrogateDiagTailX0RatChunk001Sub001Block096Part018
    + surrogateDiagTailX0RatChunk001Sub001Block096Part019

def surrogateDiagonalTailChunk001Sub001Block096TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block096Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block096Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block096Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block096Part020
    + surrogateDiagTailX0RatChunk001Sub001Block096Part021
    + surrogateDiagTailX0RatChunk001Sub001Block096Part022
    + surrogateDiagTailX0RatChunk001Sub001Block096Part023
    + surrogateDiagTailX0RatChunk001Sub001Block096Part024

def surrogateDiagonalTailChunk001Sub001Block096Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block096HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block096MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block096TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block096 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block096Part000
    + surrogateDiagTailX0RatChunk001Sub001Block096Part001
    + surrogateDiagTailX0RatChunk001Sub001Block096Part002
    + surrogateDiagTailX0RatChunk001Sub001Block096Part003
    + surrogateDiagTailX0RatChunk001Sub001Block096Part004
    + surrogateDiagTailX0RatChunk001Sub001Block096Part005
    + surrogateDiagTailX0RatChunk001Sub001Block096Part006
    + surrogateDiagTailX0RatChunk001Sub001Block096Part007
    + surrogateDiagTailX0RatChunk001Sub001Block096Part008
    + surrogateDiagTailX0RatChunk001Sub001Block096Part009
    + surrogateDiagTailX0RatChunk001Sub001Block096Part010
    + surrogateDiagTailX0RatChunk001Sub001Block096Part011
    + surrogateDiagTailX0RatChunk001Sub001Block096Part012
    + surrogateDiagTailX0RatChunk001Sub001Block096Part013
    + surrogateDiagTailX0RatChunk001Sub001Block096Part014
    + surrogateDiagTailX0RatChunk001Sub001Block096Part015
    + surrogateDiagTailX0RatChunk001Sub001Block096Part016
    + surrogateDiagTailX0RatChunk001Sub001Block096Part017
    + surrogateDiagTailX0RatChunk001Sub001Block096Part018
    + surrogateDiagTailX0RatChunk001Sub001Block096Part019
    + surrogateDiagTailX0RatChunk001Sub001Block096Part020
    + surrogateDiagTailX0RatChunk001Sub001Block096Part021
    + surrogateDiagTailX0RatChunk001Sub001Block096Part022
    + surrogateDiagTailX0RatChunk001Sub001Block096Part023
    + surrogateDiagTailX0RatChunk001Sub001Block096Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block096_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block096Head + surrogateDiagTailX0RatChunk001Sub001Block096Mid + surrogateDiagTailX0RatChunk001Sub001Block096Tail =
      surrogateDiagTailX0RatChunk001Sub001Block096 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block096Head surrogateDiagTailX0RatChunk001Sub001Block096Mid surrogateDiagTailX0RatChunk001Sub001Block096Tail surrogateDiagTailX0RatChunk001Sub001Block096
  ring

def SurrogateDiagonalTailChunk001Sub001Block096HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block096HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block096Head

def SurrogateDiagonalTailChunk001Sub001Block096MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block096MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block096Mid

def SurrogateDiagonalTailChunk001Sub001Block096TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block096TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block096Tail

theorem surrogateDiagonalTailChunk001Sub001Block096_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block096HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block096MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block096TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block096Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block096 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block096HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block096MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block096TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block096Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block096_eq_head_add_mid_add_tail

/-- Block 097 covers tail-support indices [17425,17450) and q from 28709 to 28754. -/

def TailChunk001Sub001Block097Part000SupportExplicit : Finset ℕ :=
  ([28709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part000 : ℚ :=
  (23012229373 : ℚ) / 54586425952746115200

def SurrogateDiagonalTailChunk001Sub001Block097Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28709
    = surrogateDiagTailX0RatChunk001Sub001Block097Part000

theorem surrogateDiagonalTailChunk001Sub001Block097Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part000] using hcert

def TailChunk001Sub001Block097Part001SupportExplicit : Finset ℕ :=
  ([28711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block097Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28711
    = surrogateDiagTailX0RatChunk001Sub001Block097Part001

theorem surrogateDiagonalTailChunk001Sub001Block097Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part001] using hcert

def TailChunk001Sub001Block097Part002SupportExplicit : Finset ℕ :=
  ([28713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part002 : ℚ :=
  (143200211675 : ℚ) / 130780212523784208384

def SurrogateDiagonalTailChunk001Sub001Block097Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28713
    = surrogateDiagTailX0RatChunk001Sub001Block097Part002

theorem surrogateDiagonalTailChunk001Sub001Block097Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part002] using hcert

def TailChunk001Sub001Block097Part003SupportExplicit : Finset ℕ :=
  ([28715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part003 : ℚ :=
  (7109375 : ℚ) / 3953729098531605888

def SurrogateDiagonalTailChunk001Sub001Block097Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28715
    = surrogateDiagTailX0RatChunk001Sub001Block097Part003

theorem surrogateDiagonalTailChunk001Sub001Block097Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part003] using hcert

def TailChunk001Sub001Block097Part004SupportExplicit : Finset ℕ :=
  ([28718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part004 : ℚ :=
  (2085159316725 : ℚ) / 16490916992797887488

def SurrogateDiagonalTailChunk001Sub001Block097Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28718
    = surrogateDiagTailX0RatChunk001Sub001Block097Part004

theorem surrogateDiagonalTailChunk001Sub001Block097Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part004] using hcert

def TailChunk001Sub001Block097Part005SupportExplicit : Finset ℕ :=
  ([28721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part005 : ℚ :=
  (4897373879 : ℚ) / 1241176704052469760

def SurrogateDiagonalTailChunk001Sub001Block097Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28721
    = surrogateDiagTailX0RatChunk001Sub001Block097Part005

theorem surrogateDiagonalTailChunk001Sub001Block097Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part005] using hcert

def TailChunk001Sub001Block097Part006SupportExplicit : Finset ℕ :=
  ([28722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part006 : ℚ :=
  (5727073521325 : ℚ) / 20991217019667788928

def SurrogateDiagonalTailChunk001Sub001Block097Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28722
    = surrogateDiagTailX0RatChunk001Sub001Block097Part006

theorem surrogateDiagonalTailChunk001Sub001Block097Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part006] using hcert

def TailChunk001Sub001Block097Part007SupportExplicit : Finset ℕ :=
  ([28723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block097Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28723
    = surrogateDiagTailX0RatChunk001Sub001Block097Part007

theorem surrogateDiagonalTailChunk001Sub001Block097Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part007] using hcert

def TailChunk001Sub001Block097Part008SupportExplicit : Finset ℕ :=
  ([28726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part008 : ℚ :=
  (248302280891 : ℚ) / 1943234828579865600

def SurrogateDiagonalTailChunk001Sub001Block097Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28726
    = surrogateDiagTailX0RatChunk001Sub001Block097Part008

theorem surrogateDiagonalTailChunk001Sub001Block097Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part008] using hcert

def TailChunk001Sub001Block097Part009SupportExplicit : Finset ℕ :=
  ([28727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part009 : ℚ :=
  (66001249225 : ℚ) / 236823433437939499008

def SurrogateDiagonalTailChunk001Sub001Block097Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28727
    = surrogateDiagTailX0RatChunk001Sub001Block097Part009

theorem surrogateDiagonalTailChunk001Sub001Block097Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part009] using hcert

def TailChunk001Sub001Block097Part010SupportExplicit : Finset ℕ :=
  ([28729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block097Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28729
    = surrogateDiagTailX0RatChunk001Sub001Block097Part010

theorem surrogateDiagonalTailChunk001Sub001Block097Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part010] using hcert

def TailChunk001Sub001Block097Part011SupportExplicit : Finset ℕ :=
  ([28731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part011 : ℚ :=
  (605235511 : ℚ) / 1364795928988876800

def SurrogateDiagonalTailChunk001Sub001Block097Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28731
    = surrogateDiagTailX0RatChunk001Sub001Block097Part011

theorem surrogateDiagonalTailChunk001Sub001Block097Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part011] using hcert

def TailChunk001Sub001Block097Part012SupportExplicit : Finset ℕ :=
  ([28733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part012 : ℚ :=
  (55178455625 : ℚ) / 526214311508323357056

def SurrogateDiagonalTailChunk001Sub001Block097Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28733
    = surrogateDiagTailX0RatChunk001Sub001Block097Part012

theorem surrogateDiagonalTailChunk001Sub001Block097Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part012] using hcert

def TailChunk001Sub001Block097Part013SupportExplicit : Finset ℕ :=
  ([28734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part013 : ℚ :=
  (5731860521125 : ℚ) / 21026326720584665088

def SurrogateDiagonalTailChunk001Sub001Block097Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28734
    = surrogateDiagTailX0RatChunk001Sub001Block097Part013

theorem surrogateDiagonalTailChunk001Sub001Block097Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part013] using hcert

def TailChunk001Sub001Block097Part014SupportExplicit : Finset ℕ :=
  ([28735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part014 : ℚ :=
  (30411436769 : ℚ) / 7501657483778457600

def SurrogateDiagonalTailChunk001Sub001Block097Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28735
    = surrogateDiagTailX0RatChunk001Sub001Block097Part014

theorem surrogateDiagonalTailChunk001Sub001Block097Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part014] using hcert

def TailChunk001Sub001Block097Part015SupportExplicit : Finset ℕ :=
  ([28738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part015 : ℚ :=
  (3226065015625 : ℚ) / 26641099517880041472

def SurrogateDiagonalTailChunk001Sub001Block097Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28738
    = surrogateDiagTailX0RatChunk001Sub001Block097Part015

theorem surrogateDiagonalTailChunk001Sub001Block097Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part015] using hcert

def TailChunk001Sub001Block097Part016SupportExplicit : Finset ℕ :=
  ([28739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part016 : ℚ :=
  (3147684601 : ℚ) / 14763854708569612800

def SurrogateDiagonalTailChunk001Sub001Block097Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28739
    = surrogateDiagTailX0RatChunk001Sub001Block097Part016

theorem surrogateDiagonalTailChunk001Sub001Block097Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part016] using hcert

def TailChunk001Sub001Block097Part017SupportExplicit : Finset ℕ :=
  ([28741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part017 : ℚ :=
  (2202369 : ℚ) / 14936320000000000

def SurrogateDiagonalTailChunk001Sub001Block097Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28741
    = surrogateDiagTailX0RatChunk001Sub001Block097Part017

theorem surrogateDiagonalTailChunk001Sub001Block097Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part017] using hcert

def TailChunk001Sub001Block097Part018SupportExplicit : Finset ℕ :=
  ([28742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part018 : ℚ :=
  (9739755052225 : ℚ) / 57456780347253639168

def SurrogateDiagonalTailChunk001Sub001Block097Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28742
    = surrogateDiagTailX0RatChunk001Sub001Block097Part018

theorem surrogateDiagonalTailChunk001Sub001Block097Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part018] using hcert

def TailChunk001Sub001Block097Part019SupportExplicit : Finset ℕ :=
  ([28743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part019 : ℚ :=
  (1085356379 : ℚ) / 190806699501158400

def SurrogateDiagonalTailChunk001Sub001Block097Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28743
    = surrogateDiagTailX0RatChunk001Sub001Block097Part019

theorem surrogateDiagonalTailChunk001Sub001Block097Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part019] using hcert

def TailChunk001Sub001Block097Part020SupportExplicit : Finset ℕ :=
  ([28745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part020 : ℚ :=
  (2066219468875 : ℚ) / 698769373651794690048

def SurrogateDiagonalTailChunk001Sub001Block097Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28745
    = surrogateDiagTailX0RatChunk001Sub001Block097Part020

theorem surrogateDiagonalTailChunk001Sub001Block097Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part020] using hcert

def TailChunk001Sub001Block097Part021SupportExplicit : Finset ℕ :=
  ([28747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part021 : ℚ :=
  (4996452025 : ℚ) / 5373116657952620544

def SurrogateDiagonalTailChunk001Sub001Block097Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28747
    = surrogateDiagTailX0RatChunk001Sub001Block097Part021

theorem surrogateDiagonalTailChunk001Sub001Block097Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part021] using hcert

def TailChunk001Sub001Block097Part022SupportExplicit : Finset ℕ :=
  ([28751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block097Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28751
    = surrogateDiagTailX0RatChunk001Sub001Block097Part022

theorem surrogateDiagonalTailChunk001Sub001Block097Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part022] using hcert

def TailChunk001Sub001Block097Part023SupportExplicit : Finset ℕ :=
  ([28753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block097Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28753
    = surrogateDiagTailX0RatChunk001Sub001Block097Part023

theorem surrogateDiagonalTailChunk001Sub001Block097Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part023] using hcert

def TailChunk001Sub001Block097Part024SupportExplicit : Finset ℕ :=
  ([28754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block097Part024 : ℚ :=
  (439372177213 : ℚ) / 2909776003328899200

def SurrogateDiagonalTailChunk001Sub001Block097Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28754
    = surrogateDiagTailX0RatChunk001Sub001Block097Part024

theorem surrogateDiagonalTailChunk001Sub001Block097Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block097Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block097Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block097Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block097Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block097Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block097Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block097HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block097Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block097Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block097Part000
    + surrogateDiagTailX0RatChunk001Sub001Block097Part001
    + surrogateDiagTailX0RatChunk001Sub001Block097Part002
    + surrogateDiagTailX0RatChunk001Sub001Block097Part003
    + surrogateDiagTailX0RatChunk001Sub001Block097Part004
    + surrogateDiagTailX0RatChunk001Sub001Block097Part005
    + surrogateDiagTailX0RatChunk001Sub001Block097Part006
    + surrogateDiagTailX0RatChunk001Sub001Block097Part007
    + surrogateDiagTailX0RatChunk001Sub001Block097Part008
    + surrogateDiagTailX0RatChunk001Sub001Block097Part009

def surrogateDiagonalTailChunk001Sub001Block097MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block097Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block097Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block097Part010
    + surrogateDiagTailX0RatChunk001Sub001Block097Part011
    + surrogateDiagTailX0RatChunk001Sub001Block097Part012
    + surrogateDiagTailX0RatChunk001Sub001Block097Part013
    + surrogateDiagTailX0RatChunk001Sub001Block097Part014
    + surrogateDiagTailX0RatChunk001Sub001Block097Part015
    + surrogateDiagTailX0RatChunk001Sub001Block097Part016
    + surrogateDiagTailX0RatChunk001Sub001Block097Part017
    + surrogateDiagTailX0RatChunk001Sub001Block097Part018
    + surrogateDiagTailX0RatChunk001Sub001Block097Part019

def surrogateDiagonalTailChunk001Sub001Block097TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block097Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block097Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block097Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block097Part020
    + surrogateDiagTailX0RatChunk001Sub001Block097Part021
    + surrogateDiagTailX0RatChunk001Sub001Block097Part022
    + surrogateDiagTailX0RatChunk001Sub001Block097Part023
    + surrogateDiagTailX0RatChunk001Sub001Block097Part024

def surrogateDiagonalTailChunk001Sub001Block097Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block097HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block097MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block097TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block097 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block097Part000
    + surrogateDiagTailX0RatChunk001Sub001Block097Part001
    + surrogateDiagTailX0RatChunk001Sub001Block097Part002
    + surrogateDiagTailX0RatChunk001Sub001Block097Part003
    + surrogateDiagTailX0RatChunk001Sub001Block097Part004
    + surrogateDiagTailX0RatChunk001Sub001Block097Part005
    + surrogateDiagTailX0RatChunk001Sub001Block097Part006
    + surrogateDiagTailX0RatChunk001Sub001Block097Part007
    + surrogateDiagTailX0RatChunk001Sub001Block097Part008
    + surrogateDiagTailX0RatChunk001Sub001Block097Part009
    + surrogateDiagTailX0RatChunk001Sub001Block097Part010
    + surrogateDiagTailX0RatChunk001Sub001Block097Part011
    + surrogateDiagTailX0RatChunk001Sub001Block097Part012
    + surrogateDiagTailX0RatChunk001Sub001Block097Part013
    + surrogateDiagTailX0RatChunk001Sub001Block097Part014
    + surrogateDiagTailX0RatChunk001Sub001Block097Part015
    + surrogateDiagTailX0RatChunk001Sub001Block097Part016
    + surrogateDiagTailX0RatChunk001Sub001Block097Part017
    + surrogateDiagTailX0RatChunk001Sub001Block097Part018
    + surrogateDiagTailX0RatChunk001Sub001Block097Part019
    + surrogateDiagTailX0RatChunk001Sub001Block097Part020
    + surrogateDiagTailX0RatChunk001Sub001Block097Part021
    + surrogateDiagTailX0RatChunk001Sub001Block097Part022
    + surrogateDiagTailX0RatChunk001Sub001Block097Part023
    + surrogateDiagTailX0RatChunk001Sub001Block097Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block097_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block097Head + surrogateDiagTailX0RatChunk001Sub001Block097Mid + surrogateDiagTailX0RatChunk001Sub001Block097Tail =
      surrogateDiagTailX0RatChunk001Sub001Block097 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block097Head surrogateDiagTailX0RatChunk001Sub001Block097Mid surrogateDiagTailX0RatChunk001Sub001Block097Tail surrogateDiagTailX0RatChunk001Sub001Block097
  ring

def SurrogateDiagonalTailChunk001Sub001Block097HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block097HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block097Head

def SurrogateDiagonalTailChunk001Sub001Block097MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block097MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block097Mid

def SurrogateDiagonalTailChunk001Sub001Block097TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block097TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block097Tail

theorem surrogateDiagonalTailChunk001Sub001Block097_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block097HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block097MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block097TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block097Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block097 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block097HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block097MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block097TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block097Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block097_eq_head_add_mid_add_tail

/-- Block 098 covers tail-support indices [17450,17475) and q from 28757 to 28795. -/

def TailChunk001Sub001Block098Part000SupportExplicit : Finset ℕ :=
  ([28757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part000 : ℚ :=
  (53228601575 : ℚ) / 815170847066013302784

def SurrogateDiagonalTailChunk001Sub001Block098Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28757
    = surrogateDiagTailX0RatChunk001Sub001Block098Part000

theorem surrogateDiagonalTailChunk001Sub001Block098Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part000] using hcert

def TailChunk001Sub001Block098Part001SupportExplicit : Finset ℕ :=
  ([28758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part001 : ℚ :=
  (5741440520725 : ℚ) / 21096678233296109568

def SurrogateDiagonalTailChunk001Sub001Block098Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28758
    = surrogateDiagTailX0RatChunk001Sub001Block098Part001

theorem surrogateDiagonalTailChunk001Sub001Block098Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part001] using hcert

def TailChunk001Sub001Block098Part002SupportExplicit : Finset ℕ :=
  ([28759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block098Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28759
    = surrogateDiagTailX0RatChunk001Sub001Block098Part002

theorem surrogateDiagonalTailChunk001Sub001Block098Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part002] using hcert

def TailChunk001Sub001Block098Part003SupportExplicit : Finset ℕ :=
  ([28761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part003 : ℚ :=
  (125025 : ℚ) / 67552229270630528

def SurrogateDiagonalTailChunk001Sub001Block098Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28761
    = surrogateDiagTailX0RatChunk001Sub001Block098Part003

theorem surrogateDiagonalTailChunk001Sub001Block098Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part003] using hcert

def TailChunk001Sub001Block098Part004SupportExplicit : Finset ℕ :=
  ([28762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part004 : ℚ :=
  (6263900816975 : ℚ) / 49585093257294249984

def SurrogateDiagonalTailChunk001Sub001Block098Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28762
    = surrogateDiagTailX0RatChunk001Sub001Block098Part004

theorem surrogateDiagonalTailChunk001Sub001Block098Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part004] using hcert

def TailChunk001Sub001Block098Part005SupportExplicit : Finset ℕ :=
  ([28765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part005 : ℚ :=
  (94506357433 : ℚ) / 19011169219085107200

def SurrogateDiagonalTailChunk001Sub001Block098Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28765
    = surrogateDiagTailX0RatChunk001Sub001Block098Part005

theorem surrogateDiagonalTailChunk001Sub001Block098Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part005] using hcert

def TailChunk001Sub001Block098Part006SupportExplicit : Finset ℕ :=
  ([28766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part006 : ℚ :=
  (842489825675 : ℚ) / 6124575963918892032

def SurrogateDiagonalTailChunk001Sub001Block098Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28766
    = surrogateDiagTailX0RatChunk001Sub001Block098Part006

theorem surrogateDiagonalTailChunk001Sub001Block098Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part006] using hcert

def TailChunk001Sub001Block098Part007SupportExplicit : Finset ℕ :=
  ([28767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part007 : ℚ :=
  (39722053075 : ℚ) / 75595494035837809152

def SurrogateDiagonalTailChunk001Sub001Block098Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28767
    = surrogateDiagTailX0RatChunk001Sub001Block098Part007

theorem surrogateDiagonalTailChunk001Sub001Block098Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part007] using hcert

def TailChunk001Sub001Block098Part008SupportExplicit : Finset ℕ :=
  ([28769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part008 : ℚ :=
  (65772352175 : ℚ) / 88667466173897490432

def SurrogateDiagonalTailChunk001Sub001Block098Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28769
    = surrogateDiagTailX0RatChunk001Sub001Block098Part008

theorem surrogateDiagonalTailChunk001Sub001Block098Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part008] using hcert

def TailChunk001Sub001Block098Part009SupportExplicit : Finset ℕ :=
  ([28770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part009 : ℚ :=
  (44640469975 : ℚ) / 63068854837837824

def SurrogateDiagonalTailChunk001Sub001Block098Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28770
    = surrogateDiagTailX0RatChunk001Sub001Block098Part009

theorem surrogateDiagonalTailChunk001Sub001Block098Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part009] using hcert

def TailChunk001Sub001Block098Part010SupportExplicit : Finset ℕ :=
  ([28771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block098Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28771
    = surrogateDiagTailX0RatChunk001Sub001Block098Part010

theorem surrogateDiagonalTailChunk001Sub001Block098Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part010] using hcert

def TailChunk001Sub001Block098Part011SupportExplicit : Finset ℕ :=
  ([28774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part011 : ℚ :=
  (3234152640625 : ℚ) / 26774852770614178002

def SurrogateDiagonalTailChunk001Sub001Block098Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28774
    = surrogateDiagTailX0RatChunk001Sub001Block098Part011

theorem surrogateDiagonalTailChunk001Sub001Block098Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part011] using hcert

def TailChunk001Sub001Block098Part012SupportExplicit : Finset ℕ :=
  ([28777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part012 : ℚ :=
  (42305248213 : ℚ) / 36987854387995267200

def SurrogateDiagonalTailChunk001Sub001Block098Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28777
    = surrogateDiagTailX0RatChunk001Sub001Block098Part012

theorem surrogateDiagonalTailChunk001Sub001Block098Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part012] using hcert

def TailChunk001Sub001Block098Part013SupportExplicit : Finset ℕ :=
  ([28778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part013 : ℚ :=
  (3235051890625 : ℚ) / 26789745269883400992

def SurrogateDiagonalTailChunk001Sub001Block098Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28778
    = surrogateDiagTailX0RatChunk001Sub001Block098Part013

theorem surrogateDiagonalTailChunk001Sub001Block098Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part013] using hcert

def TailChunk001Sub001Block098Part014SupportExplicit : Finset ℕ :=
  ([28779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part014 : ℚ :=
  (751832387 : ℚ) / 1535395420112486400

def SurrogateDiagonalTailChunk001Sub001Block098Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28779
    = surrogateDiagTailX0RatChunk001Sub001Block098Part014

theorem surrogateDiagonalTailChunk001Sub001Block098Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part014] using hcert

def TailChunk001Sub001Block098Part015SupportExplicit : Finset ℕ :=
  ([28781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part015 : ℚ :=
  (940227925 : ℚ) / 2331770163357155328

def SurrogateDiagonalTailChunk001Sub001Block098Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28781
    = surrogateDiagTailX0RatChunk001Sub001Block098Part015

theorem surrogateDiagonalTailChunk001Sub001Block098Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part015] using hcert

def TailChunk001Sub001Block098Part016SupportExplicit : Finset ℕ :=
  ([28783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part016 : ℚ :=
  (39432930675 : ℚ) / 542835499645190281216

def SurrogateDiagonalTailChunk001Sub001Block098Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28783
    = surrogateDiagTailX0RatChunk001Sub001Block098Part016

theorem surrogateDiagonalTailChunk001Sub001Block098Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part016] using hcert

def TailChunk001Sub001Block098Part017SupportExplicit : Finset ℕ :=
  ([28785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part017 : ℚ :=
  (1868881817 : ℚ) / 134396153856000000

def SurrogateDiagonalTailChunk001Sub001Block098Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28785
    = surrogateDiagTailX0RatChunk001Sub001Block098Part017

theorem surrogateDiagonalTailChunk001Sub001Block098Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part017] using hcert

def TailChunk001Sub001Block098Part018SupportExplicit : Finset ℕ :=
  ([28786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part018 : ℚ :=
  (1368833565425 : ℚ) / 10575995440032940032

def SurrogateDiagonalTailChunk001Sub001Block098Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28786
    = surrogateDiagTailX0RatChunk001Sub001Block098Part018

theorem surrogateDiagonalTailChunk001Sub001Block098Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part018] using hcert

def TailChunk001Sub001Block098Part019SupportExplicit : Finset ℕ :=
  ([28787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part019 : ℚ :=
  (1723376443 : ℚ) / 4684225660194078720

def SurrogateDiagonalTailChunk001Sub001Block098Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28787
    = surrogateDiagTailX0RatChunk001Sub001Block098Part019

theorem surrogateDiagonalTailChunk001Sub001Block098Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part019] using hcert

def TailChunk001Sub001Block098Part020SupportExplicit : Finset ℕ :=
  ([28789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block098Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28789
    = surrogateDiagTailX0RatChunk001Sub001Block098Part020

theorem surrogateDiagonalTailChunk001Sub001Block098Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part020] using hcert

def TailChunk001Sub001Block098Part021SupportExplicit : Finset ℕ :=
  ([28790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part021 : ℚ :=
  (8802642941725 : ℚ) / 43916728698193594368

def SurrogateDiagonalTailChunk001Sub001Block098Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28790
    = surrogateDiagTailX0RatChunk001Sub001Block098Part021

theorem surrogateDiagonalTailChunk001Sub001Block098Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part021] using hcert

def TailChunk001Sub001Block098Part022SupportExplicit : Finset ℕ :=
  ([28793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block098Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28793
    = surrogateDiagTailX0RatChunk001Sub001Block098Part022

theorem surrogateDiagonalTailChunk001Sub001Block098Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part022] using hcert

def TailChunk001Sub001Block098Part023SupportExplicit : Finset ℕ :=
  ([28794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part023 : ℚ :=
  (5755825520125 : ℚ) / 21202536331591091328

def SurrogateDiagonalTailChunk001Sub001Block098Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28794
    = surrogateDiagTailX0RatChunk001Sub001Block098Part023

theorem surrogateDiagonalTailChunk001Sub001Block098Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part023] using hcert

def TailChunk001Sub001Block098Part024SupportExplicit : Finset ℕ :=
  ([28795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block098Part024 : ℚ :=
  (1130894435525 : ℚ) / 253309157300177731584

def SurrogateDiagonalTailChunk001Sub001Block098Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28795
    = surrogateDiagTailX0RatChunk001Sub001Block098Part024

theorem surrogateDiagonalTailChunk001Sub001Block098Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block098Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block098Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block098Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block098Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block098Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block098Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block098HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block098Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block098Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block098Part000
    + surrogateDiagTailX0RatChunk001Sub001Block098Part001
    + surrogateDiagTailX0RatChunk001Sub001Block098Part002
    + surrogateDiagTailX0RatChunk001Sub001Block098Part003
    + surrogateDiagTailX0RatChunk001Sub001Block098Part004
    + surrogateDiagTailX0RatChunk001Sub001Block098Part005
    + surrogateDiagTailX0RatChunk001Sub001Block098Part006
    + surrogateDiagTailX0RatChunk001Sub001Block098Part007
    + surrogateDiagTailX0RatChunk001Sub001Block098Part008
    + surrogateDiagTailX0RatChunk001Sub001Block098Part009

def surrogateDiagonalTailChunk001Sub001Block098MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block098Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block098Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block098Part010
    + surrogateDiagTailX0RatChunk001Sub001Block098Part011
    + surrogateDiagTailX0RatChunk001Sub001Block098Part012
    + surrogateDiagTailX0RatChunk001Sub001Block098Part013
    + surrogateDiagTailX0RatChunk001Sub001Block098Part014
    + surrogateDiagTailX0RatChunk001Sub001Block098Part015
    + surrogateDiagTailX0RatChunk001Sub001Block098Part016
    + surrogateDiagTailX0RatChunk001Sub001Block098Part017
    + surrogateDiagTailX0RatChunk001Sub001Block098Part018
    + surrogateDiagTailX0RatChunk001Sub001Block098Part019

def surrogateDiagonalTailChunk001Sub001Block098TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block098Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block098Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block098Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block098Part020
    + surrogateDiagTailX0RatChunk001Sub001Block098Part021
    + surrogateDiagTailX0RatChunk001Sub001Block098Part022
    + surrogateDiagTailX0RatChunk001Sub001Block098Part023
    + surrogateDiagTailX0RatChunk001Sub001Block098Part024

def surrogateDiagonalTailChunk001Sub001Block098Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block098HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block098MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block098TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block098 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block098Part000
    + surrogateDiagTailX0RatChunk001Sub001Block098Part001
    + surrogateDiagTailX0RatChunk001Sub001Block098Part002
    + surrogateDiagTailX0RatChunk001Sub001Block098Part003
    + surrogateDiagTailX0RatChunk001Sub001Block098Part004
    + surrogateDiagTailX0RatChunk001Sub001Block098Part005
    + surrogateDiagTailX0RatChunk001Sub001Block098Part006
    + surrogateDiagTailX0RatChunk001Sub001Block098Part007
    + surrogateDiagTailX0RatChunk001Sub001Block098Part008
    + surrogateDiagTailX0RatChunk001Sub001Block098Part009
    + surrogateDiagTailX0RatChunk001Sub001Block098Part010
    + surrogateDiagTailX0RatChunk001Sub001Block098Part011
    + surrogateDiagTailX0RatChunk001Sub001Block098Part012
    + surrogateDiagTailX0RatChunk001Sub001Block098Part013
    + surrogateDiagTailX0RatChunk001Sub001Block098Part014
    + surrogateDiagTailX0RatChunk001Sub001Block098Part015
    + surrogateDiagTailX0RatChunk001Sub001Block098Part016
    + surrogateDiagTailX0RatChunk001Sub001Block098Part017
    + surrogateDiagTailX0RatChunk001Sub001Block098Part018
    + surrogateDiagTailX0RatChunk001Sub001Block098Part019
    + surrogateDiagTailX0RatChunk001Sub001Block098Part020
    + surrogateDiagTailX0RatChunk001Sub001Block098Part021
    + surrogateDiagTailX0RatChunk001Sub001Block098Part022
    + surrogateDiagTailX0RatChunk001Sub001Block098Part023
    + surrogateDiagTailX0RatChunk001Sub001Block098Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block098_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block098Head + surrogateDiagTailX0RatChunk001Sub001Block098Mid + surrogateDiagTailX0RatChunk001Sub001Block098Tail =
      surrogateDiagTailX0RatChunk001Sub001Block098 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block098Head surrogateDiagTailX0RatChunk001Sub001Block098Mid surrogateDiagTailX0RatChunk001Sub001Block098Tail surrogateDiagTailX0RatChunk001Sub001Block098
  ring

def SurrogateDiagonalTailChunk001Sub001Block098HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block098HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block098Head

def SurrogateDiagonalTailChunk001Sub001Block098MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block098MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block098Mid

def SurrogateDiagonalTailChunk001Sub001Block098TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block098TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block098Tail

theorem surrogateDiagonalTailChunk001Sub001Block098_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block098HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block098MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block098TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block098Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block098 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block098HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block098MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block098TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block098Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block098_eq_head_add_mid_add_tail

/-- Block 099 covers tail-support indices [17475,17500) and q from 28797 to 28837. -/

def TailChunk001Sub001Block099Part000SupportExplicit : Finset ℕ :=
  ([28797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part000 : ℚ :=
  (177312497 : ℚ) / 233305358357643264

def SurrogateDiagonalTailChunk001Sub001Block099Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28797
    = surrogateDiagTailX0RatChunk001Sub001Block099Part000

theorem surrogateDiagonalTailChunk001Sub001Block099Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part000] using hcert

def TailChunk001Sub001Block099Part001SupportExplicit : Finset ℕ :=
  ([28799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part001 : ℚ :=
  (742041581 : ℚ) / 4005645530934804480

def SurrogateDiagonalTailChunk001Sub001Block099Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28799
    = surrogateDiagTailX0RatChunk001Sub001Block099Part001

theorem surrogateDiagonalTailChunk001Sub001Block099Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part001] using hcert

def TailChunk001Sub001Block099Part002SupportExplicit : Finset ℕ :=
  ([28801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part002 : ℚ :=
  (45816084375 : ℚ) / 540089095484109064576

def SurrogateDiagonalTailChunk001Sub001Block099Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28801
    = surrogateDiagTailX0RatChunk001Sub001Block099Part002

theorem surrogateDiagonalTailChunk001Sub001Block099Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part002] using hcert

def TailChunk001Sub001Block099Part003SupportExplicit : Finset ℕ :=
  ([28802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part003 : ℚ :=
  (207388801 : ℚ) / 1720270769356800

def SurrogateDiagonalTailChunk001Sub001Block099Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28802
    = surrogateDiagTailX0RatChunk001Sub001Block099Part003

theorem surrogateDiagonalTailChunk001Sub001Block099Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part003] using hcert

def TailChunk001Sub001Block099Part004SupportExplicit : Finset ℕ :=
  ([28803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part004 : ℚ :=
  (1667 : ℚ) / 905969664000000

def SurrogateDiagonalTailChunk001Sub001Block099Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28803
    = surrogateDiagTailX0RatChunk001Sub001Block099Part004

theorem surrogateDiagonalTailChunk001Sub001Block099Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part004] using hcert

def TailChunk001Sub001Block099Part005SupportExplicit : Finset ℕ :=
  ([28805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part005 : ℚ :=
  (197713739425 : ℚ) / 31562969077755961344

def SurrogateDiagonalTailChunk001Sub001Block099Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28805
    = surrogateDiagTailX0RatChunk001Sub001Block099Part005

theorem surrogateDiagonalTailChunk001Sub001Block099Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part005] using hcert

def TailChunk001Sub001Block099Part006SupportExplicit : Finset ℕ :=
  ([28806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part006 : ℚ :=
  (230424980797 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk001Sub001Block099Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28806
    = surrogateDiagTailX0RatChunk001Sub001Block099Part006

theorem surrogateDiagonalTailChunk001Sub001Block099Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part006] using hcert

def TailChunk001Sub001Block099Part007SupportExplicit : Finset ℕ :=
  ([28807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block099Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28807
    = surrogateDiagTailX0RatChunk001Sub001Block099Part007

theorem surrogateDiagonalTailChunk001Sub001Block099Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part007] using hcert

def TailChunk001Sub001Block099Part008SupportExplicit : Finset ℕ :=
  ([28810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part008 : ℚ :=
  (251280316075 : ℚ) / 1145317213755703296

def SurrogateDiagonalTailChunk001Sub001Block099Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28810
    = surrogateDiagTailX0RatChunk001Sub001Block099Part008

theorem surrogateDiagonalTailChunk001Sub001Block099Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part008] using hcert

def TailChunk001Sub001Block099Part009SupportExplicit : Finset ℕ :=
  ([28811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part009 : ℚ :=
  (8753824625 : ℚ) / 68286686244620138496

def SurrogateDiagonalTailChunk001Sub001Block099Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28811
    = surrogateDiagTailX0RatChunk001Sub001Block099Part009

theorem surrogateDiagonalTailChunk001Sub001Block099Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part009] using hcert

def TailChunk001Sub001Block099Part010SupportExplicit : Finset ℕ :=
  ([28813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block099Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28813
    = surrogateDiagTailX0RatChunk001Sub001Block099Part010

theorem surrogateDiagonalTailChunk001Sub001Block099Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part010] using hcert

def TailChunk001Sub001Block099Part011SupportExplicit : Finset ℕ :=
  ([28814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part011 : ℚ :=
  (3243150765625 : ℚ) / 26924057496129085362

def SurrogateDiagonalTailChunk001Sub001Block099Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28814
    = surrogateDiagTailX0RatChunk001Sub001Block099Part011

theorem surrogateDiagonalTailChunk001Sub001Block099Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part011] using hcert

def TailChunk001Sub001Block099Part012SupportExplicit : Finset ℕ :=
  ([28815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part012 : ℚ :=
  (62965296825 : ℚ) / 5029438864331112448

def SurrogateDiagonalTailChunk001Sub001Block099Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28815
    = surrogateDiagTailX0RatChunk001Sub001Block099Part012

theorem surrogateDiagonalTailChunk001Sub001Block099Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part012] using hcert

def TailChunk001Sub001Block099Part013SupportExplicit : Finset ℕ :=
  ([28817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block099Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28817
    = surrogateDiagTailX0RatChunk001Sub001Block099Part013

theorem surrogateDiagonalTailChunk001Sub001Block099Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part013] using hcert

def TailChunk001Sub001Block099Part014SupportExplicit : Finset ℕ :=
  ([28819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part014 : ℚ :=
  (1330334501125 : ℚ) / 762083560009715632128

def SurrogateDiagonalTailChunk001Sub001Block099Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28819
    = surrogateDiagTailX0RatChunk001Sub001Block099Part014

theorem surrogateDiagonalTailChunk001Sub001Block099Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part014] using hcert

def TailChunk001Sub001Block099Part015SupportExplicit : Finset ℕ :=
  ([28821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part015 : ℚ :=
  (112525858825 : ℚ) / 61522968438838075392

def SurrogateDiagonalTailChunk001Sub001Block099Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28821
    = surrogateDiagTailX0RatChunk001Sub001Block099Part015

theorem surrogateDiagonalTailChunk001Sub001Block099Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part015] using hcert

def TailChunk001Sub001Block099Part016SupportExplicit : Finset ℕ :=
  ([28822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part016 : ℚ :=
  (5191923025 : ℚ) / 43126356980296722

def SurrogateDiagonalTailChunk001Sub001Block099Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28822
    = surrogateDiagTailX0RatChunk001Sub001Block099Part016

theorem surrogateDiagonalTailChunk001Sub001Block099Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part016] using hcert

def TailChunk001Sub001Block099Part017SupportExplicit : Finset ℕ :=
  ([28823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part017 : ℚ :=
  (11010900113 : ℚ) / 15048928690333286400

def SurrogateDiagonalTailChunk001Sub001Block099Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28823
    = surrogateDiagTailX0RatChunk001Sub001Block099Part017

theorem surrogateDiagonalTailChunk001Sub001Block099Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part017] using hcert

def TailChunk001Sub001Block099Part018SupportExplicit : Finset ℕ :=
  ([28826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part018 : ℚ :=
  (20647305667 : ℚ) / 106278063394406400

def SurrogateDiagonalTailChunk001Sub001Block099Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28826
    = surrogateDiagTailX0RatChunk001Sub001Block099Part018

theorem surrogateDiagonalTailChunk001Sub001Block099Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part018] using hcert

def TailChunk001Sub001Block099Part019SupportExplicit : Finset ℕ :=
  ([28829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part019 : ℚ :=
  (54476030375 : ℚ) / 822077572713509818944

def SurrogateDiagonalTailChunk001Sub001Block099Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28829
    = surrogateDiagTailX0RatChunk001Sub001Block099Part019

theorem surrogateDiagonalTailChunk001Sub001Block099Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part019] using hcert

def TailChunk001Sub001Block099Part020SupportExplicit : Finset ℕ :=
  ([28831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part020 : ℚ :=
  (8610059791 : ℚ) / 11782352839368000000

def SurrogateDiagonalTailChunk001Sub001Block099Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28831
    = surrogateDiagTailX0RatChunk001Sub001Block099Part020

theorem surrogateDiagonalTailChunk001Sub001Block099Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part020] using hcert

def TailChunk001Sub001Block099Part021SupportExplicit : Finset ℕ :=
  ([28833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part021 : ℚ :=
  (241375 : ℚ) / 62479005474816

def SurrogateDiagonalTailChunk001Sub001Block099Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28833
    = surrogateDiagTailX0RatChunk001Sub001Block099Part021

theorem surrogateDiagonalTailChunk001Sub001Block099Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part021] using hcert

def TailChunk001Sub001Block099Part022SupportExplicit : Finset ℕ :=
  ([28834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part022 : ℚ :=
  (1893487526575 : ℚ) / 13024457239755276288

def SurrogateDiagonalTailChunk001Sub001Block099Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28834
    = surrogateDiagTailX0RatChunk001Sub001Block099Part022

theorem surrogateDiagonalTailChunk001Sub001Block099Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part022] using hcert

def TailChunk001Sub001Block099Part023SupportExplicit : Finset ℕ :=
  ([28835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part023 : ℚ :=
  (1079938843775 : ℚ) / 318379594314525179904

def SurrogateDiagonalTailChunk001Sub001Block099Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28835
    = surrogateDiagTailX0RatChunk001Sub001Block099Part023

theorem surrogateDiagonalTailChunk001Sub001Block099Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part023] using hcert

def TailChunk001Sub001Block099Part024SupportExplicit : Finset ℕ :=
  ([28837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block099Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block099Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28837
    = surrogateDiagTailX0RatChunk001Sub001Block099Part024

theorem surrogateDiagonalTailChunk001Sub001Block099Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block099Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block099Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block099Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block099Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block099Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block099Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block099HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block099Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block099Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block099Part000
    + surrogateDiagTailX0RatChunk001Sub001Block099Part001
    + surrogateDiagTailX0RatChunk001Sub001Block099Part002
    + surrogateDiagTailX0RatChunk001Sub001Block099Part003
    + surrogateDiagTailX0RatChunk001Sub001Block099Part004
    + surrogateDiagTailX0RatChunk001Sub001Block099Part005
    + surrogateDiagTailX0RatChunk001Sub001Block099Part006
    + surrogateDiagTailX0RatChunk001Sub001Block099Part007
    + surrogateDiagTailX0RatChunk001Sub001Block099Part008
    + surrogateDiagTailX0RatChunk001Sub001Block099Part009

def surrogateDiagonalTailChunk001Sub001Block099MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block099Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block099Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block099Part010
    + surrogateDiagTailX0RatChunk001Sub001Block099Part011
    + surrogateDiagTailX0RatChunk001Sub001Block099Part012
    + surrogateDiagTailX0RatChunk001Sub001Block099Part013
    + surrogateDiagTailX0RatChunk001Sub001Block099Part014
    + surrogateDiagTailX0RatChunk001Sub001Block099Part015
    + surrogateDiagTailX0RatChunk001Sub001Block099Part016
    + surrogateDiagTailX0RatChunk001Sub001Block099Part017
    + surrogateDiagTailX0RatChunk001Sub001Block099Part018
    + surrogateDiagTailX0RatChunk001Sub001Block099Part019

def surrogateDiagonalTailChunk001Sub001Block099TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block099Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block099Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block099Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block099Part020
    + surrogateDiagTailX0RatChunk001Sub001Block099Part021
    + surrogateDiagTailX0RatChunk001Sub001Block099Part022
    + surrogateDiagTailX0RatChunk001Sub001Block099Part023
    + surrogateDiagTailX0RatChunk001Sub001Block099Part024

def surrogateDiagonalTailChunk001Sub001Block099Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block099HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block099MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block099TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block099 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block099Part000
    + surrogateDiagTailX0RatChunk001Sub001Block099Part001
    + surrogateDiagTailX0RatChunk001Sub001Block099Part002
    + surrogateDiagTailX0RatChunk001Sub001Block099Part003
    + surrogateDiagTailX0RatChunk001Sub001Block099Part004
    + surrogateDiagTailX0RatChunk001Sub001Block099Part005
    + surrogateDiagTailX0RatChunk001Sub001Block099Part006
    + surrogateDiagTailX0RatChunk001Sub001Block099Part007
    + surrogateDiagTailX0RatChunk001Sub001Block099Part008
    + surrogateDiagTailX0RatChunk001Sub001Block099Part009
    + surrogateDiagTailX0RatChunk001Sub001Block099Part010
    + surrogateDiagTailX0RatChunk001Sub001Block099Part011
    + surrogateDiagTailX0RatChunk001Sub001Block099Part012
    + surrogateDiagTailX0RatChunk001Sub001Block099Part013
    + surrogateDiagTailX0RatChunk001Sub001Block099Part014
    + surrogateDiagTailX0RatChunk001Sub001Block099Part015
    + surrogateDiagTailX0RatChunk001Sub001Block099Part016
    + surrogateDiagTailX0RatChunk001Sub001Block099Part017
    + surrogateDiagTailX0RatChunk001Sub001Block099Part018
    + surrogateDiagTailX0RatChunk001Sub001Block099Part019
    + surrogateDiagTailX0RatChunk001Sub001Block099Part020
    + surrogateDiagTailX0RatChunk001Sub001Block099Part021
    + surrogateDiagTailX0RatChunk001Sub001Block099Part022
    + surrogateDiagTailX0RatChunk001Sub001Block099Part023
    + surrogateDiagTailX0RatChunk001Sub001Block099Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block099_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block099Head + surrogateDiagTailX0RatChunk001Sub001Block099Mid + surrogateDiagTailX0RatChunk001Sub001Block099Tail =
      surrogateDiagTailX0RatChunk001Sub001Block099 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block099Head surrogateDiagTailX0RatChunk001Sub001Block099Mid surrogateDiagTailX0RatChunk001Sub001Block099Tail surrogateDiagTailX0RatChunk001Sub001Block099
  ring

def SurrogateDiagonalTailChunk001Sub001Block099HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block099HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block099Head

def SurrogateDiagonalTailChunk001Sub001Block099MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block099MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block099Mid

def SurrogateDiagonalTailChunk001Sub001Block099TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block099TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block099Tail

theorem surrogateDiagonalTailChunk001Sub001Block099_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block099HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block099MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block099TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block099Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block099 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block099HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block099MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block099TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block099Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block099_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
