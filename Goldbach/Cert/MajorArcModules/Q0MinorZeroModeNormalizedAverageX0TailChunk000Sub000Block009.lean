import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [9,10). -/

/- Block 009 covers tail-support indices [225,250) and q from 421 to 458. -/

def TailChunk000Sub000Block009Part000SupportExplicit : Finset ℕ :=
  ([421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part000 : ℚ :=
  (294751783 : ℚ) / 172906574400

def SurrogateDiagonalTailChunk000Sub000Block009Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 421
    = surrogateDiagTailX0RatChunk000Sub000Block009Part000

theorem surrogateDiagonalTailChunk000Sub000Block009Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part000] using hcert

def TailChunk000Sub000Block009Part001SupportExplicit : Finset ℕ :=
  ([422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part001 : ℚ :=
  (3517159 : ℚ) / 257301450

def SurrogateDiagonalTailChunk000Sub000Block009Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 422
    = surrogateDiagTailX0RatChunk000Sub000Block009Part001

theorem surrogateDiagonalTailChunk000Sub000Block009Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part001] using hcert

def TailChunk000Sub000Block009Part002SupportExplicit : Finset ℕ :=
  ([426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part002 : ℚ :=
  (1727750461 : ℚ) / 38423683200

def SurrogateDiagonalTailChunk000Sub000Block009Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 426
    = surrogateDiagTailX0RatChunk000Sub000Block009Part002

theorem surrogateDiagonalTailChunk000Sub000Block009Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part002] using hcert

def TailChunk000Sub000Block009Part003SupportExplicit : Finset ℕ :=
  ([427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part003 : ℚ :=
  (574079129 : ℚ) / 209993990400

def SurrogateDiagonalTailChunk000Sub000Block009Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 427
    = surrogateDiagTailX0RatChunk000Sub000Block009Part003

theorem surrogateDiagonalTailChunk000Sub000Block009Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part003] using hcert

def TailChunk000Sub000Block009Part004SupportExplicit : Finset ℕ :=
  ([429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part004 : ℚ :=
  (75971491 : ℚ) / 8296058880

def SurrogateDiagonalTailChunk000Sub000Block009Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 429
    = surrogateDiagTailX0RatChunk000Sub000Block009Part004

theorem surrogateDiagonalTailChunk000Sub000Block009Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part004] using hcert

def TailChunk000Sub000Block009Part005SupportExplicit : Finset ℕ :=
  ([430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part005 : ℚ :=
  (5796439475 : ℚ) / 221320415232

def SurrogateDiagonalTailChunk000Sub000Block009Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 430
    = surrogateDiagTailX0RatChunk000Sub000Block009Part005

theorem surrogateDiagonalTailChunk000Sub000Block009Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part005] using hcert

def TailChunk000Sub000Block009Part006SupportExplicit : Finset ℕ :=
  ([431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part006 : ℚ :=
  (1019642129 : ℚ) / 683896952040

def SurrogateDiagonalTailChunk000Sub000Block009Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 431
    = surrogateDiagTailX0RatChunk000Sub000Block009Part006

theorem surrogateDiagonalTailChunk000Sub000Block009Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part006] using hcert

def TailChunk000Sub000Block009Part007SupportExplicit : Finset ℕ :=
  ([433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part007 : ℚ :=
  (7794855175 : ℚ) / 4838261538816

def SurrogateDiagonalTailChunk000Sub000Block009Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 433
    = surrogateDiagTailX0RatChunk000Sub000Block009Part007

theorem surrogateDiagonalTailChunk000Sub000Block009Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part007] using hcert

def TailChunk000Sub000Block009Part008SupportExplicit : Finset ℕ :=
  ([434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part008 : ℚ :=
  (62403103 : ℚ) / 2916583200

def SurrogateDiagonalTailChunk000Sub000Block009Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 434
    = surrogateDiagTailX0RatChunk000Sub000Block009Part008

theorem surrogateDiagonalTailChunk000Sub000Block009Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part008] using hcert

def TailChunk000Sub000Block009Part009SupportExplicit : Finset ℕ :=
  ([435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part009 : ℚ :=
  (68481428125 : ℚ) / 6295336255488

def SurrogateDiagonalTailChunk000Sub000Block009Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 435
    = surrogateDiagTailX0RatChunk000Sub000Block009Part009

theorem surrogateDiagonalTailChunk000Sub000Block009Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part009] using hcert

def TailChunk000Sub000Block009Part010SupportExplicit : Finset ℕ :=
  ([437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part010 : ℚ :=
  (19908705125 : ℚ) / 10248406711488

def SurrogateDiagonalTailChunk000Sub000Block009Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 437
    = surrogateDiagTailX0RatChunk000Sub000Block009Part010

theorem surrogateDiagonalTailChunk000Sub000Block009Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part010] using hcert

def TailChunk000Sub000Block009Part011SupportExplicit : Finset ℕ :=
  ([438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part011 : ℚ :=
  (11010322525 : ℚ) / 268792307712

def SurrogateDiagonalTailChunk000Sub000Block009Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 438
    = surrogateDiagTailX0RatChunk000Sub000Block009Part011

theorem surrogateDiagonalTailChunk000Sub000Block009Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part011] using hcert

def TailChunk000Sub000Block009Part012SupportExplicit : Finset ℕ :=
  ([439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part012 : ℚ :=
  (8012375575 : ℚ) / 5112705716676

def SurrogateDiagonalTailChunk000Sub000Block009Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 439
    = surrogateDiagTailX0RatChunk000Sub000Block009Part012

theorem surrogateDiagonalTailChunk000Sub000Block009Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part012] using hcert

def TailChunk000Sub000Block009Part013SupportExplicit : Finset ℕ :=
  ([442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part013 : ℚ :=
  (634058875 : ℚ) / 35396517888

def SurrogateDiagonalTailChunk000Sub000Block009Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 442
    = surrogateDiagTailX0RatChunk000Sub000Block009Part013

theorem surrogateDiagonalTailChunk000Sub000Block009Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part013] using hcert

def TailChunk000Sub000Block009Part014SupportExplicit : Finset ℕ :=
  ([443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part014 : ℚ :=
  (134651345125 : ℚ) / 95436814786248

def SurrogateDiagonalTailChunk000Sub000Block009Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 443
    = surrogateDiagTailX0RatChunk000Sub000Block009Part014

theorem surrogateDiagonalTailChunk000Sub000Block009Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part014] using hcert

def TailChunk000Sub000Block009Part015SupportExplicit : Finset ℕ :=
  ([445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part015 : ℚ :=
  (108706447975 : ℚ) / 38388179140608

def SurrogateDiagonalTailChunk000Sub000Block009Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 445
    = surrogateDiagTailX0RatChunk000Sub000Block009Part015

theorem surrogateDiagonalTailChunk000Sub000Block009Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part015] using hcert

def TailChunk000Sub000Block009Part016SupportExplicit : Finset ℕ :=
  ([446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part016 : ℚ :=
  (68090190025 : ℚ) / 6073496096328

def SurrogateDiagonalTailChunk000Sub000Block009Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 446
    = surrogateDiagTailX0RatChunk000Sub000Block009Part016

theorem surrogateDiagonalTailChunk000Sub000Block009Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part016] using hcert

def TailChunk000Sub000Block009Part017SupportExplicit : Finset ℕ :=
  ([447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part017 : ℚ :=
  (92362128775 : ℚ) / 19195246921728

def SurrogateDiagonalTailChunk000Sub000Block009Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 447
    = surrogateDiagTailX0RatChunk000Sub000Block009Part017

theorem surrogateDiagonalTailChunk000Sub000Block009Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part017] using hcert

def TailChunk000Sub000Block009Part018SupportExplicit : Finset ℕ :=
  ([449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part018 : ℚ :=
  (138323486125 : ℚ) / 100725380087808

def SurrogateDiagonalTailChunk000Sub000Block009Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 449
    = surrogateDiagTailX0RatChunk000Sub000Block009Part018

theorem surrogateDiagonalTailChunk000Sub000Block009Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part018] using hcert

def TailChunk000Sub000Block009Part019SupportExplicit : Finset ℕ :=
  ([451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part019 : ℚ :=
  (331138647 : ℚ) / 170700800000

def SurrogateDiagonalTailChunk000Sub000Block009Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 451
    = surrogateDiagTailX0RatChunk000Sub000Block009Part019

theorem surrogateDiagonalTailChunk000Sub000Block009Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part019] using hcert

def TailChunk000Sub000Block009Part020SupportExplicit : Finset ℕ :=
  ([453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part020 : ℚ :=
  (2307 : ℚ) / 500000

def SurrogateDiagonalTailChunk000Sub000Block009Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 453
    = surrogateDiagTailX0RatChunk000Sub000Block009Part020

theorem surrogateDiagonalTailChunk000Sub000Block009Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part020] using hcert

def TailChunk000Sub000Block009Part021SupportExplicit : Finset ℕ :=
  ([454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part021 : ℚ :=
  (70554795025 : ℚ) / 6523198818888

def SurrogateDiagonalTailChunk000Sub000Block009Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 454
    = surrogateDiagTailX0RatChunk000Sub000Block009Part021

theorem surrogateDiagonalTailChunk000Sub000Block009Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part021] using hcert

def TailChunk000Sub000Block009Part022SupportExplicit : Finset ℕ :=
  ([455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part022 : ℚ :=
  (834310925 : ℚ) / 159284330496

def SurrogateDiagonalTailChunk000Sub000Block009Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 455
    = surrogateDiagTailX0RatChunk000Sub000Block009Part022

theorem surrogateDiagonalTailChunk000Sub000Block009Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part022] using hcert

def TailChunk000Sub000Block009Part023SupportExplicit : Finset ℕ :=
  ([457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part023 : ℚ :=
  (143296520125 : ℚ) / 108115068930048

def SurrogateDiagonalTailChunk000Sub000Block009Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 457
    = surrogateDiagTailX0RatChunk000Sub000Block009Part023

theorem surrogateDiagonalTailChunk000Sub000Block009Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part023] using hcert

def TailChunk000Sub000Block009Part024SupportExplicit : Finset ℕ :=
  ([458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block009Part024 : ℚ :=
  (71803528225 : ℚ) / 6757191808128

def SurrogateDiagonalTailChunk000Sub000Block009Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 458
    = surrogateDiagTailX0RatChunk000Sub000Block009Part024

theorem surrogateDiagonalTailChunk000Sub000Block009Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block009Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block009Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block009Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block009Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block009Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block009HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block009Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block009Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block009Part000
    + surrogateDiagTailX0RatChunk000Sub000Block009Part001
    + surrogateDiagTailX0RatChunk000Sub000Block009Part002
    + surrogateDiagTailX0RatChunk000Sub000Block009Part003
    + surrogateDiagTailX0RatChunk000Sub000Block009Part004
    + surrogateDiagTailX0RatChunk000Sub000Block009Part005
    + surrogateDiagTailX0RatChunk000Sub000Block009Part006
    + surrogateDiagTailX0RatChunk000Sub000Block009Part007
    + surrogateDiagTailX0RatChunk000Sub000Block009Part008
    + surrogateDiagTailX0RatChunk000Sub000Block009Part009

def surrogateDiagonalTailChunk000Sub000Block009MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block009Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block009Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block009Part010
    + surrogateDiagTailX0RatChunk000Sub000Block009Part011
    + surrogateDiagTailX0RatChunk000Sub000Block009Part012
    + surrogateDiagTailX0RatChunk000Sub000Block009Part013
    + surrogateDiagTailX0RatChunk000Sub000Block009Part014
    + surrogateDiagTailX0RatChunk000Sub000Block009Part015
    + surrogateDiagTailX0RatChunk000Sub000Block009Part016
    + surrogateDiagTailX0RatChunk000Sub000Block009Part017
    + surrogateDiagTailX0RatChunk000Sub000Block009Part018
    + surrogateDiagTailX0RatChunk000Sub000Block009Part019

def surrogateDiagonalTailChunk000Sub000Block009TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block009Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block009Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block009Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block009Part020
    + surrogateDiagTailX0RatChunk000Sub000Block009Part021
    + surrogateDiagTailX0RatChunk000Sub000Block009Part022
    + surrogateDiagTailX0RatChunk000Sub000Block009Part023
    + surrogateDiagTailX0RatChunk000Sub000Block009Part024

def surrogateDiagonalTailChunk000Sub000Block009Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block009HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block009MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block009TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block009 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block009Part000
    + surrogateDiagTailX0RatChunk000Sub000Block009Part001
    + surrogateDiagTailX0RatChunk000Sub000Block009Part002
    + surrogateDiagTailX0RatChunk000Sub000Block009Part003
    + surrogateDiagTailX0RatChunk000Sub000Block009Part004
    + surrogateDiagTailX0RatChunk000Sub000Block009Part005
    + surrogateDiagTailX0RatChunk000Sub000Block009Part006
    + surrogateDiagTailX0RatChunk000Sub000Block009Part007
    + surrogateDiagTailX0RatChunk000Sub000Block009Part008
    + surrogateDiagTailX0RatChunk000Sub000Block009Part009
    + surrogateDiagTailX0RatChunk000Sub000Block009Part010
    + surrogateDiagTailX0RatChunk000Sub000Block009Part011
    + surrogateDiagTailX0RatChunk000Sub000Block009Part012
    + surrogateDiagTailX0RatChunk000Sub000Block009Part013
    + surrogateDiagTailX0RatChunk000Sub000Block009Part014
    + surrogateDiagTailX0RatChunk000Sub000Block009Part015
    + surrogateDiagTailX0RatChunk000Sub000Block009Part016
    + surrogateDiagTailX0RatChunk000Sub000Block009Part017
    + surrogateDiagTailX0RatChunk000Sub000Block009Part018
    + surrogateDiagTailX0RatChunk000Sub000Block009Part019
    + surrogateDiagTailX0RatChunk000Sub000Block009Part020
    + surrogateDiagTailX0RatChunk000Sub000Block009Part021
    + surrogateDiagTailX0RatChunk000Sub000Block009Part022
    + surrogateDiagTailX0RatChunk000Sub000Block009Part023
    + surrogateDiagTailX0RatChunk000Sub000Block009Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block009_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block009Head + surrogateDiagTailX0RatChunk000Sub000Block009Mid + surrogateDiagTailX0RatChunk000Sub000Block009Tail =
      surrogateDiagTailX0RatChunk000Sub000Block009 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block009Head surrogateDiagTailX0RatChunk000Sub000Block009Mid surrogateDiagTailX0RatChunk000Sub000Block009Tail surrogateDiagTailX0RatChunk000Sub000Block009
  ring

def SurrogateDiagonalTailChunk000Sub000Block009HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block009HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block009Head

def SurrogateDiagonalTailChunk000Sub000Block009MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block009MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block009Mid

def SurrogateDiagonalTailChunk000Sub000Block009TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block009TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block009Tail

theorem surrogateDiagonalTailChunk000Sub000Block009_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block009HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block009MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block009TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block009Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block009 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block009HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block009MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block009TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block009Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block009_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
