import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [85,86). -/

/- Block 085 covers tail-support indices [2125,2150) and q from 3541 to 3583. -/

def TailChunk000Sub000Block085Part000SupportExplicit : Finset ℕ :=
  ([3541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part000 : ℚ :=
  (313467025 : ℚ) / 157072406759712

def SurrogateDiagonalTailChunk000Sub000Block085Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3541
    = surrogateDiagTailX0RatChunk000Sub000Block085Part000

theorem surrogateDiagonalTailChunk000Sub000Block085Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part000] using hcert

def TailChunk000Sub000Block085Part001SupportExplicit : Finset ℕ :=
  ([3542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part001 : ℚ :=
  (4317262969 : ℚ) / 75914123788800

def SurrogateDiagonalTailChunk000Sub000Block085Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3542
    = surrogateDiagTailX0RatChunk000Sub000Block085Part001

theorem surrogateDiagonalTailChunk000Sub000Block085Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part001] using hcert

def TailChunk000Sub000Block085Part002SupportExplicit : Finset ℕ :=
  ([3543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part002 : ℚ :=
  (24396168517 : ℚ) / 3102664824883200

def SurrogateDiagonalTailChunk000Sub000Block085Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3543
    = surrogateDiagTailX0RatChunk000Sub000Block085Part002

theorem surrogateDiagonalTailChunk000Sub000Block085Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part002] using hcert

def TailChunk000Sub000Block085Part003SupportExplicit : Finset ℕ :=
  ([3545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part003 : ℚ :=
  (230200148825 : ℚ) / 53614048173981696

def SurrogateDiagonalTailChunk000Sub000Block085Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3545
    = surrogateDiagTailX0RatChunk000Sub000Block085Part003

theorem surrogateDiagonalTailChunk000Sub000Block085Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part003] using hcert

def TailChunk000Sub000Block085Part004SupportExplicit : Finset ℕ :=
  ([3547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part004 : ℚ :=
  (1572336594775 : ℚ) / 395350037150230728

def SurrogateDiagonalTailChunk000Sub000Block085Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3547
    = surrogateDiagTailX0RatChunk000Sub000Block085Part004

theorem surrogateDiagonalTailChunk000Sub000Block085Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part004] using hcert

def TailChunk000Sub000Block085Part005SupportExplicit : Finset ℕ :=
  ([3551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part005 : ℚ :=
  (83803932425 : ℚ) / 19272740351394816

def SurrogateDiagonalTailChunk000Sub000Block085Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3551
    = surrogateDiagTailX0RatChunk000Sub000Block085Part005

theorem surrogateDiagonalTailChunk000Sub000Block085Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part005] using hcert

def TailChunk000Sub000Block085Part006SupportExplicit : Finset ℕ :=
  ([3553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part006 : ℚ :=
  (16073578459 : ℚ) / 2293694359142400

def SurrogateDiagonalTailChunk000Sub000Block085Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3553
    = surrogateDiagTailX0RatChunk000Sub000Block085Part006

theorem surrogateDiagonalTailChunk000Sub000Block085Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part006] using hcert

def TailChunk000Sub000Block085Part007SupportExplicit : Finset ℕ :=
  ([3554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part007 : ℚ :=
  (65759706425 : ℚ) / 2764115556728832

def SurrogateDiagonalTailChunk000Sub000Block085Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3554
    = surrogateDiagTailX0RatChunk000Sub000Block085Part007

theorem surrogateDiagonalTailChunk000Sub000Block085Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part007] using hcert

def TailChunk000Sub000Block085Part008SupportExplicit : Finset ℕ :=
  ([3557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part008 : ℚ :=
  (197691390625 : ℚ) / 99957152719617312

def SurrogateDiagonalTailChunk000Sub000Block085Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3557
    = surrogateDiagTailX0RatChunk000Sub000Block085Part008

theorem surrogateDiagonalTailChunk000Sub000Block085Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part008] using hcert

def TailChunk000Sub000Block085Part009SupportExplicit : Finset ℕ :=
  ([3558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part009 : ℚ :=
  (19207757725 : ℚ) / 307123950747648

def SurrogateDiagonalTailChunk000Sub000Block085Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3558
    = surrogateDiagTailX0RatChunk000Sub000Block085Part009

theorem surrogateDiagonalTailChunk000Sub000Block085Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part009] using hcert

def TailChunk000Sub000Block085Part010SupportExplicit : Finset ℕ :=
  ([3559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part010 : ℚ :=
  (197913765625 : ℚ) / 100182217989920562

def SurrogateDiagonalTailChunk000Sub000Block085Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3559
    = surrogateDiagTailX0RatChunk000Sub000Block085Part010

theorem surrogateDiagonalTailChunk000Sub000Block085Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part010] using hcert

def TailChunk000Sub000Block085Part011SupportExplicit : Finset ℕ :=
  ([3561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part011 : ℚ :=
  (616116027475 : ℚ) / 79156320387097728

def SurrogateDiagonalTailChunk000Sub000Block085Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3561
    = surrogateDiagTailX0RatChunk000Sub000Block085Part011

theorem surrogateDiagonalTailChunk000Sub000Block085Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part011] using hcert

def TailChunk000Sub000Block085Part012SupportExplicit : Finset ℕ :=
  ([3562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part012 : ℚ :=
  (180842649275 : ℚ) / 5912705141047296

def SurrogateDiagonalTailChunk000Sub000Block085Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3562
    = surrogateDiagTailX0RatChunk000Sub000Block085Part012

theorem surrogateDiagonalTailChunk000Sub000Block085Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part012] using hcert

def TailChunk000Sub000Block085Part013SupportExplicit : Finset ℕ :=
  ([3563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part013 : ℚ :=
  (80865903125 : ℚ) / 23979725100582912

def SurrogateDiagonalTailChunk000Sub000Block085Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3563
    = surrogateDiagTailX0RatChunk000Sub000Block085Part013

theorem surrogateDiagonalTailChunk000Sub000Block085Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part013] using hcert

def TailChunk000Sub000Block085Part014SupportExplicit : Finset ℕ :=
  ([3565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part014 : ℚ :=
  (529386029 : ℚ) / 97170078449664

def SurrogateDiagonalTailChunk000Sub000Block085Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3565
    = surrogateDiagTailX0RatChunk000Sub000Block085Part014

theorem surrogateDiagonalTailChunk000Sub000Block085Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part014] using hcert

def TailChunk000Sub000Block085Part015SupportExplicit : Finset ℕ :=
  ([3566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part015 : ℚ :=
  (66204528425 : ℚ) / 2801658184753032

def SurrogateDiagonalTailChunk000Sub000Block085Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3566
    = surrogateDiagTailX0RatChunk000Sub000Block085Part015

theorem surrogateDiagonalTailChunk000Sub000Block085Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part015] using hcert

def TailChunk000Sub000Block085Part016SupportExplicit : Finset ℕ :=
  ([3567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part016 : ℚ :=
  (11789126891 : ℚ) / 1259067251097600

def SurrogateDiagonalTailChunk000Sub000Block085Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3567
    = surrogateDiagTailX0RatChunk000Sub000Block085Part016

theorem surrogateDiagonalTailChunk000Sub000Block085Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part016] using hcert

def TailChunk000Sub000Block085Part017SupportExplicit : Finset ℕ :=
  ([3569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part017 : ℚ :=
  (389668098875 : ℚ) / 175893355649922624

def SurrogateDiagonalTailChunk000Sub000Block085Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3569
    = surrogateDiagTailX0RatChunk000Sub000Block085Part017

theorem surrogateDiagonalTailChunk000Sub000Block085Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part017] using hcert

def TailChunk000Sub000Block085Part018SupportExplicit : Finset ℕ :=
  ([3570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part018 : ℚ :=
  (8032563575 : ℚ) / 32218697170944

def SurrogateDiagonalTailChunk000Sub000Block085Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3570
    = surrogateDiagTailX0RatChunk000Sub000Block085Part018

theorem surrogateDiagonalTailChunk000Sub000Block085Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part018] using hcert

def TailChunk000Sub000Block085Part019SupportExplicit : Finset ℕ :=
  ([3571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part019 : ℚ :=
  (318801025 : ℚ) / 162464962505202

def SurrogateDiagonalTailChunk000Sub000Block085Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3571
    = surrogateDiagTailX0RatChunk000Sub000Block085Part019

theorem surrogateDiagonalTailChunk000Sub000Block085Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part019] using hcert

def TailChunk000Sub000Block085Part020SupportExplicit : Finset ℕ :=
  ([3574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part020 : ℚ :=
  (199505728275 : ℚ) / 8480694567766936

def SurrogateDiagonalTailChunk000Sub000Block085Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3574
    = surrogateDiagTailX0RatChunk000Sub000Block085Part020

theorem surrogateDiagonalTailChunk000Sub000Block085Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part020] using hcert

def TailChunk000Sub000Block085Part021SupportExplicit : Finset ℕ :=
  ([3578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part021 : ℚ :=
  (66650849825 : ℚ) / 2839581952589952

def SurrogateDiagonalTailChunk000Sub000Block085Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3578
    = surrogateDiagTailX0RatChunk000Sub000Block085Part021

theorem surrogateDiagonalTailChunk000Sub000Block085Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part021] using hcert

def TailChunk000Sub000Block085Part022SupportExplicit : Finset ℕ :=
  ([3579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part022 : ℚ :=
  (444385535225 : ℚ) / 40385165547945984

def SurrogateDiagonalTailChunk000Sub000Block085Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3579
    = surrogateDiagTailX0RatChunk000Sub000Block085Part022

theorem surrogateDiagonalTailChunk000Sub000Block085Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part022] using hcert

def TailChunk000Sub000Block085Part023SupportExplicit : Finset ℕ :=
  ([3581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part023 : ℚ :=
  (64104981439 : ℚ) / 16429296098179200

def SurrogateDiagonalTailChunk000Sub000Block085Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3581
    = surrogateDiagTailX0RatChunk000Sub000Block085Part023

theorem surrogateDiagonalTailChunk000Sub000Block085Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part023] using hcert

def TailChunk000Sub000Block085Part024SupportExplicit : Finset ℕ :=
  ([3583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block085Part024 : ℚ :=
  (200592015625 : ℚ) / 102912752412405522

def SurrogateDiagonalTailChunk000Sub000Block085Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3583
    = surrogateDiagTailX0RatChunk000Sub000Block085Part024

theorem surrogateDiagonalTailChunk000Sub000Block085Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block085Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block085Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block085Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block085Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block085Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block085Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block085HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block085Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block085Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block085Part000
    + surrogateDiagTailX0RatChunk000Sub000Block085Part001
    + surrogateDiagTailX0RatChunk000Sub000Block085Part002
    + surrogateDiagTailX0RatChunk000Sub000Block085Part003
    + surrogateDiagTailX0RatChunk000Sub000Block085Part004
    + surrogateDiagTailX0RatChunk000Sub000Block085Part005
    + surrogateDiagTailX0RatChunk000Sub000Block085Part006
    + surrogateDiagTailX0RatChunk000Sub000Block085Part007
    + surrogateDiagTailX0RatChunk000Sub000Block085Part008
    + surrogateDiagTailX0RatChunk000Sub000Block085Part009

def surrogateDiagonalTailChunk000Sub000Block085MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block085Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block085Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block085Part010
    + surrogateDiagTailX0RatChunk000Sub000Block085Part011
    + surrogateDiagTailX0RatChunk000Sub000Block085Part012
    + surrogateDiagTailX0RatChunk000Sub000Block085Part013
    + surrogateDiagTailX0RatChunk000Sub000Block085Part014
    + surrogateDiagTailX0RatChunk000Sub000Block085Part015
    + surrogateDiagTailX0RatChunk000Sub000Block085Part016
    + surrogateDiagTailX0RatChunk000Sub000Block085Part017
    + surrogateDiagTailX0RatChunk000Sub000Block085Part018
    + surrogateDiagTailX0RatChunk000Sub000Block085Part019

def surrogateDiagonalTailChunk000Sub000Block085TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block085Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block085Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block085Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block085Part020
    + surrogateDiagTailX0RatChunk000Sub000Block085Part021
    + surrogateDiagTailX0RatChunk000Sub000Block085Part022
    + surrogateDiagTailX0RatChunk000Sub000Block085Part023
    + surrogateDiagTailX0RatChunk000Sub000Block085Part024

def surrogateDiagonalTailChunk000Sub000Block085Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block085HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block085MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block085TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block085 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block085Part000
    + surrogateDiagTailX0RatChunk000Sub000Block085Part001
    + surrogateDiagTailX0RatChunk000Sub000Block085Part002
    + surrogateDiagTailX0RatChunk000Sub000Block085Part003
    + surrogateDiagTailX0RatChunk000Sub000Block085Part004
    + surrogateDiagTailX0RatChunk000Sub000Block085Part005
    + surrogateDiagTailX0RatChunk000Sub000Block085Part006
    + surrogateDiagTailX0RatChunk000Sub000Block085Part007
    + surrogateDiagTailX0RatChunk000Sub000Block085Part008
    + surrogateDiagTailX0RatChunk000Sub000Block085Part009
    + surrogateDiagTailX0RatChunk000Sub000Block085Part010
    + surrogateDiagTailX0RatChunk000Sub000Block085Part011
    + surrogateDiagTailX0RatChunk000Sub000Block085Part012
    + surrogateDiagTailX0RatChunk000Sub000Block085Part013
    + surrogateDiagTailX0RatChunk000Sub000Block085Part014
    + surrogateDiagTailX0RatChunk000Sub000Block085Part015
    + surrogateDiagTailX0RatChunk000Sub000Block085Part016
    + surrogateDiagTailX0RatChunk000Sub000Block085Part017
    + surrogateDiagTailX0RatChunk000Sub000Block085Part018
    + surrogateDiagTailX0RatChunk000Sub000Block085Part019
    + surrogateDiagTailX0RatChunk000Sub000Block085Part020
    + surrogateDiagTailX0RatChunk000Sub000Block085Part021
    + surrogateDiagTailX0RatChunk000Sub000Block085Part022
    + surrogateDiagTailX0RatChunk000Sub000Block085Part023
    + surrogateDiagTailX0RatChunk000Sub000Block085Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block085_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block085Head + surrogateDiagTailX0RatChunk000Sub000Block085Mid + surrogateDiagTailX0RatChunk000Sub000Block085Tail =
      surrogateDiagTailX0RatChunk000Sub000Block085 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block085Head surrogateDiagTailX0RatChunk000Sub000Block085Mid surrogateDiagTailX0RatChunk000Sub000Block085Tail surrogateDiagTailX0RatChunk000Sub000Block085
  ring

def SurrogateDiagonalTailChunk000Sub000Block085HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block085HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block085Head

def SurrogateDiagonalTailChunk000Sub000Block085MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block085MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block085Mid

def SurrogateDiagonalTailChunk000Sub000Block085TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block085TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block085Tail

theorem surrogateDiagonalTailChunk000Sub000Block085_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block085HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block085MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block085TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block085Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block085 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block085HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block085MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block085TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block085Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block085_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
