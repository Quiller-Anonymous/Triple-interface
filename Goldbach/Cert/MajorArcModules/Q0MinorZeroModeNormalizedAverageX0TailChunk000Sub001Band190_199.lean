import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [190,200). -/

/-- Block 190 covers tail-support indices [9750,9775) and q from 16089 to 16130. -/

def TailChunk000Sub001Block190Part000SupportExplicit : Finset ℕ :=
  ([16089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part000 : ℚ :=
  (35800528601 : ℚ) / 567251487900057600

def SurrogateDiagonalTailChunk000Sub001Block190Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16089
    = surrogateDiagTailX0RatChunk000Sub001Block190Part000

theorem surrogateDiagonalTailChunk000Sub001Block190Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part000] using hcert

def TailChunk000Sub001Block190Part001SupportExplicit : Finset ℕ :=
  ([16090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part001 : ℚ :=
  (242934146525 : ℚ) / 2139838544819257344

def SurrogateDiagonalTailChunk000Sub001Block190Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16090
    = surrogateDiagTailX0RatChunk000Sub001Block190Part001

theorem surrogateDiagonalTailChunk000Sub001Block190Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part001] using hcert

def TailChunk000Sub001Block190Part002SupportExplicit : Finset ℕ :=
  ([16091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block190Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16091
    = surrogateDiagTailX0RatChunk000Sub001Block190Part002

theorem surrogateDiagonalTailChunk000Sub001Block190Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part002] using hcert

def TailChunk000Sub001Block190Part003SupportExplicit : Finset ℕ :=
  ([16094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part003 : ℚ :=
  (1350325825 : ℚ) / 52522241387167872

def SurrogateDiagonalTailChunk000Sub001Block190Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16094
    = surrogateDiagTailX0RatChunk000Sub001Block190Part003

theorem surrogateDiagonalTailChunk000Sub001Block190Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part003] using hcert

def TailChunk000Sub001Block190Part004SupportExplicit : Finset ℕ :=
  ([16095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part004 : ℚ :=
  (806842687325 : ℚ) / 5286873750048866304

def SurrogateDiagonalTailChunk000Sub001Block190Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16095
    = surrogateDiagTailX0RatChunk000Sub001Block190Part004

theorem surrogateDiagonalTailChunk000Sub001Block190Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part004] using hcert

def TailChunk000Sub001Block190Part005SupportExplicit : Finset ℕ :=
  ([16097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block190Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16097
    = surrogateDiagTailX0RatChunk000Sub001Block190Part005

theorem surrogateDiagonalTailChunk000Sub001Block190Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part005] using hcert

def TailChunk000Sub001Block190Part006SupportExplicit : Finset ℕ :=
  ([16098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part006 : ℚ :=
  (449792764325 : ℚ) / 1035027621719037504

def SurrogateDiagonalTailChunk000Sub001Block190Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16098
    = surrogateDiagTailX0RatChunk000Sub001Block190Part006

theorem surrogateDiagonalTailChunk000Sub001Block190Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part006] using hcert

def TailChunk000Sub001Block190Part007SupportExplicit : Finset ℕ :=
  ([16099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part007 : ℚ :=
  (5155398375 : ℚ) / 1988508261122572288

def SurrogateDiagonalTailChunk000Sub001Block190Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16099
    = surrogateDiagTailX0RatChunk000Sub001Block190Part007

theorem surrogateDiagonalTailChunk000Sub001Block190Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part007] using hcert

def TailChunk000Sub001Block190Part008SupportExplicit : Finset ℕ :=
  ([16102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part008 : ℚ :=
  (6896034425 : ℚ) / 1200265197404553216

def SurrogateDiagonalTailChunk000Sub001Block190Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16102
    = surrogateDiagTailX0RatChunk000Sub001Block190Part008

theorem surrogateDiagonalTailChunk000Sub001Block190Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part008] using hcert

def TailChunk000Sub001Block190Part009SupportExplicit : Finset ℕ :=
  ([16103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block190Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16103
    = surrogateDiagTailX0RatChunk000Sub001Block190Part009

theorem surrogateDiagonalTailChunk000Sub001Block190Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part009] using hcert

def TailChunk000Sub001Block190Part010SupportExplicit : Finset ℕ :=
  ([16105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part010 : ℚ :=
  (1731402093 : ℚ) / 183509707611668480

def SurrogateDiagonalTailChunk000Sub001Block190Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16105
    = surrogateDiagTailX0RatChunk000Sub001Block190Part010

theorem surrogateDiagonalTailChunk000Sub001Block190Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part010] using hcert

def TailChunk000Sub001Block190Part011SupportExplicit : Finset ℕ :=
  ([16106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block190Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16106
    = surrogateDiagTailX0RatChunk000Sub001Block190Part011

theorem surrogateDiagonalTailChunk000Sub001Block190Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part011] using hcert

def TailChunk000Sub001Block190Part012SupportExplicit : Finset ℕ :=
  ([16107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part012 : ℚ :=
  (1700252495575 : ℚ) / 12167148300214468608

def SurrogateDiagonalTailChunk000Sub001Block190Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16107
    = surrogateDiagTailX0RatChunk000Sub001Block190Part012

theorem surrogateDiagonalTailChunk000Sub001Block190Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part012] using hcert

def TailChunk000Sub001Block190Part013SupportExplicit : Finset ℕ :=
  ([16109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part013 : ℚ :=
  (1685638481 : ℚ) / 3148310541769113600

def SurrogateDiagonalTailChunk000Sub001Block190Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16109
    = surrogateDiagTailX0RatChunk000Sub001Block190Part013

theorem surrogateDiagonalTailChunk000Sub001Block190Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part013] using hcert

def TailChunk000Sub001Block190Part014SupportExplicit : Finset ℕ :=
  ([16111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block190Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16111
    = surrogateDiagTailX0RatChunk000Sub001Block190Part014

theorem surrogateDiagonalTailChunk000Sub001Block190Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part014] using hcert

def TailChunk000Sub001Block190Part015SupportExplicit : Finset ℕ :=
  ([16113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part015 : ℚ :=
  (5513397433 : ℚ) / 90007117824000000

def SurrogateDiagonalTailChunk000Sub001Block190Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16113
    = surrogateDiagTailX0RatChunk000Sub001Block190Part015

theorem surrogateDiagonalTailChunk000Sub001Block190Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part015] using hcert

def TailChunk000Sub001Block190Part016SupportExplicit : Finset ℕ :=
  ([16114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part016 : ℚ :=
  (13292042893 : ℚ) / 226716544242000000

def SurrogateDiagonalTailChunk000Sub001Block190Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16114
    = surrogateDiagTailX0RatChunk000Sub001Block190Part016

theorem surrogateDiagonalTailChunk000Sub001Block190Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part016] using hcert

def TailChunk000Sub001Block190Part017SupportExplicit : Finset ℕ :=
  ([16115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part017 : ℚ :=
  (1392893797 : ℚ) / 74459173744017408

def SurrogateDiagonalTailChunk000Sub001Block190Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16115
    = surrogateDiagTailX0RatChunk000Sub001Block190Part017

theorem surrogateDiagonalTailChunk000Sub001Block190Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part017] using hcert

def TailChunk000Sub001Block190Part018SupportExplicit : Finset ℕ :=
  ([16117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part018 : ℚ :=
  (1833686303 : ℚ) / 3132440072830017600

def SurrogateDiagonalTailChunk000Sub001Block190Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16117
    = surrogateDiagTailX0RatChunk000Sub001Block190Part018

theorem surrogateDiagonalTailChunk000Sub001Block190Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part018] using hcert

def TailChunk000Sub001Block190Part019SupportExplicit : Finset ℕ :=
  ([16118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block190Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16118
    = surrogateDiagTailX0RatChunk000Sub001Block190Part019

theorem surrogateDiagonalTailChunk000Sub001Block190Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part019] using hcert

def TailChunk000Sub001Block190Part020SupportExplicit : Finset ℕ :=
  ([16122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part020 : ℚ :=
  (225768685175 : ℚ) / 1041216110446092864

def SurrogateDiagonalTailChunk000Sub001Block190Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16122
    = surrogateDiagTailX0RatChunk000Sub001Block190Part020

theorem surrogateDiagonalTailChunk000Sub001Block190Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part020] using hcert

def TailChunk000Sub001Block190Part021SupportExplicit : Finset ℕ :=
  ([16123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part021 : ℚ :=
  (631378007 : ℚ) / 401829389808000000

def SurrogateDiagonalTailChunk000Sub001Block190Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16123
    = surrogateDiagTailX0RatChunk000Sub001Block190Part021

theorem surrogateDiagonalTailChunk000Sub001Block190Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part021] using hcert

def TailChunk000Sub001Block190Part022SupportExplicit : Finset ℕ :=
  ([16126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part022 : ℚ :=
  (815440369 : ℚ) / 28716478044779520

def SurrogateDiagonalTailChunk000Sub001Block190Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16126
    = surrogateDiagTailX0RatChunk000Sub001Block190Part022

theorem surrogateDiagonalTailChunk000Sub001Block190Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part022] using hcert

def TailChunk000Sub001Block190Part023SupportExplicit : Finset ℕ :=
  ([16127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block190Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16127
    = surrogateDiagTailX0RatChunk000Sub001Block190Part023

theorem surrogateDiagonalTailChunk000Sub001Block190Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part023] using hcert

def TailChunk000Sub001Block190Part024SupportExplicit : Finset ℕ :=
  ([16130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block190Part024 : ℚ :=
  (1543802927825 : ℚ) / 2161210049958395904

def SurrogateDiagonalTailChunk000Sub001Block190Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16130
    = surrogateDiagTailX0RatChunk000Sub001Block190Part024

theorem surrogateDiagonalTailChunk000Sub001Block190Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block190Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block190Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block190Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block190Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block190Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block190Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block190HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block190Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block190Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block190Part000
    + surrogateDiagTailX0RatChunk000Sub001Block190Part001
    + surrogateDiagTailX0RatChunk000Sub001Block190Part002
    + surrogateDiagTailX0RatChunk000Sub001Block190Part003
    + surrogateDiagTailX0RatChunk000Sub001Block190Part004
    + surrogateDiagTailX0RatChunk000Sub001Block190Part005
    + surrogateDiagTailX0RatChunk000Sub001Block190Part006
    + surrogateDiagTailX0RatChunk000Sub001Block190Part007
    + surrogateDiagTailX0RatChunk000Sub001Block190Part008
    + surrogateDiagTailX0RatChunk000Sub001Block190Part009

def surrogateDiagonalTailChunk000Sub001Block190MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block190Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block190Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block190Part010
    + surrogateDiagTailX0RatChunk000Sub001Block190Part011
    + surrogateDiagTailX0RatChunk000Sub001Block190Part012
    + surrogateDiagTailX0RatChunk000Sub001Block190Part013
    + surrogateDiagTailX0RatChunk000Sub001Block190Part014
    + surrogateDiagTailX0RatChunk000Sub001Block190Part015
    + surrogateDiagTailX0RatChunk000Sub001Block190Part016
    + surrogateDiagTailX0RatChunk000Sub001Block190Part017
    + surrogateDiagTailX0RatChunk000Sub001Block190Part018
    + surrogateDiagTailX0RatChunk000Sub001Block190Part019

def surrogateDiagonalTailChunk000Sub001Block190TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block190Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block190Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block190Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block190Part020
    + surrogateDiagTailX0RatChunk000Sub001Block190Part021
    + surrogateDiagTailX0RatChunk000Sub001Block190Part022
    + surrogateDiagTailX0RatChunk000Sub001Block190Part023
    + surrogateDiagTailX0RatChunk000Sub001Block190Part024

def surrogateDiagonalTailChunk000Sub001Block190Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block190HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block190MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block190TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block190 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block190Part000
    + surrogateDiagTailX0RatChunk000Sub001Block190Part001
    + surrogateDiagTailX0RatChunk000Sub001Block190Part002
    + surrogateDiagTailX0RatChunk000Sub001Block190Part003
    + surrogateDiagTailX0RatChunk000Sub001Block190Part004
    + surrogateDiagTailX0RatChunk000Sub001Block190Part005
    + surrogateDiagTailX0RatChunk000Sub001Block190Part006
    + surrogateDiagTailX0RatChunk000Sub001Block190Part007
    + surrogateDiagTailX0RatChunk000Sub001Block190Part008
    + surrogateDiagTailX0RatChunk000Sub001Block190Part009
    + surrogateDiagTailX0RatChunk000Sub001Block190Part010
    + surrogateDiagTailX0RatChunk000Sub001Block190Part011
    + surrogateDiagTailX0RatChunk000Sub001Block190Part012
    + surrogateDiagTailX0RatChunk000Sub001Block190Part013
    + surrogateDiagTailX0RatChunk000Sub001Block190Part014
    + surrogateDiagTailX0RatChunk000Sub001Block190Part015
    + surrogateDiagTailX0RatChunk000Sub001Block190Part016
    + surrogateDiagTailX0RatChunk000Sub001Block190Part017
    + surrogateDiagTailX0RatChunk000Sub001Block190Part018
    + surrogateDiagTailX0RatChunk000Sub001Block190Part019
    + surrogateDiagTailX0RatChunk000Sub001Block190Part020
    + surrogateDiagTailX0RatChunk000Sub001Block190Part021
    + surrogateDiagTailX0RatChunk000Sub001Block190Part022
    + surrogateDiagTailX0RatChunk000Sub001Block190Part023
    + surrogateDiagTailX0RatChunk000Sub001Block190Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block190_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block190Head + surrogateDiagTailX0RatChunk000Sub001Block190Mid + surrogateDiagTailX0RatChunk000Sub001Block190Tail =
      surrogateDiagTailX0RatChunk000Sub001Block190 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block190Head surrogateDiagTailX0RatChunk000Sub001Block190Mid surrogateDiagTailX0RatChunk000Sub001Block190Tail surrogateDiagTailX0RatChunk000Sub001Block190
  ring

def SurrogateDiagonalTailChunk000Sub001Block190HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block190HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block190Head

def SurrogateDiagonalTailChunk000Sub001Block190MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block190MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block190Mid

def SurrogateDiagonalTailChunk000Sub001Block190TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block190TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block190Tail

theorem surrogateDiagonalTailChunk000Sub001Block190_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block190HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block190MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block190TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block190Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block190 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block190HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block190MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block190TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block190Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block190_eq_head_add_mid_add_tail

/-- Block 191 covers tail-support indices [9775,9800) and q from 16131 to 16169. -/

def TailChunk000Sub001Block191Part000SupportExplicit : Finset ℕ :=
  ([16131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part000 : ℚ :=
  (6611554769275 : ℚ) / 26560319516990097408

def SurrogateDiagonalTailChunk000Sub001Block191Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16131
    = surrogateDiagTailX0RatChunk000Sub001Block191Part000

theorem surrogateDiagonalTailChunk000Sub001Block191Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part000] using hcert

def TailChunk000Sub001Block191Part001SupportExplicit : Finset ℕ :=
  ([16133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part001 : ℚ :=
  (12504780497125 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk000Sub001Block191Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16133
    = surrogateDiagTailX0RatChunk000Sub001Block191Part001

theorem surrogateDiagonalTailChunk000Sub001Block191Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part001] using hcert

def TailChunk000Sub001Block191Part002SupportExplicit : Finset ℕ :=
  ([16134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part002 : ℚ :=
  (1129453068725 : ℚ) / 1044320740750393344

def SurrogateDiagonalTailChunk000Sub001Block191Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16134
    = surrogateDiagTailX0RatChunk000Sub001Block191Part002

theorem surrogateDiagonalTailChunk000Sub001Block191Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part002] using hcert

def TailChunk000Sub001Block191Part003SupportExplicit : Finset ℕ :=
  ([16135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part003 : ℚ :=
  (344715824737 : ℚ) / 1485809544344371200

def SurrogateDiagonalTailChunk000Sub001Block191Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16135
    = surrogateDiagTailX0RatChunk000Sub001Block191Part003

theorem surrogateDiagonalTailChunk000Sub001Block191Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part003] using hcert

def TailChunk000Sub001Block191Part004SupportExplicit : Finset ℕ :=
  ([16138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part004 : ℚ :=
  (1017324390625 : ℚ) / 2648685693215760672

def SurrogateDiagonalTailChunk000Sub001Block191Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16138
    = surrogateDiagTailX0RatChunk000Sub001Block191Part004

theorem surrogateDiagonalTailChunk000Sub001Block191Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part004] using hcert

def TailChunk000Sub001Block191Part005SupportExplicit : Finset ℕ :=
  ([16139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part005 : ℚ :=
  (4069801890625 : ℚ) / 42399985891069120242

def SurrogateDiagonalTailChunk000Sub001Block191Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16139
    = surrogateDiagTailX0RatChunk000Sub001Block191Part005

theorem surrogateDiagonalTailChunk000Sub001Block191Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part005] using hcert

def TailChunk000Sub001Block191Part006SupportExplicit : Finset ℕ :=
  ([16141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part006 : ℚ :=
  (6513297025 : ℚ) / 67873613608480032

def SurrogateDiagonalTailChunk000Sub001Block191Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16141
    = surrogateDiagTailX0RatChunk000Sub001Block191Part006

theorem surrogateDiagonalTailChunk000Sub001Block191Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part006] using hcert

def TailChunk000Sub001Block191Part007SupportExplicit : Finset ℕ :=
  ([16142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part007 : ℚ :=
  (179843639975 : ℚ) / 317080308207845376

def SurrogateDiagonalTailChunk000Sub001Block191Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16142
    = surrogateDiagTailX0RatChunk000Sub001Block191Part007

theorem surrogateDiagonalTailChunk000Sub001Block191Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part007] using hcert

def TailChunk000Sub001Block191Part008SupportExplicit : Finset ℕ :=
  ([16143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part008 : ℚ :=
  (289468978477 : ℚ) / 1340713355229235200

def SurrogateDiagonalTailChunk000Sub001Block191Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16143
    = surrogateDiagTailX0RatChunk000Sub001Block191Part008

theorem surrogateDiagonalTailChunk000Sub001Block191Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part008] using hcert

def TailChunk000Sub001Block191Part009SupportExplicit : Finset ℕ :=
  ([16145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part009 : ℚ :=
  (11073525427975 : ℚ) / 69502580335083552768

def SurrogateDiagonalTailChunk000Sub001Block191Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16145
    = surrogateDiagTailX0RatChunk000Sub001Block191Part009

theorem surrogateDiagonalTailChunk000Sub001Block191Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part009] using hcert

def TailChunk000Sub001Block191Part010SupportExplicit : Finset ℕ :=
  ([16147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part010 : ℚ :=
  (631027133503 : ℚ) / 6296621083538227200

def SurrogateDiagonalTailChunk000Sub001Block191Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16147
    = surrogateDiagTailX0RatChunk000Sub001Block191Part010

theorem surrogateDiagonalTailChunk000Sub001Block191Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part010] using hcert

def TailChunk000Sub001Block191Part011SupportExplicit : Finset ℕ :=
  ([16149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part011 : ℚ :=
  (5606739954025 : ℚ) / 18038346422490759168

def SurrogateDiagonalTailChunk000Sub001Block191Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16149
    = surrogateDiagTailX0RatChunk000Sub001Block191Part011

theorem surrogateDiagonalTailChunk000Sub001Block191Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part011] using hcert

def TailChunk000Sub001Block191Part012SupportExplicit : Finset ℕ :=
  ([16151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part012 : ℚ :=
  (122983817303 : ℚ) / 1184718688358400000

def SurrogateDiagonalTailChunk000Sub001Block191Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16151
    = surrogateDiagTailX0RatChunk000Sub001Block191Part012

theorem surrogateDiagonalTailChunk000Sub001Block191Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part012] using hcert

def TailChunk000Sub001Block191Part013SupportExplicit : Finset ℕ :=
  ([16153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part013 : ℚ :=
  (7656209813675 : ℚ) / 73439236800584761344

def SurrogateDiagonalTailChunk000Sub001Block191Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16153
    = surrogateDiagTailX0RatChunk000Sub001Block191Part013

theorem surrogateDiagonalTailChunk000Sub001Block191Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part013] using hcert

def TailChunk000Sub001Block191Part014SupportExplicit : Finset ℕ :=
  ([16154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part014 : ℚ :=
  (22355918017 : ℚ) / 53982508390809600

def SurrogateDiagonalTailChunk000Sub001Block191Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16154
    = surrogateDiagTailX0RatChunk000Sub001Block191Part014

theorem surrogateDiagonalTailChunk000Sub001Block191Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part014] using hcert

def TailChunk000Sub001Block191Part015SupportExplicit : Finset ℕ :=
  ([16157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part015 : ℚ :=
  (635194354231 : ℚ) / 6392567867922000000

def SurrogateDiagonalTailChunk000Sub001Block191Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16157
    = surrogateDiagTailX0RatChunk000Sub001Block191Part015

theorem surrogateDiagonalTailChunk000Sub001Block191Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part015] using hcert

def TailChunk000Sub001Block191Part016SupportExplicit : Finset ℕ :=
  ([16158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part016 : ℚ :=
  (1132816106675 : ℚ) / 1050550824841257984

def SurrogateDiagonalTailChunk000Sub001Block191Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16158
    = surrogateDiagTailX0RatChunk000Sub001Block191Part016

theorem surrogateDiagonalTailChunk000Sub001Block191Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part016] using hcert

def TailChunk000Sub001Block191Part017SupportExplicit : Finset ℕ :=
  ([16159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part017 : ℚ :=
  (29545921753 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub001Block191Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16159
    = surrogateDiagTailX0RatChunk000Sub001Block191Part017

theorem surrogateDiagonalTailChunk000Sub001Block191Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part017] using hcert

def TailChunk000Sub001Block191Part018SupportExplicit : Finset ℕ :=
  ([16161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part018 : ℚ :=
  (7252873461325 : ℚ) / 33667606131912064128

def SurrogateDiagonalTailChunk000Sub001Block191Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16161
    = surrogateDiagTailX0RatChunk000Sub001Block191Part018

theorem surrogateDiagonalTailChunk000Sub001Block191Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part018] using hcert

def TailChunk000Sub001Block191Part019SupportExplicit : Finset ℕ :=
  ([16162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part019 : ℚ :=
  (1632564025 : ℚ) / 4263166487764992

def SurrogateDiagonalTailChunk000Sub001Block191Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16162
    = surrogateDiagTailX0RatChunk000Sub001Block191Part019

theorem surrogateDiagonalTailChunk000Sub001Block191Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part019] using hcert

def TailChunk000Sub001Block191Part020SupportExplicit : Finset ℕ :=
  ([16163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part020 : ℚ :=
  (12321042220225 : ℚ) / 91954942752455313408

def SurrogateDiagonalTailChunk000Sub001Block191Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16163
    = surrogateDiagTailX0RatChunk000Sub001Block191Part020

theorem surrogateDiagonalTailChunk000Sub001Block191Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part020] using hcert

def TailChunk000Sub001Block191Part021SupportExplicit : Finset ℕ :=
  ([16165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part021 : ℚ :=
  (139664911343 : ℚ) / 808767957919334400

def SurrogateDiagonalTailChunk000Sub001Block191Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16165
    = surrogateDiagTailX0RatChunk000Sub001Block191Part021

theorem surrogateDiagonalTailChunk000Sub001Block191Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part021] using hcert

def TailChunk000Sub001Block191Part022SupportExplicit : Finset ℕ :=
  ([16166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part022 : ℚ :=
  (82271732775 : ℚ) / 201675540358076416

def SurrogateDiagonalTailChunk000Sub001Block191Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16166
    = surrogateDiagTailX0RatChunk000Sub001Block191Part022

theorem surrogateDiagonalTailChunk000Sub001Block191Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part022] using hcert

def TailChunk000Sub001Block191Part023SupportExplicit : Finset ℕ :=
  ([16167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part023 : ℚ :=
  (1646993957425 : ℚ) / 6536046169389268992

def SurrogateDiagonalTailChunk000Sub001Block191Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16167
    = surrogateDiagTailX0RatChunk000Sub001Block191Part023

theorem surrogateDiagonalTailChunk000Sub001Block191Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part023] using hcert

def TailChunk000Sub001Block191Part024SupportExplicit : Finset ℕ :=
  ([16169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block191Part024 : ℚ :=
  (6587962179725 : ℚ) / 51640163661367885824

def SurrogateDiagonalTailChunk000Sub001Block191Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16169
    = surrogateDiagTailX0RatChunk000Sub001Block191Part024

theorem surrogateDiagonalTailChunk000Sub001Block191Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block191Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block191Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block191Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block191Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block191Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block191Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block191HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block191Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block191Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block191Part000
    + surrogateDiagTailX0RatChunk000Sub001Block191Part001
    + surrogateDiagTailX0RatChunk000Sub001Block191Part002
    + surrogateDiagTailX0RatChunk000Sub001Block191Part003
    + surrogateDiagTailX0RatChunk000Sub001Block191Part004
    + surrogateDiagTailX0RatChunk000Sub001Block191Part005
    + surrogateDiagTailX0RatChunk000Sub001Block191Part006
    + surrogateDiagTailX0RatChunk000Sub001Block191Part007
    + surrogateDiagTailX0RatChunk000Sub001Block191Part008
    + surrogateDiagTailX0RatChunk000Sub001Block191Part009

def surrogateDiagonalTailChunk000Sub001Block191MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block191Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block191Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block191Part010
    + surrogateDiagTailX0RatChunk000Sub001Block191Part011
    + surrogateDiagTailX0RatChunk000Sub001Block191Part012
    + surrogateDiagTailX0RatChunk000Sub001Block191Part013
    + surrogateDiagTailX0RatChunk000Sub001Block191Part014
    + surrogateDiagTailX0RatChunk000Sub001Block191Part015
    + surrogateDiagTailX0RatChunk000Sub001Block191Part016
    + surrogateDiagTailX0RatChunk000Sub001Block191Part017
    + surrogateDiagTailX0RatChunk000Sub001Block191Part018
    + surrogateDiagTailX0RatChunk000Sub001Block191Part019

def surrogateDiagonalTailChunk000Sub001Block191TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block191Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block191Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block191Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block191Part020
    + surrogateDiagTailX0RatChunk000Sub001Block191Part021
    + surrogateDiagTailX0RatChunk000Sub001Block191Part022
    + surrogateDiagTailX0RatChunk000Sub001Block191Part023
    + surrogateDiagTailX0RatChunk000Sub001Block191Part024

def surrogateDiagonalTailChunk000Sub001Block191Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block191HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block191MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block191TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block191 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block191Part000
    + surrogateDiagTailX0RatChunk000Sub001Block191Part001
    + surrogateDiagTailX0RatChunk000Sub001Block191Part002
    + surrogateDiagTailX0RatChunk000Sub001Block191Part003
    + surrogateDiagTailX0RatChunk000Sub001Block191Part004
    + surrogateDiagTailX0RatChunk000Sub001Block191Part005
    + surrogateDiagTailX0RatChunk000Sub001Block191Part006
    + surrogateDiagTailX0RatChunk000Sub001Block191Part007
    + surrogateDiagTailX0RatChunk000Sub001Block191Part008
    + surrogateDiagTailX0RatChunk000Sub001Block191Part009
    + surrogateDiagTailX0RatChunk000Sub001Block191Part010
    + surrogateDiagTailX0RatChunk000Sub001Block191Part011
    + surrogateDiagTailX0RatChunk000Sub001Block191Part012
    + surrogateDiagTailX0RatChunk000Sub001Block191Part013
    + surrogateDiagTailX0RatChunk000Sub001Block191Part014
    + surrogateDiagTailX0RatChunk000Sub001Block191Part015
    + surrogateDiagTailX0RatChunk000Sub001Block191Part016
    + surrogateDiagTailX0RatChunk000Sub001Block191Part017
    + surrogateDiagTailX0RatChunk000Sub001Block191Part018
    + surrogateDiagTailX0RatChunk000Sub001Block191Part019
    + surrogateDiagTailX0RatChunk000Sub001Block191Part020
    + surrogateDiagTailX0RatChunk000Sub001Block191Part021
    + surrogateDiagTailX0RatChunk000Sub001Block191Part022
    + surrogateDiagTailX0RatChunk000Sub001Block191Part023
    + surrogateDiagTailX0RatChunk000Sub001Block191Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block191_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block191Head + surrogateDiagTailX0RatChunk000Sub001Block191Mid + surrogateDiagTailX0RatChunk000Sub001Block191Tail =
      surrogateDiagTailX0RatChunk000Sub001Block191 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block191Head surrogateDiagTailX0RatChunk000Sub001Block191Mid surrogateDiagTailX0RatChunk000Sub001Block191Tail surrogateDiagTailX0RatChunk000Sub001Block191
  ring

def SurrogateDiagonalTailChunk000Sub001Block191HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block191HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block191Head

def SurrogateDiagonalTailChunk000Sub001Block191MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block191MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block191Mid

def SurrogateDiagonalTailChunk000Sub001Block191TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block191TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block191Tail

theorem surrogateDiagonalTailChunk000Sub001Block191_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block191HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block191MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block191TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block191Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block191 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block191HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block191MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block191TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block191Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block191_eq_head_add_mid_add_tail

/-- Block 192 covers tail-support indices [9800,9825) and q from 16171 to 16210. -/

def TailChunk000Sub001Block192Part000SupportExplicit : Finset ℕ :=
  ([16171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part000 : ℚ :=
  (15904115755675 : ℚ) / 160297201104018720768

def SurrogateDiagonalTailChunk000Sub001Block192Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16171
    = surrogateDiagTailX0RatChunk000Sub001Block192Part000

theorem surrogateDiagonalTailChunk000Sub001Block192Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part000] using hcert

def TailChunk000Sub001Block192Part001SupportExplicit : Finset ℕ :=
  ([16174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part001 : ℚ :=
  (1021868265625 : ℚ) / 2672402168867071602

def SurrogateDiagonalTailChunk000Sub001Block192Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16174
    = surrogateDiagTailX0RatChunk000Sub001Block192Part001

theorem surrogateDiagonalTailChunk000Sub001Block192Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part001] using hcert

def TailChunk000Sub001Block192Part002SupportExplicit : Finset ℕ :=
  ([16177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part002 : ℚ :=
  (98739214829 : ℚ) / 738192735428480640

def SurrogateDiagonalTailChunk000Sub001Block192Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16177
    = surrogateDiagTailX0RatChunk000Sub001Block192Part002

theorem surrogateDiagonalTailChunk000Sub001Block192Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part002] using hcert

def TailChunk000Sub001Block192Part003SupportExplicit : Finset ℕ :=
  ([16178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part003 : ℚ :=
  (1022373765625 : ℚ) / 2675047129366344192

def SurrogateDiagonalTailChunk000Sub001Block192Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16178
    = surrogateDiagTailX0RatChunk000Sub001Block192Part003

theorem surrogateDiagonalTailChunk000Sub001Block192Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part003] using hcert

def TailChunk000Sub001Block192Part004SupportExplicit : Finset ℕ :=
  ([16179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part004 : ℚ :=
  (7269040460725 : ℚ) / 33817879758902919168

def SurrogateDiagonalTailChunk000Sub001Block192Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16179
    = surrogateDiagTailX0RatChunk000Sub001Block192Part004

theorem surrogateDiagonalTailChunk000Sub001Block192Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part004] using hcert

def TailChunk000Sub001Block192Part005SupportExplicit : Finset ℕ :=
  ([16181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part005 : ℚ :=
  (185538315299 : ℚ) / 1556807569254000000

def SurrogateDiagonalTailChunk000Sub001Block192Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16181
    = surrogateDiagTailX0RatChunk000Sub001Block192Part005

theorem surrogateDiagonalTailChunk000Sub001Block192Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part005] using hcert

def TailChunk000Sub001Block192Part006SupportExplicit : Finset ℕ :=
  ([16183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part006 : ℚ :=
  (4092023265625 : ℚ) / 42864292012643303922

def SurrogateDiagonalTailChunk000Sub001Block192Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16183
    = surrogateDiagTailX0RatChunk000Sub001Block192Part006

theorem surrogateDiagonalTailChunk000Sub001Block192Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part006] using hcert

def TailChunk000Sub001Block192Part007SupportExplicit : Finset ℕ :=
  ([16185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part007 : ℚ :=
  (140540589275 : ℚ) / 300066299351138304

def SurrogateDiagonalTailChunk000Sub001Block192Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16185
    = surrogateDiagTailX0RatChunk000Sub001Block192Part007

theorem surrogateDiagonalTailChunk000Sub001Block192Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part007] using hcert

def TailChunk000Sub001Block192Part008SupportExplicit : Finset ℕ :=
  ([16186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part008 : ℚ :=
  (1023385140625 : ℚ) / 2680342939930266912

def SurrogateDiagonalTailChunk000Sub001Block192Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16186
    = surrogateDiagTailX0RatChunk000Sub001Block192Part008

theorem surrogateDiagonalTailChunk000Sub001Block192Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part008] using hcert

def TailChunk000Sub001Block192Part009SupportExplicit : Finset ℕ :=
  ([16187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part009 : ℚ :=
  (4094046390625 : ℚ) / 42906689924352468402

def SurrogateDiagonalTailChunk000Sub001Block192Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16187
    = surrogateDiagTailX0RatChunk000Sub001Block192Part009

theorem surrogateDiagonalTailChunk000Sub001Block192Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part009] using hcert

def TailChunk000Sub001Block192Part010SupportExplicit : Finset ℕ :=
  ([16189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part010 : ℚ :=
  (4095058140625 : ℚ) / 42927900670990485792

def SurrogateDiagonalTailChunk000Sub001Block192Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16189
    = surrogateDiagTailX0RatChunk000Sub001Block192Part010

theorem surrogateDiagonalTailChunk000Sub001Block192Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part010] using hcert

def TailChunk000Sub001Block192Part011SupportExplicit : Finset ℕ :=
  ([16190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part011 : ℚ :=
  (982290974475 : ℚ) / 1462377978664523776

def SurrogateDiagonalTailChunk000Sub001Block192Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16190
    = surrogateDiagTailX0RatChunk000Sub001Block192Part011

theorem surrogateDiagonalTailChunk000Sub001Block192Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part011] using hcert

def TailChunk000Sub001Block192Part012SupportExplicit : Finset ℕ :=
  ([16193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part012 : ℚ :=
  (4097082015625 : ℚ) / 42970345755547533312

def SurrogateDiagonalTailChunk000Sub001Block192Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16193
    = surrogateDiagTailX0RatChunk000Sub001Block192Part012

theorem surrogateDiagonalTailChunk000Sub001Block192Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part012] using hcert

def TailChunk000Sub001Block192Part013SupportExplicit : Finset ℕ :=
  ([16194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part013 : ℚ :=
  (284467510025 : ℚ) / 264987041178953616

def SurrogateDiagonalTailChunk000Sub001Block192Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16194
    = surrogateDiagTailX0RatChunk000Sub001Block192Part013

theorem surrogateDiagonalTailChunk000Sub001Block192Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part013] using hcert

def TailChunk000Sub001Block192Part014SupportExplicit : Finset ℕ :=
  ([16195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part014 : ℚ :=
  (197482522541 : ℚ) / 1213151936879001600

def SurrogateDiagonalTailChunk000Sub001Block192Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16195
    = surrogateDiagTailX0RatChunk000Sub001Block192Part014

theorem surrogateDiagonalTailChunk000Sub001Block192Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part014] using hcert

def TailChunk000Sub001Block192Part015SupportExplicit : Finset ℕ :=
  ([16197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part015 : ℚ :=
  (7285225460125 : ℚ) / 33968655879389977728

def SurrogateDiagonalTailChunk000Sub001Block192Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16197
    = surrogateDiagTailX0RatChunk000Sub001Block192Part015

theorem surrogateDiagonalTailChunk000Sub001Block192Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part015] using hcert

def TailChunk000Sub001Block192Part016SupportExplicit : Finset ℕ :=
  ([16198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part016 : ℚ :=
  (2884945189675 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk000Sub001Block192Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16198
    = surrogateDiagTailX0RatChunk000Sub001Block192Part016

theorem surrogateDiagonalTailChunk000Sub001Block192Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part016] using hcert

def TailChunk000Sub001Block192Part017SupportExplicit : Finset ℕ :=
  ([16199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part017 : ℚ :=
  (664656366475 : ℚ) / 6719437232843784192

def SurrogateDiagonalTailChunk000Sub001Block192Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16199
    = surrogateDiagTailX0RatChunk000Sub001Block192Part017

theorem surrogateDiagonalTailChunk000Sub001Block192Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part017] using hcert

def TailChunk000Sub001Block192Part018SupportExplicit : Finset ℕ :=
  ([16201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part018 : ℚ :=
  (4911244262625 : ℚ) / 44867650508340330496

def SurrogateDiagonalTailChunk000Sub001Block192Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16201
    = surrogateDiagTailX0RatChunk000Sub001Block192Part018

theorem surrogateDiagonalTailChunk000Sub001Block192Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part018] using hcert

def TailChunk000Sub001Block192Part019SupportExplicit : Finset ℕ :=
  ([16202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part019 : ℚ :=
  (65626201 : ℚ) / 172221321376800

def SurrogateDiagonalTailChunk000Sub001Block192Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16202
    = surrogateDiagTailX0RatChunk000Sub001Block192Part019

theorem surrogateDiagonalTailChunk000Sub001Block192Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part019] using hcert

def TailChunk000Sub001Block192Part020SupportExplicit : Finset ℕ :=
  ([16203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part020 : ℚ :=
  (62334854719 : ℚ) / 230638158408000000

def SurrogateDiagonalTailChunk000Sub001Block192Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16203
    = surrogateDiagTailX0RatChunk000Sub001Block192Part020

theorem surrogateDiagonalTailChunk000Sub001Block192Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part020] using hcert

def TailChunk000Sub001Block192Part021SupportExplicit : Finset ℕ :=
  ([16205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part021 : ℚ :=
  (685430245925 : ℚ) / 3149622337828184064

def SurrogateDiagonalTailChunk000Sub001Block192Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16205
    = surrogateDiagTailX0RatChunk000Sub001Block192Part021

theorem surrogateDiagonalTailChunk000Sub001Block192Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part021] using hcert

def TailChunk000Sub001Block192Part022SupportExplicit : Finset ℕ :=
  ([16206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part022 : ℚ :=
  (1743846147625 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk000Sub001Block192Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16206
    = surrogateDiagTailX0RatChunk000Sub001Block192Part022

theorem surrogateDiagonalTailChunk000Sub001Block192Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part022] using hcert

def TailChunk000Sub001Block192Part023SupportExplicit : Finset ℕ :=
  ([16207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part023 : ℚ :=
  (7466725264925 : ℚ) / 69158451835665736704

def SurrogateDiagonalTailChunk000Sub001Block192Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16207
    = surrogateDiagTailX0RatChunk000Sub001Block192Part023

theorem surrogateDiagonalTailChunk000Sub001Block192Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part023] using hcert

def TailChunk000Sub001Block192Part024SupportExplicit : Finset ℕ :=
  ([16210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block192Part024 : ℚ :=
  (118166382277 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub001Block192Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16210
    = surrogateDiagTailX0RatChunk000Sub001Block192Part024

theorem surrogateDiagonalTailChunk000Sub001Block192Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block192Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block192Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block192Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block192Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block192Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block192Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block192HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block192Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block192Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block192Part000
    + surrogateDiagTailX0RatChunk000Sub001Block192Part001
    + surrogateDiagTailX0RatChunk000Sub001Block192Part002
    + surrogateDiagTailX0RatChunk000Sub001Block192Part003
    + surrogateDiagTailX0RatChunk000Sub001Block192Part004
    + surrogateDiagTailX0RatChunk000Sub001Block192Part005
    + surrogateDiagTailX0RatChunk000Sub001Block192Part006
    + surrogateDiagTailX0RatChunk000Sub001Block192Part007
    + surrogateDiagTailX0RatChunk000Sub001Block192Part008
    + surrogateDiagTailX0RatChunk000Sub001Block192Part009

def surrogateDiagonalTailChunk000Sub001Block192MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block192Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block192Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block192Part010
    + surrogateDiagTailX0RatChunk000Sub001Block192Part011
    + surrogateDiagTailX0RatChunk000Sub001Block192Part012
    + surrogateDiagTailX0RatChunk000Sub001Block192Part013
    + surrogateDiagTailX0RatChunk000Sub001Block192Part014
    + surrogateDiagTailX0RatChunk000Sub001Block192Part015
    + surrogateDiagTailX0RatChunk000Sub001Block192Part016
    + surrogateDiagTailX0RatChunk000Sub001Block192Part017
    + surrogateDiagTailX0RatChunk000Sub001Block192Part018
    + surrogateDiagTailX0RatChunk000Sub001Block192Part019

def surrogateDiagonalTailChunk000Sub001Block192TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block192Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block192Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block192Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block192Part020
    + surrogateDiagTailX0RatChunk000Sub001Block192Part021
    + surrogateDiagTailX0RatChunk000Sub001Block192Part022
    + surrogateDiagTailX0RatChunk000Sub001Block192Part023
    + surrogateDiagTailX0RatChunk000Sub001Block192Part024

def surrogateDiagonalTailChunk000Sub001Block192Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block192HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block192MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block192TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block192 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block192Part000
    + surrogateDiagTailX0RatChunk000Sub001Block192Part001
    + surrogateDiagTailX0RatChunk000Sub001Block192Part002
    + surrogateDiagTailX0RatChunk000Sub001Block192Part003
    + surrogateDiagTailX0RatChunk000Sub001Block192Part004
    + surrogateDiagTailX0RatChunk000Sub001Block192Part005
    + surrogateDiagTailX0RatChunk000Sub001Block192Part006
    + surrogateDiagTailX0RatChunk000Sub001Block192Part007
    + surrogateDiagTailX0RatChunk000Sub001Block192Part008
    + surrogateDiagTailX0RatChunk000Sub001Block192Part009
    + surrogateDiagTailX0RatChunk000Sub001Block192Part010
    + surrogateDiagTailX0RatChunk000Sub001Block192Part011
    + surrogateDiagTailX0RatChunk000Sub001Block192Part012
    + surrogateDiagTailX0RatChunk000Sub001Block192Part013
    + surrogateDiagTailX0RatChunk000Sub001Block192Part014
    + surrogateDiagTailX0RatChunk000Sub001Block192Part015
    + surrogateDiagTailX0RatChunk000Sub001Block192Part016
    + surrogateDiagTailX0RatChunk000Sub001Block192Part017
    + surrogateDiagTailX0RatChunk000Sub001Block192Part018
    + surrogateDiagTailX0RatChunk000Sub001Block192Part019
    + surrogateDiagTailX0RatChunk000Sub001Block192Part020
    + surrogateDiagTailX0RatChunk000Sub001Block192Part021
    + surrogateDiagTailX0RatChunk000Sub001Block192Part022
    + surrogateDiagTailX0RatChunk000Sub001Block192Part023
    + surrogateDiagTailX0RatChunk000Sub001Block192Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block192_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block192Head + surrogateDiagTailX0RatChunk000Sub001Block192Mid + surrogateDiagTailX0RatChunk000Sub001Block192Tail =
      surrogateDiagTailX0RatChunk000Sub001Block192 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block192Head surrogateDiagTailX0RatChunk000Sub001Block192Mid surrogateDiagTailX0RatChunk000Sub001Block192Tail surrogateDiagTailX0RatChunk000Sub001Block192
  ring

def SurrogateDiagonalTailChunk000Sub001Block192HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block192HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block192Head

def SurrogateDiagonalTailChunk000Sub001Block192MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block192MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block192Mid

def SurrogateDiagonalTailChunk000Sub001Block192TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block192TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block192Tail

theorem surrogateDiagonalTailChunk000Sub001Block192_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block192HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block192MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block192TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block192Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block192 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block192HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block192MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block192TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block192Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block192_eq_head_add_mid_add_tail

/-- Block 193 covers tail-support indices [9825,9850) and q from 16211 to 16253. -/

def TailChunk000Sub001Block193Part000SupportExplicit : Finset ℕ :=
  ([16211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part000 : ℚ :=
  (808845517225 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk000Sub001Block193Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16211
    = surrogateDiagTailX0RatChunk000Sub001Block193Part000

theorem surrogateDiagonalTailChunk000Sub001Block193Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part000] using hcert

def TailChunk000Sub001Block193Part001SupportExplicit : Finset ℕ :=
  ([16213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part001 : ℚ :=
  (9671378641 : ℚ) / 93988324386346050

def SurrogateDiagonalTailChunk000Sub001Block193Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16213
    = surrogateDiagTailX0RatChunk000Sub001Block193Part001

theorem surrogateDiagonalTailChunk000Sub001Block193Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part001] using hcert

def TailChunk000Sub001Block193Part002SupportExplicit : Finset ℕ :=
  ([16215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part002 : ℚ :=
  (136545401175 : ℚ) / 325532922390511616

def SurrogateDiagonalTailChunk000Sub001Block193Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16215
    = surrogateDiagTailX0RatChunk000Sub001Block193Part002

theorem surrogateDiagonalTailChunk000Sub001Block193Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part002] using hcert

def TailChunk000Sub001Block193Part003SupportExplicit : Finset ℕ :=
  ([16217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part003 : ℚ :=
  (4109235765625 : ℚ) / 43225677635174625792

def SurrogateDiagonalTailChunk000Sub001Block193Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16217
    = surrogateDiagTailX0RatChunk000Sub001Block193Part003

theorem surrogateDiagonalTailChunk000Sub001Block193Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part003] using hcert

def TailChunk000Sub001Block193Part004SupportExplicit : Finset ℕ :=
  ([16221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part004 : ℚ :=
  (7306833459325 : ℚ) / 34170474297389655168

def SurrogateDiagonalTailChunk000Sub001Block193Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16221
    = surrogateDiagTailX0RatChunk000Sub001Block193Part004

theorem surrogateDiagonalTailChunk000Sub001Block193Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part004] using hcert

def TailChunk000Sub001Block193Part005SupportExplicit : Finset ℕ :=
  ([16222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part005 : ℚ :=
  (1644708025 : ℚ) / 4326834332237682

def SurrogateDiagonalTailChunk000Sub001Block193Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16222
    = surrogateDiagTailX0RatChunk000Sub001Block193Part005

theorem surrogateDiagonalTailChunk000Sub001Block193Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part005] using hcert

def TailChunk000Sub001Block193Part006SupportExplicit : Finset ℕ :=
  ([16223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part006 : ℚ :=
  (4112277015625 : ℚ) / 43289688006350408082

def SurrogateDiagonalTailChunk000Sub001Block193Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16223
    = surrogateDiagTailX0RatChunk000Sub001Block193Part006

theorem surrogateDiagonalTailChunk000Sub001Block193Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part006] using hcert

def TailChunk000Sub001Block193Part007SupportExplicit : Finset ℕ :=
  ([16226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part007 : ℚ :=
  (119209277671 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub001Block193Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16226
    = surrogateDiagTailX0RatChunk000Sub001Block193Part007

theorem surrogateDiagonalTailChunk000Sub001Block193Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part007] using hcert

def TailChunk000Sub001Block193Part008SupportExplicit : Finset ℕ :=
  ([16229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part008 : ℚ :=
  (4115319390625 : ℚ) / 43353769443124768032

def SurrogateDiagonalTailChunk000Sub001Block193Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16229
    = surrogateDiagTailX0RatChunk000Sub001Block193Part008

theorem surrogateDiagonalTailChunk000Sub001Block193Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part008] using hcert

def TailChunk000Sub001Block193Part009SupportExplicit : Finset ℕ :=
  ([16230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part009 : ℚ :=
  (3772592569 : ℚ) / 1935304615526400

def SurrogateDiagonalTailChunk000Sub001Block193Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16230
    = surrogateDiagTailX0RatChunk000Sub001Block193Part009

theorem surrogateDiagonalTailChunk000Sub001Block193Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part009] using hcert

def TailChunk000Sub001Block193Part010SupportExplicit : Finset ℕ :=
  ([16231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part010 : ℚ :=
  (6586134025 : ℚ) / 69400233157587282

def SurrogateDiagonalTailChunk000Sub001Block193Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16231
    = surrogateDiagTailX0RatChunk000Sub001Block193Part010

theorem surrogateDiagonalTailChunk000Sub001Block193Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part010] using hcert

def TailChunk000Sub001Block193Part011SupportExplicit : Finset ℕ :=
  ([16233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part011 : ℚ :=
  (105598080175 : ℚ) / 341057248935985152

def SurrogateDiagonalTailChunk000Sub001Block193Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16233
    = surrogateDiagTailX0RatChunk000Sub001Block193Part011

theorem surrogateDiagonalTailChunk000Sub001Block193Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part011] using hcert

def TailChunk000Sub001Block193Part012SupportExplicit : Finset ℕ :=
  ([16234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part012 : ℚ :=
  (1029463890625 : ℚ) / 2712283119239176992

def SurrogateDiagonalTailChunk000Sub001Block193Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16234
    = surrogateDiagTailX0RatChunk000Sub001Block193Part012

theorem surrogateDiagonalTailChunk000Sub001Block193Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part012] using hcert

def TailChunk000Sub001Block193Part013SupportExplicit : Finset ℕ :=
  ([16235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part013 : ℚ :=
  (100292649283 : ℚ) / 546715212762316800

def SurrogateDiagonalTailChunk000Sub001Block193Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16235
    = surrogateDiagTailX0RatChunk000Sub001Block193Part013

theorem surrogateDiagonalTailChunk000Sub001Block193Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part013] using hcert

def TailChunk000Sub001Block193Part014SupportExplicit : Finset ℕ :=
  ([16237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part014 : ℚ :=
  (7157298298925 : ℚ) / 62889796407807442944

def SurrogateDiagonalTailChunk000Sub001Block193Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16237
    = surrogateDiagTailX0RatChunk000Sub001Block193Part014

theorem surrogateDiagonalTailChunk000Sub001Block193Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part014] using hcert

def TailChunk000Sub001Block193Part015SupportExplicit : Finset ℕ :=
  ([16238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part015 : ℚ :=
  (3856244345425 : ℚ) / 8992661292762267648

def SurrogateDiagonalTailChunk000Sub001Block193Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16238
    = surrogateDiagTailX0RatChunk000Sub001Block193Part015

theorem surrogateDiagonalTailChunk000Sub001Block193Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part015] using hcert

def TailChunk000Sub001Block193Part016SupportExplicit : Finset ℕ :=
  ([16239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part016 : ℚ :=
  (665732768975 : ℚ) / 3120220659659102208

def SurrogateDiagonalTailChunk000Sub001Block193Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16239
    = surrogateDiagTailX0RatChunk000Sub001Block193Part016

theorem surrogateDiagonalTailChunk000Sub001Block193Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part016] using hcert

def TailChunk000Sub001Block193Part017SupportExplicit : Finset ℕ :=
  ([16241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part017 : ℚ :=
  (16047957508075 : ℚ) / 163218259509280800768

def SurrogateDiagonalTailChunk000Sub001Block193Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16241
    = surrogateDiagTailX0RatChunk000Sub001Block193Part017

theorem surrogateDiagonalTailChunk000Sub001Block193Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part017] using hcert

def TailChunk000Sub001Block193Part018SupportExplicit : Finset ℕ :=
  ([16242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part018 : ℚ :=
  (35769566275 : ℚ) / 33517995367431762

def SurrogateDiagonalTailChunk000Sub001Block193Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16242
    = surrogateDiagTailX0RatChunk000Sub001Block193Part018

theorem surrogateDiagonalTailChunk000Sub001Block193Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part018] using hcert

def TailChunk000Sub001Block193Part019SupportExplicit : Finset ℕ :=
  ([16243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part019 : ℚ :=
  (15684043390825 : ℚ) / 154572881850368575488

def SurrogateDiagonalTailChunk000Sub001Block193Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16243
    = surrogateDiagTailX0RatChunk000Sub001Block193Part019

theorem surrogateDiagonalTailChunk000Sub001Block193Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part019] using hcert

def TailChunk000Sub001Block193Part020SupportExplicit : Finset ℕ :=
  ([16246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part020 : ℚ :=
  (1030986390625 : ℚ) / 2720312569141493682

def SurrogateDiagonalTailChunk000Sub001Block193Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16246
    = surrogateDiagTailX0RatChunk000Sub001Block193Part020

theorem surrogateDiagonalTailChunk000Sub001Block193Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part020] using hcert

def TailChunk000Sub001Block193Part021SupportExplicit : Finset ℕ :=
  ([16247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part021 : ℚ :=
  (29915577623 : ℚ) / 180069846768000000

def SurrogateDiagonalTailChunk000Sub001Block193Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16247
    = surrogateDiagTailX0RatChunk000Sub001Block193Part021

theorem surrogateDiagonalTailChunk000Sub001Block193Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part021] using hcert

def TailChunk000Sub001Block193Part022SupportExplicit : Finset ℕ :=
  ([16249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part022 : ℚ :=
  (4125468765625 : ℚ) / 43567888159158538752

def SurrogateDiagonalTailChunk000Sub001Block193Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16249
    = surrogateDiagTailX0RatChunk000Sub001Block193Part022

theorem surrogateDiagonalTailChunk000Sub001Block193Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part022] using hcert

def TailChunk000Sub001Block193Part023SupportExplicit : Finset ℕ :=
  ([16251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part023 : ℚ :=
  (7333888458325 : ℚ) / 34424010397359833088

def SurrogateDiagonalTailChunk000Sub001Block193Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16251
    = surrogateDiagTailX0RatChunk000Sub001Block193Part023

theorem surrogateDiagonalTailChunk000Sub001Block193Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part023] using hcert

def TailChunk000Sub001Block193Part024SupportExplicit : Finset ℕ :=
  ([16253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block193Part024 : ℚ :=
  (4127500140625 : ℚ) / 43610806898089918752

def SurrogateDiagonalTailChunk000Sub001Block193Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16253
    = surrogateDiagTailX0RatChunk000Sub001Block193Part024

theorem surrogateDiagonalTailChunk000Sub001Block193Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block193Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block193Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block193Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block193Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block193Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block193Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block193HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block193Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block193Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block193Part000
    + surrogateDiagTailX0RatChunk000Sub001Block193Part001
    + surrogateDiagTailX0RatChunk000Sub001Block193Part002
    + surrogateDiagTailX0RatChunk000Sub001Block193Part003
    + surrogateDiagTailX0RatChunk000Sub001Block193Part004
    + surrogateDiagTailX0RatChunk000Sub001Block193Part005
    + surrogateDiagTailX0RatChunk000Sub001Block193Part006
    + surrogateDiagTailX0RatChunk000Sub001Block193Part007
    + surrogateDiagTailX0RatChunk000Sub001Block193Part008
    + surrogateDiagTailX0RatChunk000Sub001Block193Part009

def surrogateDiagonalTailChunk000Sub001Block193MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block193Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block193Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block193Part010
    + surrogateDiagTailX0RatChunk000Sub001Block193Part011
    + surrogateDiagTailX0RatChunk000Sub001Block193Part012
    + surrogateDiagTailX0RatChunk000Sub001Block193Part013
    + surrogateDiagTailX0RatChunk000Sub001Block193Part014
    + surrogateDiagTailX0RatChunk000Sub001Block193Part015
    + surrogateDiagTailX0RatChunk000Sub001Block193Part016
    + surrogateDiagTailX0RatChunk000Sub001Block193Part017
    + surrogateDiagTailX0RatChunk000Sub001Block193Part018
    + surrogateDiagTailX0RatChunk000Sub001Block193Part019

def surrogateDiagonalTailChunk000Sub001Block193TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block193Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block193Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block193Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block193Part020
    + surrogateDiagTailX0RatChunk000Sub001Block193Part021
    + surrogateDiagTailX0RatChunk000Sub001Block193Part022
    + surrogateDiagTailX0RatChunk000Sub001Block193Part023
    + surrogateDiagTailX0RatChunk000Sub001Block193Part024

def surrogateDiagonalTailChunk000Sub001Block193Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block193HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block193MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block193TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block193 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block193Part000
    + surrogateDiagTailX0RatChunk000Sub001Block193Part001
    + surrogateDiagTailX0RatChunk000Sub001Block193Part002
    + surrogateDiagTailX0RatChunk000Sub001Block193Part003
    + surrogateDiagTailX0RatChunk000Sub001Block193Part004
    + surrogateDiagTailX0RatChunk000Sub001Block193Part005
    + surrogateDiagTailX0RatChunk000Sub001Block193Part006
    + surrogateDiagTailX0RatChunk000Sub001Block193Part007
    + surrogateDiagTailX0RatChunk000Sub001Block193Part008
    + surrogateDiagTailX0RatChunk000Sub001Block193Part009
    + surrogateDiagTailX0RatChunk000Sub001Block193Part010
    + surrogateDiagTailX0RatChunk000Sub001Block193Part011
    + surrogateDiagTailX0RatChunk000Sub001Block193Part012
    + surrogateDiagTailX0RatChunk000Sub001Block193Part013
    + surrogateDiagTailX0RatChunk000Sub001Block193Part014
    + surrogateDiagTailX0RatChunk000Sub001Block193Part015
    + surrogateDiagTailX0RatChunk000Sub001Block193Part016
    + surrogateDiagTailX0RatChunk000Sub001Block193Part017
    + surrogateDiagTailX0RatChunk000Sub001Block193Part018
    + surrogateDiagTailX0RatChunk000Sub001Block193Part019
    + surrogateDiagTailX0RatChunk000Sub001Block193Part020
    + surrogateDiagTailX0RatChunk000Sub001Block193Part021
    + surrogateDiagTailX0RatChunk000Sub001Block193Part022
    + surrogateDiagTailX0RatChunk000Sub001Block193Part023
    + surrogateDiagTailX0RatChunk000Sub001Block193Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block193_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block193Head + surrogateDiagTailX0RatChunk000Sub001Block193Mid + surrogateDiagTailX0RatChunk000Sub001Block193Tail =
      surrogateDiagTailX0RatChunk000Sub001Block193 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block193Head surrogateDiagTailX0RatChunk000Sub001Block193Mid surrogateDiagTailX0RatChunk000Sub001Block193Tail surrogateDiagTailX0RatChunk000Sub001Block193
  ring

def SurrogateDiagonalTailChunk000Sub001Block193HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block193HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block193Head

def SurrogateDiagonalTailChunk000Sub001Block193MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block193MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block193Mid

def SurrogateDiagonalTailChunk000Sub001Block193TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block193TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block193Tail

theorem surrogateDiagonalTailChunk000Sub001Block193_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block193HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block193MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block193TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block193Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block193 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block193HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block193MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block193TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block193Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block193_eq_head_add_mid_add_tail

/-- Block 194 covers tail-support indices [9850,9875) and q from 16255 to 16293. -/

def TailChunk000Sub001Block194Part000SupportExplicit : Finset ℕ :=
  ([16255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part000 : ℚ :=
  (448998517249 : ℚ) / 2856671220000000000

def SurrogateDiagonalTailChunk000Sub001Block194Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16255
    = surrogateDiagTailX0RatChunk000Sub001Block194Part000

theorem surrogateDiagonalTailChunk000Sub001Block194Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part000] using hcert

def TailChunk000Sub001Block194Part001SupportExplicit : Finset ℕ :=
  ([16257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part001 : ℚ :=
  (7339305458125 : ℚ) / 34474886443215969408

def SurrogateDiagonalTailChunk000Sub001Block194Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16257
    = surrogateDiagTailX0RatChunk000Sub001Block194Part001

theorem surrogateDiagonalTailChunk000Sub001Block194Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part001] using hcert

def TailChunk000Sub001Block194Part002SupportExplicit : Finset ℕ :=
  ([16258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part002 : ℚ :=
  (963200293 : ℚ) / 1977976094355648

def SurrogateDiagonalTailChunk000Sub001Block194Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16258
    = surrogateDiagTailX0RatChunk000Sub001Block194Part002

theorem surrogateDiagonalTailChunk000Sub001Block194Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part002] using hcert

def TailChunk000Sub001Block194Part003SupportExplicit : Finset ℕ :=
  ([16259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part003 : ℚ :=
  (18298727411 : ℚ) / 185417343215032320

def SurrogateDiagonalTailChunk000Sub001Block194Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16259
    = surrogateDiagTailX0RatChunk000Sub001Block194Part003

theorem surrogateDiagonalTailChunk000Sub001Block194Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part003] using hcert

def TailChunk000Sub001Block194Part004SupportExplicit : Finset ℕ :=
  ([16261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part004 : ℚ :=
  (455774280661 : ℚ) / 3036564951552000000

def SurrogateDiagonalTailChunk000Sub001Block194Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16261
    = surrogateDiagTailX0RatChunk000Sub001Block194Part004

theorem surrogateDiagonalTailChunk000Sub001Block194Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part004] using hcert

def TailChunk000Sub001Block194Part005SupportExplicit : Finset ℕ :=
  ([16262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part005 : ℚ :=
  (3979119430675 : ℚ) / 9798779236138272768

def SurrogateDiagonalTailChunk000Sub001Block194Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16262
    = surrogateDiagTailX0RatChunk000Sub001Block194Part005

theorem surrogateDiagonalTailChunk000Sub001Block194Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part005] using hcert

def TailChunk000Sub001Block194Part006SupportExplicit : Finset ℕ :=
  ([16265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part006 : ℚ :=
  (11238780981775 : ℚ) / 71592737991031554048

def SurrogateDiagonalTailChunk000Sub001Block194Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16265
    = surrogateDiagTailX0RatChunk000Sub001Block194Part006

theorem surrogateDiagonalTailChunk000Sub001Block194Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part006] using hcert

def TailChunk000Sub001Block194Part007SupportExplicit : Finset ℕ :=
  ([16266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part007 : ℚ :=
  (22960233247 : ℚ) / 21578636788384800

def SurrogateDiagonalTailChunk000Sub001Block194Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16266
    = surrogateDiagTailX0RatChunk000Sub001Block194Part007

theorem surrogateDiagonalTailChunk000Sub001Block194Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part007] using hcert

def TailChunk000Sub001Block194Part008SupportExplicit : Finset ℕ :=
  ([16267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part008 : ℚ :=
  (4134613890625 : ℚ) / 43761272237193779442

def SurrogateDiagonalTailChunk000Sub001Block194Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16267
    = surrogateDiagTailX0RatChunk000Sub001Block194Part008

theorem surrogateDiagonalTailChunk000Sub001Block194Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part008] using hcert

def TailChunk000Sub001Block194Part009SupportExplicit : Finset ℕ :=
  ([16269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part009 : ℚ :=
  (36306776361 : ℚ) / 107440405426995200

def SurrogateDiagonalTailChunk000Sub001Block194Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16269
    = surrogateDiagTailX0RatChunk000Sub001Block194Part009

theorem surrogateDiagonalTailChunk000Sub001Block194Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part009] using hcert

def TailChunk000Sub001Block194Part010SupportExplicit : Finset ℕ :=
  ([16270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part010 : ℚ :=
  (2976073465825 : ℚ) / 4474546124439472128

def SurrogateDiagonalTailChunk000Sub001Block194Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16270
    = surrogateDiagTailX0RatChunk000Sub001Block194Part010

theorem surrogateDiagonalTailChunk000Sub001Block194Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part010] using hcert

def TailChunk000Sub001Block194Part011SupportExplicit : Finset ℕ :=
  ([16271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part011 : ℚ :=
  (5310013978025 : ℚ) / 53432400368006240256

def SurrogateDiagonalTailChunk000Sub001Block194Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16271
    = surrogateDiagTailX0RatChunk000Sub001Block194Part011

theorem surrogateDiagonalTailChunk000Sub001Block194Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part011] using hcert

def TailChunk000Sub001Block194Part012SupportExplicit : Finset ℕ :=
  ([16273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part012 : ℚ :=
  (4137664515625 : ℚ) / 43825876429541548032

def SurrogateDiagonalTailChunk000Sub001Block194Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16273
    = surrogateDiagTailX0RatChunk000Sub001Block194Part012

theorem surrogateDiagonalTailChunk000Sub001Block194Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part012] using hcert

def TailChunk000Sub001Block194Part013SupportExplicit : Finset ℕ :=
  ([16274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part013 : ℚ :=
  (4011236686675 : ℚ) / 10018575069001170048

def SurrogateDiagonalTailChunk000Sub001Block194Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16274
    = surrogateDiagTailX0RatChunk000Sub001Block194Part013

theorem surrogateDiagonalTailChunk000Sub001Block194Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part013] using hcert

def TailChunk000Sub001Block194Part014SupportExplicit : Finset ℕ :=
  ([16277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part014 : ℚ :=
  (210843122939 : ℚ) / 2098873694512742400

def SurrogateDiagonalTailChunk000Sub001Block194Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16277
    = surrogateDiagTailX0RatChunk000Sub001Block194Part014

theorem surrogateDiagonalTailChunk000Sub001Block194Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part014] using hcert

def TailChunk000Sub001Block194Part015SupportExplicit : Finset ℕ :=
  ([16278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part015 : ℚ :=
  (1149706308425 : ℚ) / 1082120405667692544

def SurrogateDiagonalTailChunk000Sub001Block194Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16278
    = surrogateDiagTailX0RatChunk000Sub001Block194Part015

theorem surrogateDiagonalTailChunk000Sub001Block194Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part015] using hcert

def TailChunk000Sub001Block194Part016SupportExplicit : Finset ℕ :=
  ([16279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part016 : ℚ :=
  (1003518740125 : ℚ) / 10201141219330050048

def SurrogateDiagonalTailChunk000Sub001Block194Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16279
    = surrogateDiagTailX0RatChunk000Sub001Block194Part016

theorem surrogateDiagonalTailChunk000Sub001Block194Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part016] using hcert

def TailChunk000Sub001Block194Part017SupportExplicit : Finset ℕ :=
  ([16282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part017 : ℚ :=
  (3378089630875 : ℚ) / 5908216111837619328

def SurrogateDiagonalTailChunk000Sub001Block194Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16282
    = surrogateDiagTailX0RatChunk000Sub001Block194Part017

theorem surrogateDiagonalTailChunk000Sub001Block194Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part017] using hcert

def TailChunk000Sub001Block194Part018SupportExplicit : Finset ℕ :=
  ([16283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part018 : ℚ :=
  (2512324528625 : ℚ) / 23488792297838788608

def SurrogateDiagonalTailChunk000Sub001Block194Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16283
    = surrogateDiagTailX0RatChunk000Sub001Block194Part018

theorem surrogateDiagonalTailChunk000Sub001Block194Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part018] using hcert

def TailChunk000Sub001Block194Part019SupportExplicit : Finset ℕ :=
  ([16285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part019 : ℚ :=
  (11266442585275 : ℚ) / 71945628206341029888

def SurrogateDiagonalTailChunk000Sub001Block194Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16285
    = surrogateDiagTailX0RatChunk000Sub001Block194Part019

theorem surrogateDiagonalTailChunk000Sub001Block194Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part019] using hcert

def TailChunk000Sub001Block194Part020SupportExplicit : Finset ℕ :=
  ([16286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part020 : ℚ :=
  (19813465125 : ℚ) / 44557123621249024

def SurrogateDiagonalTailChunk000Sub001Block194Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16286
    = surrogateDiagTailX0RatChunk000Sub001Block194Part020

theorem surrogateDiagonalTailChunk000Sub001Block194Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part020] using hcert

def TailChunk000Sub001Block194Part021SupportExplicit : Finset ℕ :=
  ([16287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part021 : ℚ :=
  (70591446001 : ℚ) / 310944251038924800

def SurrogateDiagonalTailChunk000Sub001Block194Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16287
    = surrogateDiagTailX0RatChunk000Sub001Block194Part021

theorem surrogateDiagonalTailChunk000Sub001Block194Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part021] using hcert

def TailChunk000Sub001Block194Part022SupportExplicit : Finset ℕ :=
  ([16289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part022 : ℚ :=
  (11116671255775 : ℚ) / 67458526997649850368

def SurrogateDiagonalTailChunk000Sub001Block194Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16289
    = surrogateDiagTailX0RatChunk000Sub001Block194Part022

theorem surrogateDiagonalTailChunk000Sub001Block194Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part022] using hcert

def TailChunk000Sub001Block194Part023SupportExplicit : Finset ℕ :=
  ([16291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part023 : ℚ :=
  (16546530217 : ℚ) / 4798811730432000000

def SurrogateDiagonalTailChunk000Sub001Block194Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16291
    = surrogateDiagTailX0RatChunk000Sub001Block194Part023

theorem surrogateDiagonalTailChunk000Sub001Block194Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part023] using hcert

def TailChunk000Sub001Block194Part024SupportExplicit : Finset ℕ :=
  ([16293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block194Part024 : ℚ :=
  (1667 : ℚ) / 92731661654400

def SurrogateDiagonalTailChunk000Sub001Block194Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16293
    = surrogateDiagTailX0RatChunk000Sub001Block194Part024

theorem surrogateDiagonalTailChunk000Sub001Block194Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block194Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block194Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block194Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block194Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block194Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block194Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block194HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block194Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block194Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block194Part000
    + surrogateDiagTailX0RatChunk000Sub001Block194Part001
    + surrogateDiagTailX0RatChunk000Sub001Block194Part002
    + surrogateDiagTailX0RatChunk000Sub001Block194Part003
    + surrogateDiagTailX0RatChunk000Sub001Block194Part004
    + surrogateDiagTailX0RatChunk000Sub001Block194Part005
    + surrogateDiagTailX0RatChunk000Sub001Block194Part006
    + surrogateDiagTailX0RatChunk000Sub001Block194Part007
    + surrogateDiagTailX0RatChunk000Sub001Block194Part008
    + surrogateDiagTailX0RatChunk000Sub001Block194Part009

def surrogateDiagonalTailChunk000Sub001Block194MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block194Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block194Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block194Part010
    + surrogateDiagTailX0RatChunk000Sub001Block194Part011
    + surrogateDiagTailX0RatChunk000Sub001Block194Part012
    + surrogateDiagTailX0RatChunk000Sub001Block194Part013
    + surrogateDiagTailX0RatChunk000Sub001Block194Part014
    + surrogateDiagTailX0RatChunk000Sub001Block194Part015
    + surrogateDiagTailX0RatChunk000Sub001Block194Part016
    + surrogateDiagTailX0RatChunk000Sub001Block194Part017
    + surrogateDiagTailX0RatChunk000Sub001Block194Part018
    + surrogateDiagTailX0RatChunk000Sub001Block194Part019

def surrogateDiagonalTailChunk000Sub001Block194TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block194Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block194Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block194Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block194Part020
    + surrogateDiagTailX0RatChunk000Sub001Block194Part021
    + surrogateDiagTailX0RatChunk000Sub001Block194Part022
    + surrogateDiagTailX0RatChunk000Sub001Block194Part023
    + surrogateDiagTailX0RatChunk000Sub001Block194Part024

def surrogateDiagonalTailChunk000Sub001Block194Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block194HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block194MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block194TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block194 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block194Part000
    + surrogateDiagTailX0RatChunk000Sub001Block194Part001
    + surrogateDiagTailX0RatChunk000Sub001Block194Part002
    + surrogateDiagTailX0RatChunk000Sub001Block194Part003
    + surrogateDiagTailX0RatChunk000Sub001Block194Part004
    + surrogateDiagTailX0RatChunk000Sub001Block194Part005
    + surrogateDiagTailX0RatChunk000Sub001Block194Part006
    + surrogateDiagTailX0RatChunk000Sub001Block194Part007
    + surrogateDiagTailX0RatChunk000Sub001Block194Part008
    + surrogateDiagTailX0RatChunk000Sub001Block194Part009
    + surrogateDiagTailX0RatChunk000Sub001Block194Part010
    + surrogateDiagTailX0RatChunk000Sub001Block194Part011
    + surrogateDiagTailX0RatChunk000Sub001Block194Part012
    + surrogateDiagTailX0RatChunk000Sub001Block194Part013
    + surrogateDiagTailX0RatChunk000Sub001Block194Part014
    + surrogateDiagTailX0RatChunk000Sub001Block194Part015
    + surrogateDiagTailX0RatChunk000Sub001Block194Part016
    + surrogateDiagTailX0RatChunk000Sub001Block194Part017
    + surrogateDiagTailX0RatChunk000Sub001Block194Part018
    + surrogateDiagTailX0RatChunk000Sub001Block194Part019
    + surrogateDiagTailX0RatChunk000Sub001Block194Part020
    + surrogateDiagTailX0RatChunk000Sub001Block194Part021
    + surrogateDiagTailX0RatChunk000Sub001Block194Part022
    + surrogateDiagTailX0RatChunk000Sub001Block194Part023
    + surrogateDiagTailX0RatChunk000Sub001Block194Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block194_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block194Head + surrogateDiagTailX0RatChunk000Sub001Block194Mid + surrogateDiagTailX0RatChunk000Sub001Block194Tail =
      surrogateDiagTailX0RatChunk000Sub001Block194 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block194Head surrogateDiagTailX0RatChunk000Sub001Block194Mid surrogateDiagTailX0RatChunk000Sub001Block194Tail surrogateDiagTailX0RatChunk000Sub001Block194
  ring

def SurrogateDiagonalTailChunk000Sub001Block194HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block194HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block194Head

def SurrogateDiagonalTailChunk000Sub001Block194MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block194MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block194Mid

def SurrogateDiagonalTailChunk000Sub001Block194TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block194TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block194Tail

theorem surrogateDiagonalTailChunk000Sub001Block194_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block194HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block194MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block194TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block194Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block194 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block194HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block194MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block194TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block194Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block194_eq_head_add_mid_add_tail

/-- Block 195 covers tail-support indices [9875,9900) and q from 16294 to 16331. -/

def TailChunk000Sub001Block195Part000SupportExplicit : Finset ℕ :=
  ([16294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block195Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16294
    = surrogateDiagTailX0RatChunk000Sub001Block195Part000

theorem surrogateDiagonalTailChunk000Sub001Block195Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part000] using hcert

def TailChunk000Sub001Block195Part001SupportExplicit : Finset ℕ :=
  ([16295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part001 : ℚ :=
  (664661030125 : ℚ) / 72122561730481932288

def SurrogateDiagonalTailChunk000Sub001Block195Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16295
    = surrogateDiagTailX0RatChunk000Sub001Block195Part001

theorem surrogateDiagonalTailChunk000Sub001Block195Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part001] using hcert

def TailChunk000Sub001Block195Part002SupportExplicit : Finset ℕ :=
  ([16297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part002 : ℚ :=
  (129015648775 : ℚ) / 158851463311087682688

def SurrogateDiagonalTailChunk000Sub001Block195Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16297
    = surrogateDiagTailX0RatChunk000Sub001Block195Part002

theorem surrogateDiagonalTailChunk000Sub001Block195Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part002] using hcert

def TailChunk000Sub001Block195Part003SupportExplicit : Finset ℕ :=
  ([16298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part003 : ℚ :=
  (3865196917 : ℚ) / 377877558735667200

def SurrogateDiagonalTailChunk000Sub001Block195Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16298
    = surrogateDiagTailX0RatChunk000Sub001Block195Part003

theorem surrogateDiagonalTailChunk000Sub001Block195Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part003] using hcert

def TailChunk000Sub001Block195Part004SupportExplicit : Finset ℕ :=
  ([16301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block195Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16301
    = surrogateDiagTailX0RatChunk000Sub001Block195Part004

theorem surrogateDiagonalTailChunk000Sub001Block195Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part004] using hcert

def TailChunk000Sub001Block195Part005SupportExplicit : Finset ℕ :=
  ([16302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part005 : ℚ :=
  (7822374797 : ℚ) / 11611827693158400

def SurrogateDiagonalTailChunk000Sub001Block195Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16302
    = surrogateDiagTailX0RatChunk000Sub001Block195Part005

theorem surrogateDiagonalTailChunk000Sub001Block195Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part005] using hcert

def TailChunk000Sub001Block195Part006SupportExplicit : Finset ℕ :=
  ([16303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part006 : ℚ :=
  (108063425675 : ℚ) / 9081915096648646656

def SurrogateDiagonalTailChunk000Sub001Block195Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16303
    = surrogateDiagTailX0RatChunk000Sub001Block195Part006

theorem surrogateDiagonalTailChunk000Sub001Block195Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part006] using hcert

def TailChunk000Sub001Block195Part007SupportExplicit : Finset ℕ :=
  ([16305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part007 : ℚ :=
  (1698087901075 : ℚ) / 14246431946761863168

def SurrogateDiagonalTailChunk000Sub001Block195Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16305
    = surrogateDiagTailX0RatChunk000Sub001Block195Part007

theorem surrogateDiagonalTailChunk000Sub001Block195Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part007] using hcert

def TailChunk000Sub001Block195Part008SupportExplicit : Finset ℕ :=
  ([16306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part008 : ℚ :=
  (1811592197 : ℚ) / 190874115997761600

def SurrogateDiagonalTailChunk000Sub001Block195Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16306
    = surrogateDiagTailX0RatChunk000Sub001Block195Part008

theorem surrogateDiagonalTailChunk000Sub001Block195Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part008] using hcert

def TailChunk000Sub001Block195Part009SupportExplicit : Finset ℕ :=
  ([16307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part009 : ℚ :=
  (37650732175 : ℚ) / 24530102478602062848

def SurrogateDiagonalTailChunk000Sub001Block195Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16307
    = surrogateDiagTailX0RatChunk000Sub001Block195Part009

theorem surrogateDiagonalTailChunk000Sub001Block195Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part009] using hcert

def TailChunk000Sub001Block195Part010SupportExplicit : Finset ℕ :=
  ([16309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part010 : ℚ :=
  (29831375 : ℚ) / 37915511721147024

def SurrogateDiagonalTailChunk000Sub001Block195Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16309
    = surrogateDiagTailX0RatChunk000Sub001Block195Part010

theorem surrogateDiagonalTailChunk000Sub001Block195Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part010] using hcert

def TailChunk000Sub001Block195Part011SupportExplicit : Finset ℕ :=
  ([16310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part011 : ℚ :=
  (636443376025 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk000Sub001Block195Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16310
    = surrogateDiagTailX0RatChunk000Sub001Block195Part011

theorem surrogateDiagonalTailChunk000Sub001Block195Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part011] using hcert

def TailChunk000Sub001Block195Part012SupportExplicit : Finset ℕ :=
  ([16311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part012 : ℚ :=
  (115469128225 : ℚ) / 2183457038109844608

def SurrogateDiagonalTailChunk000Sub001Block195Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16311
    = surrogateDiagTailX0RatChunk000Sub001Block195Part012

theorem surrogateDiagonalTailChunk000Sub001Block195Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part012] using hcert

def TailChunk000Sub001Block195Part013SupportExplicit : Finset ℕ :=
  ([16313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part013 : ℚ :=
  (16590942403 : ℚ) / 4824803880798595200

def SurrogateDiagonalTailChunk000Sub001Block195Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16313
    = surrogateDiagTailX0RatChunk000Sub001Block195Part013

theorem surrogateDiagonalTailChunk000Sub001Block195Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part013] using hcert

def TailChunk000Sub001Block195Part014SupportExplicit : Finset ℕ :=
  ([16314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part014 : ℚ :=
  (461940332525 : ℚ) / 1091728519054922304

def SurrogateDiagonalTailChunk000Sub001Block195Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16314
    = surrogateDiagTailX0RatChunk000Sub001Block195Part014

theorem surrogateDiagonalTailChunk000Sub001Block195Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part014] using hcert

def TailChunk000Sub001Block195Part015SupportExplicit : Finset ℕ :=
  ([16315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part015 : ℚ :=
  (11762810819 : ℚ) / 691338240000000000

def SurrogateDiagonalTailChunk000Sub001Block195Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16315
    = surrogateDiagTailX0RatChunk000Sub001Block195Part015

theorem surrogateDiagonalTailChunk000Sub001Block195Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part015] using hcert

def TailChunk000Sub001Block195Part016SupportExplicit : Finset ℕ :=
  ([16318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part016 : ℚ :=
  (2938594789 : ℚ) / 393538817721139200

def SurrogateDiagonalTailChunk000Sub001Block195Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16318
    = surrogateDiagTailX0RatChunk000Sub001Block195Part016

theorem surrogateDiagonalTailChunk000Sub001Block195Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part016] using hcert

def TailChunk000Sub001Block195Part017SupportExplicit : Finset ℕ :=
  ([16319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block195Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16319
    = surrogateDiagTailX0RatChunk000Sub001Block195Part017

theorem surrogateDiagonalTailChunk000Sub001Block195Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part017] using hcert

def TailChunk000Sub001Block195Part018SupportExplicit : Finset ℕ :=
  ([16321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part018 : ℚ :=
  (117744894275 : ℚ) / 71127252813094530624

def SurrogateDiagonalTailChunk000Sub001Block195Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16321
    = surrogateDiagTailX0RatChunk000Sub001Block195Part018

theorem surrogateDiagonalTailChunk000Sub001Block195Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part018] using hcert

def TailChunk000Sub001Block195Part019SupportExplicit : Finset ℕ :=
  ([16322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block195Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16322
    = surrogateDiagTailX0RatChunk000Sub001Block195Part019

theorem surrogateDiagonalTailChunk000Sub001Block195Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part019] using hcert

def TailChunk000Sub001Block195Part020SupportExplicit : Finset ℕ :=
  ([16323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part020 : ℚ :=
  (3700450103 : ℚ) / 70076505375375360

def SurrogateDiagonalTailChunk000Sub001Block195Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16323
    = surrogateDiagTailX0RatChunk000Sub001Block195Part020

theorem surrogateDiagonalTailChunk000Sub001Block195Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part020] using hcert

def TailChunk000Sub001Block195Part021SupportExplicit : Finset ℕ :=
  ([16327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part021 : ℚ :=
  (27738754875 : ℚ) / 25553653179492666368

def SurrogateDiagonalTailChunk000Sub001Block195Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16327
    = surrogateDiagTailX0RatChunk000Sub001Block195Part021

theorem surrogateDiagonalTailChunk000Sub001Block195Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part021] using hcert

def TailChunk000Sub001Block195Part022SupportExplicit : Finset ℕ :=
  ([16329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part022 : ℚ :=
  (925792650725 : ℚ) / 17544903976189329984

def SurrogateDiagonalTailChunk000Sub001Block195Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16329
    = surrogateDiagTailX0RatChunk000Sub001Block195Part022

theorem surrogateDiagonalTailChunk000Sub001Block195Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part022] using hcert

def TailChunk000Sub001Block195Part023SupportExplicit : Finset ℕ :=
  ([16330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part023 : ℚ :=
  (22277081341 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub001Block195Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16330
    = surrogateDiagTailX0RatChunk000Sub001Block195Part023

theorem surrogateDiagonalTailChunk000Sub001Block195Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part023] using hcert

def TailChunk000Sub001Block195Part024SupportExplicit : Finset ℕ :=
  ([16331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block195Part024 : ℚ :=
  (340758424175 : ℚ) / 47919916110973953024

def SurrogateDiagonalTailChunk000Sub001Block195Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16331
    = surrogateDiagTailX0RatChunk000Sub001Block195Part024

theorem surrogateDiagonalTailChunk000Sub001Block195Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block195Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block195Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block195Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block195Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block195Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block195Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block195HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block195Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block195Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block195Part000
    + surrogateDiagTailX0RatChunk000Sub001Block195Part001
    + surrogateDiagTailX0RatChunk000Sub001Block195Part002
    + surrogateDiagTailX0RatChunk000Sub001Block195Part003
    + surrogateDiagTailX0RatChunk000Sub001Block195Part004
    + surrogateDiagTailX0RatChunk000Sub001Block195Part005
    + surrogateDiagTailX0RatChunk000Sub001Block195Part006
    + surrogateDiagTailX0RatChunk000Sub001Block195Part007
    + surrogateDiagTailX0RatChunk000Sub001Block195Part008
    + surrogateDiagTailX0RatChunk000Sub001Block195Part009

def surrogateDiagonalTailChunk000Sub001Block195MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block195Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block195Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block195Part010
    + surrogateDiagTailX0RatChunk000Sub001Block195Part011
    + surrogateDiagTailX0RatChunk000Sub001Block195Part012
    + surrogateDiagTailX0RatChunk000Sub001Block195Part013
    + surrogateDiagTailX0RatChunk000Sub001Block195Part014
    + surrogateDiagTailX0RatChunk000Sub001Block195Part015
    + surrogateDiagTailX0RatChunk000Sub001Block195Part016
    + surrogateDiagTailX0RatChunk000Sub001Block195Part017
    + surrogateDiagTailX0RatChunk000Sub001Block195Part018
    + surrogateDiagTailX0RatChunk000Sub001Block195Part019

def surrogateDiagonalTailChunk000Sub001Block195TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block195Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block195Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block195Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block195Part020
    + surrogateDiagTailX0RatChunk000Sub001Block195Part021
    + surrogateDiagTailX0RatChunk000Sub001Block195Part022
    + surrogateDiagTailX0RatChunk000Sub001Block195Part023
    + surrogateDiagTailX0RatChunk000Sub001Block195Part024

def surrogateDiagonalTailChunk000Sub001Block195Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block195HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block195MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block195TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block195 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block195Part000
    + surrogateDiagTailX0RatChunk000Sub001Block195Part001
    + surrogateDiagTailX0RatChunk000Sub001Block195Part002
    + surrogateDiagTailX0RatChunk000Sub001Block195Part003
    + surrogateDiagTailX0RatChunk000Sub001Block195Part004
    + surrogateDiagTailX0RatChunk000Sub001Block195Part005
    + surrogateDiagTailX0RatChunk000Sub001Block195Part006
    + surrogateDiagTailX0RatChunk000Sub001Block195Part007
    + surrogateDiagTailX0RatChunk000Sub001Block195Part008
    + surrogateDiagTailX0RatChunk000Sub001Block195Part009
    + surrogateDiagTailX0RatChunk000Sub001Block195Part010
    + surrogateDiagTailX0RatChunk000Sub001Block195Part011
    + surrogateDiagTailX0RatChunk000Sub001Block195Part012
    + surrogateDiagTailX0RatChunk000Sub001Block195Part013
    + surrogateDiagTailX0RatChunk000Sub001Block195Part014
    + surrogateDiagTailX0RatChunk000Sub001Block195Part015
    + surrogateDiagTailX0RatChunk000Sub001Block195Part016
    + surrogateDiagTailX0RatChunk000Sub001Block195Part017
    + surrogateDiagTailX0RatChunk000Sub001Block195Part018
    + surrogateDiagTailX0RatChunk000Sub001Block195Part019
    + surrogateDiagTailX0RatChunk000Sub001Block195Part020
    + surrogateDiagTailX0RatChunk000Sub001Block195Part021
    + surrogateDiagTailX0RatChunk000Sub001Block195Part022
    + surrogateDiagTailX0RatChunk000Sub001Block195Part023
    + surrogateDiagTailX0RatChunk000Sub001Block195Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block195_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block195Head + surrogateDiagTailX0RatChunk000Sub001Block195Mid + surrogateDiagTailX0RatChunk000Sub001Block195Tail =
      surrogateDiagTailX0RatChunk000Sub001Block195 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block195Head surrogateDiagTailX0RatChunk000Sub001Block195Mid surrogateDiagTailX0RatChunk000Sub001Block195Tail surrogateDiagTailX0RatChunk000Sub001Block195
  ring

def SurrogateDiagonalTailChunk000Sub001Block195HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block195HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block195Head

def SurrogateDiagonalTailChunk000Sub001Block195MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block195MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block195Mid

def SurrogateDiagonalTailChunk000Sub001Block195TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block195TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block195Tail

theorem surrogateDiagonalTailChunk000Sub001Block195_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block195HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block195MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block195TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block195Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block195 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block195HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block195MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block195TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block195Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block195_eq_head_add_mid_add_tail

/-- Block 196 covers tail-support indices [9900,9925) and q from 16333 to 16374. -/

def TailChunk000Sub001Block196Part000SupportExplicit : Finset ℕ :=
  ([16333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block196Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16333
    = surrogateDiagTailX0RatChunk000Sub001Block196Part000

theorem surrogateDiagonalTailChunk000Sub001Block196Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part000] using hcert

def TailChunk000Sub001Block196Part001SupportExplicit : Finset ℕ :=
  ([16334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block196Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16334
    = surrogateDiagTailX0RatChunk000Sub001Block196Part001

theorem surrogateDiagonalTailChunk000Sub001Block196Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part001] using hcert

def TailChunk000Sub001Block196Part002SupportExplicit : Finset ℕ :=
  ([16338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part002 : ℚ :=
  (897457791475 : ℚ) / 1175110604448104448

def SurrogateDiagonalTailChunk000Sub001Block196Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16338
    = surrogateDiagTailX0RatChunk000Sub001Block196Part002

theorem surrogateDiagonalTailChunk000Sub001Block196Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part002] using hcert

def TailChunk000Sub001Block196Part003SupportExplicit : Finset ℕ :=
  ([16339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block196Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16339
    = surrogateDiagTailX0RatChunk000Sub001Block196Part003

theorem surrogateDiagonalTailChunk000Sub001Block196Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part003] using hcert

def TailChunk000Sub001Block196Part004SupportExplicit : Finset ℕ :=
  ([16341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part004 : ℚ :=
  (1831166504425 : ℚ) / 25326603587277324288

def SurrogateDiagonalTailChunk000Sub001Block196Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16341
    = surrogateDiagTailX0RatChunk000Sub001Block196Part004

theorem surrogateDiagonalTailChunk000Sub001Block196Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part004] using hcert

def TailChunk000Sub001Block196Part005SupportExplicit : Finset ℕ :=
  ([16342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block196Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16342
    = surrogateDiagTailX0RatChunk000Sub001Block196Part005

theorem surrogateDiagonalTailChunk000Sub001Block196Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part005] using hcert

def TailChunk000Sub001Block196Part006SupportExplicit : Finset ℕ :=
  ([16343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part006 : ℚ :=
  (103583650075 : ℚ) / 164200759427098626048

def SurrogateDiagonalTailChunk000Sub001Block196Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16343
    = surrogateDiagTailX0RatChunk000Sub001Block196Part006

theorem surrogateDiagonalTailChunk000Sub001Block196Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part006] using hcert

def TailChunk000Sub001Block196Part007SupportExplicit : Finset ℕ :=
  ([16345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part007 : ℚ :=
  (1513859510125 : ℚ) / 39121499486362042368

def SurrogateDiagonalTailChunk000Sub001Block196Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16345
    = surrogateDiagTailX0RatChunk000Sub001Block196Part007

theorem surrogateDiagonalTailChunk000Sub001Block196Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part007] using hcert

def TailChunk000Sub001Block196Part008SupportExplicit : Finset ℕ :=
  ([16346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part008 : ℚ :=
  (464208261 : ℚ) / 14437206773315200

def SurrogateDiagonalTailChunk000Sub001Block196Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16346
    = surrogateDiagTailX0RatChunk000Sub001Block196Part008

theorem surrogateDiagonalTailChunk000Sub001Block196Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part008] using hcert

def TailChunk000Sub001Block196Part009SupportExplicit : Finset ℕ :=
  ([16347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part009 : ℚ :=
  (463917262825 : ℚ) / 8811203787736031232

def SurrogateDiagonalTailChunk000Sub001Block196Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16347
    = surrogateDiagTailX0RatChunk000Sub001Block196Part009

theorem surrogateDiagonalTailChunk000Sub001Block196Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part009] using hcert

def TailChunk000Sub001Block196Part010SupportExplicit : Finset ℕ :=
  ([16349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block196Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16349
    = surrogateDiagTailX0RatChunk000Sub001Block196Part010

theorem surrogateDiagonalTailChunk000Sub001Block196Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part010] using hcert

def TailChunk000Sub001Block196Part011SupportExplicit : Finset ℕ :=
  ([16351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part011 : ℚ :=
  (42631872125 : ℚ) / 83421224082067006464

def SurrogateDiagonalTailChunk000Sub001Block196Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16351
    = surrogateDiagTailX0RatChunk000Sub001Block196Part011

theorem surrogateDiagonalTailChunk000Sub001Block196Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part011] using hcert

def TailChunk000Sub001Block196Part012SupportExplicit : Finset ℕ :=
  ([16354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part012 : ℚ :=
  (176202106325 : ℚ) / 2853722773870608384

def SurrogateDiagonalTailChunk000Sub001Block196Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16354
    = surrogateDiagTailX0RatChunk000Sub001Block196Part012

theorem surrogateDiagonalTailChunk000Sub001Block196Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part012] using hcert

def TailChunk000Sub001Block196Part013SupportExplicit : Finset ℕ :=
  ([16355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part013 : ℚ :=
  (17834604283 : ℚ) / 975880345873766400

def SurrogateDiagonalTailChunk000Sub001Block196Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16355
    = surrogateDiagTailX0RatChunk000Sub001Block196Part013

theorem surrogateDiagonalTailChunk000Sub001Block196Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part013] using hcert

def TailChunk000Sub001Block196Part014SupportExplicit : Finset ℕ :=
  ([16357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part014 : ℚ :=
  (16679946703 : ℚ) / 4877104800330883200

def SurrogateDiagonalTailChunk000Sub001Block196Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16357
    = surrogateDiagTailX0RatChunk000Sub001Block196Part014

theorem surrogateDiagonalTailChunk000Sub001Block196Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part014] using hcert

def TailChunk000Sub001Block196Part015SupportExplicit : Finset ℕ :=
  ([16358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block196Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16358
    = surrogateDiagTailX0RatChunk000Sub001Block196Part015

theorem surrogateDiagonalTailChunk000Sub001Block196Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part015] using hcert

def TailChunk000Sub001Block196Part016SupportExplicit : Finset ℕ :=
  ([16359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part016 : ℚ :=
  (18585642193 : ℚ) / 139341932317900800

def SurrogateDiagonalTailChunk000Sub001Block196Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16359
    = surrogateDiagTailX0RatChunk000Sub001Block196Part016

theorem surrogateDiagonalTailChunk000Sub001Block196Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part016] using hcert

def TailChunk000Sub001Block196Part017SupportExplicit : Finset ℕ :=
  ([16361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block196Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16361
    = surrogateDiagTailX0RatChunk000Sub001Block196Part017

theorem surrogateDiagonalTailChunk000Sub001Block196Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part017] using hcert

def TailChunk000Sub001Block196Part018SupportExplicit : Finset ℕ :=
  ([16363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block196Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16363
    = surrogateDiagTailX0RatChunk000Sub001Block196Part018

theorem surrogateDiagonalTailChunk000Sub001Block196Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part018] using hcert

def TailChunk000Sub001Block196Part019SupportExplicit : Finset ℕ :=
  ([16365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part019 : ℚ :=
  (37170989087 : ℚ) / 289149732110745600

def SurrogateDiagonalTailChunk000Sub001Block196Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16365
    = surrogateDiagTailX0RatChunk000Sub001Block196Part019

theorem surrogateDiagonalTailChunk000Sub001Block196Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part019] using hcert

def TailChunk000Sub001Block196Part020SupportExplicit : Finset ℕ :=
  ([16367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part020 : ℚ :=
  (66526101475 : ℚ) / 21643283945020197888

def SurrogateDiagonalTailChunk000Sub001Block196Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16367
    = surrogateDiagTailX0RatChunk000Sub001Block196Part020

theorem surrogateDiagonalTailChunk000Sub001Block196Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part020] using hcert

def TailChunk000Sub001Block196Part021SupportExplicit : Finset ℕ :=
  ([16369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block196Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16369
    = surrogateDiagTailX0RatChunk000Sub001Block196Part021

theorem surrogateDiagonalTailChunk000Sub001Block196Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part021] using hcert

def TailChunk000Sub001Block196Part022SupportExplicit : Finset ℕ :=
  ([16370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part022 : ℚ :=
  (251446232975 : ℚ) / 2292820340538753024

def SurrogateDiagonalTailChunk000Sub001Block196Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16370
    = surrogateDiagTailX0RatChunk000Sub001Block196Part022

theorem surrogateDiagonalTailChunk000Sub001Block196Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part022] using hcert

def TailChunk000Sub001Block196Part023SupportExplicit : Finset ℕ :=
  ([16373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part023 : ℚ :=
  (342509324075 : ℚ) / 48414995080211801664

def SurrogateDiagonalTailChunk000Sub001Block196Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16373
    = surrogateDiagTailX0RatChunk000Sub001Block196Part023

theorem surrogateDiagonalTailChunk000Sub001Block196Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part023] using hcert

def TailChunk000Sub001Block196Part024SupportExplicit : Finset ℕ :=
  ([16374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block196Part024 : ℚ :=
  (465343401275 : ℚ) / 1107884049628545024

def SurrogateDiagonalTailChunk000Sub001Block196Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16374
    = surrogateDiagTailX0RatChunk000Sub001Block196Part024

theorem surrogateDiagonalTailChunk000Sub001Block196Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block196Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block196Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block196Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block196Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block196Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block196Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block196HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block196Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block196Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block196Part000
    + surrogateDiagTailX0RatChunk000Sub001Block196Part001
    + surrogateDiagTailX0RatChunk000Sub001Block196Part002
    + surrogateDiagTailX0RatChunk000Sub001Block196Part003
    + surrogateDiagTailX0RatChunk000Sub001Block196Part004
    + surrogateDiagTailX0RatChunk000Sub001Block196Part005
    + surrogateDiagTailX0RatChunk000Sub001Block196Part006
    + surrogateDiagTailX0RatChunk000Sub001Block196Part007
    + surrogateDiagTailX0RatChunk000Sub001Block196Part008
    + surrogateDiagTailX0RatChunk000Sub001Block196Part009

def surrogateDiagonalTailChunk000Sub001Block196MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block196Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block196Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block196Part010
    + surrogateDiagTailX0RatChunk000Sub001Block196Part011
    + surrogateDiagTailX0RatChunk000Sub001Block196Part012
    + surrogateDiagTailX0RatChunk000Sub001Block196Part013
    + surrogateDiagTailX0RatChunk000Sub001Block196Part014
    + surrogateDiagTailX0RatChunk000Sub001Block196Part015
    + surrogateDiagTailX0RatChunk000Sub001Block196Part016
    + surrogateDiagTailX0RatChunk000Sub001Block196Part017
    + surrogateDiagTailX0RatChunk000Sub001Block196Part018
    + surrogateDiagTailX0RatChunk000Sub001Block196Part019

def surrogateDiagonalTailChunk000Sub001Block196TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block196Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block196Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block196Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block196Part020
    + surrogateDiagTailX0RatChunk000Sub001Block196Part021
    + surrogateDiagTailX0RatChunk000Sub001Block196Part022
    + surrogateDiagTailX0RatChunk000Sub001Block196Part023
    + surrogateDiagTailX0RatChunk000Sub001Block196Part024

def surrogateDiagonalTailChunk000Sub001Block196Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block196HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block196MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block196TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block196 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block196Part000
    + surrogateDiagTailX0RatChunk000Sub001Block196Part001
    + surrogateDiagTailX0RatChunk000Sub001Block196Part002
    + surrogateDiagTailX0RatChunk000Sub001Block196Part003
    + surrogateDiagTailX0RatChunk000Sub001Block196Part004
    + surrogateDiagTailX0RatChunk000Sub001Block196Part005
    + surrogateDiagTailX0RatChunk000Sub001Block196Part006
    + surrogateDiagTailX0RatChunk000Sub001Block196Part007
    + surrogateDiagTailX0RatChunk000Sub001Block196Part008
    + surrogateDiagTailX0RatChunk000Sub001Block196Part009
    + surrogateDiagTailX0RatChunk000Sub001Block196Part010
    + surrogateDiagTailX0RatChunk000Sub001Block196Part011
    + surrogateDiagTailX0RatChunk000Sub001Block196Part012
    + surrogateDiagTailX0RatChunk000Sub001Block196Part013
    + surrogateDiagTailX0RatChunk000Sub001Block196Part014
    + surrogateDiagTailX0RatChunk000Sub001Block196Part015
    + surrogateDiagTailX0RatChunk000Sub001Block196Part016
    + surrogateDiagTailX0RatChunk000Sub001Block196Part017
    + surrogateDiagTailX0RatChunk000Sub001Block196Part018
    + surrogateDiagTailX0RatChunk000Sub001Block196Part019
    + surrogateDiagTailX0RatChunk000Sub001Block196Part020
    + surrogateDiagTailX0RatChunk000Sub001Block196Part021
    + surrogateDiagTailX0RatChunk000Sub001Block196Part022
    + surrogateDiagTailX0RatChunk000Sub001Block196Part023
    + surrogateDiagTailX0RatChunk000Sub001Block196Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block196_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block196Head + surrogateDiagTailX0RatChunk000Sub001Block196Mid + surrogateDiagTailX0RatChunk000Sub001Block196Tail =
      surrogateDiagTailX0RatChunk000Sub001Block196 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block196Head surrogateDiagTailX0RatChunk000Sub001Block196Mid surrogateDiagTailX0RatChunk000Sub001Block196Tail surrogateDiagTailX0RatChunk000Sub001Block196
  ring

def SurrogateDiagonalTailChunk000Sub001Block196HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block196HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block196Head

def SurrogateDiagonalTailChunk000Sub001Block196MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block196MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block196Mid

def SurrogateDiagonalTailChunk000Sub001Block196TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block196TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block196Tail

theorem surrogateDiagonalTailChunk000Sub001Block196_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block196HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block196MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block196TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block196Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block196 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block196HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block196MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block196TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block196Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block196_eq_head_add_mid_add_tail

/-- Block 197 covers tail-support indices [9925,9950) and q from 16377 to 16417. -/

def TailChunk000Sub001Block197Part000SupportExplicit : Finset ℕ :=
  ([16377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part000 : ℚ :=
  (231594722075 : ℚ) / 3957955582815277056

def SurrogateDiagonalTailChunk000Sub001Block197Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16377
    = surrogateDiagTailX0RatChunk000Sub001Block197Part000

theorem surrogateDiagonalTailChunk000Sub001Block197Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part000] using hcert

def TailChunk000Sub001Block197Part001SupportExplicit : Finset ℕ :=
  ([16378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part001 : ℚ :=
  (353295989 : ℚ) / 23930922145783680

def SurrogateDiagonalTailChunk000Sub001Block197Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16378
    = surrogateDiagTailX0RatChunk000Sub001Block197Part001

theorem surrogateDiagonalTailChunk000Sub001Block197Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part001] using hcert

def TailChunk000Sub001Block197Part002SupportExplicit : Finset ℕ :=
  ([16379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part002 : ℚ :=
  (22253237509 : ℚ) / 4903414139466547200

def SurrogateDiagonalTailChunk000Sub001Block197Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16379
    = surrogateDiagTailX0RatChunk000Sub001Block197Part002

theorem surrogateDiagonalTailChunk000Sub001Block197Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part002] using hcert

def TailChunk000Sub001Block197Part003SupportExplicit : Finset ℕ :=
  ([16381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block197Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16381
    = surrogateDiagTailX0RatChunk000Sub001Block197Part003

theorem surrogateDiagonalTailChunk000Sub001Block197Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part003] using hcert

def TailChunk000Sub001Block197Part004SupportExplicit : Finset ℕ :=
  ([16382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block197Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16382
    = surrogateDiagTailX0RatChunk000Sub001Block197Part004

theorem surrogateDiagonalTailChunk000Sub001Block197Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part004] using hcert

def TailChunk000Sub001Block197Part005SupportExplicit : Finset ℕ :=
  ([16383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part005 : ℚ :=
  (1853024011225 : ℚ) / 31378066826881517568

def SurrogateDiagonalTailChunk000Sub001Block197Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16383
    = surrogateDiagTailX0RatChunk000Sub001Block197Part005

theorem surrogateDiagonalTailChunk000Sub001Block197Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part005] using hcert

def TailChunk000Sub001Block197Part006SupportExplicit : Finset ℕ :=
  ([16385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part006 : ℚ :=
  (233855850075 : ℚ) / 10318576537208619008

def SurrogateDiagonalTailChunk000Sub001Block197Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16385
    = surrogateDiagTailX0RatChunk000Sub001Block197Part006

theorem surrogateDiagonalTailChunk000Sub001Block197Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part006] using hcert

def TailChunk000Sub001Block197Part007SupportExplicit : Finset ℕ :=
  ([16386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part007 : ℚ :=
  (266532211 : ℚ) / 1269870344084160

def SurrogateDiagonalTailChunk000Sub001Block197Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16386
    = surrogateDiagTailX0RatChunk000Sub001Block197Part007

theorem surrogateDiagonalTailChunk000Sub001Block197Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part007] using hcert

def TailChunk000Sub001Block197Part008SupportExplicit : Finset ℕ :=
  ([16387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part008 : ℚ :=
  (13723758287 : ℚ) / 1943234828579865600

def SurrogateDiagonalTailChunk000Sub001Block197Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16387
    = surrogateDiagTailX0RatChunk000Sub001Block197Part008

theorem surrogateDiagonalTailChunk000Sub001Block197Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part008] using hcert

def TailChunk000Sub001Block197Part009SupportExplicit : Finset ℕ :=
  ([16390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part009 : ℚ :=
  (1569919329 : ℚ) / 8189972019937280

def SurrogateDiagonalTailChunk000Sub001Block197Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16390
    = surrogateDiagTailX0RatChunk000Sub001Block197Part009

theorem surrogateDiagonalTailChunk000Sub001Block197Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part009] using hcert

def TailChunk000Sub001Block197Part010SupportExplicit : Finset ℕ :=
  ([16391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part010 : ℚ :=
  (145284201625 : ℚ) / 160297201104018720768

def SurrogateDiagonalTailChunk000Sub001Block197Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16391
    = surrogateDiagTailX0RatChunk000Sub001Block197Part010

theorem surrogateDiagonalTailChunk000Sub001Block197Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part010] using hcert

def TailChunk000Sub001Block197Part011SupportExplicit : Finset ℕ :=
  ([16394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part011 : ℚ :=
  (136989520963 : ℚ) / 242904353572483200

def SurrogateDiagonalTailChunk000Sub001Block197Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16394
    = surrogateDiagTailX0RatChunk000Sub001Block197Part011

theorem surrogateDiagonalTailChunk000Sub001Block197Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part011] using hcert

def TailChunk000Sub001Block197Part012SupportExplicit : Finset ℕ :=
  ([16395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part012 : ℚ :=
  (485026149175 : ℚ) / 3640972250558103552

def SurrogateDiagonalTailChunk000Sub001Block197Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16395
    = surrogateDiagTailX0RatChunk000Sub001Block197Part012

theorem surrogateDiagonalTailChunk000Sub001Block197Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part012] using hcert

def TailChunk000Sub001Block197Part013SupportExplicit : Finset ℕ :=
  ([16397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part013 : ℚ :=
  (141992612075 : ℚ) / 72462939412466424384

def SurrogateDiagonalTailChunk000Sub001Block197Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16397
    = surrogateDiagTailX0RatChunk000Sub001Block197Part013

theorem surrogateDiagonalTailChunk000Sub001Block197Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part013] using hcert

def TailChunk000Sub001Block197Part014SupportExplicit : Finset ℕ :=
  ([16401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part014 : ℚ :=
  (488181791 : ℚ) / 3556935244800000

def SurrogateDiagonalTailChunk000Sub001Block197Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16401
    = surrogateDiagTailX0RatChunk000Sub001Block197Part014

theorem surrogateDiagonalTailChunk000Sub001Block197Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part014] using hcert

def TailChunk000Sub001Block197Part015SupportExplicit : Finset ℕ :=
  ([16402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part015 : ℚ :=
  (8362781675 : ℚ) / 21116352806982848

def SurrogateDiagonalTailChunk000Sub001Block197Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16402
    = surrogateDiagTailX0RatChunk000Sub001Block197Part015

theorem surrogateDiagonalTailChunk000Sub001Block197Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part015] using hcert

def TailChunk000Sub001Block197Part016SupportExplicit : Finset ℕ :=
  ([16403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part016 : ℚ :=
  (30004381075 : ℚ) / 41050189856774656512

def SurrogateDiagonalTailChunk000Sub001Block197Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16403
    = surrogateDiagTailX0RatChunk000Sub001Block197Part016

theorem surrogateDiagonalTailChunk000Sub001Block197Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part016] using hcert

def TailChunk000Sub001Block197Part017SupportExplicit : Finset ℕ :=
  ([16405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part017 : ℚ :=
  (105036363575 : ℚ) / 7126260315058077696

def SurrogateDiagonalTailChunk000Sub001Block197Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16405
    = surrogateDiagTailX0RatChunk000Sub001Block197Part017

theorem surrogateDiagonalTailChunk000Sub001Block197Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part017] using hcert

def TailChunk000Sub001Block197Part018SupportExplicit : Finset ℕ :=
  ([16406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part018 : ℚ :=
  (75002272001 : ℚ) / 163359364987929600

def SurrogateDiagonalTailChunk000Sub001Block197Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16406
    = surrogateDiagTailX0RatChunk000Sub001Block197Part018

theorem surrogateDiagonalTailChunk000Sub001Block197Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part018] using hcert

def TailChunk000Sub001Block197Part019SupportExplicit : Finset ℕ :=
  ([16409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part019 : ℚ :=
  (691609351 : ℚ) / 1114499242093363200

def SurrogateDiagonalTailChunk000Sub001Block197Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16409
    = surrogateDiagTailX0RatChunk000Sub001Block197Part019

theorem surrogateDiagonalTailChunk000Sub001Block197Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part019] using hcert

def TailChunk000Sub001Block197Part020SupportExplicit : Finset ℕ :=
  ([16410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part020 : ℚ :=
  (1854216275 : ℚ) / 972481904529408

def SurrogateDiagonalTailChunk000Sub001Block197Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16410
    = surrogateDiagTailX0RatChunk000Sub001Block197Part020

theorem surrogateDiagonalTailChunk000Sub001Block197Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part020] using hcert

def TailChunk000Sub001Block197Part021SupportExplicit : Finset ℕ :=
  ([16411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block197Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16411
    = surrogateDiagTailX0RatChunk000Sub001Block197Part021

theorem surrogateDiagonalTailChunk000Sub001Block197Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part021] using hcert

def TailChunk000Sub001Block197Part022SupportExplicit : Finset ℕ :=
  ([16413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part022 : ℚ :=
  (7482725203 : ℚ) / 143270289417817920

def SurrogateDiagonalTailChunk000Sub001Block197Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16413
    = surrogateDiagTailX0RatChunk000Sub001Block197Part022

theorem surrogateDiagonalTailChunk000Sub001Block197Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part022] using hcert

def TailChunk000Sub001Block197Part023SupportExplicit : Finset ℕ :=
  ([16414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part023 : ℚ :=
  (73898626325 : ℚ) / 179995504186616832

def SurrogateDiagonalTailChunk000Sub001Block197Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16414
    = surrogateDiagTailX0RatChunk000Sub001Block197Part023

theorem surrogateDiagonalTailChunk000Sub001Block197Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part023] using hcert

def TailChunk000Sub001Block197Part024SupportExplicit : Finset ℕ :=
  ([16417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block197Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block197Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16417
    = surrogateDiagTailX0RatChunk000Sub001Block197Part024

theorem surrogateDiagonalTailChunk000Sub001Block197Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block197Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block197Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block197Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block197Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block197Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block197Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block197HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block197Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block197Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block197Part000
    + surrogateDiagTailX0RatChunk000Sub001Block197Part001
    + surrogateDiagTailX0RatChunk000Sub001Block197Part002
    + surrogateDiagTailX0RatChunk000Sub001Block197Part003
    + surrogateDiagTailX0RatChunk000Sub001Block197Part004
    + surrogateDiagTailX0RatChunk000Sub001Block197Part005
    + surrogateDiagTailX0RatChunk000Sub001Block197Part006
    + surrogateDiagTailX0RatChunk000Sub001Block197Part007
    + surrogateDiagTailX0RatChunk000Sub001Block197Part008
    + surrogateDiagTailX0RatChunk000Sub001Block197Part009

def surrogateDiagonalTailChunk000Sub001Block197MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block197Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block197Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block197Part010
    + surrogateDiagTailX0RatChunk000Sub001Block197Part011
    + surrogateDiagTailX0RatChunk000Sub001Block197Part012
    + surrogateDiagTailX0RatChunk000Sub001Block197Part013
    + surrogateDiagTailX0RatChunk000Sub001Block197Part014
    + surrogateDiagTailX0RatChunk000Sub001Block197Part015
    + surrogateDiagTailX0RatChunk000Sub001Block197Part016
    + surrogateDiagTailX0RatChunk000Sub001Block197Part017
    + surrogateDiagTailX0RatChunk000Sub001Block197Part018
    + surrogateDiagTailX0RatChunk000Sub001Block197Part019

def surrogateDiagonalTailChunk000Sub001Block197TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block197Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block197Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block197Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block197Part020
    + surrogateDiagTailX0RatChunk000Sub001Block197Part021
    + surrogateDiagTailX0RatChunk000Sub001Block197Part022
    + surrogateDiagTailX0RatChunk000Sub001Block197Part023
    + surrogateDiagTailX0RatChunk000Sub001Block197Part024

def surrogateDiagonalTailChunk000Sub001Block197Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block197HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block197MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block197TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block197 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block197Part000
    + surrogateDiagTailX0RatChunk000Sub001Block197Part001
    + surrogateDiagTailX0RatChunk000Sub001Block197Part002
    + surrogateDiagTailX0RatChunk000Sub001Block197Part003
    + surrogateDiagTailX0RatChunk000Sub001Block197Part004
    + surrogateDiagTailX0RatChunk000Sub001Block197Part005
    + surrogateDiagTailX0RatChunk000Sub001Block197Part006
    + surrogateDiagTailX0RatChunk000Sub001Block197Part007
    + surrogateDiagTailX0RatChunk000Sub001Block197Part008
    + surrogateDiagTailX0RatChunk000Sub001Block197Part009
    + surrogateDiagTailX0RatChunk000Sub001Block197Part010
    + surrogateDiagTailX0RatChunk000Sub001Block197Part011
    + surrogateDiagTailX0RatChunk000Sub001Block197Part012
    + surrogateDiagTailX0RatChunk000Sub001Block197Part013
    + surrogateDiagTailX0RatChunk000Sub001Block197Part014
    + surrogateDiagTailX0RatChunk000Sub001Block197Part015
    + surrogateDiagTailX0RatChunk000Sub001Block197Part016
    + surrogateDiagTailX0RatChunk000Sub001Block197Part017
    + surrogateDiagTailX0RatChunk000Sub001Block197Part018
    + surrogateDiagTailX0RatChunk000Sub001Block197Part019
    + surrogateDiagTailX0RatChunk000Sub001Block197Part020
    + surrogateDiagTailX0RatChunk000Sub001Block197Part021
    + surrogateDiagTailX0RatChunk000Sub001Block197Part022
    + surrogateDiagTailX0RatChunk000Sub001Block197Part023
    + surrogateDiagTailX0RatChunk000Sub001Block197Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block197_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block197Head + surrogateDiagTailX0RatChunk000Sub001Block197Mid + surrogateDiagTailX0RatChunk000Sub001Block197Tail =
      surrogateDiagTailX0RatChunk000Sub001Block197 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block197Head surrogateDiagTailX0RatChunk000Sub001Block197Mid surrogateDiagTailX0RatChunk000Sub001Block197Tail surrogateDiagTailX0RatChunk000Sub001Block197
  ring

def SurrogateDiagonalTailChunk000Sub001Block197HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block197HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block197Head

def SurrogateDiagonalTailChunk000Sub001Block197MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block197MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block197Mid

def SurrogateDiagonalTailChunk000Sub001Block197TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block197TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block197Tail

theorem surrogateDiagonalTailChunk000Sub001Block197_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block197HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block197MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block197TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block197Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block197 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block197HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block197MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block197TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block197Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block197_eq_head_add_mid_add_tail

/-- Block 198 covers tail-support indices [9950,9975) and q from 16418 to 16455. -/

def TailChunk000Sub001Block198Part000SupportExplicit : Finset ℕ :=
  ([16418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part000 : ℚ :=
  (1052932515625 : ℚ) / 2837371869000179712

def SurrogateDiagonalTailChunk000Sub001Block198Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16418
    = surrogateDiagTailX0RatChunk000Sub001Block198Part000

theorem surrogateDiagonalTailChunk000Sub001Block198Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part000] using hcert

def TailChunk000Sub001Block198Part001SupportExplicit : Finset ℕ :=
  ([16419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part001 : ℚ :=
  (8216265389 : ℚ) / 114732503256268800

def SurrogateDiagonalTailChunk000Sub001Block198Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16419
    = surrogateDiagTailX0RatChunk000Sub001Block198Part001

theorem surrogateDiagonalTailChunk000Sub001Block198Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part001] using hcert

def TailChunk000Sub001Block198Part002SupportExplicit : Finset ℕ :=
  ([16421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block198Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16421
    = surrogateDiagTailX0RatChunk000Sub001Block198Part002

theorem surrogateDiagonalTailChunk000Sub001Block198Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part002] using hcert

def TailChunk000Sub001Block198Part003SupportExplicit : Finset ℕ :=
  ([16422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part003 : ℚ :=
  (1677262452625 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub001Block198Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16422
    = surrogateDiagTailX0RatChunk000Sub001Block198Part003

theorem surrogateDiagonalTailChunk000Sub001Block198Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part003] using hcert

def TailChunk000Sub001Block198Part004SupportExplicit : Finset ℕ :=
  ([16423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part004 : ℚ :=
  (7457455287 : ℚ) / 1652117334760806400

def SurrogateDiagonalTailChunk000Sub001Block198Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16423
    = surrogateDiagTailX0RatChunk000Sub001Block198Part004

theorem surrogateDiagonalTailChunk000Sub001Block198Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part004] using hcert

def TailChunk000Sub001Block198Part005SupportExplicit : Finset ℕ :=
  ([16426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part005 : ℚ :=
  (162008179147 : ℚ) / 405600438282883200

def SurrogateDiagonalTailChunk000Sub001Block198Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16426
    = surrogateDiagTailX0RatChunk000Sub001Block198Part005

theorem surrogateDiagonalTailChunk000Sub001Block198Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part005] using hcert

def TailChunk000Sub001Block198Part006SupportExplicit : Finset ℕ :=
  ([16427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block198Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16427
    = surrogateDiagTailX0RatChunk000Sub001Block198Part006

theorem surrogateDiagonalTailChunk000Sub001Block198Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part006] using hcert

def TailChunk000Sub001Block198Part007SupportExplicit : Finset ℕ :=
  ([16429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part007 : ℚ :=
  (344850855875 : ℚ) / 49081055738320724544

def SurrogateDiagonalTailChunk000Sub001Block198Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16429
    = surrogateDiagTailX0RatChunk000Sub001Block198Part007

theorem surrogateDiagonalTailChunk000Sub001Block198Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part007] using hcert

def TailChunk000Sub001Block198Part008SupportExplicit : Finset ℕ :=
  ([16430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part008 : ℚ :=
  (22691958329 : ℚ) / 30328798421975040

def SurrogateDiagonalTailChunk000Sub001Block198Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16430
    = surrogateDiagTailX0RatChunk000Sub001Block198Part008

theorem surrogateDiagonalTailChunk000Sub001Block198Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part008] using hcert

def TailChunk000Sub001Block198Part009SupportExplicit : Finset ℕ :=
  ([16431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part009 : ℚ :=
  (234348256325 : ℚ) / 4496872895759083776

def SurrogateDiagonalTailChunk000Sub001Block198Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16431
    = surrogateDiagTailX0RatChunk000Sub001Block198Part009

theorem surrogateDiagonalTailChunk000Sub001Block198Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part009] using hcert

def TailChunk000Sub001Block198Part010SupportExplicit : Finset ℕ :=
  ([16433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block198Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16433
    = surrogateDiagTailX0RatChunk000Sub001Block198Part010

theorem surrogateDiagonalTailChunk000Sub001Block198Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part010] using hcert

def TailChunk000Sub001Block198Part011SupportExplicit : Finset ℕ :=
  ([16435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part011 : ℚ :=
  (811884971125 : ℚ) / 58812634265477971968

def SurrogateDiagonalTailChunk000Sub001Block198Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16435
    = surrogateDiagTailX0RatChunk000Sub001Block198Part011

theorem surrogateDiagonalTailChunk000Sub001Block198Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part011] using hcert

def TailChunk000Sub001Block198Part012SupportExplicit : Finset ℕ :=
  ([16437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part012 : ℚ :=
  (938077650275 : ℚ) / 18013784276013033024

def SurrogateDiagonalTailChunk000Sub001Block198Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16437
    = surrogateDiagTailX0RatChunk000Sub001Block198Part012

theorem surrogateDiagonalTailChunk000Sub001Block198Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part012] using hcert

def TailChunk000Sub001Block198Part013SupportExplicit : Finset ℕ :=
  ([16438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part013 : ℚ :=
  (1055499390625 : ℚ) / 2851224507096854322

def SurrogateDiagonalTailChunk000Sub001Block198Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16438
    = surrogateDiagTailX0RatChunk000Sub001Block198Part013

theorem surrogateDiagonalTailChunk000Sub001Block198Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part013] using hcert

def TailChunk000Sub001Block198Part014SupportExplicit : Finset ℕ :=
  ([16439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part014 : ℚ :=
  (296376594025 : ℚ) / 142697148638833410048

def SurrogateDiagonalTailChunk000Sub001Block198Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16439
    = surrogateDiagTailX0RatChunk000Sub001Block198Part014

theorem surrogateDiagonalTailChunk000Sub001Block198Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part014] using hcert

def TailChunk000Sub001Block198Part015SupportExplicit : Finset ℕ :=
  ([16441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part015 : ℚ :=
  (379180809 : ℚ) / 436994048000000000

def SurrogateDiagonalTailChunk000Sub001Block198Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16441
    = surrogateDiagTailX0RatChunk000Sub001Block198Part015

theorem surrogateDiagonalTailChunk000Sub001Block198Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part015] using hcert

def TailChunk000Sub001Block198Part016SupportExplicit : Finset ℕ :=
  ([16442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part016 : ℚ :=
  (1689621025 : ℚ) / 4566401776295712

def SurrogateDiagonalTailChunk000Sub001Block198Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16442
    = surrogateDiagTailX0RatChunk000Sub001Block198Part016

theorem surrogateDiagonalTailChunk000Sub001Block198Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part016] using hcert

def TailChunk000Sub001Block198Part017SupportExplicit : Finset ℕ :=
  ([16445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part017 : ℚ :=
  (14753513627 : ℚ) / 414592334718566400

def SurrogateDiagonalTailChunk000Sub001Block198Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16445
    = surrogateDiagTailX0RatChunk000Sub001Block198Part017

theorem surrogateDiagonalTailChunk000Sub001Block198Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part017] using hcert

def TailChunk000Sub001Block198Part018SupportExplicit : Finset ℕ :=
  ([16446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part018 : ℚ :=
  (46942504979 : ℚ) / 45100264457241600

def SurrogateDiagonalTailChunk000Sub001Block198Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16446
    = surrogateDiagTailX0RatChunk000Sub001Block198Part018

theorem surrogateDiagonalTailChunk000Sub001Block198Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part018] using hcert

def TailChunk000Sub001Block198Part019SupportExplicit : Finset ℕ :=
  ([16447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block198Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16447
    = surrogateDiagTailX0RatChunk000Sub001Block198Part019

theorem surrogateDiagonalTailChunk000Sub001Block198Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part019] using hcert

def TailChunk000Sub001Block198Part020SupportExplicit : Finset ℕ :=
  ([16449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part020 : ℚ :=
  (939447650225 : ℚ) / 18066456124730723904

def SurrogateDiagonalTailChunk000Sub001Block198Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16449
    = surrogateDiagTailX0RatChunk000Sub001Block198Part020

theorem surrogateDiagonalTailChunk000Sub001Block198Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part020] using hcert

def TailChunk000Sub001Block198Part021SupportExplicit : Finset ℕ :=
  ([16451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block198Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16451
    = surrogateDiagTailX0RatChunk000Sub001Block198Part021

theorem surrogateDiagonalTailChunk000Sub001Block198Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part021] using hcert

def TailChunk000Sub001Block198Part022SupportExplicit : Finset ℕ :=
  ([16453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block198Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16453
    = surrogateDiagTailX0RatChunk000Sub001Block198Part022

theorem surrogateDiagonalTailChunk000Sub001Block198Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part022] using hcert

def TailChunk000Sub001Block198Part023SupportExplicit : Finset ℕ :=
  ([16454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part023 : ℚ :=
  (3913708405375 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk000Sub001Block198Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16454
    = surrogateDiagTailX0RatChunk000Sub001Block198Part023

theorem surrogateDiagonalTailChunk000Sub001Block198Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part023] using hcert

def TailChunk000Sub001Block198Part024SupportExplicit : Finset ℕ :=
  ([16455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block198Part024 : ℚ :=
  (488581376275 : ℚ) / 3694613664337231872

def SurrogateDiagonalTailChunk000Sub001Block198Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16455
    = surrogateDiagTailX0RatChunk000Sub001Block198Part024

theorem surrogateDiagonalTailChunk000Sub001Block198Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block198Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block198Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block198Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block198Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block198Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block198Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block198HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block198Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block198Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block198Part000
    + surrogateDiagTailX0RatChunk000Sub001Block198Part001
    + surrogateDiagTailX0RatChunk000Sub001Block198Part002
    + surrogateDiagTailX0RatChunk000Sub001Block198Part003
    + surrogateDiagTailX0RatChunk000Sub001Block198Part004
    + surrogateDiagTailX0RatChunk000Sub001Block198Part005
    + surrogateDiagTailX0RatChunk000Sub001Block198Part006
    + surrogateDiagTailX0RatChunk000Sub001Block198Part007
    + surrogateDiagTailX0RatChunk000Sub001Block198Part008
    + surrogateDiagTailX0RatChunk000Sub001Block198Part009

def surrogateDiagonalTailChunk000Sub001Block198MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block198Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block198Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block198Part010
    + surrogateDiagTailX0RatChunk000Sub001Block198Part011
    + surrogateDiagTailX0RatChunk000Sub001Block198Part012
    + surrogateDiagTailX0RatChunk000Sub001Block198Part013
    + surrogateDiagTailX0RatChunk000Sub001Block198Part014
    + surrogateDiagTailX0RatChunk000Sub001Block198Part015
    + surrogateDiagTailX0RatChunk000Sub001Block198Part016
    + surrogateDiagTailX0RatChunk000Sub001Block198Part017
    + surrogateDiagTailX0RatChunk000Sub001Block198Part018
    + surrogateDiagTailX0RatChunk000Sub001Block198Part019

def surrogateDiagonalTailChunk000Sub001Block198TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block198Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block198Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block198Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block198Part020
    + surrogateDiagTailX0RatChunk000Sub001Block198Part021
    + surrogateDiagTailX0RatChunk000Sub001Block198Part022
    + surrogateDiagTailX0RatChunk000Sub001Block198Part023
    + surrogateDiagTailX0RatChunk000Sub001Block198Part024

def surrogateDiagonalTailChunk000Sub001Block198Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block198HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block198MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block198TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block198 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block198Part000
    + surrogateDiagTailX0RatChunk000Sub001Block198Part001
    + surrogateDiagTailX0RatChunk000Sub001Block198Part002
    + surrogateDiagTailX0RatChunk000Sub001Block198Part003
    + surrogateDiagTailX0RatChunk000Sub001Block198Part004
    + surrogateDiagTailX0RatChunk000Sub001Block198Part005
    + surrogateDiagTailX0RatChunk000Sub001Block198Part006
    + surrogateDiagTailX0RatChunk000Sub001Block198Part007
    + surrogateDiagTailX0RatChunk000Sub001Block198Part008
    + surrogateDiagTailX0RatChunk000Sub001Block198Part009
    + surrogateDiagTailX0RatChunk000Sub001Block198Part010
    + surrogateDiagTailX0RatChunk000Sub001Block198Part011
    + surrogateDiagTailX0RatChunk000Sub001Block198Part012
    + surrogateDiagTailX0RatChunk000Sub001Block198Part013
    + surrogateDiagTailX0RatChunk000Sub001Block198Part014
    + surrogateDiagTailX0RatChunk000Sub001Block198Part015
    + surrogateDiagTailX0RatChunk000Sub001Block198Part016
    + surrogateDiagTailX0RatChunk000Sub001Block198Part017
    + surrogateDiagTailX0RatChunk000Sub001Block198Part018
    + surrogateDiagTailX0RatChunk000Sub001Block198Part019
    + surrogateDiagTailX0RatChunk000Sub001Block198Part020
    + surrogateDiagTailX0RatChunk000Sub001Block198Part021
    + surrogateDiagTailX0RatChunk000Sub001Block198Part022
    + surrogateDiagTailX0RatChunk000Sub001Block198Part023
    + surrogateDiagTailX0RatChunk000Sub001Block198Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block198_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block198Head + surrogateDiagTailX0RatChunk000Sub001Block198Mid + surrogateDiagTailX0RatChunk000Sub001Block198Tail =
      surrogateDiagTailX0RatChunk000Sub001Block198 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block198Head surrogateDiagTailX0RatChunk000Sub001Block198Mid surrogateDiagTailX0RatChunk000Sub001Block198Tail surrogateDiagTailX0RatChunk000Sub001Block198
  ring

def SurrogateDiagonalTailChunk000Sub001Block198HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block198HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block198Head

def SurrogateDiagonalTailChunk000Sub001Block198MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block198MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block198Mid

def SurrogateDiagonalTailChunk000Sub001Block198TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block198TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block198Tail

theorem surrogateDiagonalTailChunk000Sub001Block198_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block198HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block198MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block198TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block198Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block198 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block198HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block198MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block198TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block198Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block198_eq_head_add_mid_add_tail

/-- Block 199 covers tail-support indices [9975,10000) and q from 16457 to 16495. -/

def TailChunk000Sub001Block199Part000SupportExplicit : Finset ℕ :=
  ([16457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part000 : ℚ :=
  (13840984847 : ℚ) / 1976666059161000000

def SurrogateDiagonalTailChunk000Sub001Block199Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16457
    = surrogateDiagTailX0RatChunk000Sub001Block199Part000

theorem surrogateDiagonalTailChunk000Sub001Block199Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part000] using hcert

def TailChunk000Sub001Block199Part001SupportExplicit : Finset ℕ :=
  ([16458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part001 : ℚ :=
  (16886370197 : ℚ) / 12907406616330240

def SurrogateDiagonalTailChunk000Sub001Block199Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16458
    = surrogateDiagTailX0RatChunk000Sub001Block199Part001

theorem surrogateDiagonalTailChunk000Sub001Block199Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part001] using hcert

def TailChunk000Sub001Block199Part002SupportExplicit : Finset ℕ :=
  ([16459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part002 : ℚ :=
  (127923079 : ℚ) / 275554114202880000

def SurrogateDiagonalTailChunk000Sub001Block199Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16459
    = surrogateDiagTailX0RatChunk000Sub001Block199Part002

theorem surrogateDiagonalTailChunk000Sub001Block199Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part002] using hcert

def TailChunk000Sub001Block199Part003SupportExplicit : Finset ℕ :=
  ([16462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part003 : ℚ :=
  (1693734025 : ℚ) / 4588663291558482

def SurrogateDiagonalTailChunk000Sub001Block199Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16462
    = surrogateDiagTailX0RatChunk000Sub001Block199Part003

theorem surrogateDiagonalTailChunk000Sub001Block199Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part003] using hcert

def TailChunk000Sub001Block199Part004SupportExplicit : Finset ℕ :=
  ([16463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part004 : ℚ :=
  (82096351 : ℚ) / 172221321376800000

def SurrogateDiagonalTailChunk000Sub001Block199Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16463
    = surrogateDiagTailX0RatChunk000Sub001Block199Part004

theorem surrogateDiagonalTailChunk000Sub001Block199Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part004] using hcert

def TailChunk000Sub001Block199Part005SupportExplicit : Finset ℕ :=
  ([16465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part005 : ℚ :=
  (351389504425 : ℚ) / 16119349973857861632

def SurrogateDiagonalTailChunk000Sub001Block199Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16465
    = surrogateDiagTailX0RatChunk000Sub001Block199Part005

theorem surrogateDiagonalTailChunk000Sub001Block199Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part005] using hcert

def TailChunk000Sub001Block199Part006SupportExplicit : Finset ℕ :=
  ([16466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part006 : ℚ :=
  (1059098265625 : ℚ) / 2870703339862159872

def SurrogateDiagonalTailChunk000Sub001Block199Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16466
    = surrogateDiagTailX0RatChunk000Sub001Block199Part006

theorem surrogateDiagonalTailChunk000Sub001Block199Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part006] using hcert

def TailChunk000Sub001Block199Part007SupportExplicit : Finset ℕ :=
  ([16467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part007 : ℚ :=
  (3669943 : ℚ) / 49204787212800

def SurrogateDiagonalTailChunk000Sub001Block199Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16467
    = surrogateDiagTailX0RatChunk000Sub001Block199Part007

theorem surrogateDiagonalTailChunk000Sub001Block199Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part007] using hcert

def TailChunk000Sub001Block199Part008SupportExplicit : Finset ℕ :=
  ([16469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part008 : ℚ :=
  (131479664875 : ℚ) / 165682817816386002048

def SurrogateDiagonalTailChunk000Sub001Block199Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16469
    = surrogateDiagTailX0RatChunk000Sub001Block199Part008

theorem surrogateDiagonalTailChunk000Sub001Block199Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part008] using hcert

def TailChunk000Sub001Block199Part009SupportExplicit : Finset ℕ :=
  ([16471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part009 : ℚ :=
  (37670114893 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk000Sub001Block199Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16471
    = surrogateDiagTailX0RatChunk000Sub001Block199Part009

theorem surrogateDiagonalTailChunk000Sub001Block199Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part009] using hcert

def TailChunk000Sub001Block199Part010SupportExplicit : Finset ℕ :=
  ([16474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part010 : ℚ :=
  (1060127640625 : ℚ) / 2876287006270539552

def SurrogateDiagonalTailChunk000Sub001Block199Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16474
    = surrogateDiagTailX0RatChunk000Sub001Block199Part010

theorem surrogateDiagonalTailChunk000Sub001Block199Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part010] using hcert

def TailChunk000Sub001Block199Part011SupportExplicit : Finset ℕ :=
  ([16477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block199Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16477
    = surrogateDiagTailX0RatChunk000Sub001Block199Part011

theorem surrogateDiagonalTailChunk000Sub001Block199Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part011] using hcert

def TailChunk000Sub001Block199Part012SupportExplicit : Finset ℕ :=
  ([16478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part012 : ℚ :=
  (15025056857 : ℚ) / 20456217177350400

def SurrogateDiagonalTailChunk000Sub001Block199Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16478
    = surrogateDiagTailX0RatChunk000Sub001Block199Part012

theorem surrogateDiagonalTailChunk000Sub001Block199Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part012] using hcert

def TailChunk000Sub001Block199Part013SupportExplicit : Finset ℕ :=
  ([16481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block199Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16481
    = surrogateDiagTailX0RatChunk000Sub001Block199Part013

theorem surrogateDiagonalTailChunk000Sub001Block199Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part013] using hcert

def TailChunk000Sub001Block199Part014SupportExplicit : Finset ℕ :=
  ([16482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part014 : ℚ :=
  (72260881507 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk000Sub001Block199Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16482
    = surrogateDiagTailX0RatChunk000Sub001Block199Part014

theorem surrogateDiagonalTailChunk000Sub001Block199Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part014] using hcert

def TailChunk000Sub001Block199Part015SupportExplicit : Finset ℕ :=
  ([16483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part015 : ℚ :=
  (299118309 : ℚ) / 450252093741332480

def SurrogateDiagonalTailChunk000Sub001Block199Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16483
    = surrogateDiagTailX0RatChunk000Sub001Block199Part015

theorem surrogateDiagonalTailChunk000Sub001Block199Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part015] using hcert

def TailChunk000Sub001Block199Part016SupportExplicit : Finset ℕ :=
  ([16485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part016 : ℚ :=
  (15337531175 : ℚ) / 67189953427144704

def SurrogateDiagonalTailChunk000Sub001Block199Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16485
    = surrogateDiagTailX0RatChunk000Sub001Block199Part016

theorem surrogateDiagonalTailChunk000Sub001Block199Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part016] using hcert

def TailChunk000Sub001Block199Part017SupportExplicit : Finset ℕ :=
  ([16486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part017 : ℚ :=
  (1061672640625 : ℚ) / 2884677773539479762

def SurrogateDiagonalTailChunk000Sub001Block199Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16486
    = surrogateDiagTailX0RatChunk000Sub001Block199Part017

theorem surrogateDiagonalTailChunk000Sub001Block199Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part017] using hcert

def TailChunk000Sub001Block199Part018SupportExplicit : Finset ℕ :=
  ([16487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block199Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16487
    = surrogateDiagTailX0RatChunk000Sub001Block199Part018

theorem surrogateDiagonalTailChunk000Sub001Block199Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part018] using hcert

def TailChunk000Sub001Block199Part019SupportExplicit : Finset ℕ :=
  ([16489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part019 : ℚ :=
  (2421199861 : ℚ) / 719508723258057600

def SurrogateDiagonalTailChunk000Sub001Block199Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16489
    = surrogateDiagTailX0RatChunk000Sub001Block199Part019

theorem surrogateDiagonalTailChunk000Sub001Block199Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part019] using hcert

def TailChunk000Sub001Block199Part020SupportExplicit : Finset ℕ :=
  ([16490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part020 : ℚ :=
  (929672846375 : ℚ) / 1187710052509679616

def SurrogateDiagonalTailChunk000Sub001Block199Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16490
    = surrogateDiagTailX0RatChunk000Sub001Block199Part020

theorem surrogateDiagonalTailChunk000Sub001Block199Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part020] using hcert

def TailChunk000Sub001Block199Part021SupportExplicit : Finset ℕ :=
  ([16491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part021 : ℚ :=
  (233590041725 : ℚ) / 3758853556209244416

def SurrogateDiagonalTailChunk000Sub001Block199Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16491
    = surrogateDiagTailX0RatChunk000Sub001Block199Part021

theorem surrogateDiagonalTailChunk000Sub001Block199Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part021] using hcert

def TailChunk000Sub001Block199Part022SupportExplicit : Finset ℕ :=
  ([16493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block199Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16493
    = surrogateDiagTailX0RatChunk000Sub001Block199Part022

theorem surrogateDiagonalTailChunk000Sub001Block199Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part022] using hcert

def TailChunk000Sub001Block199Part023SupportExplicit : Finset ℕ :=
  ([16494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part023 : ℚ :=
  (1180423721975 : ℚ) / 1140732354090968064

def SurrogateDiagonalTailChunk000Sub001Block199Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16494
    = surrogateDiagTailX0RatChunk000Sub001Block199Part023

theorem surrogateDiagonalTailChunk000Sub001Block199Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part023] using hcert

def TailChunk000Sub001Block199Part024SupportExplicit : Finset ℕ :=
  ([16495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block199Part024 : ℚ :=
  (1360578715225 : ℚ) / 75730256785578805248

def SurrogateDiagonalTailChunk000Sub001Block199Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 16495
    = surrogateDiagTailX0RatChunk000Sub001Block199Part024

theorem surrogateDiagonalTailChunk000Sub001Block199Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block199Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block199Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block199Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block199Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block199Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block199Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block199HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block199Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block199Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block199Part000
    + surrogateDiagTailX0RatChunk000Sub001Block199Part001
    + surrogateDiagTailX0RatChunk000Sub001Block199Part002
    + surrogateDiagTailX0RatChunk000Sub001Block199Part003
    + surrogateDiagTailX0RatChunk000Sub001Block199Part004
    + surrogateDiagTailX0RatChunk000Sub001Block199Part005
    + surrogateDiagTailX0RatChunk000Sub001Block199Part006
    + surrogateDiagTailX0RatChunk000Sub001Block199Part007
    + surrogateDiagTailX0RatChunk000Sub001Block199Part008
    + surrogateDiagTailX0RatChunk000Sub001Block199Part009

def surrogateDiagonalTailChunk000Sub001Block199MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block199Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block199Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block199Part010
    + surrogateDiagTailX0RatChunk000Sub001Block199Part011
    + surrogateDiagTailX0RatChunk000Sub001Block199Part012
    + surrogateDiagTailX0RatChunk000Sub001Block199Part013
    + surrogateDiagTailX0RatChunk000Sub001Block199Part014
    + surrogateDiagTailX0RatChunk000Sub001Block199Part015
    + surrogateDiagTailX0RatChunk000Sub001Block199Part016
    + surrogateDiagTailX0RatChunk000Sub001Block199Part017
    + surrogateDiagTailX0RatChunk000Sub001Block199Part018
    + surrogateDiagTailX0RatChunk000Sub001Block199Part019

def surrogateDiagonalTailChunk000Sub001Block199TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block199Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block199Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block199Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block199Part020
    + surrogateDiagTailX0RatChunk000Sub001Block199Part021
    + surrogateDiagTailX0RatChunk000Sub001Block199Part022
    + surrogateDiagTailX0RatChunk000Sub001Block199Part023
    + surrogateDiagTailX0RatChunk000Sub001Block199Part024

def surrogateDiagonalTailChunk000Sub001Block199Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block199HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block199MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block199TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block199 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block199Part000
    + surrogateDiagTailX0RatChunk000Sub001Block199Part001
    + surrogateDiagTailX0RatChunk000Sub001Block199Part002
    + surrogateDiagTailX0RatChunk000Sub001Block199Part003
    + surrogateDiagTailX0RatChunk000Sub001Block199Part004
    + surrogateDiagTailX0RatChunk000Sub001Block199Part005
    + surrogateDiagTailX0RatChunk000Sub001Block199Part006
    + surrogateDiagTailX0RatChunk000Sub001Block199Part007
    + surrogateDiagTailX0RatChunk000Sub001Block199Part008
    + surrogateDiagTailX0RatChunk000Sub001Block199Part009
    + surrogateDiagTailX0RatChunk000Sub001Block199Part010
    + surrogateDiagTailX0RatChunk000Sub001Block199Part011
    + surrogateDiagTailX0RatChunk000Sub001Block199Part012
    + surrogateDiagTailX0RatChunk000Sub001Block199Part013
    + surrogateDiagTailX0RatChunk000Sub001Block199Part014
    + surrogateDiagTailX0RatChunk000Sub001Block199Part015
    + surrogateDiagTailX0RatChunk000Sub001Block199Part016
    + surrogateDiagTailX0RatChunk000Sub001Block199Part017
    + surrogateDiagTailX0RatChunk000Sub001Block199Part018
    + surrogateDiagTailX0RatChunk000Sub001Block199Part019
    + surrogateDiagTailX0RatChunk000Sub001Block199Part020
    + surrogateDiagTailX0RatChunk000Sub001Block199Part021
    + surrogateDiagTailX0RatChunk000Sub001Block199Part022
    + surrogateDiagTailX0RatChunk000Sub001Block199Part023
    + surrogateDiagTailX0RatChunk000Sub001Block199Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block199_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block199Head + surrogateDiagTailX0RatChunk000Sub001Block199Mid + surrogateDiagTailX0RatChunk000Sub001Block199Tail =
      surrogateDiagTailX0RatChunk000Sub001Block199 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block199Head surrogateDiagTailX0RatChunk000Sub001Block199Mid surrogateDiagTailX0RatChunk000Sub001Block199Tail surrogateDiagTailX0RatChunk000Sub001Block199
  ring

def SurrogateDiagonalTailChunk000Sub001Block199HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block199HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block199Head

def SurrogateDiagonalTailChunk000Sub001Block199MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block199MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block199Mid

def SurrogateDiagonalTailChunk000Sub001Block199TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block199TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block199Tail

theorem surrogateDiagonalTailChunk000Sub001Block199_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block199HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block199MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block199TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block199Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block199 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block199HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block199MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block199TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block199Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block199_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
