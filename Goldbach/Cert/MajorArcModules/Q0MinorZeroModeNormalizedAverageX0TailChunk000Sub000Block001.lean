import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [1,2). -/

/- Block 001 covers tail-support indices [25,50) and q from 91 to 131. -/

def TailChunk000Sub000Block001Part000SupportExplicit : Finset ℕ :=
  ([91] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part000 : ℚ :=
  (6517525 : ℚ) / 19443888

def SurrogateDiagonalTailChunk000Sub000Block001Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 91
    = surrogateDiagTailX0RatChunk000Sub000Block001Part000

theorem surrogateDiagonalTailChunk000Sub000Block001Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part000] using hcert

def TailChunk000Sub000Block001Part001SupportExplicit : Finset ℕ :=
  ([93] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part001 : ℚ :=
  (751097209 : ℚ) / 1296259200

def SurrogateDiagonalTailChunk000Sub000Block001Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 93
    = surrogateDiagTailX0RatChunk000Sub000Block001Part001

theorem surrogateDiagonalTailChunk000Sub000Block001Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part001] using hcert

def TailChunk000Sub000Block001Part002SupportExplicit : Finset ℕ :=
  ([94] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part002 : ℚ :=
  (14327297875 : ℚ) / 11195878728

def SurrogateDiagonalTailChunk000Sub000Block001Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 94
    = surrogateDiagTailX0RatChunk000Sub000Block001Part002

theorem surrogateDiagonalTailChunk000Sub000Block001Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part002] using hcert

def TailChunk000Sub000Block001Part003SupportExplicit : Finset ℕ :=
  ([95] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part003 : ℚ :=
  (5577744325 : ℚ) / 16799519232

def SurrogateDiagonalTailChunk000Sub000Block001Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 95
    = surrogateDiagTailX0RatChunk000Sub000Block001Part003

theorem surrogateDiagonalTailChunk000Sub000Block001Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part003] using hcert

def TailChunk000Sub000Block001Part004SupportExplicit : Finset ℕ :=
  ([97] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part004 : ℚ :=
  (15133670825 : ℚ) / 106189553664

def SurrogateDiagonalTailChunk000Sub000Block001Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 97
    = surrogateDiagTailX0RatChunk000Sub000Block001Part004

theorem surrogateDiagonalTailChunk000Sub000Block001Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part004] using hcert

def TailChunk000Sub000Block001Part005SupportExplicit : Finset ℕ :=
  ([101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part005 : ℚ :=
  (50505151 : ℚ) / 400080000

def SurrogateDiagonalTailChunk000Sub000Block001Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 101
    = surrogateDiagTailX0RatChunk000Sub000Block001Part005

theorem surrogateDiagonalTailChunk000Sub000Block001Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part005] using hcert

def TailChunk000Sub000Block001Part006SupportExplicit : Finset ℕ :=
  ([102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part006 : ℚ :=
  (1999275 : ℚ) / 524288

def SurrogateDiagonalTailChunk000Sub000Block001Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 102
    = surrogateDiagTailX0RatChunk000Sub000Block001Part006

theorem surrogateDiagonalTailChunk000Sub000Block001Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part006] using hcert

def TailChunk000Sub000Block001Part007SupportExplicit : Finset ℕ :=
  ([103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part007 : ℚ :=
  (437886475 : ℚ) / 3759196689

def SurrogateDiagonalTailChunk000Sub000Block001Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 103
    = surrogateDiagTailX0RatChunk000Sub000Block001Part007

theorem surrogateDiagonalTailChunk000Sub000Block001Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part007] using hcert

def TailChunk000Sub000Block001Part008SupportExplicit : Finset ℕ :=
  ([105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part008 : ℚ :=
  (208945075 : ℚ) / 184356864

def SurrogateDiagonalTailChunk000Sub000Block001Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 105
    = surrogateDiagTailX0RatChunk000Sub000Block001Part008

theorem surrogateDiagonalTailChunk000Sub000Block001Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part008] using hcert

def TailChunk000Sub000Block001Part009SupportExplicit : Finset ℕ :=
  ([106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part009 : ℚ :=
  (16364882875 : ℚ) / 18282695808

def SurrogateDiagonalTailChunk000Sub000Block001Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 106
    = surrogateDiagTailX0RatChunk000Sub000Block001Part009

theorem surrogateDiagonalTailChunk000Sub000Block001Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part009] using hcert

def TailChunk000Sub000Block001Part010SupportExplicit : Finset ℕ :=
  ([107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part010 : ℚ :=
  (33322028275 : ℚ) / 315682363848

def SurrogateDiagonalTailChunk000Sub000Block001Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 107
    = surrogateDiagTailX0RatChunk000Sub000Block001Part010

theorem surrogateDiagonalTailChunk000Sub000Block001Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part010] using hcert

def TailChunk000Sub000Block001Part011SupportExplicit : Finset ℕ :=
  ([109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part011 : ℚ :=
  (33850454125 : ℚ) / 340190264448

def SurrogateDiagonalTailChunk000Sub000Block001Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 109
    = surrogateDiagTailX0RatChunk000Sub000Block001Part011

theorem surrogateDiagonalTailChunk000Sub000Block001Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part011] using hcert

def TailChunk000Sub000Block001Part012SupportExplicit : Finset ℕ :=
  ([110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part012 : ℚ :=
  (50059009 : ℚ) / 25605120

def SurrogateDiagonalTailChunk000Sub000Block001Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 110
    = surrogateDiagTailX0RatChunk000Sub000Block001Part012

theorem surrogateDiagonalTailChunk000Sub000Block001Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part012] using hcert

def TailChunk000Sub000Block001Part013SupportExplicit : Finset ℕ :=
  ([111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part013 : ℚ :=
  (749275 : ℚ) / 2239488

def SurrogateDiagonalTailChunk000Sub000Block001Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 111
    = surrogateDiagTailX0RatChunk000Sub000Block001Part013

theorem surrogateDiagonalTailChunk000Sub000Block001Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part013] using hcert

def TailChunk000Sub000Block001Part014SupportExplicit : Finset ℕ :=
  ([113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part014 : ℚ :=
  (847542375 : ℚ) / 9368059904

def SurrogateDiagonalTailChunk000Sub000Block001Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 113
    = surrogateDiagTailX0RatChunk000Sub000Block001Part014

theorem surrogateDiagonalTailChunk000Sub000Block001Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part014] using hcert

def TailChunk000Sub000Block001Part015SupportExplicit : Finset ℕ :=
  ([114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part015 : ℚ :=
  (11266185775 : ℚ) / 4199879808

def SurrogateDiagonalTailChunk000Sub000Block001Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 114
    = surrogateDiagTailX0RatChunk000Sub000Block001Part015

theorem surrogateDiagonalTailChunk000Sub000Block001Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part015] using hcert

def TailChunk000Sub000Block001Part016SupportExplicit : Finset ℕ :=
  ([115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part016 : ℚ :=
  (27730929775 : ℚ) / 149953824768

def SurrogateDiagonalTailChunk000Sub000Block001Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 115
    = surrogateDiagTailX0RatChunk000Sub000Block001Part016

theorem surrogateDiagonalTailChunk000Sub000Block001Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part016] using hcert

def TailChunk000Sub000Block001Part017SupportExplicit : Finset ℕ :=
  ([118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part017 : ℚ :=
  (9091066625 : ℚ) / 14148449124

def SurrogateDiagonalTailChunk000Sub000Block001Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 118
    = surrogateDiagTailX0RatChunk000Sub000Block001Part017

theorem surrogateDiagonalTailChunk000Sub000Block001Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part017] using hcert

def TailChunk000Sub000Block001Part018SupportExplicit : Finset ℕ :=
  ([119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part018 : ℚ :=
  (3332687225 : ℚ) / 23597678592

def SurrogateDiagonalTailChunk000Sub000Block001Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 119
    = surrogateDiagTailX0RatChunk000Sub000Block001Part018

theorem surrogateDiagonalTailChunk000Sub000Block001Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part018] using hcert

def TailChunk000Sub000Block001Part019SupportExplicit : Finset ℕ :=
  ([122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part019 : ℚ :=
  (750447559 : ℚ) / 1296259200

def SurrogateDiagonalTailChunk000Sub000Block001Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 122
    = surrogateDiagTailX0RatChunk000Sub000Block001Part019

theorem surrogateDiagonalTailChunk000Sub000Block001Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part019] using hcert

def TailChunk000Sub000Block001Part020SupportExplicit : Finset ℕ :=
  ([123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part020 : ℚ :=
  (496297559 : ℚ) / 2048409600

def SurrogateDiagonalTailChunk000Sub000Block001Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 123
    = surrogateDiagTailX0RatChunk000Sub000Block001Part020

theorem surrogateDiagonalTailChunk000Sub000Block001Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part020] using hcert

def TailChunk000Sub000Block001Part021SupportExplicit : Finset ℕ :=
  ([127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part021 : ℚ :=
  (4335071975 : ℚ) / 70027162632

def SurrogateDiagonalTailChunk000Sub000Block001Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 127
    = surrogateDiagTailX0RatChunk000Sub000Block001Part021

theorem surrogateDiagonalTailChunk000Sub000Block001Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part021] using hcert

def TailChunk000Sub000Block001Part022SupportExplicit : Finset ℕ :=
  ([129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part022 : ℚ :=
  (220075 : ℚ) / 1037232

def SurrogateDiagonalTailChunk000Sub000Block001Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 129
    = surrogateDiagTailX0RatChunk000Sub000Block001Part022

theorem surrogateDiagonalTailChunk000Sub000Block001Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part022] using hcert

def TailChunk000Sub000Block001Part023SupportExplicit : Finset ℕ :=
  ([130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part023 : ℚ :=
  (7508876375 : ℚ) / 6636847104

def SurrogateDiagonalTailChunk000Sub000Block001Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 130
    = surrogateDiagTailX0RatChunk000Sub000Block001Part023

theorem surrogateDiagonalTailChunk000Sub000Block001Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part023] using hcert

def TailChunk000Sub000Block001Part024SupportExplicit : Finset ℕ :=
  ([131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block001Part024 : ℚ :=
  (1618230817 : ℚ) / 28566712200

def SurrogateDiagonalTailChunk000Sub000Block001Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 131
    = surrogateDiagTailX0RatChunk000Sub000Block001Part024

theorem surrogateDiagonalTailChunk000Sub000Block001Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block001Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block001Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block001Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block001Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block001Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block001Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block001HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block001Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block001Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block001Part000
    + surrogateDiagTailX0RatChunk000Sub000Block001Part001
    + surrogateDiagTailX0RatChunk000Sub000Block001Part002
    + surrogateDiagTailX0RatChunk000Sub000Block001Part003
    + surrogateDiagTailX0RatChunk000Sub000Block001Part004
    + surrogateDiagTailX0RatChunk000Sub000Block001Part005
    + surrogateDiagTailX0RatChunk000Sub000Block001Part006
    + surrogateDiagTailX0RatChunk000Sub000Block001Part007
    + surrogateDiagTailX0RatChunk000Sub000Block001Part008
    + surrogateDiagTailX0RatChunk000Sub000Block001Part009

def surrogateDiagonalTailChunk000Sub000Block001MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block001Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block001Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block001Part010
    + surrogateDiagTailX0RatChunk000Sub000Block001Part011
    + surrogateDiagTailX0RatChunk000Sub000Block001Part012
    + surrogateDiagTailX0RatChunk000Sub000Block001Part013
    + surrogateDiagTailX0RatChunk000Sub000Block001Part014
    + surrogateDiagTailX0RatChunk000Sub000Block001Part015
    + surrogateDiagTailX0RatChunk000Sub000Block001Part016
    + surrogateDiagTailX0RatChunk000Sub000Block001Part017
    + surrogateDiagTailX0RatChunk000Sub000Block001Part018
    + surrogateDiagTailX0RatChunk000Sub000Block001Part019

def surrogateDiagonalTailChunk000Sub000Block001TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block001Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block001Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block001Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block001Part020
    + surrogateDiagTailX0RatChunk000Sub000Block001Part021
    + surrogateDiagTailX0RatChunk000Sub000Block001Part022
    + surrogateDiagTailX0RatChunk000Sub000Block001Part023
    + surrogateDiagTailX0RatChunk000Sub000Block001Part024

def surrogateDiagonalTailChunk000Sub000Block001Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block001HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block001MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block001TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block001 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block001Part000
    + surrogateDiagTailX0RatChunk000Sub000Block001Part001
    + surrogateDiagTailX0RatChunk000Sub000Block001Part002
    + surrogateDiagTailX0RatChunk000Sub000Block001Part003
    + surrogateDiagTailX0RatChunk000Sub000Block001Part004
    + surrogateDiagTailX0RatChunk000Sub000Block001Part005
    + surrogateDiagTailX0RatChunk000Sub000Block001Part006
    + surrogateDiagTailX0RatChunk000Sub000Block001Part007
    + surrogateDiagTailX0RatChunk000Sub000Block001Part008
    + surrogateDiagTailX0RatChunk000Sub000Block001Part009
    + surrogateDiagTailX0RatChunk000Sub000Block001Part010
    + surrogateDiagTailX0RatChunk000Sub000Block001Part011
    + surrogateDiagTailX0RatChunk000Sub000Block001Part012
    + surrogateDiagTailX0RatChunk000Sub000Block001Part013
    + surrogateDiagTailX0RatChunk000Sub000Block001Part014
    + surrogateDiagTailX0RatChunk000Sub000Block001Part015
    + surrogateDiagTailX0RatChunk000Sub000Block001Part016
    + surrogateDiagTailX0RatChunk000Sub000Block001Part017
    + surrogateDiagTailX0RatChunk000Sub000Block001Part018
    + surrogateDiagTailX0RatChunk000Sub000Block001Part019
    + surrogateDiagTailX0RatChunk000Sub000Block001Part020
    + surrogateDiagTailX0RatChunk000Sub000Block001Part021
    + surrogateDiagTailX0RatChunk000Sub000Block001Part022
    + surrogateDiagTailX0RatChunk000Sub000Block001Part023
    + surrogateDiagTailX0RatChunk000Sub000Block001Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block001_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block001Head + surrogateDiagTailX0RatChunk000Sub000Block001Mid + surrogateDiagTailX0RatChunk000Sub000Block001Tail =
      surrogateDiagTailX0RatChunk000Sub000Block001 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block001Head surrogateDiagTailX0RatChunk000Sub000Block001Mid surrogateDiagTailX0RatChunk000Sub000Block001Tail surrogateDiagTailX0RatChunk000Sub000Block001
  ring

def SurrogateDiagonalTailChunk000Sub000Block001HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block001HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block001Head

def SurrogateDiagonalTailChunk000Sub000Block001MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block001MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block001Mid

def SurrogateDiagonalTailChunk000Sub000Block001TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block001TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block001Tail

theorem surrogateDiagonalTailChunk000Sub000Block001_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block001HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block001MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block001TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block001Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block001 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block001HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block001MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block001TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block001Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block001_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
