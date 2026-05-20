import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [147,148). -/

/- Block 147 covers tail-support indices [3675,3700) and q from 6097 to 6134. -/

def TailChunk000Sub000Block147Part000SupportExplicit : Finset ℕ :=
  ([6097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part000 : ℚ :=
  (684522775 : ℚ) / 2623592118140928

def SurrogateDiagonalTailChunk000Sub000Block147Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6097
    = surrogateDiagTailX0RatChunk000Sub000Block147Part000

theorem surrogateDiagonalTailChunk000Sub000Block147Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part000] using hcert

def TailChunk000Sub000Block147Part001SupportExplicit : Finset ℕ :=
  ([6098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part001 : ℚ :=
  (1161817714975 : ℚ) / 215817525905246208

def SurrogateDiagonalTailChunk000Sub000Block147Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6098
    = surrogateDiagTailX0RatChunk000Sub000Block147Part001

theorem surrogateDiagonalTailChunk000Sub000Block147Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part001] using hcert

def TailChunk000Sub000Block147Part002SupportExplicit : Finset ℕ :=
  ([6099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part002 : ℚ :=
  (479699562925 : ℚ) / 176741716412307456

def SurrogateDiagonalTailChunk000Sub000Block147Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6099
    = surrogateDiagTailX0RatChunk000Sub000Block147Part002

theorem surrogateDiagonalTailChunk000Sub000Block147Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part002] using hcert

def TailChunk000Sub000Block147Part003SupportExplicit : Finset ℕ :=
  ([6101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part003 : ℚ :=
  (37222201 : ℚ) / 55394440672800

def SurrogateDiagonalTailChunk000Sub000Block147Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6101
    = surrogateDiagTailX0RatChunk000Sub000Block147Part003

theorem surrogateDiagonalTailChunk000Sub000Block147Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part003] using hcert

def TailChunk000Sub000Block147Part004SupportExplicit : Finset ℕ :=
  ([6103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part004 : ℚ :=
  (720051997575 : ℚ) / 897258624241893376

def SurrogateDiagonalTailChunk000Sub000Block147Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6103
    = surrogateDiagTailX0RatChunk000Sub000Block147Part004

theorem surrogateDiagonalTailChunk000Sub000Block147Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part004] using hcert

def TailChunk000Sub000Block147Part005SupportExplicit : Finset ℕ :=
  ([6105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part005 : ℚ :=
  (8208113981 : ℚ) / 1376216615485440

def SurrogateDiagonalTailChunk000Sub000Block147Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6105
    = surrogateDiagTailX0RatChunk000Sub000Block147Part005

theorem surrogateDiagonalTailChunk000Sub000Block147Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part005] using hcert

def TailChunk000Sub000Block147Part006SupportExplicit : Finset ℕ :=
  ([6106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part006 : ℚ :=
  (318417803 : ℚ) / 53376259517280

def SurrogateDiagonalTailChunk000Sub000Block147Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6106
    = surrogateDiagTailX0RatChunk000Sub000Block147Part006

theorem surrogateDiagonalTailChunk000Sub000Block147Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part006] using hcert

def TailChunk000Sub000Block147Part007SupportExplicit : Finset ℕ :=
  ([6107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part007 : ℚ :=
  (11141264021 : ℚ) / 14945352664838400

def SurrogateDiagonalTailChunk000Sub000Block147Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6107
    = surrogateDiagTailX0RatChunk000Sub000Block147Part007

theorem surrogateDiagonalTailChunk000Sub000Block147Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part007] using hcert

def TailChunk000Sub000Block147Part008SupportExplicit : Finset ℕ :=
  ([6109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part008 : ℚ :=
  (89936635957 : ℚ) / 122849580299059200

def SurrogateDiagonalTailChunk000Sub000Block147Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6109
    = surrogateDiagTailX0RatChunk000Sub000Block147Part008

theorem surrogateDiagonalTailChunk000Sub000Block147Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part008] using hcert

def TailChunk000Sub000Block147Part009SupportExplicit : Finset ℕ :=
  ([6110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part009 : ℚ :=
  (2144320925 : ℚ) / 161501037428736

def SurrogateDiagonalTailChunk000Sub000Block147Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6110
    = surrogateDiagTailX0RatChunk000Sub000Block147Part009

theorem surrogateDiagonalTailChunk000Sub000Block147Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part009] using hcert

def TailChunk000Sub000Block147Part010SupportExplicit : Finset ℕ :=
  ([6113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part010 : ℚ :=
  (583887015625 : ℚ) / 872369051187412992

def SurrogateDiagonalTailChunk000Sub000Block147Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6113
    = surrogateDiagTailX0RatChunk000Sub000Block147Part010

theorem surrogateDiagonalTailChunk000Sub000Block147Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part010] using hcert

def TailChunk000Sub000Block147Part011SupportExplicit : Finset ℕ :=
  ([6114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part011 : ℚ :=
  (713226827425 : ℚ) / 42967289058503808

def SurrogateDiagonalTailChunk000Sub000Block147Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6114
    = surrogateDiagTailX0RatChunk000Sub000Block147Part011

theorem surrogateDiagonalTailChunk000Sub000Block147Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part011] using hcert

def TailChunk000Sub000Block147Part012SupportExplicit : Finset ℕ :=
  ([6115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part012 : ℚ :=
  (443715223225 : ℚ) / 356854893452308992

def SurrogateDiagonalTailChunk000Sub000Block147Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6115
    = surrogateDiagTailX0RatChunk000Sub000Block147Part012

theorem surrogateDiagonalTailChunk000Sub000Block147Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part012] using hcert

def TailChunk000Sub000Block147Part013SupportExplicit : Finset ℕ :=
  ([6117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part013 : ℚ :=
  (324695952175 : ℚ) / 172545472805482272

def SurrogateDiagonalTailChunk000Sub000Block147Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6117
    = surrogateDiagTailX0RatChunk000Sub000Block147Part013

theorem surrogateDiagonalTailChunk000Sub000Block147Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part013] using hcert

def TailChunk000Sub000Block147Part014SupportExplicit : Finset ℕ :=
  ([6118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part014 : ℚ :=
  (431287396025 : ℚ) / 39845805294265344

def SurrogateDiagonalTailChunk000Sub000Block147Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6118
    = surrogateDiagTailX0RatChunk000Sub000Block147Part014

theorem surrogateDiagonalTailChunk000Sub000Block147Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part014] using hcert

def TailChunk000Sub000Block147Part015SupportExplicit : Finset ℕ :=
  ([6119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part015 : ℚ :=
  (9926246497 : ℚ) / 13284757924300800

def SurrogateDiagonalTailChunk000Sub000Block147Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6119
    = surrogateDiagTailX0RatChunk000Sub000Block147Part015

theorem surrogateDiagonalTailChunk000Sub000Block147Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part015] using hcert

def TailChunk000Sub000Block147Part016SupportExplicit : Finset ℕ :=
  ([6121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part016 : ℚ :=
  (936666025 : ℚ) / 1403112645775872

def SurrogateDiagonalTailChunk000Sub000Block147Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6121
    = surrogateDiagTailX0RatChunk000Sub000Block147Part016

theorem surrogateDiagonalTailChunk000Sub000Block147Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part016] using hcert

def TailChunk000Sub000Block147Part017SupportExplicit : Finset ℕ :=
  ([6122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part017 : ℚ :=
  (234243025 : ℚ) / 87694540360992

def SurrogateDiagonalTailChunk000Sub000Block147Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6122
    = surrogateDiagTailX0RatChunk000Sub000Block147Part017

theorem surrogateDiagonalTailChunk000Sub000Block147Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part017] using hcert

def TailChunk000Sub000Block147Part018SupportExplicit : Finset ℕ :=
  ([6123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part018 : ℚ :=
  (156845042275 : ℚ) / 54591837159555072

def SurrogateDiagonalTailChunk000Sub000Block147Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6123
    = surrogateDiagTailX0RatChunk000Sub000Block147Part018

theorem surrogateDiagonalTailChunk000Sub000Block147Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part018] using hcert

def TailChunk000Sub000Block147Part019SupportExplicit : Finset ℕ :=
  ([6126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part019 : ℚ :=
  (4167013343 : ℚ) / 346447566858240

def SurrogateDiagonalTailChunk000Sub000Block147Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6126
    = surrogateDiagTailX0RatChunk000Sub000Block147Part019

theorem surrogateDiagonalTailChunk000Sub000Block147Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part019] using hcert

def TailChunk000Sub000Block147Part020SupportExplicit : Finset ℕ :=
  ([6127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part020 : ℚ :=
  (27869222421 : ℚ) / 31861393169766400

def SurrogateDiagonalTailChunk000Sub000Block147Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6127
    = surrogateDiagTailX0RatChunk000Sub000Block147Part020

theorem surrogateDiagonalTailChunk000Sub000Block147Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part020] using hcert

def TailChunk000Sub000Block147Part021SupportExplicit : Finset ℕ :=
  ([6130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part021 : ℚ :=
  (134930508925 : ℚ) / 22449802332413952

def SurrogateDiagonalTailChunk000Sub000Block147Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6130
    = surrogateDiagTailX0RatChunk000Sub000Block147Part021

theorem surrogateDiagonalTailChunk000Sub000Block147Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part021] using hcert

def TailChunk000Sub000Block147Part022SupportExplicit : Finset ℕ :=
  ([6131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part022 : ℚ :=
  (939729025 : ℚ) / 1412305818292722

def SurrogateDiagonalTailChunk000Sub000Block147Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6131
    = surrogateDiagTailX0RatChunk000Sub000Block147Part022

theorem surrogateDiagonalTailChunk000Sub000Block147Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part022] using hcert

def TailChunk000Sub000Block147Part023SupportExplicit : Finset ℕ :=
  ([6133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part023 : ℚ :=
  (587713890625 : ℚ) / 883843662653213472

def SurrogateDiagonalTailChunk000Sub000Block147Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6133
    = surrogateDiagTailX0RatChunk000Sub000Block147Part023

theorem surrogateDiagonalTailChunk000Sub000Block147Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part023] using hcert

def TailChunk000Sub000Block147Part024SupportExplicit : Finset ℕ :=
  ([6134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block147Part024 : ℚ :=
  (146976390625 : ℚ) / 55240228915825842

def SurrogateDiagonalTailChunk000Sub000Block147Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6134
    = surrogateDiagTailX0RatChunk000Sub000Block147Part024

theorem surrogateDiagonalTailChunk000Sub000Block147Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block147Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block147Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block147Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block147Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block147Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block147Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block147HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block147Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block147Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block147Part000
    + surrogateDiagTailX0RatChunk000Sub000Block147Part001
    + surrogateDiagTailX0RatChunk000Sub000Block147Part002
    + surrogateDiagTailX0RatChunk000Sub000Block147Part003
    + surrogateDiagTailX0RatChunk000Sub000Block147Part004
    + surrogateDiagTailX0RatChunk000Sub000Block147Part005
    + surrogateDiagTailX0RatChunk000Sub000Block147Part006
    + surrogateDiagTailX0RatChunk000Sub000Block147Part007
    + surrogateDiagTailX0RatChunk000Sub000Block147Part008
    + surrogateDiagTailX0RatChunk000Sub000Block147Part009

def surrogateDiagonalTailChunk000Sub000Block147MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block147Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block147Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block147Part010
    + surrogateDiagTailX0RatChunk000Sub000Block147Part011
    + surrogateDiagTailX0RatChunk000Sub000Block147Part012
    + surrogateDiagTailX0RatChunk000Sub000Block147Part013
    + surrogateDiagTailX0RatChunk000Sub000Block147Part014
    + surrogateDiagTailX0RatChunk000Sub000Block147Part015
    + surrogateDiagTailX0RatChunk000Sub000Block147Part016
    + surrogateDiagTailX0RatChunk000Sub000Block147Part017
    + surrogateDiagTailX0RatChunk000Sub000Block147Part018
    + surrogateDiagTailX0RatChunk000Sub000Block147Part019

def surrogateDiagonalTailChunk000Sub000Block147TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block147Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block147Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block147Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block147Part020
    + surrogateDiagTailX0RatChunk000Sub000Block147Part021
    + surrogateDiagTailX0RatChunk000Sub000Block147Part022
    + surrogateDiagTailX0RatChunk000Sub000Block147Part023
    + surrogateDiagTailX0RatChunk000Sub000Block147Part024

def surrogateDiagonalTailChunk000Sub000Block147Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block147HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block147MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block147TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block147 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block147Part000
    + surrogateDiagTailX0RatChunk000Sub000Block147Part001
    + surrogateDiagTailX0RatChunk000Sub000Block147Part002
    + surrogateDiagTailX0RatChunk000Sub000Block147Part003
    + surrogateDiagTailX0RatChunk000Sub000Block147Part004
    + surrogateDiagTailX0RatChunk000Sub000Block147Part005
    + surrogateDiagTailX0RatChunk000Sub000Block147Part006
    + surrogateDiagTailX0RatChunk000Sub000Block147Part007
    + surrogateDiagTailX0RatChunk000Sub000Block147Part008
    + surrogateDiagTailX0RatChunk000Sub000Block147Part009
    + surrogateDiagTailX0RatChunk000Sub000Block147Part010
    + surrogateDiagTailX0RatChunk000Sub000Block147Part011
    + surrogateDiagTailX0RatChunk000Sub000Block147Part012
    + surrogateDiagTailX0RatChunk000Sub000Block147Part013
    + surrogateDiagTailX0RatChunk000Sub000Block147Part014
    + surrogateDiagTailX0RatChunk000Sub000Block147Part015
    + surrogateDiagTailX0RatChunk000Sub000Block147Part016
    + surrogateDiagTailX0RatChunk000Sub000Block147Part017
    + surrogateDiagTailX0RatChunk000Sub000Block147Part018
    + surrogateDiagTailX0RatChunk000Sub000Block147Part019
    + surrogateDiagTailX0RatChunk000Sub000Block147Part020
    + surrogateDiagTailX0RatChunk000Sub000Block147Part021
    + surrogateDiagTailX0RatChunk000Sub000Block147Part022
    + surrogateDiagTailX0RatChunk000Sub000Block147Part023
    + surrogateDiagTailX0RatChunk000Sub000Block147Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block147_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block147Head + surrogateDiagTailX0RatChunk000Sub000Block147Mid + surrogateDiagTailX0RatChunk000Sub000Block147Tail =
      surrogateDiagTailX0RatChunk000Sub000Block147 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block147Head surrogateDiagTailX0RatChunk000Sub000Block147Mid surrogateDiagTailX0RatChunk000Sub000Block147Tail surrogateDiagTailX0RatChunk000Sub000Block147
  ring

def SurrogateDiagonalTailChunk000Sub000Block147HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block147HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block147Head

def SurrogateDiagonalTailChunk000Sub000Block147MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block147MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block147Mid

def SurrogateDiagonalTailChunk000Sub000Block147TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block147TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block147Tail

theorem surrogateDiagonalTailChunk000Sub000Block147_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block147HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block147MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block147TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block147Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block147 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block147HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block147MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block147TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block147Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block147_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
