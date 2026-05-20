import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [145,146). -/

/- Block 145 covers tail-support indices [3625,3650) and q from 6015 to 6055. -/

def TailChunk000Sub000Block145Part000SupportExplicit : Finset ℕ :=
  ([6015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part000 : ℚ :=
  (22097811073 : ℚ) / 10487857152000000

def SurrogateDiagonalTailChunk000Sub000Block145Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6015
    = surrogateDiagTailX0RatChunk000Sub000Block145Part000

theorem surrogateDiagonalTailChunk000Sub000Block145Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part000] using hcert

def TailChunk000Sub000Block145Part001SupportExplicit : Finset ℕ :=
  ([6017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part001 : ℚ :=
  (32797747 : ℚ) / 427360211951400

def SurrogateDiagonalTailChunk000Sub000Block145Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6017
    = surrogateDiagTailX0RatChunk000Sub000Block145Part001

theorem surrogateDiagonalTailChunk000Sub000Block145Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part001] using hcert

def TailChunk000Sub000Block145Part002SupportExplicit : Finset ℕ :=
  ([6018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part002 : ℚ :=
  (158323239675 : ℚ) / 9890482792431616

def SurrogateDiagonalTailChunk000Sub000Block145Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6018
    = surrogateDiagTailX0RatChunk000Sub000Block145Part002

theorem surrogateDiagonalTailChunk000Sub000Block145Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part002] using hcert

def TailChunk000Sub000Block145Part003SupportExplicit : Finset ℕ :=
  ([6019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part003 : ℚ :=
  (63215875 : ℚ) / 994198970274048

def SurrogateDiagonalTailChunk000Sub000Block145Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6019
    = surrogateDiagTailX0RatChunk000Sub000Block145Part003

theorem surrogateDiagonalTailChunk000Sub000Block145Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part003] using hcert

def TailChunk000Sub000Block145Part004SupportExplicit : Finset ℕ :=
  ([6022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part004 : ℚ :=
  (226653025 : ℚ) / 82101829092402

def SurrogateDiagonalTailChunk000Sub000Block145Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6022
    = surrogateDiagTailX0RatChunk000Sub000Block145Part004

theorem surrogateDiagonalTailChunk000Sub000Block145Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part004] using hcert

def TailChunk000Sub000Block145Part005SupportExplicit : Finset ℕ :=
  ([6023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part005 : ℚ :=
  (105176912575 : ℚ) / 2617370539389831168

def SurrogateDiagonalTailChunk000Sub000Block145Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6023
    = surrogateDiagTailX0RatChunk000Sub000Block145Part005

theorem surrogateDiagonalTailChunk000Sub000Block145Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part005] using hcert

def TailChunk000Sub000Block145Part006SupportExplicit : Finset ℕ :=
  ([6026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part006 : ℚ :=
  (21349499261 : ℚ) / 3345961866561600

def SurrogateDiagonalTailChunk000Sub000Block145Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6026
    = surrogateDiagTailX0RatChunk000Sub000Block145Part006

theorem surrogateDiagonalTailChunk000Sub000Block145Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part006] using hcert

def TailChunk000Sub000Block145Part007SupportExplicit : Finset ℕ :=
  ([6029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part007 : ℚ :=
  (567950640625 : ℚ) / 825391214898092832

def SurrogateDiagonalTailChunk000Sub000Block145Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6029
    = surrogateDiagTailX0RatChunk000Sub000Block145Part007

theorem surrogateDiagonalTailChunk000Sub000Block145Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part007] using hcert

def TailChunk000Sub000Block145Part008SupportExplicit : Finset ℕ :=
  ([6031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part008 : ℚ :=
  (121475159575 : ℚ) / 160703159403119616

def SurrogateDiagonalTailChunk000Sub000Block145Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6031
    = surrogateDiagTailX0RatChunk000Sub000Block145Part008

theorem surrogateDiagonalTailChunk000Sub000Block145Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part008] using hcert

def TailChunk000Sub000Block145Part009SupportExplicit : Finset ℕ :=
  ([6033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part009 : ℚ :=
  (2020883 : ℚ) / 870528427200

def SurrogateDiagonalTailChunk000Sub000Block145Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6033
    = surrogateDiagTailX0RatChunk000Sub000Block145Part009

theorem surrogateDiagonalTailChunk000Sub000Block145Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part009] using hcert

def TailChunk000Sub000Block145Part010SupportExplicit : Finset ℕ :=
  ([6034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part010 : ℚ :=
  (4169298733 : ℚ) / 492405805468800

def SurrogateDiagonalTailChunk000Sub000Block145Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6034
    = surrogateDiagTailX0RatChunk000Sub000Block145Part010

theorem surrogateDiagonalTailChunk000Sub000Block145Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part010] using hcert

def TailChunk000Sub000Block145Part011SupportExplicit : Finset ℕ :=
  ([6035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part011 : ℚ :=
  (13246269 : ℚ) / 8393781673984

def SurrogateDiagonalTailChunk000Sub000Block145Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6035
    = surrogateDiagTailX0RatChunk000Sub000Block145Part011

theorem surrogateDiagonalTailChunk000Sub000Block145Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part011] using hcert

def TailChunk000Sub000Block145Part012SupportExplicit : Finset ℕ :=
  ([6037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part012 : ℚ :=
  (569458890625 : ℚ) / 829781584021937952

def SurrogateDiagonalTailChunk000Sub000Block145Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6037
    = surrogateDiagTailX0RatChunk000Sub000Block145Part012

theorem surrogateDiagonalTailChunk000Sub000Block145Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part012] using hcert

def TailChunk000Sub000Block145Part013SupportExplicit : Finset ℕ :=
  ([6038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part013 : ℚ :=
  (1139067265975 : ℚ) / 207445396005484488

def SurrogateDiagonalTailChunk000Sub000Block145Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6038
    = surrogateDiagTailX0RatChunk000Sub000Block145Part013

theorem surrogateDiagonalTailChunk000Sub000Block145Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part013] using hcert

def TailChunk000Sub000Block145Part014SupportExplicit : Finset ℕ :=
  ([6041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part014 : ℚ :=
  (1906293934975 : ℚ) / 1789208380554726528

def SurrogateDiagonalTailChunk000Sub000Block145Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6041
    = surrogateDiagTailX0RatChunk000Sub000Block145Part014

theorem surrogateDiagonalTailChunk000Sub000Block145Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part014] using hcert

def TailChunk000Sub000Block145Part015SupportExplicit : Finset ℕ :=
  ([6042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part015 : ℚ :=
  (643883762875 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block145Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6042
    = surrogateDiagTailX0RatChunk000Sub000Block145Part015

theorem surrogateDiagonalTailChunk000Sub000Block145Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part015] using hcert

def TailChunk000Sub000Block145Part016SupportExplicit : Finset ℕ :=
  ([6043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part016 : ℚ :=
  (570591390625 : ℚ) / 833085837115462962

def SurrogateDiagonalTailChunk000Sub000Block145Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6043
    = surrogateDiagTailX0RatChunk000Sub000Block145Part016

theorem surrogateDiagonalTailChunk000Sub000Block145Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part016] using hcert

def TailChunk000Sub000Block145Part017SupportExplicit : Finset ℕ :=
  ([6045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part017 : ℚ :=
  (302368579 : ℚ) / 57342358978560

def SurrogateDiagonalTailChunk000Sub000Block145Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6045
    = surrogateDiagTailX0RatChunk000Sub000Block145Part017

theorem surrogateDiagonalTailChunk000Sub000Block145Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part017] using hcert

def TailChunk000Sub000Block145Part018SupportExplicit : Finset ℕ :=
  ([6046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part018 : ℚ :=
  (1142087661775 : ℚ) / 208547361157645128

def SurrogateDiagonalTailChunk000Sub000Block145Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6046
    = surrogateDiagTailX0RatChunk000Sub000Block145Part018

theorem surrogateDiagonalTailChunk000Sub000Block145Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part018] using hcert

def TailChunk000Sub000Block145Part019SupportExplicit : Finset ℕ :=
  ([6047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part019 : ℚ :=
  (571347015625 : ℚ) / 835294148262977682

def SurrogateDiagonalTailChunk000Sub000Block145Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6047
    = surrogateDiagTailX0RatChunk000Sub000Block145Part019

theorem surrogateDiagonalTailChunk000Sub000Block145Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part019] using hcert

def TailChunk000Sub000Block145Part020SupportExplicit : Finset ℕ :=
  ([6049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part020 : ℚ :=
  (720318461475 : ℚ) / 920028948912996736

def SurrogateDiagonalTailChunk000Sub000Block145Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6049
    = surrogateDiagTailX0RatChunk000Sub000Block145Part020

theorem surrogateDiagonalTailChunk000Sub000Block145Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part020] using hcert

def TailChunk000Sub000Block145Part021SupportExplicit : Finset ℕ :=
  ([6051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part021 : ℚ :=
  (148175 : ℚ) / 64210599936

def SurrogateDiagonalTailChunk000Sub000Block145Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6051
    = surrogateDiagTailX0RatChunk000Sub000Block145Part021

theorem surrogateDiagonalTailChunk000Sub000Block145Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part021] using hcert

def TailChunk000Sub000Block145Part022SupportExplicit : Finset ℕ :=
  ([6053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part022 : ℚ :=
  (572481390625 : ℚ) / 838614843120497952

def SurrogateDiagonalTailChunk000Sub000Block145Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6053
    = surrogateDiagTailX0RatChunk000Sub000Block145Part022

theorem surrogateDiagonalTailChunk000Sub000Block145Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part022] using hcert

def TailChunk000Sub000Block145Part023SupportExplicit : Finset ℕ :=
  ([6054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part023 : ℚ :=
  (508707452275 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub000Block145Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6054
    = surrogateDiagTailX0RatChunk000Sub000Block145Part023

theorem surrogateDiagonalTailChunk000Sub000Block145Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part023] using hcert

def TailChunk000Sub000Block145Part024SupportExplicit : Finset ℕ :=
  ([6055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block145Part024 : ℚ :=
  (747171844325 : ℚ) / 363040952256036864

def SurrogateDiagonalTailChunk000Sub000Block145Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6055
    = surrogateDiagTailX0RatChunk000Sub000Block145Part024

theorem surrogateDiagonalTailChunk000Sub000Block145Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block145Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block145Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block145Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block145Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block145Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block145Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block145HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block145Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block145Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block145Part000
    + surrogateDiagTailX0RatChunk000Sub000Block145Part001
    + surrogateDiagTailX0RatChunk000Sub000Block145Part002
    + surrogateDiagTailX0RatChunk000Sub000Block145Part003
    + surrogateDiagTailX0RatChunk000Sub000Block145Part004
    + surrogateDiagTailX0RatChunk000Sub000Block145Part005
    + surrogateDiagTailX0RatChunk000Sub000Block145Part006
    + surrogateDiagTailX0RatChunk000Sub000Block145Part007
    + surrogateDiagTailX0RatChunk000Sub000Block145Part008
    + surrogateDiagTailX0RatChunk000Sub000Block145Part009

def surrogateDiagonalTailChunk000Sub000Block145MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block145Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block145Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block145Part010
    + surrogateDiagTailX0RatChunk000Sub000Block145Part011
    + surrogateDiagTailX0RatChunk000Sub000Block145Part012
    + surrogateDiagTailX0RatChunk000Sub000Block145Part013
    + surrogateDiagTailX0RatChunk000Sub000Block145Part014
    + surrogateDiagTailX0RatChunk000Sub000Block145Part015
    + surrogateDiagTailX0RatChunk000Sub000Block145Part016
    + surrogateDiagTailX0RatChunk000Sub000Block145Part017
    + surrogateDiagTailX0RatChunk000Sub000Block145Part018
    + surrogateDiagTailX0RatChunk000Sub000Block145Part019

def surrogateDiagonalTailChunk000Sub000Block145TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block145Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block145Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block145Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block145Part020
    + surrogateDiagTailX0RatChunk000Sub000Block145Part021
    + surrogateDiagTailX0RatChunk000Sub000Block145Part022
    + surrogateDiagTailX0RatChunk000Sub000Block145Part023
    + surrogateDiagTailX0RatChunk000Sub000Block145Part024

def surrogateDiagonalTailChunk000Sub000Block145Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block145HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block145MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block145TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block145 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block145Part000
    + surrogateDiagTailX0RatChunk000Sub000Block145Part001
    + surrogateDiagTailX0RatChunk000Sub000Block145Part002
    + surrogateDiagTailX0RatChunk000Sub000Block145Part003
    + surrogateDiagTailX0RatChunk000Sub000Block145Part004
    + surrogateDiagTailX0RatChunk000Sub000Block145Part005
    + surrogateDiagTailX0RatChunk000Sub000Block145Part006
    + surrogateDiagTailX0RatChunk000Sub000Block145Part007
    + surrogateDiagTailX0RatChunk000Sub000Block145Part008
    + surrogateDiagTailX0RatChunk000Sub000Block145Part009
    + surrogateDiagTailX0RatChunk000Sub000Block145Part010
    + surrogateDiagTailX0RatChunk000Sub000Block145Part011
    + surrogateDiagTailX0RatChunk000Sub000Block145Part012
    + surrogateDiagTailX0RatChunk000Sub000Block145Part013
    + surrogateDiagTailX0RatChunk000Sub000Block145Part014
    + surrogateDiagTailX0RatChunk000Sub000Block145Part015
    + surrogateDiagTailX0RatChunk000Sub000Block145Part016
    + surrogateDiagTailX0RatChunk000Sub000Block145Part017
    + surrogateDiagTailX0RatChunk000Sub000Block145Part018
    + surrogateDiagTailX0RatChunk000Sub000Block145Part019
    + surrogateDiagTailX0RatChunk000Sub000Block145Part020
    + surrogateDiagTailX0RatChunk000Sub000Block145Part021
    + surrogateDiagTailX0RatChunk000Sub000Block145Part022
    + surrogateDiagTailX0RatChunk000Sub000Block145Part023
    + surrogateDiagTailX0RatChunk000Sub000Block145Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block145_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block145Head + surrogateDiagTailX0RatChunk000Sub000Block145Mid + surrogateDiagTailX0RatChunk000Sub000Block145Tail =
      surrogateDiagTailX0RatChunk000Sub000Block145 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block145Head surrogateDiagTailX0RatChunk000Sub000Block145Mid surrogateDiagTailX0RatChunk000Sub000Block145Tail surrogateDiagTailX0RatChunk000Sub000Block145
  ring

def SurrogateDiagonalTailChunk000Sub000Block145HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block145HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block145Head

def SurrogateDiagonalTailChunk000Sub000Block145MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block145MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block145Mid

def SurrogateDiagonalTailChunk000Sub000Block145TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block145TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block145Tail

theorem surrogateDiagonalTailChunk000Sub000Block145_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block145HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block145MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block145TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block145Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block145 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block145HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block145MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block145TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block145Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block145_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
