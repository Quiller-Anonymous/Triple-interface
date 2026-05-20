import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [172,173). -/

/-- Block 172 covers tail-support indices [4300,4325) and q from 7127 to 7167. -/

def TailChunk000Sub000Block172Part000SupportExplicit : Finset ℕ :=
  ([7127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block172Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7127
    = surrogateDiagTailX0RatChunk000Sub000Block172Part000

theorem surrogateDiagonalTailChunk000Sub000Block172Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part000] using hcert

def TailChunk000Sub000Block172Part001SupportExplicit : Finset ℕ :=
  ([7129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block172Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7129
    = surrogateDiagTailX0RatChunk000Sub000Block172Part001

theorem surrogateDiagonalTailChunk000Sub000Block172Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part001] using hcert

def TailChunk000Sub000Block172Part002SupportExplicit : Finset ℕ :=
  ([7130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part002 : ℚ :=
  (529386029 : ℚ) / 97170078449664

def SurrogateDiagonalTailChunk000Sub000Block172Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7130
    = surrogateDiagTailX0RatChunk000Sub000Block172Part002

theorem surrogateDiagonalTailChunk000Sub000Block172Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part002] using hcert

def TailChunk000Sub000Block172Part003SupportExplicit : Finset ℕ :=
  ([7131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part003 : ℚ :=
  (353077876475 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub000Block172Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7131
    = surrogateDiagTailX0RatChunk000Sub000Block172Part003

theorem surrogateDiagonalTailChunk000Sub000Block172Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part003] using hcert

def TailChunk000Sub000Block172Part004SupportExplicit : Finset ℕ :=
  ([7133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part004 : ℚ :=
  (325466414275 : ℚ) / 3480350413738808448

def SurrogateDiagonalTailChunk000Sub000Block172Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7133
    = surrogateDiagTailX0RatChunk000Sub000Block172Part004

theorem surrogateDiagonalTailChunk000Sub000Block172Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part004] using hcert

def TailChunk000Sub000Block172Part005SupportExplicit : Finset ℕ :=
  ([7134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part005 : ℚ :=
  (11789126891 : ℚ) / 1259067251097600

def SurrogateDiagonalTailChunk000Sub000Block172Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7134
    = surrogateDiagTailX0RatChunk000Sub000Block172Part005

theorem surrogateDiagonalTailChunk000Sub000Block172Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part005] using hcert

def TailChunk000Sub000Block172Part006SupportExplicit : Finset ℕ :=
  ([7135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part006 : ℚ :=
  (95593638175 : ℚ) / 661736263600722432

def SurrogateDiagonalTailChunk000Sub000Block172Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7135
    = surrogateDiagTailX0RatChunk000Sub000Block172Part006

theorem surrogateDiagonalTailChunk000Sub000Block172Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part006] using hcert

def TailChunk000Sub000Block172Part007SupportExplicit : Finset ℕ :=
  ([7138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part007 : ℚ :=
  (389668098875 : ℚ) / 175893355649922624

def SurrogateDiagonalTailChunk000Sub000Block172Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7138
    = surrogateDiagTailX0RatChunk000Sub000Block172Part007

theorem surrogateDiagonalTailChunk000Sub000Block172Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part007] using hcert

def TailChunk000Sub000Block172Part008SupportExplicit : Finset ℕ :=
  ([7141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part008 : ℚ :=
  (17710431625 : ℚ) / 1426861386935304192

def SurrogateDiagonalTailChunk000Sub000Block172Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7141
    = surrogateDiagTailX0RatChunk000Sub000Block172Part008

theorem surrogateDiagonalTailChunk000Sub000Block172Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part008] using hcert

def TailChunk000Sub000Block172Part009SupportExplicit : Finset ℕ :=
  ([7142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part009 : ℚ :=
  (318801025 : ℚ) / 162464962505202

def SurrogateDiagonalTailChunk000Sub000Block172Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7142
    = surrogateDiagTailX0RatChunk000Sub000Block172Part009

theorem surrogateDiagonalTailChunk000Sub000Block172Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part009] using hcert

def TailChunk000Sub000Block172Part010SupportExplicit : Finset ℕ :=
  ([7143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part010 : ℚ :=
  (10203 : ℚ) / 6162867200

def SurrogateDiagonalTailChunk000Sub000Block172Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7143
    = surrogateDiagTailX0RatChunk000Sub000Block172Part010

theorem surrogateDiagonalTailChunk000Sub000Block172Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part010] using hcert

def TailChunk000Sub000Block172Part011SupportExplicit : Finset ℕ :=
  ([7145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part011 : ℚ :=
  (403873330975 : ℚ) / 443637657614204928

def SurrogateDiagonalTailChunk000Sub000Block172Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7145
    = surrogateDiagTailX0RatChunk000Sub000Block172Part011

theorem surrogateDiagonalTailChunk000Sub000Block172Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part011] using hcert

def TailChunk000Sub000Block172Part012SupportExplicit : Finset ℕ :=
  ([7147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part012 : ℚ :=
  (6125506439 : ℚ) / 8253603798681600

def SurrogateDiagonalTailChunk000Sub000Block172Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7147
    = surrogateDiagTailX0RatChunk000Sub000Block172Part012

theorem surrogateDiagonalTailChunk000Sub000Block172Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part012] using hcert

def TailChunk000Sub000Block172Part013SupportExplicit : Finset ℕ :=
  ([7149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part013 : ℚ :=
  (443502456025 : ℚ) / 321998522404875552

def SurrogateDiagonalTailChunk000Sub000Block172Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7149
    = surrogateDiagTailX0RatChunk000Sub000Block172Part013

theorem surrogateDiagonalTailChunk000Sub000Block172Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part013] using hcert

def TailChunk000Sub000Block172Part014SupportExplicit : Finset ℕ :=
  ([7151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part014 : ℚ :=
  (51136801 : ℚ) / 104561308330050

def SurrogateDiagonalTailChunk000Sub000Block172Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7151
    = surrogateDiagTailX0RatChunk000Sub000Block172Part014

theorem surrogateDiagonalTailChunk000Sub000Block172Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part014] using hcert

def TailChunk000Sub000Block172Part015SupportExplicit : Finset ℕ :=
  ([7153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part015 : ℚ :=
  (20029945437 : ℚ) / 36063933907179200

def SurrogateDiagonalTailChunk000Sub000Block172Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7153
    = surrogateDiagTailX0RatChunk000Sub000Block172Part015

theorem surrogateDiagonalTailChunk000Sub000Block172Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part015] using hcert

def TailChunk000Sub000Block172Part016SupportExplicit : Finset ℕ :=
  ([7157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part016 : ℚ :=
  (5898381371 : ℚ) / 10198444733890560

def SurrogateDiagonalTailChunk000Sub000Block172Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7157
    = surrogateDiagTailX0RatChunk000Sub000Block172Part016

theorem surrogateDiagonalTailChunk000Sub000Block172Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part016] using hcert

def TailChunk000Sub000Block172Part017SupportExplicit : Finset ℕ :=
  ([7158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part017 : ℚ :=
  (444385535225 : ℚ) / 40385165547945984

def SurrogateDiagonalTailChunk000Sub000Block172Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7158
    = surrogateDiagTailX0RatChunk000Sub000Block172Part017

theorem surrogateDiagonalTailChunk000Sub000Block172Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part017] using hcert

def TailChunk000Sub000Block172Part018SupportExplicit : Finset ℕ :=
  ([7159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part018 : ℚ :=
  (800801265625 : ℚ) / 1641094703270802162

def SurrogateDiagonalTailChunk000Sub000Block172Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7159
    = surrogateDiagTailX0RatChunk000Sub000Block172Part018

theorem surrogateDiagonalTailChunk000Sub000Block172Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part018] using hcert

def TailChunk000Sub000Block172Part019SupportExplicit : Finset ℕ :=
  ([7161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part019 : ℚ :=
  (1892409113 : ℚ) / 622204416000000

def SurrogateDiagonalTailChunk000Sub000Block172Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7161
    = surrogateDiagTailX0RatChunk000Sub000Block172Part019

theorem surrogateDiagonalTailChunk000Sub000Block172Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part019] using hcert

def TailChunk000Sub000Block172Part020SupportExplicit : Finset ℕ :=
  ([7162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part020 : ℚ :=
  (64104981439 : ℚ) / 16429296098179200

def SurrogateDiagonalTailChunk000Sub000Block172Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7162
    = surrogateDiagTailX0RatChunk000Sub000Block172Part020

theorem surrogateDiagonalTailChunk000Sub000Block172Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part020] using hcert

def TailChunk000Sub000Block172Part021SupportExplicit : Finset ℕ :=
  ([7163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part021 : ℚ :=
  (856423747175 : ℚ) / 1115199931650932736

def SurrogateDiagonalTailChunk000Sub000Block172Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7163
    = surrogateDiagTailX0RatChunk000Sub000Block172Part021

theorem surrogateDiagonalTailChunk000Sub000Block172Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part021] using hcert

def TailChunk000Sub000Block172Part022SupportExplicit : Finset ℕ :=
  ([7165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part022 : ℚ :=
  (1218413780075 : ℚ) / 1345887936362840064

def SurrogateDiagonalTailChunk000Sub000Block172Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7165
    = surrogateDiagTailX0RatChunk000Sub000Block172Part022

theorem surrogateDiagonalTailChunk000Sub000Block172Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part022] using hcert

def TailChunk000Sub000Block172Part023SupportExplicit : Finset ℕ :=
  ([7166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part023 : ℚ :=
  (200592015625 : ℚ) / 102912752412405522

def SurrogateDiagonalTailChunk000Sub000Block172Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7166
    = surrogateDiagTailX0RatChunk000Sub000Block172Part023

theorem surrogateDiagonalTailChunk000Sub000Block172Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part023] using hcert

def TailChunk000Sub000Block172Part024SupportExplicit : Finset ℕ :=
  ([7167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block172Part024 : ℚ :=
  (891477502475 : ℚ) / 650510237471007744

def SurrogateDiagonalTailChunk000Sub000Block172Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7167
    = surrogateDiagTailX0RatChunk000Sub000Block172Part024

theorem surrogateDiagonalTailChunk000Sub000Block172Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block172Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block172Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block172Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block172Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block172Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block172Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block172HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block172Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block172Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block172Part000
    + surrogateDiagTailX0RatChunk000Sub000Block172Part001
    + surrogateDiagTailX0RatChunk000Sub000Block172Part002
    + surrogateDiagTailX0RatChunk000Sub000Block172Part003
    + surrogateDiagTailX0RatChunk000Sub000Block172Part004
    + surrogateDiagTailX0RatChunk000Sub000Block172Part005
    + surrogateDiagTailX0RatChunk000Sub000Block172Part006
    + surrogateDiagTailX0RatChunk000Sub000Block172Part007
    + surrogateDiagTailX0RatChunk000Sub000Block172Part008
    + surrogateDiagTailX0RatChunk000Sub000Block172Part009

def surrogateDiagonalTailChunk000Sub000Block172MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block172Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block172Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block172Part010
    + surrogateDiagTailX0RatChunk000Sub000Block172Part011
    + surrogateDiagTailX0RatChunk000Sub000Block172Part012
    + surrogateDiagTailX0RatChunk000Sub000Block172Part013
    + surrogateDiagTailX0RatChunk000Sub000Block172Part014
    + surrogateDiagTailX0RatChunk000Sub000Block172Part015
    + surrogateDiagTailX0RatChunk000Sub000Block172Part016
    + surrogateDiagTailX0RatChunk000Sub000Block172Part017
    + surrogateDiagTailX0RatChunk000Sub000Block172Part018
    + surrogateDiagTailX0RatChunk000Sub000Block172Part019

def surrogateDiagonalTailChunk000Sub000Block172TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block172Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block172Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block172Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block172Part020
    + surrogateDiagTailX0RatChunk000Sub000Block172Part021
    + surrogateDiagTailX0RatChunk000Sub000Block172Part022
    + surrogateDiagTailX0RatChunk000Sub000Block172Part023
    + surrogateDiagTailX0RatChunk000Sub000Block172Part024

def surrogateDiagonalTailChunk000Sub000Block172Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block172HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block172MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block172TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block172 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block172Part000
    + surrogateDiagTailX0RatChunk000Sub000Block172Part001
    + surrogateDiagTailX0RatChunk000Sub000Block172Part002
    + surrogateDiagTailX0RatChunk000Sub000Block172Part003
    + surrogateDiagTailX0RatChunk000Sub000Block172Part004
    + surrogateDiagTailX0RatChunk000Sub000Block172Part005
    + surrogateDiagTailX0RatChunk000Sub000Block172Part006
    + surrogateDiagTailX0RatChunk000Sub000Block172Part007
    + surrogateDiagTailX0RatChunk000Sub000Block172Part008
    + surrogateDiagTailX0RatChunk000Sub000Block172Part009
    + surrogateDiagTailX0RatChunk000Sub000Block172Part010
    + surrogateDiagTailX0RatChunk000Sub000Block172Part011
    + surrogateDiagTailX0RatChunk000Sub000Block172Part012
    + surrogateDiagTailX0RatChunk000Sub000Block172Part013
    + surrogateDiagTailX0RatChunk000Sub000Block172Part014
    + surrogateDiagTailX0RatChunk000Sub000Block172Part015
    + surrogateDiagTailX0RatChunk000Sub000Block172Part016
    + surrogateDiagTailX0RatChunk000Sub000Block172Part017
    + surrogateDiagTailX0RatChunk000Sub000Block172Part018
    + surrogateDiagTailX0RatChunk000Sub000Block172Part019
    + surrogateDiagTailX0RatChunk000Sub000Block172Part020
    + surrogateDiagTailX0RatChunk000Sub000Block172Part021
    + surrogateDiagTailX0RatChunk000Sub000Block172Part022
    + surrogateDiagTailX0RatChunk000Sub000Block172Part023
    + surrogateDiagTailX0RatChunk000Sub000Block172Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block172_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block172Head + surrogateDiagTailX0RatChunk000Sub000Block172Mid + surrogateDiagTailX0RatChunk000Sub000Block172Tail =
      surrogateDiagTailX0RatChunk000Sub000Block172 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block172Head surrogateDiagTailX0RatChunk000Sub000Block172Mid surrogateDiagTailX0RatChunk000Sub000Block172Tail surrogateDiagTailX0RatChunk000Sub000Block172
  ring

def SurrogateDiagonalTailChunk000Sub000Block172HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block172HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block172Head

def SurrogateDiagonalTailChunk000Sub000Block172MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block172MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block172Mid

def SurrogateDiagonalTailChunk000Sub000Block172TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block172TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block172Tail

theorem surrogateDiagonalTailChunk000Sub000Block172_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block172HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block172MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block172TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block172Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block172 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block172HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block172MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block172TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block172Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block172_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
