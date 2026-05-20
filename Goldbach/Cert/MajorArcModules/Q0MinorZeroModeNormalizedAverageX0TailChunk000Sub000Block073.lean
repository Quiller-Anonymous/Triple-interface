import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [73,74). -/

/- Block 073 covers tail-support indices [1825,1850) and q from 3054 to 3091. -/

def TailChunk000Sub000Block073Part000SupportExplicit : Finset ℕ :=
  ([3054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part000 : ℚ :=
  (307133113975 : ℚ) / 2664413900064768

def SurrogateDiagonalTailChunk000Sub000Block073Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3054
    = surrogateDiagTailX0RatChunk000Sub000Block073Part000

theorem surrogateDiagonalTailChunk000Sub000Block073Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part000] using hcert

def TailChunk000Sub000Block073Part001SupportExplicit : Finset ℕ :=
  ([3055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part001 : ℚ :=
  (2144320925 : ℚ) / 161501037428736

def SurrogateDiagonalTailChunk000Sub000Block073Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3055
    = surrogateDiagTailX0RatChunk000Sub000Block073Part001

theorem surrogateDiagonalTailChunk000Sub000Block073Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part001] using hcert

def TailChunk000Sub000Block073Part002SupportExplicit : Finset ℕ :=
  ([3057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part002 : ℚ :=
  (713226827425 : ℚ) / 42967289058503808

def SurrogateDiagonalTailChunk000Sub000Block073Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3057
    = surrogateDiagTailX0RatChunk000Sub000Block073Part002

theorem surrogateDiagonalTailChunk000Sub000Block073Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part002] using hcert

def TailChunk000Sub000Block073Part003SupportExplicit : Finset ℕ :=
  ([3058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part003 : ℚ :=
  (7990759781 : ℚ) / 181373235393600

def SurrogateDiagonalTailChunk000Sub000Block073Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3058
    = surrogateDiagTailX0RatChunk000Sub000Block073Part003

theorem surrogateDiagonalTailChunk000Sub000Block073Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part003] using hcert

def TailChunk000Sub000Block073Part004SupportExplicit : Finset ℕ :=
  ([3059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part004 : ℚ :=
  (431287396025 : ℚ) / 39845805294265344

def SurrogateDiagonalTailChunk000Sub000Block073Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3059
    = surrogateDiagTailX0RatChunk000Sub000Block073Part004

theorem surrogateDiagonalTailChunk000Sub000Block073Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part004] using hcert

def TailChunk000Sub000Block073Part005SupportExplicit : Finset ℕ :=
  ([3061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part005 : ℚ :=
  (234243025 : ℚ) / 87694540360992

def SurrogateDiagonalTailChunk000Sub000Block073Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3061
    = surrogateDiagTailX0RatChunk000Sub000Block073Part005

theorem surrogateDiagonalTailChunk000Sub000Block073Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part005] using hcert

def TailChunk000Sub000Block073Part006SupportExplicit : Finset ℕ :=
  ([3062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part006 : ℚ :=
  (114854089 : ℚ) / 3582293315400

def SurrogateDiagonalTailChunk000Sub000Block073Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3062
    = surrogateDiagTailX0RatChunk000Sub000Block073Part006

theorem surrogateDiagonalTailChunk000Sub000Block073Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part006] using hcert

def TailChunk000Sub000Block073Part007SupportExplicit : Finset ℕ :=
  ([3063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part007 : ℚ :=
  (4167013343 : ℚ) / 346447566858240

def SurrogateDiagonalTailChunk000Sub000Block073Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3063
    = surrogateDiagTailX0RatChunk000Sub000Block073Part007

theorem surrogateDiagonalTailChunk000Sub000Block073Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part007] using hcert

def TailChunk000Sub000Block073Part008SupportExplicit : Finset ℕ :=
  ([3065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part008 : ℚ :=
  (134930508925 : ℚ) / 22449802332413952

def SurrogateDiagonalTailChunk000Sub000Block073Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3065
    = surrogateDiagTailX0RatChunk000Sub000Block073Part008

theorem surrogateDiagonalTailChunk000Sub000Block073Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part008] using hcert

def TailChunk000Sub000Block073Part009SupportExplicit : Finset ℕ :=
  ([3066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part009 : ℚ :=
  (262625787175 : ℚ) / 1393419323179008

def SurrogateDiagonalTailChunk000Sub000Block073Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3066
    = surrogateDiagTailX0RatChunk000Sub000Block073Part009

theorem surrogateDiagonalTailChunk000Sub000Block073Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part009] using hcert

def TailChunk000Sub000Block073Part010SupportExplicit : Finset ℕ :=
  ([3067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part010 : ℚ :=
  (146976390625 : ℚ) / 55240228915825842

def SurrogateDiagonalTailChunk000Sub000Block073Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3067
    = surrogateDiagTailX0RatChunk000Sub000Block073Part010

theorem surrogateDiagonalTailChunk000Sub000Block073Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part010] using hcert

def TailChunk000Sub000Block073Part011SupportExplicit : Finset ℕ :=
  ([3070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part011 : ℚ :=
  (21076757375 : ℚ) / 330144151947264

def SurrogateDiagonalTailChunk000Sub000Block073Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3070
    = surrogateDiagTailX0RatChunk000Sub000Block073Part011

theorem surrogateDiagonalTailChunk000Sub000Block073Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part011] using hcert

def TailChunk000Sub000Block073Part012SupportExplicit : Finset ℕ :=
  ([3071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part012 : ℚ :=
  (8788624175 : ℚ) / 1483482070766736

def SurrogateDiagonalTailChunk000Sub000Block073Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3071
    = surrogateDiagTailX0RatChunk000Sub000Block073Part012

theorem surrogateDiagonalTailChunk000Sub000Block073Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part012] using hcert

def TailChunk000Sub000Block073Part013SupportExplicit : Finset ℕ :=
  ([3073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part013 : ℚ :=
  (492628562225 : ℚ) / 59634599479308864

def SurrogateDiagonalTailChunk000Sub000Block073Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3073
    = surrogateDiagTailX0RatChunk000Sub000Block073Part013

theorem surrogateDiagonalTailChunk000Sub000Block073Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part013] using hcert

def TailChunk000Sub000Block073Part014SupportExplicit : Finset ℕ :=
  ([3074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part014 : ℚ :=
  (1098164775 : ℚ) / 29264501756672

def SurrogateDiagonalTailChunk000Sub000Block073Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3074
    = surrogateDiagTailX0RatChunk000Sub000Block073Part014

theorem surrogateDiagonalTailChunk000Sub000Block073Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part014] using hcert

def TailChunk000Sub000Block073Part015SupportExplicit : Finset ℕ :=
  ([3077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part015 : ℚ :=
  (1824364369 : ℚ) / 286711794892800

def SurrogateDiagonalTailChunk000Sub000Block073Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3077
    = surrogateDiagTailX0RatChunk000Sub000Block073Part015

theorem surrogateDiagonalTailChunk000Sub000Block073Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part015] using hcert

def TailChunk000Sub000Block073Part016SupportExplicit : Finset ℕ :=
  ([3079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part016 : ℚ :=
  (1184793118975 : ℚ) / 224440548231459528

def SurrogateDiagonalTailChunk000Sub000Block073Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3079
    = surrogateDiagTailX0RatChunk000Sub000Block073Part016

theorem surrogateDiagonalTailChunk000Sub000Block073Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part016] using hcert

def TailChunk000Sub000Block073Part017SupportExplicit : Finset ℕ :=
  ([3081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part017 : ℚ :=
  (490382183725 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block073Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3081
    = surrogateDiagTailX0RatChunk000Sub000Block073Part017

theorem surrogateDiagonalTailChunk000Sub000Block073Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part017] using hcert

def TailChunk000Sub000Block073Part018SupportExplicit : Finset ℕ :=
  ([3082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part018 : ℚ :=
  (52719926825 : ℚ) / 1389323357989776

def SurrogateDiagonalTailChunk000Sub000Block073Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3082
    = surrogateDiagTailX0RatChunk000Sub000Block073Part018

theorem surrogateDiagonalTailChunk000Sub000Block073Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part018] using hcert

def TailChunk000Sub000Block073Part019SupportExplicit : Finset ℕ :=
  ([3083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part019 : ℚ :=
  (148513890625 : ℚ) / 56402376737313522

def SurrogateDiagonalTailChunk000Sub000Block073Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3083
    = surrogateDiagTailX0RatChunk000Sub000Block073Part019

theorem surrogateDiagonalTailChunk000Sub000Block073Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part019] using hcert

def TailChunk000Sub000Block073Part020SupportExplicit : Finset ℕ :=
  ([3085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part020 : ℚ :=
  (34173993325 : ℚ) / 5760626132287488

def SurrogateDiagonalTailChunk000Sub000Block073Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3085
    = surrogateDiagTailX0RatChunk000Sub000Block073Part020

theorem surrogateDiagonalTailChunk000Sub000Block073Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part020] using hcert

def TailChunk000Sub000Block073Part021SupportExplicit : Finset ℕ :=
  ([3086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part021 : ℚ :=
  (49581180425 : ℚ) / 1570803442228872

def SurrogateDiagonalTailChunk000Sub000Block073Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3086
    = surrogateDiagTailX0RatChunk000Sub000Block073Part021

theorem surrogateDiagonalTailChunk000Sub000Block073Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part021] using hcert

def TailChunk000Sub000Block073Part022SupportExplicit : Finset ℕ :=
  ([3089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part022 : ℚ :=
  (1192501576975 : ℚ) / 227371499290656768

def SurrogateDiagonalTailChunk000Sub000Block073Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3089
    = surrogateDiagTailX0RatChunk000Sub000Block073Part022

theorem surrogateDiagonalTailChunk000Sub000Block073Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part022] using hcert

def TailChunk000Sub000Block073Part023SupportExplicit : Finset ℕ :=
  ([3090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part023 : ℚ :=
  (31283552375 : ℚ) / 138579026743296

def SurrogateDiagonalTailChunk000Sub000Block073Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3090
    = surrogateDiagTailX0RatChunk000Sub000Block073Part023

theorem surrogateDiagonalTailChunk000Sub000Block073Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part023] using hcert

def TailChunk000Sub000Block073Part024SupportExplicit : Finset ℕ :=
  ([3091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block073Part024 : ℚ :=
  (8493687983 : ℚ) / 1229557862400000

def SurrogateDiagonalTailChunk000Sub000Block073Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3091
    = surrogateDiagTailX0RatChunk000Sub000Block073Part024

theorem surrogateDiagonalTailChunk000Sub000Block073Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block073Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block073Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block073Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block073Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block073Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block073Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block073HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block073Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block073Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block073Part000
    + surrogateDiagTailX0RatChunk000Sub000Block073Part001
    + surrogateDiagTailX0RatChunk000Sub000Block073Part002
    + surrogateDiagTailX0RatChunk000Sub000Block073Part003
    + surrogateDiagTailX0RatChunk000Sub000Block073Part004
    + surrogateDiagTailX0RatChunk000Sub000Block073Part005
    + surrogateDiagTailX0RatChunk000Sub000Block073Part006
    + surrogateDiagTailX0RatChunk000Sub000Block073Part007
    + surrogateDiagTailX0RatChunk000Sub000Block073Part008
    + surrogateDiagTailX0RatChunk000Sub000Block073Part009

def surrogateDiagonalTailChunk000Sub000Block073MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block073Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block073Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block073Part010
    + surrogateDiagTailX0RatChunk000Sub000Block073Part011
    + surrogateDiagTailX0RatChunk000Sub000Block073Part012
    + surrogateDiagTailX0RatChunk000Sub000Block073Part013
    + surrogateDiagTailX0RatChunk000Sub000Block073Part014
    + surrogateDiagTailX0RatChunk000Sub000Block073Part015
    + surrogateDiagTailX0RatChunk000Sub000Block073Part016
    + surrogateDiagTailX0RatChunk000Sub000Block073Part017
    + surrogateDiagTailX0RatChunk000Sub000Block073Part018
    + surrogateDiagTailX0RatChunk000Sub000Block073Part019

def surrogateDiagonalTailChunk000Sub000Block073TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block073Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block073Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block073Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block073Part020
    + surrogateDiagTailX0RatChunk000Sub000Block073Part021
    + surrogateDiagTailX0RatChunk000Sub000Block073Part022
    + surrogateDiagTailX0RatChunk000Sub000Block073Part023
    + surrogateDiagTailX0RatChunk000Sub000Block073Part024

def surrogateDiagonalTailChunk000Sub000Block073Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block073HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block073MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block073TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block073 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block073Part000
    + surrogateDiagTailX0RatChunk000Sub000Block073Part001
    + surrogateDiagTailX0RatChunk000Sub000Block073Part002
    + surrogateDiagTailX0RatChunk000Sub000Block073Part003
    + surrogateDiagTailX0RatChunk000Sub000Block073Part004
    + surrogateDiagTailX0RatChunk000Sub000Block073Part005
    + surrogateDiagTailX0RatChunk000Sub000Block073Part006
    + surrogateDiagTailX0RatChunk000Sub000Block073Part007
    + surrogateDiagTailX0RatChunk000Sub000Block073Part008
    + surrogateDiagTailX0RatChunk000Sub000Block073Part009
    + surrogateDiagTailX0RatChunk000Sub000Block073Part010
    + surrogateDiagTailX0RatChunk000Sub000Block073Part011
    + surrogateDiagTailX0RatChunk000Sub000Block073Part012
    + surrogateDiagTailX0RatChunk000Sub000Block073Part013
    + surrogateDiagTailX0RatChunk000Sub000Block073Part014
    + surrogateDiagTailX0RatChunk000Sub000Block073Part015
    + surrogateDiagTailX0RatChunk000Sub000Block073Part016
    + surrogateDiagTailX0RatChunk000Sub000Block073Part017
    + surrogateDiagTailX0RatChunk000Sub000Block073Part018
    + surrogateDiagTailX0RatChunk000Sub000Block073Part019
    + surrogateDiagTailX0RatChunk000Sub000Block073Part020
    + surrogateDiagTailX0RatChunk000Sub000Block073Part021
    + surrogateDiagTailX0RatChunk000Sub000Block073Part022
    + surrogateDiagTailX0RatChunk000Sub000Block073Part023
    + surrogateDiagTailX0RatChunk000Sub000Block073Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block073_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block073Head + surrogateDiagTailX0RatChunk000Sub000Block073Mid + surrogateDiagTailX0RatChunk000Sub000Block073Tail =
      surrogateDiagTailX0RatChunk000Sub000Block073 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block073Head surrogateDiagTailX0RatChunk000Sub000Block073Mid surrogateDiagTailX0RatChunk000Sub000Block073Tail surrogateDiagTailX0RatChunk000Sub000Block073
  ring

def SurrogateDiagonalTailChunk000Sub000Block073HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block073HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block073Head

def SurrogateDiagonalTailChunk000Sub000Block073MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block073MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block073Mid

def SurrogateDiagonalTailChunk000Sub000Block073TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block073TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block073Tail

theorem surrogateDiagonalTailChunk000Sub000Block073_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block073HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block073MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block073TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block073Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block073 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block073HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block073MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block073TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block073Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block073_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
