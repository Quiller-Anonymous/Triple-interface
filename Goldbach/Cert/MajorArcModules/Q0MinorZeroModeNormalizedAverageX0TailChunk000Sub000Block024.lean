import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [24,25). -/

/- Block 024 covers tail-support indices [600,625) and q from 1039 to 1081. -/

def TailChunk000Sub000Block024Part000SupportExplicit : Finset ℕ :=
  ([1039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part000 : ℚ :=
  (168540216125 : ℚ) / 1451397187813284

def SurrogateDiagonalTailChunk000Sub000Block024Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1039
    = surrogateDiagTailX0RatChunk000Sub000Block024Part000

theorem surrogateDiagonalTailChunk000Sub000Block024Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part000] using hcert

def TailChunk000Sub000Block024Part001SupportExplicit : Finset ℕ :=
  ([1041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part001 : ℚ :=
  (22509075 : ℚ) / 57327682624

def SurrogateDiagonalTailChunk000Sub000Block024Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1041
    = surrogateDiagTailX0RatChunk000Sub000Block024Part001

theorem surrogateDiagonalTailChunk000Sub000Block024Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part001] using hcert

def TailChunk000Sub000Block024Part002SupportExplicit : Finset ℕ :=
  ([1042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part002 : ℚ :=
  (1354762031 : ℚ) / 1462615664640

def SurrogateDiagonalTailChunk000Sub000Block024Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1042
    = surrogateDiagTailX0RatChunk000Sub000Block024Part002

theorem surrogateDiagonalTailChunk000Sub000Block024Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part002] using hcert

def TailChunk000Sub000Block024Part003SupportExplicit : Finset ℕ :=
  ([1043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part003 : ℚ :=
  (288039682675 : ℚ) / 1554815000659968

def SurrogateDiagonalTailChunk000Sub000Block024Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1043
    = surrogateDiagTailX0RatChunk000Sub000Block024Part003

theorem surrogateDiagonalTailChunk000Sub000Block024Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part003] using hcert

def TailChunk000Sub000Block024Part004SupportExplicit : Finset ℕ :=
  ([1045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part004 : ℚ :=
  (1543139159 : ℚ) / 4479871795200

def SurrogateDiagonalTailChunk000Sub000Block024Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1045
    = surrogateDiagTailX0RatChunk000Sub000Block024Part004

theorem surrogateDiagonalTailChunk000Sub000Block024Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part004] using hcert

def TailChunk000Sub000Block024Part005SupportExplicit : Finset ℕ :=
  ([1046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part005 : ℚ :=
  (711175400 : ℚ) / 859518284283

def SurrogateDiagonalTailChunk000Sub000Block024Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1046
    = surrogateDiagTailX0RatChunk000Sub000Block024Part005

theorem surrogateDiagonalTailChunk000Sub000Block024Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part005] using hcert

def TailChunk000Sub000Block024Part006SupportExplicit : Finset ℕ :=
  ([1047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part006 : ℚ :=
  (110083407425 : ℚ) / 293382241035264

def SurrogateDiagonalTailChunk000Sub000Block024Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1047
    = surrogateDiagTailX0RatChunk000Sub000Block024Part006

theorem surrogateDiagonalTailChunk000Sub000Block024Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part006] using hcert

def TailChunk000Sub000Block024Part007SupportExplicit : Finset ℕ :=
  ([1049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part007 : ℚ :=
  (171800106125 : ℚ) / 1508141163439104

def SurrogateDiagonalTailChunk000Sub000Block024Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1049
    = surrogateDiagTailX0RatChunk000Sub000Block024Part007

theorem surrogateDiagonalTailChunk000Sub000Block024Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part007] using hcert

def TailChunk000Sub000Block024Part008SupportExplicit : Finset ℕ :=
  ([1051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part008 : ℚ :=
  (1379646649 : ℚ) / 12157493512500

def SurrogateDiagonalTailChunk000Sub000Block024Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1051
    = surrogateDiagTailX0RatChunk000Sub000Block024Part008

theorem surrogateDiagonalTailChunk000Sub000Block024Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part008] using hcert

def TailChunk000Sub000Block024Part009SupportExplicit : Finset ℕ :=
  ([1054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part009 : ℚ :=
  (1049019803 : ℚ) / 884912947200

def SurrogateDiagonalTailChunk000Sub000Block024Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1054
    = surrogateDiagTailX0RatChunk000Sub000Block024Part009

theorem surrogateDiagonalTailChunk000Sub000Block024Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part009] using hcert

def TailChunk000Sub000Block024Part010SupportExplicit : Finset ℕ :=
  ([1055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part010 : ℚ :=
  (3173239 : ℚ) / 14408881200

def SurrogateDiagonalTailChunk000Sub000Block024Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1055
    = surrogateDiagTailX0RatChunk000Sub000Block024Part010

theorem surrogateDiagonalTailChunk000Sub000Block024Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part010] using hcert

def TailChunk000Sub000Block024Part011SupportExplicit : Finset ℕ :=
  ([1057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part011 : ℚ :=
  (9807473407 : ℚ) / 65623122000000

def SurrogateDiagonalTailChunk000Sub000Block024Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1057
    = surrogateDiagTailX0RatChunk000Sub000Block024Part011

theorem surrogateDiagonalTailChunk000Sub000Block024Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part011] using hcert

def TailChunk000Sub000Block024Part012SupportExplicit : Finset ℕ :=
  ([1059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part012 : ℚ :=
  (9181893775 : ℚ) / 27918675738624

def SurrogateDiagonalTailChunk000Sub000Block024Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1059
    = surrogateDiagTailX0RatChunk000Sub000Block024Part012

theorem surrogateDiagonalTailChunk000Sub000Block024Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part012] using hcert

def TailChunk000Sub000Block024Part013SupportExplicit : Finset ℕ :=
  ([1061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part013 : ℚ :=
  (5625227837 : ℚ) / 63136472769600

def SurrogateDiagonalTailChunk000Sub000Block024Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1061
    = surrogateDiagTailX0RatChunk000Sub000Block024Part013

theorem surrogateDiagonalTailChunk000Sub000Block024Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part013] using hcert

def TailChunk000Sub000Block024Part014SupportExplicit : Finset ℕ :=
  ([1063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part014 : ℚ :=
  (176416410125 : ℚ) / 1590358118442084

def SurrogateDiagonalTailChunk000Sub000Block024Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1063
    = surrogateDiagTailX0RatChunk000Sub000Block024Part014

theorem surrogateDiagonalTailChunk000Sub000Block024Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part014] using hcert

def TailChunk000Sub000Block024Part015SupportExplicit : Finset ℕ :=
  ([1065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part015 : ℚ :=
  (3565700483 : ℚ) / 4918231449600

def SurrogateDiagonalTailChunk000Sub000Block024Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1065
    = surrogateDiagTailX0RatChunk000Sub000Block024Part015

theorem surrogateDiagonalTailChunk000Sub000Block024Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part015] using hcert

def TailChunk000Sub000Block024Part016SupportExplicit : Finset ℕ :=
  ([1066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part016 : ℚ :=
  (5783752183 : ℚ) / 5309477683200

def SurrogateDiagonalTailChunk000Sub000Block024Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1066
    = surrogateDiagTailX0RatChunk000Sub000Block024Part016

theorem surrogateDiagonalTailChunk000Sub000Block024Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part016] using hcert

def TailChunk000Sub000Block024Part017SupportExplicit : Finset ℕ :=
  ([1067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part017 : ℚ :=
  (12729131641 : ℚ) / 84951642931200

def SurrogateDiagonalTailChunk000Sub000Block024Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1067
    = surrogateDiagTailX0RatChunk000Sub000Block024Part017

theorem surrogateDiagonalTailChunk000Sub000Block024Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part017] using hcert

def TailChunk000Sub000Block024Part018SupportExplicit : Finset ℕ :=
  ([1069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part018 : ℚ :=
  (178413561125 : ℚ) / 1626604142497344

def SurrogateDiagonalTailChunk000Sub000Block024Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1069
    = surrogateDiagTailX0RatChunk000Sub000Block024Part018

theorem surrogateDiagonalTailChunk000Sub000Block024Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part018] using hcert

def TailChunk000Sub000Block024Part019SupportExplicit : Finset ℕ :=
  ([1070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part019 : ℚ :=
  (129074340775 : ℚ) / 80814685145088

def SurrogateDiagonalTailChunk000Sub000Block024Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1070
    = surrogateDiagTailX0RatChunk000Sub000Block024Part019

theorem surrogateDiagonalTailChunk000Sub000Block024Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part019] using hcert

def TailChunk000Sub000Block024Part020SupportExplicit : Finset ℕ :=
  ([1073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part020 : ℚ :=
  (48084594175 : ℚ) / 368783046180864

def SurrogateDiagonalTailChunk000Sub000Block024Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1073
    = surrogateDiagTailX0RatChunk000Sub000Block024Part020

theorem surrogateDiagonalTailChunk000Sub000Block024Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part020] using hcert

def TailChunk000Sub000Block024Part021SupportExplicit : Finset ℕ :=
  ([1074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part021 : ℚ :=
  (109556944075 : ℚ) / 40163065246848

def SurrogateDiagonalTailChunk000Sub000Block024Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1074
    = surrogateDiagTailX0RatChunk000Sub000Block024Part021

theorem surrogateDiagonalTailChunk000Sub000Block024Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part021] using hcert

def TailChunk000Sub000Block024Part022SupportExplicit : Finset ℕ :=
  ([1077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part022 : ℚ :=
  (104462666975 : ℚ) / 328585921963584

def SurrogateDiagonalTailChunk000Sub000Block024Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1077
    = surrogateDiagTailX0RatChunk000Sub000Block024Part022

theorem surrogateDiagonalTailChunk000Sub000Block024Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part022] using hcert

def TailChunk000Sub000Block024Part023SupportExplicit : Finset ℕ :=
  ([1079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part023 : ℚ :=
  (54910430125 : ℚ) / 390711327280128

def SurrogateDiagonalTailChunk000Sub000Block024Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1079
    = surrogateDiagTailX0RatChunk000Sub000Block024Part023

theorem surrogateDiagonalTailChunk000Sub000Block024Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part023] using hcert

def TailChunk000Sub000Block024Part024SupportExplicit : Finset ℕ :=
  ([1081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block024Part024 : ℚ :=
  (340173615475 : ℚ) / 2622701767306368

def SurrogateDiagonalTailChunk000Sub000Block024Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1081
    = surrogateDiagTailX0RatChunk000Sub000Block024Part024

theorem surrogateDiagonalTailChunk000Sub000Block024Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block024Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block024Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block024Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block024Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block024Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block024Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block024HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block024Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block024Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block024Part000
    + surrogateDiagTailX0RatChunk000Sub000Block024Part001
    + surrogateDiagTailX0RatChunk000Sub000Block024Part002
    + surrogateDiagTailX0RatChunk000Sub000Block024Part003
    + surrogateDiagTailX0RatChunk000Sub000Block024Part004
    + surrogateDiagTailX0RatChunk000Sub000Block024Part005
    + surrogateDiagTailX0RatChunk000Sub000Block024Part006
    + surrogateDiagTailX0RatChunk000Sub000Block024Part007
    + surrogateDiagTailX0RatChunk000Sub000Block024Part008
    + surrogateDiagTailX0RatChunk000Sub000Block024Part009

def surrogateDiagonalTailChunk000Sub000Block024MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block024Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block024Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block024Part010
    + surrogateDiagTailX0RatChunk000Sub000Block024Part011
    + surrogateDiagTailX0RatChunk000Sub000Block024Part012
    + surrogateDiagTailX0RatChunk000Sub000Block024Part013
    + surrogateDiagTailX0RatChunk000Sub000Block024Part014
    + surrogateDiagTailX0RatChunk000Sub000Block024Part015
    + surrogateDiagTailX0RatChunk000Sub000Block024Part016
    + surrogateDiagTailX0RatChunk000Sub000Block024Part017
    + surrogateDiagTailX0RatChunk000Sub000Block024Part018
    + surrogateDiagTailX0RatChunk000Sub000Block024Part019

def surrogateDiagonalTailChunk000Sub000Block024TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block024Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block024Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block024Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block024Part020
    + surrogateDiagTailX0RatChunk000Sub000Block024Part021
    + surrogateDiagTailX0RatChunk000Sub000Block024Part022
    + surrogateDiagTailX0RatChunk000Sub000Block024Part023
    + surrogateDiagTailX0RatChunk000Sub000Block024Part024

def surrogateDiagonalTailChunk000Sub000Block024Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block024HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block024MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block024TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block024 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block024Part000
    + surrogateDiagTailX0RatChunk000Sub000Block024Part001
    + surrogateDiagTailX0RatChunk000Sub000Block024Part002
    + surrogateDiagTailX0RatChunk000Sub000Block024Part003
    + surrogateDiagTailX0RatChunk000Sub000Block024Part004
    + surrogateDiagTailX0RatChunk000Sub000Block024Part005
    + surrogateDiagTailX0RatChunk000Sub000Block024Part006
    + surrogateDiagTailX0RatChunk000Sub000Block024Part007
    + surrogateDiagTailX0RatChunk000Sub000Block024Part008
    + surrogateDiagTailX0RatChunk000Sub000Block024Part009
    + surrogateDiagTailX0RatChunk000Sub000Block024Part010
    + surrogateDiagTailX0RatChunk000Sub000Block024Part011
    + surrogateDiagTailX0RatChunk000Sub000Block024Part012
    + surrogateDiagTailX0RatChunk000Sub000Block024Part013
    + surrogateDiagTailX0RatChunk000Sub000Block024Part014
    + surrogateDiagTailX0RatChunk000Sub000Block024Part015
    + surrogateDiagTailX0RatChunk000Sub000Block024Part016
    + surrogateDiagTailX0RatChunk000Sub000Block024Part017
    + surrogateDiagTailX0RatChunk000Sub000Block024Part018
    + surrogateDiagTailX0RatChunk000Sub000Block024Part019
    + surrogateDiagTailX0RatChunk000Sub000Block024Part020
    + surrogateDiagTailX0RatChunk000Sub000Block024Part021
    + surrogateDiagTailX0RatChunk000Sub000Block024Part022
    + surrogateDiagTailX0RatChunk000Sub000Block024Part023
    + surrogateDiagTailX0RatChunk000Sub000Block024Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block024_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block024Head + surrogateDiagTailX0RatChunk000Sub000Block024Mid + surrogateDiagTailX0RatChunk000Sub000Block024Tail =
      surrogateDiagTailX0RatChunk000Sub000Block024 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block024Head surrogateDiagTailX0RatChunk000Sub000Block024Mid surrogateDiagTailX0RatChunk000Sub000Block024Tail surrogateDiagTailX0RatChunk000Sub000Block024
  ring

def SurrogateDiagonalTailChunk000Sub000Block024HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block024HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block024Head

def SurrogateDiagonalTailChunk000Sub000Block024MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block024MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block024Mid

def SurrogateDiagonalTailChunk000Sub000Block024TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block024TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block024Tail

theorem surrogateDiagonalTailChunk000Sub000Block024_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block024HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block024MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block024TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block024Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block024 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block024HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block024MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block024TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block024Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block024_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
