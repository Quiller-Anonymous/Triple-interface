import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [74,75). -/

/- Block 074 covers tail-support indices [1850,1875) and q from 3093 to 3130. -/

def TailChunk000Sub000Block074Part000SupportExplicit : Finset ℕ :=
  ([3093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part000 : ℚ :=
  (5841007193 : ℚ) / 360234851763840

def SurrogateDiagonalTailChunk000Sub000Block074Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3093
    = surrogateDiagTailX0RatChunk000Sub000Block074Part000

theorem surrogateDiagonalTailChunk000Sub000Block074Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part000] using hcert

def TailChunk000Sub000Block074Part001SupportExplicit : Finset ℕ :=
  ([3094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part001 : ℚ :=
  (171209903975 : ℚ) / 2201946584776704

def SurrogateDiagonalTailChunk000Sub000Block074Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3094
    = surrogateDiagTailX0RatChunk000Sub000Block074Part001

theorem surrogateDiagonalTailChunk000Sub000Block074Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part001] using hcert

def TailChunk000Sub000Block074Part002SupportExplicit : Finset ℕ :=
  ([3095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part002 : ℚ :=
  (908480754175 : ℚ) / 93372873577187328

def SurrogateDiagonalTailChunk000Sub000Block074Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3095
    = surrogateDiagTailX0RatChunk000Sub000Block074Part002

theorem surrogateDiagonalTailChunk000Sub000Block074Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part002] using hcert

def TailChunk000Sub000Block074Part003SupportExplicit : Finset ℕ :=
  ([3097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part003 : ℚ :=
  (558117815225 : ℚ) / 90395527164254784

def SurrogateDiagonalTailChunk000Sub000Block074Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3097
    = surrogateDiagTailX0RatChunk000Sub000Block074Part003

theorem surrogateDiagonalTailChunk000Sub000Block074Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part003] using hcert

def TailChunk000Sub000Block074Part004SupportExplicit : Finset ℕ :=
  ([3098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part004 : ℚ :=
  (299745169925 : ℚ) / 7179276643735104

def SurrogateDiagonalTailChunk000Sub000Block074Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3098
    = surrogateDiagTailX0RatChunk000Sub000Block074Part004

theorem surrogateDiagonalTailChunk000Sub000Block074Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part004] using hcert

def TailChunk000Sub000Block074Part005SupportExplicit : Finset ℕ :=
  ([3099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part005 : ℚ :=
  (466652663425 : ℚ) / 45380119032004608

def SurrogateDiagonalTailChunk000Sub000Block074Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3099
    = surrogateDiagTailX0RatChunk000Sub000Block074Part005

theorem surrogateDiagonalTailChunk000Sub000Block074Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part005] using hcert

def TailChunk000Sub000Block074Part006SupportExplicit : Finset ℕ :=
  ([3101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part006 : ℚ :=
  (140904163525 : ℚ) / 30921527990744352

def SurrogateDiagonalTailChunk000Sub000Block074Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3101
    = surrogateDiagTailX0RatChunk000Sub000Block074Part006

theorem surrogateDiagonalTailChunk000Sub000Block074Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part006] using hcert

def TailChunk000Sub000Block074Part007SupportExplicit : Finset ℕ :=
  ([3102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part007 : ℚ :=
  (719374803 : ℚ) / 4776908257280

def SurrogateDiagonalTailChunk000Sub000Block074Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3102
    = surrogateDiagTailX0RatChunk000Sub000Block074Part007

theorem surrogateDiagonalTailChunk000Sub000Block074Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part007] using hcert

def TailChunk000Sub000Block074Part008SupportExplicit : Finset ℕ :=
  ([3103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part008 : ℚ :=
  (1724833825 : ℚ) / 565702796015616

def SurrogateDiagonalTailChunk000Sub000Block074Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3103
    = surrogateDiagTailX0RatChunk000Sub000Block074Part008

theorem surrogateDiagonalTailChunk000Sub000Block074Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part008] using hcert

def TailChunk000Sub000Block074Part009SupportExplicit : Finset ℕ :=
  ([3106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part009 : ℚ :=
  (301295239325 : ℚ) / 7253769163259904

def SurrogateDiagonalTailChunk000Sub000Block074Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3106
    = surrogateDiagTailX0RatChunk000Sub000Block074Part009

theorem surrogateDiagonalTailChunk000Sub000Block074Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part009] using hcert

def TailChunk000Sub000Block074Part010SupportExplicit : Finset ℕ :=
  ([3107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part010 : ℚ :=
  (1087242723925 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk000Sub000Block074Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3107
    = surrogateDiagTailX0RatChunk000Sub000Block074Part010

theorem surrogateDiagonalTailChunk000Sub000Block074Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part010] using hcert

def TailChunk000Sub000Block074Part011SupportExplicit : Finset ℕ :=
  ([3109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part011 : ℚ :=
  (1207993477975 : ℚ) / 233319426036536448

def SurrogateDiagonalTailChunk000Sub000Block074Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3109
    = surrogateDiagTailX0RatChunk000Sub000Block074Part011

theorem surrogateDiagonalTailChunk000Sub000Block074Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part011] using hcert

def TailChunk000Sub000Block074Part012SupportExplicit : Finset ℕ :=
  ([3110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part012 : ℚ :=
  (980535261 : ℚ) / 15764577351680

def SurrogateDiagonalTailChunk000Sub000Block074Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3110
    = surrogateDiagTailX0RatChunk000Sub000Block074Part012

theorem surrogateDiagonalTailChunk000Sub000Block074Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part012] using hcert

def TailChunk000Sub000Block074Part013SupportExplicit : Finset ℕ :=
  ([3111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part013 : ℚ :=
  (12406377701 : ℚ) / 679613143449600

def SurrogateDiagonalTailChunk000Sub000Block074Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3111
    = surrogateDiagTailX0RatChunk000Sub000Block074Part013

theorem surrogateDiagonalTailChunk000Sub000Block074Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part013] using hcert

def TailChunk000Sub000Block074Part014SupportExplicit : Finset ℕ :=
  ([3113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part014 : ℚ :=
  (319077869 : ℚ) / 46854306587520

def SurrogateDiagonalTailChunk000Sub000Block074Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3113
    = surrogateDiagTailX0RatChunk000Sub000Block074Part014

theorem surrogateDiagonalTailChunk000Sub000Block074Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part014] using hcert

def TailChunk000Sub000Block074Part015SupportExplicit : Finset ℕ :=
  ([3115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part015 : ℚ :=
  (47418908575 : ℚ) / 3109442510389248

def SurrogateDiagonalTailChunk000Sub000Block074Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3115
    = surrogateDiagTailX0RatChunk000Sub000Block074Part015

theorem surrogateDiagonalTailChunk000Sub000Block074Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part015] using hcert

def TailChunk000Sub000Block074Part016SupportExplicit : Finset ℕ :=
  ([3117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part016 : ℚ :=
  (741501966925 : ℚ) / 46444710010025088

def SurrogateDiagonalTailChunk000Sub000Block074Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3117
    = surrogateDiagTailX0RatChunk000Sub000Block074Part016

theorem surrogateDiagonalTailChunk000Sub000Block074Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part016] using hcert

def TailChunk000Sub000Block074Part017SupportExplicit : Finset ℕ :=
  ([3118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part017 : ℚ :=
  (151844300475 : ℚ) / 4911062006411416

def SurrogateDiagonalTailChunk000Sub000Block074Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3118
    = surrogateDiagTailX0RatChunk000Sub000Block074Part017

theorem surrogateDiagonalTailChunk000Sub000Block074Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part017] using hcert

def TailChunk000Sub000Block074Part018SupportExplicit : Finset ℕ :=
  ([3119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part018 : ℚ :=
  (152002515625 : ℚ) / 59084193389392722

def SurrogateDiagonalTailChunk000Sub000Block074Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3119
    = surrogateDiagTailX0RatChunk000Sub000Block074Part018

theorem surrogateDiagonalTailChunk000Sub000Block074Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part018] using hcert

def TailChunk000Sub000Block074Part019SupportExplicit : Finset ℕ :=
  ([3121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part019 : ℚ :=
  (243516025 : ℚ) / 94777495068672

def SurrogateDiagonalTailChunk000Sub000Block074Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3121
    = surrogateDiagTailX0RatChunk000Sub000Block074Part019

theorem surrogateDiagonalTailChunk000Sub000Block074Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part019] using hcert

def TailChunk000Sub000Block074Part020SupportExplicit : Finset ℕ :=
  ([3122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part020 : ℚ :=
  (196568128325 : ℚ) / 3935625470420544

def SurrogateDiagonalTailChunk000Sub000Block074Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3122
    = surrogateDiagTailX0RatChunk000Sub000Block074Part020

theorem surrogateDiagonalTailChunk000Sub000Block074Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part020] using hcert

def TailChunk000Sub000Block074Part021SupportExplicit : Finset ℕ :=
  ([3126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part021 : ℚ :=
  (3724846627 : ℚ) / 29252313292800

def SurrogateDiagonalTailChunk000Sub000Block074Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3126
    = surrogateDiagTailX0RatChunk000Sub000Block074Part021

theorem surrogateDiagonalTailChunk000Sub000Block074Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part021] using hcert

def TailChunk000Sub000Block074Part022SupportExplicit : Finset ℕ :=
  ([3127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part022 : ℚ :=
  (1170717137425 : ℚ) / 206896053980448768

def SurrogateDiagonalTailChunk000Sub000Block074Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3127
    = surrogateDiagTailX0RatChunk000Sub000Block074Part022

theorem surrogateDiagonalTailChunk000Sub000Block074Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part022] using hcert

def TailChunk000Sub000Block074Part023SupportExplicit : Finset ℕ :=
  ([3129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part023 : ℚ :=
  (622615365925 : ℚ) / 24877040010559488

def SurrogateDiagonalTailChunk000Sub000Block074Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3129
    = surrogateDiagTailX0RatChunk000Sub000Block074Part023

theorem surrogateDiagonalTailChunk000Sub000Block074Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part023] using hcert

def TailChunk000Sub000Block074Part024SupportExplicit : Finset ℕ :=
  ([3130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block074Part024 : ℚ :=
  (372444405625 : ℚ) / 6065759684395008

def SurrogateDiagonalTailChunk000Sub000Block074Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3130
    = surrogateDiagTailX0RatChunk000Sub000Block074Part024

theorem surrogateDiagonalTailChunk000Sub000Block074Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block074Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block074Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block074Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block074Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block074Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block074Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block074HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block074Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block074Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block074Part000
    + surrogateDiagTailX0RatChunk000Sub000Block074Part001
    + surrogateDiagTailX0RatChunk000Sub000Block074Part002
    + surrogateDiagTailX0RatChunk000Sub000Block074Part003
    + surrogateDiagTailX0RatChunk000Sub000Block074Part004
    + surrogateDiagTailX0RatChunk000Sub000Block074Part005
    + surrogateDiagTailX0RatChunk000Sub000Block074Part006
    + surrogateDiagTailX0RatChunk000Sub000Block074Part007
    + surrogateDiagTailX0RatChunk000Sub000Block074Part008
    + surrogateDiagTailX0RatChunk000Sub000Block074Part009

def surrogateDiagonalTailChunk000Sub000Block074MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block074Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block074Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block074Part010
    + surrogateDiagTailX0RatChunk000Sub000Block074Part011
    + surrogateDiagTailX0RatChunk000Sub000Block074Part012
    + surrogateDiagTailX0RatChunk000Sub000Block074Part013
    + surrogateDiagTailX0RatChunk000Sub000Block074Part014
    + surrogateDiagTailX0RatChunk000Sub000Block074Part015
    + surrogateDiagTailX0RatChunk000Sub000Block074Part016
    + surrogateDiagTailX0RatChunk000Sub000Block074Part017
    + surrogateDiagTailX0RatChunk000Sub000Block074Part018
    + surrogateDiagTailX0RatChunk000Sub000Block074Part019

def surrogateDiagonalTailChunk000Sub000Block074TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block074Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block074Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block074Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block074Part020
    + surrogateDiagTailX0RatChunk000Sub000Block074Part021
    + surrogateDiagTailX0RatChunk000Sub000Block074Part022
    + surrogateDiagTailX0RatChunk000Sub000Block074Part023
    + surrogateDiagTailX0RatChunk000Sub000Block074Part024

def surrogateDiagonalTailChunk000Sub000Block074Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block074HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block074MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block074TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block074 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block074Part000
    + surrogateDiagTailX0RatChunk000Sub000Block074Part001
    + surrogateDiagTailX0RatChunk000Sub000Block074Part002
    + surrogateDiagTailX0RatChunk000Sub000Block074Part003
    + surrogateDiagTailX0RatChunk000Sub000Block074Part004
    + surrogateDiagTailX0RatChunk000Sub000Block074Part005
    + surrogateDiagTailX0RatChunk000Sub000Block074Part006
    + surrogateDiagTailX0RatChunk000Sub000Block074Part007
    + surrogateDiagTailX0RatChunk000Sub000Block074Part008
    + surrogateDiagTailX0RatChunk000Sub000Block074Part009
    + surrogateDiagTailX0RatChunk000Sub000Block074Part010
    + surrogateDiagTailX0RatChunk000Sub000Block074Part011
    + surrogateDiagTailX0RatChunk000Sub000Block074Part012
    + surrogateDiagTailX0RatChunk000Sub000Block074Part013
    + surrogateDiagTailX0RatChunk000Sub000Block074Part014
    + surrogateDiagTailX0RatChunk000Sub000Block074Part015
    + surrogateDiagTailX0RatChunk000Sub000Block074Part016
    + surrogateDiagTailX0RatChunk000Sub000Block074Part017
    + surrogateDiagTailX0RatChunk000Sub000Block074Part018
    + surrogateDiagTailX0RatChunk000Sub000Block074Part019
    + surrogateDiagTailX0RatChunk000Sub000Block074Part020
    + surrogateDiagTailX0RatChunk000Sub000Block074Part021
    + surrogateDiagTailX0RatChunk000Sub000Block074Part022
    + surrogateDiagTailX0RatChunk000Sub000Block074Part023
    + surrogateDiagTailX0RatChunk000Sub000Block074Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block074_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block074Head + surrogateDiagTailX0RatChunk000Sub000Block074Mid + surrogateDiagTailX0RatChunk000Sub000Block074Tail =
      surrogateDiagTailX0RatChunk000Sub000Block074 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block074Head surrogateDiagTailX0RatChunk000Sub000Block074Mid surrogateDiagTailX0RatChunk000Sub000Block074Tail surrogateDiagTailX0RatChunk000Sub000Block074
  ring

def SurrogateDiagonalTailChunk000Sub000Block074HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block074HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block074Head

def SurrogateDiagonalTailChunk000Sub000Block074MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block074MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block074Mid

def SurrogateDiagonalTailChunk000Sub000Block074TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block074TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block074Tail

theorem surrogateDiagonalTailChunk000Sub000Block074_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block074HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block074MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block074TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block074Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block074 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block074HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block074MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block074TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block074Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block074_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
