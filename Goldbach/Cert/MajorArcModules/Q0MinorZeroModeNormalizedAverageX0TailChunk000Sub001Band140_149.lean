import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [140,150). -/

/-- Block 140 covers tail-support indices [8500,8525) and q from 14038 to 14081. -/

def TailChunk000Sub001Block140Part000SupportExplicit : Finset ℕ :=
  ([14038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block140Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14038
    = surrogateDiagTailX0RatChunk000Sub001Block140Part000

theorem surrogateDiagonalTailChunk000Sub001Block140Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part000] using hcert

def TailChunk000Sub001Block140Part001SupportExplicit : Finset ℕ :=
  ([14039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part001 : ℚ :=
  (592815269 : ℚ) / 725492941574400000

def SurrogateDiagonalTailChunk000Sub001Block140Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14039
    = surrogateDiagTailX0RatChunk000Sub001Block140Part001

theorem surrogateDiagonalTailChunk000Sub001Block140Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part001] using hcert

def TailChunk000Sub001Block140Part002SupportExplicit : Finset ℕ :=
  ([14041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part002 : ℚ :=
  (9022888375 : ℚ) / 2883889145570534784

def SurrogateDiagonalTailChunk000Sub001Block140Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14041
    = surrogateDiagTailX0RatChunk000Sub001Block140Part002

theorem surrogateDiagonalTailChunk000Sub001Block140Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part002] using hcert

def TailChunk000Sub001Block140Part003SupportExplicit : Finset ℕ :=
  ([14042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part003 : ℚ :=
  (14959087625 : ℚ) / 89014345131884544

def SurrogateDiagonalTailChunk000Sub001Block140Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14042
    = surrogateDiagTailX0RatChunk000Sub001Block140Part003

theorem surrogateDiagonalTailChunk000Sub001Block140Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part003] using hcert

def TailChunk000Sub001Block140Part004SupportExplicit : Finset ℕ :=
  ([14043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part004 : ℚ :=
  (11005937897 : ℚ) / 131246244000000000

def SurrogateDiagonalTailChunk000Sub001Block140Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14043
    = surrogateDiagTailX0RatChunk000Sub001Block140Part004

theorem surrogateDiagonalTailChunk000Sub001Block140Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part004] using hcert

def TailChunk000Sub001Block140Part005SupportExplicit : Finset ℕ :=
  ([14046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part005 : ℚ :=
  (13698760019 : ℚ) / 23990553439257600

def SurrogateDiagonalTailChunk000Sub001Block140Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14046
    = surrogateDiagTailX0RatChunk000Sub001Block140Part005

theorem surrogateDiagonalTailChunk000Sub001Block140Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part005] using hcert

def TailChunk000Sub001Block140Part006SupportExplicit : Finset ℕ :=
  ([14047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part006 : ℚ :=
  (5465693367 : ℚ) / 883829092797798400

def SurrogateDiagonalTailChunk000Sub001Block140Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14047
    = surrogateDiagTailX0RatChunk000Sub001Block140Part006

theorem surrogateDiagonalTailChunk000Sub001Block140Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part006] using hcert

def TailChunk000Sub001Block140Part007SupportExplicit : Finset ℕ :=
  ([14051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block140Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14051
    = surrogateDiagTailX0RatChunk000Sub001Block140Part007

theorem surrogateDiagonalTailChunk000Sub001Block140Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part007] using hcert

def TailChunk000Sub001Block140Part008SupportExplicit : Finset ℕ :=
  ([14053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part008 : ℚ :=
  (187876006025 : ℚ) / 18128114615621615616

def SurrogateDiagonalTailChunk000Sub001Block140Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14053
    = surrogateDiagTailX0RatChunk000Sub001Block140Part008

theorem surrogateDiagonalTailChunk000Sub001Block140Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part008] using hcert

def TailChunk000Sub001Block140Part009SupportExplicit : Finset ℕ :=
  ([14054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block140Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14054
    = surrogateDiagTailX0RatChunk000Sub001Block140Part009

theorem surrogateDiagonalTailChunk000Sub001Block140Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part009] using hcert

def TailChunk000Sub001Block140Part010SupportExplicit : Finset ℕ :=
  ([14055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part010 : ℚ :=
  (356511512275 : ℚ) / 1965306137743982592

def SurrogateDiagonalTailChunk000Sub001Block140Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14055
    = surrogateDiagTailX0RatChunk000Sub001Block140Part010

theorem surrogateDiagonalTailChunk000Sub001Block140Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part010] using hcert

def TailChunk000Sub001Block140Part011SupportExplicit : Finset ℕ :=
  ([14057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block140Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14057
    = surrogateDiagTailX0RatChunk000Sub001Block140Part011

theorem surrogateDiagonalTailChunk000Sub001Block140Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part011] using hcert

def TailChunk000Sub001Block140Part012SupportExplicit : Finset ℕ :=
  ([14059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part012 : ℚ :=
  (43432681125 : ℚ) / 12713810337356054528

def SurrogateDiagonalTailChunk000Sub001Block140Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14059
    = surrogateDiagTailX0RatChunk000Sub001Block140Part012

theorem surrogateDiagonalTailChunk000Sub001Block140Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part012] using hcert

def TailChunk000Sub001Block140Part013SupportExplicit : Finset ℕ :=
  ([14061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part013 : ℚ :=
  (153096968975 : ℚ) / 1881899884660948992

def SurrogateDiagonalTailChunk000Sub001Block140Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14061
    = surrogateDiagTailX0RatChunk000Sub001Block140Part013

theorem surrogateDiagonalTailChunk000Sub001Block140Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part013] using hcert

def TailChunk000Sub001Block140Part014SupportExplicit : Finset ℕ :=
  ([14062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part014 : ℚ :=
  (2863362625 : ℚ) / 308363845622317056

def SurrogateDiagonalTailChunk000Sub001Block140Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14062
    = surrogateDiagTailX0RatChunk000Sub001Block140Part014

theorem surrogateDiagonalTailChunk000Sub001Block140Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part014] using hcert

def TailChunk000Sub001Block140Part015SupportExplicit : Finset ℕ :=
  ([14065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part015 : ℚ :=
  (1061306729275 : ℚ) / 33418263704012587008

def SurrogateDiagonalTailChunk000Sub001Block140Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14065
    = surrogateDiagTailX0RatChunk000Sub001Block140Part015

theorem surrogateDiagonalTailChunk000Sub001Block140Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part015] using hcert

def TailChunk000Sub001Block140Part016SupportExplicit : Finset ℕ :=
  ([14066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part016 : ℚ :=
  (6700586659 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub001Block140Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14066
    = surrogateDiagTailX0RatChunk000Sub001Block140Part016

theorem surrogateDiagonalTailChunk000Sub001Block140Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part016] using hcert

def TailChunk000Sub001Block140Part017SupportExplicit : Finset ℕ :=
  ([14069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part017 : ℚ :=
  (16448129389 : ℚ) / 2668150147980931200

def SurrogateDiagonalTailChunk000Sub001Block140Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14069
    = surrogateDiagTailX0RatChunk000Sub001Block140Part017

theorem surrogateDiagonalTailChunk000Sub001Block140Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part017] using hcert

def TailChunk000Sub001Block140Part018SupportExplicit : Finset ℕ :=
  ([14070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part018 : ℚ :=
  (215018890525 : ℚ) / 83954947780509696

def SurrogateDiagonalTailChunk000Sub001Block140Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14070
    = surrogateDiagTailX0RatChunk000Sub001Block140Part018

theorem surrogateDiagonalTailChunk000Sub001Block140Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part018] using hcert

def TailChunk000Sub001Block140Part019SupportExplicit : Finset ℕ :=
  ([14071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block140Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14071
    = surrogateDiagTailX0RatChunk000Sub001Block140Part019

theorem surrogateDiagonalTailChunk000Sub001Block140Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part019] using hcert

def TailChunk000Sub001Block140Part020SupportExplicit : Finset ℕ :=
  ([14073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part020 : ℚ :=
  (785932183 : ℚ) / 11061146991840960

def SurrogateDiagonalTailChunk000Sub001Block140Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14073
    = surrogateDiagTailX0RatChunk000Sub001Block140Part020

theorem surrogateDiagonalTailChunk000Sub001Block140Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part020] using hcert

def TailChunk000Sub001Block140Part021SupportExplicit : Finset ℕ :=
  ([14074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part021 : ℚ :=
  (3171691567 : ℚ) / 211351641731971200

def SurrogateDiagonalTailChunk000Sub001Block140Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14074
    = surrogateDiagTailX0RatChunk000Sub001Block140Part021

theorem surrogateDiagonalTailChunk000Sub001Block140Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part021] using hcert

def TailChunk000Sub001Block140Part022SupportExplicit : Finset ℕ :=
  ([14077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part022 : ℚ :=
  (562289161 : ℚ) / 39181613979844800

def SurrogateDiagonalTailChunk000Sub001Block140Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14077
    = surrogateDiagTailX0RatChunk000Sub001Block140Part022

theorem surrogateDiagonalTailChunk000Sub001Block140Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part022] using hcert

def TailChunk000Sub001Block140Part023SupportExplicit : Finset ℕ :=
  ([14078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block140Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14078
    = surrogateDiagTailX0RatChunk000Sub001Block140Part023

theorem surrogateDiagonalTailChunk000Sub001Block140Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part023] using hcert

def TailChunk000Sub001Block140Part024SupportExplicit : Finset ℕ :=
  ([14081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block140Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block140Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14081
    = surrogateDiagTailX0RatChunk000Sub001Block140Part024

theorem surrogateDiagonalTailChunk000Sub001Block140Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block140Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block140Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block140Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block140Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block140Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block140Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block140HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block140Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block140Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block140Part000
    + surrogateDiagTailX0RatChunk000Sub001Block140Part001
    + surrogateDiagTailX0RatChunk000Sub001Block140Part002
    + surrogateDiagTailX0RatChunk000Sub001Block140Part003
    + surrogateDiagTailX0RatChunk000Sub001Block140Part004
    + surrogateDiagTailX0RatChunk000Sub001Block140Part005
    + surrogateDiagTailX0RatChunk000Sub001Block140Part006
    + surrogateDiagTailX0RatChunk000Sub001Block140Part007
    + surrogateDiagTailX0RatChunk000Sub001Block140Part008
    + surrogateDiagTailX0RatChunk000Sub001Block140Part009

def surrogateDiagonalTailChunk000Sub001Block140MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block140Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block140Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block140Part010
    + surrogateDiagTailX0RatChunk000Sub001Block140Part011
    + surrogateDiagTailX0RatChunk000Sub001Block140Part012
    + surrogateDiagTailX0RatChunk000Sub001Block140Part013
    + surrogateDiagTailX0RatChunk000Sub001Block140Part014
    + surrogateDiagTailX0RatChunk000Sub001Block140Part015
    + surrogateDiagTailX0RatChunk000Sub001Block140Part016
    + surrogateDiagTailX0RatChunk000Sub001Block140Part017
    + surrogateDiagTailX0RatChunk000Sub001Block140Part018
    + surrogateDiagTailX0RatChunk000Sub001Block140Part019

def surrogateDiagonalTailChunk000Sub001Block140TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block140Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block140Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block140Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block140Part020
    + surrogateDiagTailX0RatChunk000Sub001Block140Part021
    + surrogateDiagTailX0RatChunk000Sub001Block140Part022
    + surrogateDiagTailX0RatChunk000Sub001Block140Part023
    + surrogateDiagTailX0RatChunk000Sub001Block140Part024

def surrogateDiagonalTailChunk000Sub001Block140Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block140HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block140MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block140TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block140 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block140Part000
    + surrogateDiagTailX0RatChunk000Sub001Block140Part001
    + surrogateDiagTailX0RatChunk000Sub001Block140Part002
    + surrogateDiagTailX0RatChunk000Sub001Block140Part003
    + surrogateDiagTailX0RatChunk000Sub001Block140Part004
    + surrogateDiagTailX0RatChunk000Sub001Block140Part005
    + surrogateDiagTailX0RatChunk000Sub001Block140Part006
    + surrogateDiagTailX0RatChunk000Sub001Block140Part007
    + surrogateDiagTailX0RatChunk000Sub001Block140Part008
    + surrogateDiagTailX0RatChunk000Sub001Block140Part009
    + surrogateDiagTailX0RatChunk000Sub001Block140Part010
    + surrogateDiagTailX0RatChunk000Sub001Block140Part011
    + surrogateDiagTailX0RatChunk000Sub001Block140Part012
    + surrogateDiagTailX0RatChunk000Sub001Block140Part013
    + surrogateDiagTailX0RatChunk000Sub001Block140Part014
    + surrogateDiagTailX0RatChunk000Sub001Block140Part015
    + surrogateDiagTailX0RatChunk000Sub001Block140Part016
    + surrogateDiagTailX0RatChunk000Sub001Block140Part017
    + surrogateDiagTailX0RatChunk000Sub001Block140Part018
    + surrogateDiagTailX0RatChunk000Sub001Block140Part019
    + surrogateDiagTailX0RatChunk000Sub001Block140Part020
    + surrogateDiagTailX0RatChunk000Sub001Block140Part021
    + surrogateDiagTailX0RatChunk000Sub001Block140Part022
    + surrogateDiagTailX0RatChunk000Sub001Block140Part023
    + surrogateDiagTailX0RatChunk000Sub001Block140Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block140_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block140Head + surrogateDiagTailX0RatChunk000Sub001Block140Mid + surrogateDiagTailX0RatChunk000Sub001Block140Tail =
      surrogateDiagTailX0RatChunk000Sub001Block140 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block140Head surrogateDiagTailX0RatChunk000Sub001Block140Mid surrogateDiagTailX0RatChunk000Sub001Block140Tail surrogateDiagTailX0RatChunk000Sub001Block140
  ring

def SurrogateDiagonalTailChunk000Sub001Block140HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block140HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block140Head

def SurrogateDiagonalTailChunk000Sub001Block140MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block140MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block140Mid

def SurrogateDiagonalTailChunk000Sub001Block140TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block140TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block140Tail

theorem surrogateDiagonalTailChunk000Sub001Block140_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block140HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block140MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block140TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block140Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block140 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block140HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block140MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block140TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block140Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block140_eq_head_add_mid_add_tail

/-- Block 141 covers tail-support indices [8525,8550) and q from 14082 to 14118. -/

def TailChunk000Sub001Block141Part000SupportExplicit : Finset ℕ :=
  ([14082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part000 : ℚ :=
  (344225898725 : ℚ) / 605938959732354624

def SurrogateDiagonalTailChunk000Sub001Block141Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14082
    = surrogateDiagTailX0RatChunk000Sub001Block141Part000

theorem surrogateDiagonalTailChunk000Sub001Block141Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part000] using hcert

def TailChunk000Sub001Block141Part001SupportExplicit : Finset ℕ :=
  ([14083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block141Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14083
    = surrogateDiagTailX0RatChunk000Sub001Block141Part001

theorem surrogateDiagonalTailChunk000Sub001Block141Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part001] using hcert

def TailChunk000Sub001Block141Part002SupportExplicit : Finset ℕ :=
  ([14086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part002 : ℚ :=
  (775060140625 : ℚ) / 1537272826571506962

def SurrogateDiagonalTailChunk000Sub001Block141Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14086
    = surrogateDiagTailX0RatChunk000Sub001Block141Part002

theorem surrogateDiagonalTailChunk000Sub001Block141Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part002] using hcert

def TailChunk000Sub001Block141Part003SupportExplicit : Finset ℕ :=
  ([14087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block141Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14087
    = surrogateDiagTailX0RatChunk000Sub001Block141Part003

theorem surrogateDiagonalTailChunk000Sub001Block141Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part003] using hcert

def TailChunk000Sub001Block141Part004SupportExplicit : Finset ℕ :=
  ([14089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part004 : ℚ :=
  (81949006525 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk000Sub001Block141Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14089
    = surrogateDiagTailX0RatChunk000Sub001Block141Part004

theorem surrogateDiagonalTailChunk000Sub001Block141Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part004] using hcert

def TailChunk000Sub001Block141Part005SupportExplicit : Finset ℕ :=
  ([14090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part005 : ℚ :=
  (1177936111175 : ℚ) / 1257903854079442944

def SurrogateDiagonalTailChunk000Sub001Block141Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14090
    = surrogateDiagTailX0RatChunk000Sub001Block141Part005

theorem surrogateDiagonalTailChunk000Sub001Block141Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part005] using hcert

def TailChunk000Sub001Block141Part006SupportExplicit : Finset ℕ :=
  ([14091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part006 : ℚ :=
  (53292861961 : ℚ) / 268792307712000000

def SurrogateDiagonalTailChunk000Sub001Block141Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14091
    = surrogateDiagTailX0RatChunk000Sub001Block141Part006

theorem surrogateDiagonalTailChunk000Sub001Block141Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part006] using hcert

def TailChunk000Sub001Block141Part007SupportExplicit : Finset ℕ :=
  ([14093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part007 : ℚ :=
  (632452525 : ℚ) / 186049195117903872

def SurrogateDiagonalTailChunk000Sub001Block141Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14093
    = surrogateDiagTailX0RatChunk000Sub001Block141Part007

theorem surrogateDiagonalTailChunk000Sub001Block141Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part007] using hcert

def TailChunk000Sub001Block141Part008SupportExplicit : Finset ℕ :=
  ([14095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part008 : ℚ :=
  (993692251225 : ℚ) / 40367400111009712128

def SurrogateDiagonalTailChunk000Sub001Block141Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14095
    = surrogateDiagTailX0RatChunk000Sub001Block141Part008

theorem surrogateDiagonalTailChunk000Sub001Block141Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part008] using hcert

def TailChunk000Sub001Block141Part009SupportExplicit : Finset ℕ :=
  ([14097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part009 : ℚ :=
  (1384752630325 : ℚ) / 16937098961948540928

def SurrogateDiagonalTailChunk000Sub001Block141Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14097
    = surrogateDiagTailX0RatChunk000Sub001Block141Part009

theorem surrogateDiagonalTailChunk000Sub001Block141Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part009] using hcert

def TailChunk000Sub001Block141Part010SupportExplicit : Finset ℕ :=
  ([14098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part010 : ℚ :=
  (578811000175 : ℚ) / 621835145145556992

def SurrogateDiagonalTailChunk000Sub001Block141Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14098
    = surrogateDiagTailX0RatChunk000Sub001Block141Part010

theorem surrogateDiagonalTailChunk000Sub001Block141Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part010] using hcert

def TailChunk000Sub001Block141Part011SupportExplicit : Finset ℕ :=
  ([14099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part011 : ℚ :=
  (48468546625 : ℚ) / 20542972246804541952

def SurrogateDiagonalTailChunk000Sub001Block141Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14099
    = surrogateDiagTailX0RatChunk000Sub001Block141Part011

theorem surrogateDiagonalTailChunk000Sub001Block141Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part011] using hcert

def TailChunk000Sub001Block141Part012SupportExplicit : Finset ℕ :=
  ([14101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part012 : ℚ :=
  (108716625 : ℚ) / 111264469760970008

def SurrogateDiagonalTailChunk000Sub001Block141Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14101
    = surrogateDiagTailX0RatChunk000Sub001Block141Part012

theorem surrogateDiagonalTailChunk000Sub001Block141Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part012] using hcert

def TailChunk000Sub001Block141Part013SupportExplicit : Finset ℕ :=
  ([14102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part013 : ℚ :=
  (10868730697 : ℚ) / 16780571443200000

def SurrogateDiagonalTailChunk000Sub001Block141Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14102
    = surrogateDiagTailX0RatChunk000Sub001Block141Part013

theorem surrogateDiagonalTailChunk000Sub001Block141Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part013] using hcert

def TailChunk000Sub001Block141Part014SupportExplicit : Finset ℕ :=
  ([14105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part014 : ℚ :=
  (4091893919 : ℚ) / 46447310772633600

def SurrogateDiagonalTailChunk000Sub001Block141Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14105
    = surrogateDiagTailX0RatChunk000Sub001Block141Part014

theorem surrogateDiagonalTailChunk000Sub001Block141Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part014] using hcert

def TailChunk000Sub001Block141Part015SupportExplicit : Finset ℕ :=
  ([14106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part015 : ℚ :=
  (17266822537 : ℚ) / 12201642340500000

def SurrogateDiagonalTailChunk000Sub001Block141Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14106
    = surrogateDiagTailX0RatChunk000Sub001Block141Part015

theorem surrogateDiagonalTailChunk000Sub001Block141Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part015] using hcert

def TailChunk000Sub001Block141Part016SupportExplicit : Finset ℕ :=
  ([14107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block141Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14107
    = surrogateDiagTailX0RatChunk000Sub001Block141Part016

theorem surrogateDiagonalTailChunk000Sub001Block141Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part016] using hcert

def TailChunk000Sub001Block141Part017SupportExplicit : Finset ℕ :=
  ([14109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part017 : ℚ :=
  (691212659975 : ℚ) / 9777939483065561664

def SurrogateDiagonalTailChunk000Sub001Block141Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14109
    = surrogateDiagTailX0RatChunk000Sub001Block141Part017

theorem surrogateDiagonalTailChunk000Sub001Block141Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part017] using hcert

def TailChunk000Sub001Block141Part018SupportExplicit : Finset ℕ :=
  ([14110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part018 : ℚ :=
  (2049858215875 : ℚ) / 1896715373676331008

def SurrogateDiagonalTailChunk000Sub001Block141Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14110
    = surrogateDiagTailX0RatChunk000Sub001Block141Part018

theorem surrogateDiagonalTailChunk000Sub001Block141Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part018] using hcert

def TailChunk000Sub001Block141Part019SupportExplicit : Finset ℕ :=
  ([14111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part019 : ℚ :=
  (128014025 : ℚ) / 160197354915250176

def SurrogateDiagonalTailChunk000Sub001Block141Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14111
    = surrogateDiagTailX0RatChunk000Sub001Block141Part019

theorem surrogateDiagonalTailChunk000Sub001Block141Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part019] using hcert

def TailChunk000Sub001Block141Part020SupportExplicit : Finset ℕ :=
  ([14113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part020 : ℚ :=
  (5516822607 : ℚ) / 900570457601238400

def SurrogateDiagonalTailChunk000Sub001Block141Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14113
    = surrogateDiagTailX0RatChunk000Sub001Block141Part020

theorem surrogateDiagonalTailChunk000Sub001Block141Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part020] using hcert

def TailChunk000Sub001Block141Part021SupportExplicit : Finset ℕ :=
  ([14114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part021 : ℚ :=
  (778144515625 : ℚ) / 1549534164290445312

def SurrogateDiagonalTailChunk000Sub001Block141Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14114
    = surrogateDiagTailX0RatChunk000Sub001Block141Part021

theorem surrogateDiagonalTailChunk000Sub001Block141Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part021] using hcert

def TailChunk000Sub001Block141Part022SupportExplicit : Finset ℕ :=
  ([14115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part022 : ℚ :=
  (10182634481 : ℚ) / 63971746594160640

def SurrogateDiagonalTailChunk000Sub001Block141Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14115
    = surrogateDiagTailX0RatChunk000Sub001Block141Part022

theorem surrogateDiagonalTailChunk000Sub001Block141Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part022] using hcert

def TailChunk000Sub001Block141Part023SupportExplicit : Finset ℕ :=
  ([14117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part023 : ℚ :=
  (246204876025 : ℚ) / 79566911457365662848

def SurrogateDiagonalTailChunk000Sub001Block141Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14117
    = surrogateDiagTailX0RatChunk000Sub001Block141Part023

theorem surrogateDiagonalTailChunk000Sub001Block141Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part023] using hcert

def TailChunk000Sub001Block141Part024SupportExplicit : Finset ℕ :=
  ([14118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block141Part024 : ℚ :=
  (699128491 : ℚ) / 387060923105280

def SurrogateDiagonalTailChunk000Sub001Block141Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14118
    = surrogateDiagTailX0RatChunk000Sub001Block141Part024

theorem surrogateDiagonalTailChunk000Sub001Block141Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block141Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block141Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block141Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block141Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block141Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block141Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block141HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block141Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block141Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block141Part000
    + surrogateDiagTailX0RatChunk000Sub001Block141Part001
    + surrogateDiagTailX0RatChunk000Sub001Block141Part002
    + surrogateDiagTailX0RatChunk000Sub001Block141Part003
    + surrogateDiagTailX0RatChunk000Sub001Block141Part004
    + surrogateDiagTailX0RatChunk000Sub001Block141Part005
    + surrogateDiagTailX0RatChunk000Sub001Block141Part006
    + surrogateDiagTailX0RatChunk000Sub001Block141Part007
    + surrogateDiagTailX0RatChunk000Sub001Block141Part008
    + surrogateDiagTailX0RatChunk000Sub001Block141Part009

def surrogateDiagonalTailChunk000Sub001Block141MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block141Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block141Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block141Part010
    + surrogateDiagTailX0RatChunk000Sub001Block141Part011
    + surrogateDiagTailX0RatChunk000Sub001Block141Part012
    + surrogateDiagTailX0RatChunk000Sub001Block141Part013
    + surrogateDiagTailX0RatChunk000Sub001Block141Part014
    + surrogateDiagTailX0RatChunk000Sub001Block141Part015
    + surrogateDiagTailX0RatChunk000Sub001Block141Part016
    + surrogateDiagTailX0RatChunk000Sub001Block141Part017
    + surrogateDiagTailX0RatChunk000Sub001Block141Part018
    + surrogateDiagTailX0RatChunk000Sub001Block141Part019

def surrogateDiagonalTailChunk000Sub001Block141TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block141Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block141Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block141Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block141Part020
    + surrogateDiagTailX0RatChunk000Sub001Block141Part021
    + surrogateDiagTailX0RatChunk000Sub001Block141Part022
    + surrogateDiagTailX0RatChunk000Sub001Block141Part023
    + surrogateDiagTailX0RatChunk000Sub001Block141Part024

def surrogateDiagonalTailChunk000Sub001Block141Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block141HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block141MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block141TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block141 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block141Part000
    + surrogateDiagTailX0RatChunk000Sub001Block141Part001
    + surrogateDiagTailX0RatChunk000Sub001Block141Part002
    + surrogateDiagTailX0RatChunk000Sub001Block141Part003
    + surrogateDiagTailX0RatChunk000Sub001Block141Part004
    + surrogateDiagTailX0RatChunk000Sub001Block141Part005
    + surrogateDiagTailX0RatChunk000Sub001Block141Part006
    + surrogateDiagTailX0RatChunk000Sub001Block141Part007
    + surrogateDiagTailX0RatChunk000Sub001Block141Part008
    + surrogateDiagTailX0RatChunk000Sub001Block141Part009
    + surrogateDiagTailX0RatChunk000Sub001Block141Part010
    + surrogateDiagTailX0RatChunk000Sub001Block141Part011
    + surrogateDiagTailX0RatChunk000Sub001Block141Part012
    + surrogateDiagTailX0RatChunk000Sub001Block141Part013
    + surrogateDiagTailX0RatChunk000Sub001Block141Part014
    + surrogateDiagTailX0RatChunk000Sub001Block141Part015
    + surrogateDiagTailX0RatChunk000Sub001Block141Part016
    + surrogateDiagTailX0RatChunk000Sub001Block141Part017
    + surrogateDiagTailX0RatChunk000Sub001Block141Part018
    + surrogateDiagTailX0RatChunk000Sub001Block141Part019
    + surrogateDiagTailX0RatChunk000Sub001Block141Part020
    + surrogateDiagTailX0RatChunk000Sub001Block141Part021
    + surrogateDiagTailX0RatChunk000Sub001Block141Part022
    + surrogateDiagTailX0RatChunk000Sub001Block141Part023
    + surrogateDiagTailX0RatChunk000Sub001Block141Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block141_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block141Head + surrogateDiagTailX0RatChunk000Sub001Block141Mid + surrogateDiagTailX0RatChunk000Sub001Block141Tail =
      surrogateDiagTailX0RatChunk000Sub001Block141 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block141Head surrogateDiagTailX0RatChunk000Sub001Block141Mid surrogateDiagTailX0RatChunk000Sub001Block141Tail surrogateDiagTailX0RatChunk000Sub001Block141
  ring

def SurrogateDiagonalTailChunk000Sub001Block141HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block141HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block141Head

def SurrogateDiagonalTailChunk000Sub001Block141MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block141MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block141Mid

def SurrogateDiagonalTailChunk000Sub001Block141TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block141TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block141Tail

theorem surrogateDiagonalTailChunk000Sub001Block141_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block141HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block141MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block141TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block141Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block141 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block141HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block141MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block141TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block141Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block141_eq_head_add_mid_add_tail

/-- Block 142 covers tail-support indices [8550,8575) and q from 14119 to 14159. -/

def TailChunk000Sub001Block142Part000SupportExplicit : Finset ℕ :=
  ([14119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part000 : ℚ :=
  (288593275 : ℚ) / 20230384247635968

def SurrogateDiagonalTailChunk000Sub001Block142Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14119
    = surrogateDiagTailX0RatChunk000Sub001Block142Part000

theorem surrogateDiagonalTailChunk000Sub001Block142Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part000] using hcert

def TailChunk000Sub001Block142Part001SupportExplicit : Finset ℕ :=
  ([14122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part001 : ℚ :=
  (1463815983725 : ℚ) / 2567871530850567744

def SurrogateDiagonalTailChunk000Sub001Block142Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14122
    = surrogateDiagTailX0RatChunk000Sub001Block142Part001

theorem surrogateDiagonalTailChunk000Sub001Block142Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part001] using hcert

def TailChunk000Sub001Block142Part002SupportExplicit : Finset ℕ :=
  ([14123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part002 : ℚ :=
  (52029359075 : ℚ) / 28581354498288162816

def SurrogateDiagonalTailChunk000Sub001Block142Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14123
    = surrogateDiagTailX0RatChunk000Sub001Block142Part002

theorem surrogateDiagonalTailChunk000Sub001Block142Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part002] using hcert

def TailChunk000Sub001Block142Part003SupportExplicit : Finset ℕ :=
  ([14126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part003 : ℚ :=
  (2542489288375 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub001Block142Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14126
    = surrogateDiagTailX0RatChunk000Sub001Block142Part003

theorem surrogateDiagonalTailChunk000Sub001Block142Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part003] using hcert

def TailChunk000Sub001Block142Part004SupportExplicit : Finset ℕ :=
  ([14127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part004 : ℚ :=
  (1395431089825 : ℚ) / 15214689734086361088

def SurrogateDiagonalTailChunk000Sub001Block142Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14127
    = surrogateDiagTailX0RatChunk000Sub001Block142Part004

theorem surrogateDiagonalTailChunk000Sub001Block142Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part004] using hcert

def TailChunk000Sub001Block142Part005SupportExplicit : Finset ℕ :=
  ([14129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part005 : ℚ :=
  (220563829 : ℚ) / 246064245142826880

def SurrogateDiagonalTailChunk000Sub001Block142Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14129
    = surrogateDiagTailX0RatChunk000Sub001Block142Part005

theorem surrogateDiagonalTailChunk000Sub001Block142Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part005] using hcert

def TailChunk000Sub001Block142Part006SupportExplicit : Finset ℕ :=
  ([14131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part006 : ℚ :=
  (41335457375 : ℚ) / 8013617970053548032

def SurrogateDiagonalTailChunk000Sub001Block142Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14131
    = surrogateDiagTailX0RatChunk000Sub001Block142Part006

theorem surrogateDiagonalTailChunk000Sub001Block142Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part006] using hcert

def TailChunk000Sub001Block142Part007SupportExplicit : Finset ℕ :=
  ([14133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part007 : ℚ :=
  (1471325560525 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk000Sub001Block142Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14133
    = surrogateDiagTailX0RatChunk000Sub001Block142Part007

theorem surrogateDiagonalTailChunk000Sub001Block142Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part007] using hcert

def TailChunk000Sub001Block142Part008SupportExplicit : Finset ℕ :=
  ([14134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part008 : ℚ :=
  (59844113039 : ℚ) / 109466507291673600

def SurrogateDiagonalTailChunk000Sub001Block142Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14134
    = surrogateDiagTailX0RatChunk000Sub001Block142Part008

theorem surrogateDiagonalTailChunk000Sub001Block142Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part008] using hcert

def TailChunk000Sub001Block142Part009SupportExplicit : Finset ℕ :=
  ([14135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part009 : ℚ :=
  (43423918741 : ℚ) / 1099731530101555200

def SurrogateDiagonalTailChunk000Sub001Block142Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14135
    = surrogateDiagTailX0RatChunk000Sub001Block142Part009

theorem surrogateDiagonalTailChunk000Sub001Block142Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part009] using hcert

def TailChunk000Sub001Block142Part010SupportExplicit : Finset ℕ :=
  ([14137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part010 : ℚ :=
  (18321461 : ℚ) / 19528908344668800

def SurrogateDiagonalTailChunk000Sub001Block142Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14137
    = surrogateDiagTailX0RatChunk000Sub001Block142Part010

theorem surrogateDiagonalTailChunk000Sub001Block142Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part010] using hcert

def TailChunk000Sub001Block142Part011SupportExplicit : Finset ℕ :=
  ([14138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part011 : ℚ :=
  (780793140625 : ℚ) / 1560102133958544672

def SurrogateDiagonalTailChunk000Sub001Block142Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14138
    = surrogateDiagTailX0RatChunk000Sub001Block142Part011

theorem surrogateDiagonalTailChunk000Sub001Block142Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part011] using hcert

def TailChunk000Sub001Block142Part012SupportExplicit : Finset ℕ :=
  ([14141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part012 : ℚ :=
  (79414565125 : ℚ) / 92914881827733283968

def SurrogateDiagonalTailChunk000Sub001Block142Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14141
    = surrogateDiagTailX0RatChunk000Sub001Block142Part012

theorem surrogateDiagonalTailChunk000Sub001Block142Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part012] using hcert

def TailChunk000Sub001Block142Part013SupportExplicit : Finset ℕ :=
  ([14142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part013 : ℚ :=
  (867753707675 : ℚ) / 616336645514486784

def SurrogateDiagonalTailChunk000Sub001Block142Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14142
    = surrogateDiagTailX0RatChunk000Sub001Block142Part013

theorem surrogateDiagonalTailChunk000Sub001Block142Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part013] using hcert

def TailChunk000Sub001Block142Part014SupportExplicit : Finset ℕ :=
  ([14143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block142Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14143
    = surrogateDiagTailX0RatChunk000Sub001Block142Part014

theorem surrogateDiagonalTailChunk000Sub001Block142Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part014] using hcert

def TailChunk000Sub001Block142Part015SupportExplicit : Finset ℕ :=
  ([14145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part015 : ℚ :=
  (56222610421 : ℚ) / 245684346499891200

def SurrogateDiagonalTailChunk000Sub001Block142Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14145
    = surrogateDiagTailX0RatChunk000Sub001Block142Part015

theorem surrogateDiagonalTailChunk000Sub001Block142Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part015] using hcert

def TailChunk000Sub001Block142Part016SupportExplicit : Finset ℕ :=
  ([14146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part016 : ℚ :=
  (110398940431 : ℚ) / 169913138728579200

def SurrogateDiagonalTailChunk000Sub001Block142Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14146
    = surrogateDiagTailX0RatChunk000Sub001Block142Part016

theorem surrogateDiagonalTailChunk000Sub001Block142Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part016] using hcert

def TailChunk000Sub001Block142Part017SupportExplicit : Finset ℕ :=
  ([14147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part017 : ℚ :=
  (104320186475 : ℚ) / 7525044947750980608

def SurrogateDiagonalTailChunk000Sub001Block142Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14147
    = surrogateDiagTailX0RatChunk000Sub001Block142Part017

theorem surrogateDiagonalTailChunk000Sub001Block142Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part017] using hcert

def TailChunk000Sub001Block142Part018SupportExplicit : Finset ℕ :=
  ([14149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block142Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14149
    = surrogateDiagTailX0RatChunk000Sub001Block142Part018

theorem surrogateDiagonalTailChunk000Sub001Block142Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part018] using hcert

def TailChunk000Sub001Block142Part019SupportExplicit : Finset ℕ :=
  ([14151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part019 : ℚ :=
  (2703642993325 : ℚ) / 17542476550958481408

def SurrogateDiagonalTailChunk000Sub001Block142Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14151
    = surrogateDiagTailX0RatChunk000Sub001Block142Part019

theorem surrogateDiagonalTailChunk000Sub001Block142Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part019] using hcert

def TailChunk000Sub001Block142Part020SupportExplicit : Finset ℕ :=
  ([14153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block142Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14153
    = surrogateDiagTailX0RatChunk000Sub001Block142Part020

theorem surrogateDiagonalTailChunk000Sub001Block142Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part020] using hcert

def TailChunk000Sub001Block142Part021SupportExplicit : Finset ℕ :=
  ([14154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part021 : ℚ :=
  (37714975 : ℚ) / 14682823852032

def SurrogateDiagonalTailChunk000Sub001Block142Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14154
    = surrogateDiagTailX0RatChunk000Sub001Block142Part021

theorem surrogateDiagonalTailChunk000Sub001Block142Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part021] using hcert

def TailChunk000Sub001Block142Part022SupportExplicit : Finset ℕ :=
  ([14155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part022 : ℚ :=
  (1076290589875 : ℚ) / 32240643853685096448

def SurrogateDiagonalTailChunk000Sub001Block142Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14155
    = surrogateDiagTailX0RatChunk000Sub001Block142Part022

theorem surrogateDiagonalTailChunk000Sub001Block142Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part022] using hcert

def TailChunk000Sub001Block142Part023SupportExplicit : Finset ℕ :=
  ([14158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part023 : ℚ :=
  (783003765625 : ℚ) / 1568949990046968882

def SurrogateDiagonalTailChunk000Sub001Block142Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14158
    = surrogateDiagTailX0RatChunk000Sub001Block142Part023

theorem surrogateDiagonalTailChunk000Sub001Block142Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part023] using hcert

def TailChunk000Sub001Block142Part024SupportExplicit : Finset ℕ :=
  ([14159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block142Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block142Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14159
    = surrogateDiagTailX0RatChunk000Sub001Block142Part024

theorem surrogateDiagonalTailChunk000Sub001Block142Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block142Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block142Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block142Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block142Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block142Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block142Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block142HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block142Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block142Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block142Part000
    + surrogateDiagTailX0RatChunk000Sub001Block142Part001
    + surrogateDiagTailX0RatChunk000Sub001Block142Part002
    + surrogateDiagTailX0RatChunk000Sub001Block142Part003
    + surrogateDiagTailX0RatChunk000Sub001Block142Part004
    + surrogateDiagTailX0RatChunk000Sub001Block142Part005
    + surrogateDiagTailX0RatChunk000Sub001Block142Part006
    + surrogateDiagTailX0RatChunk000Sub001Block142Part007
    + surrogateDiagTailX0RatChunk000Sub001Block142Part008
    + surrogateDiagTailX0RatChunk000Sub001Block142Part009

def surrogateDiagonalTailChunk000Sub001Block142MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block142Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block142Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block142Part010
    + surrogateDiagTailX0RatChunk000Sub001Block142Part011
    + surrogateDiagTailX0RatChunk000Sub001Block142Part012
    + surrogateDiagTailX0RatChunk000Sub001Block142Part013
    + surrogateDiagTailX0RatChunk000Sub001Block142Part014
    + surrogateDiagTailX0RatChunk000Sub001Block142Part015
    + surrogateDiagTailX0RatChunk000Sub001Block142Part016
    + surrogateDiagTailX0RatChunk000Sub001Block142Part017
    + surrogateDiagTailX0RatChunk000Sub001Block142Part018
    + surrogateDiagTailX0RatChunk000Sub001Block142Part019

def surrogateDiagonalTailChunk000Sub001Block142TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block142Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block142Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block142Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block142Part020
    + surrogateDiagTailX0RatChunk000Sub001Block142Part021
    + surrogateDiagTailX0RatChunk000Sub001Block142Part022
    + surrogateDiagTailX0RatChunk000Sub001Block142Part023
    + surrogateDiagTailX0RatChunk000Sub001Block142Part024

def surrogateDiagonalTailChunk000Sub001Block142Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block142HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block142MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block142TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block142 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block142Part000
    + surrogateDiagTailX0RatChunk000Sub001Block142Part001
    + surrogateDiagTailX0RatChunk000Sub001Block142Part002
    + surrogateDiagTailX0RatChunk000Sub001Block142Part003
    + surrogateDiagTailX0RatChunk000Sub001Block142Part004
    + surrogateDiagTailX0RatChunk000Sub001Block142Part005
    + surrogateDiagTailX0RatChunk000Sub001Block142Part006
    + surrogateDiagTailX0RatChunk000Sub001Block142Part007
    + surrogateDiagTailX0RatChunk000Sub001Block142Part008
    + surrogateDiagTailX0RatChunk000Sub001Block142Part009
    + surrogateDiagTailX0RatChunk000Sub001Block142Part010
    + surrogateDiagTailX0RatChunk000Sub001Block142Part011
    + surrogateDiagTailX0RatChunk000Sub001Block142Part012
    + surrogateDiagTailX0RatChunk000Sub001Block142Part013
    + surrogateDiagTailX0RatChunk000Sub001Block142Part014
    + surrogateDiagTailX0RatChunk000Sub001Block142Part015
    + surrogateDiagTailX0RatChunk000Sub001Block142Part016
    + surrogateDiagTailX0RatChunk000Sub001Block142Part017
    + surrogateDiagTailX0RatChunk000Sub001Block142Part018
    + surrogateDiagTailX0RatChunk000Sub001Block142Part019
    + surrogateDiagTailX0RatChunk000Sub001Block142Part020
    + surrogateDiagTailX0RatChunk000Sub001Block142Part021
    + surrogateDiagTailX0RatChunk000Sub001Block142Part022
    + surrogateDiagTailX0RatChunk000Sub001Block142Part023
    + surrogateDiagTailX0RatChunk000Sub001Block142Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block142_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block142Head + surrogateDiagTailX0RatChunk000Sub001Block142Mid + surrogateDiagTailX0RatChunk000Sub001Block142Tail =
      surrogateDiagTailX0RatChunk000Sub001Block142 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block142Head surrogateDiagTailX0RatChunk000Sub001Block142Mid surrogateDiagTailX0RatChunk000Sub001Block142Tail surrogateDiagTailX0RatChunk000Sub001Block142
  ring

def SurrogateDiagonalTailChunk000Sub001Block142HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block142HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block142Head

def SurrogateDiagonalTailChunk000Sub001Block142MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block142MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block142Mid

def SurrogateDiagonalTailChunk000Sub001Block142TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block142TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block142Tail

theorem surrogateDiagonalTailChunk000Sub001Block142_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block142HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block142MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block142TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block142Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block142 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block142HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block142MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block142TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block142Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block142_eq_head_add_mid_add_tail

/-- Block 143 covers tail-support indices [8575,8600) and q from 14162 to 14198. -/

def TailChunk000Sub001Block143Part000SupportExplicit : Finset ℕ :=
  ([14162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part000 : ℚ :=
  (3037926831175 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk000Sub001Block143Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14162
    = surrogateDiagTailX0RatChunk000Sub001Block143Part000

theorem surrogateDiagonalTailChunk000Sub001Block143Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part000] using hcert

def TailChunk000Sub001Block143Part001SupportExplicit : Finset ℕ :=
  ([14163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part001 : ℚ :=
  (2786050139 : ℚ) / 39714109758504960

def SurrogateDiagonalTailChunk000Sub001Block143Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14163
    = surrogateDiagTailX0RatChunk000Sub001Block143Part001

theorem surrogateDiagonalTailChunk000Sub001Block143Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part001] using hcert

def TailChunk000Sub001Block143Part002SupportExplicit : Finset ℕ :=
  ([14165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part002 : ℚ :=
  (334525923175 : ℚ) / 13725196332539314176

def SurrogateDiagonalTailChunk000Sub001Block143Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14165
    = surrogateDiagTailX0RatChunk000Sub001Block143Part002

theorem surrogateDiagonalTailChunk000Sub001Block143Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part002] using hcert

def TailChunk000Sub001Block143Part003SupportExplicit : Finset ℕ :=
  ([14167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part003 : ℚ :=
  (1520298967 : ℚ) / 875732058333388800

def SurrogateDiagonalTailChunk000Sub001Block143Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14167
    = surrogateDiagTailX0RatChunk000Sub001Block143Part003

theorem surrogateDiagonalTailChunk000Sub001Block143Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part003] using hcert

def TailChunk000Sub001Block143Part004SupportExplicit : Finset ℕ :=
  ([14169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part004 : ℚ :=
  (697102659725 : ℚ) / 9945366151028226624

def SurrogateDiagonalTailChunk000Sub001Block143Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14169
    = surrogateDiagTailX0RatChunk000Sub001Block143Part004

theorem surrogateDiagonalTailChunk000Sub001Block143Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part004] using hcert

def TailChunk000Sub001Block143Part005SupportExplicit : Finset ℕ :=
  ([14170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part005 : ℚ :=
  (709290619625 : ℚ) / 601957147613331456

def SurrogateDiagonalTailChunk000Sub001Block143Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14170
    = surrogateDiagTailX0RatChunk000Sub001Block143Part005

theorem surrogateDiagonalTailChunk000Sub001Block143Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part005] using hcert

def TailChunk000Sub001Block143Part006SupportExplicit : Finset ℕ :=
  ([14171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part006 : ℚ :=
  (32379597175 : ℚ) / 22357864628283658752

def SurrogateDiagonalTailChunk000Sub001Block143Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14171
    = surrogateDiagTailX0RatChunk000Sub001Block143Part006

theorem surrogateDiagonalTailChunk000Sub001Block143Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part006] using hcert

def TailChunk000Sub001Block143Part007SupportExplicit : Finset ℕ :=
  ([14173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block143Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14173
    = surrogateDiagTailX0RatChunk000Sub001Block143Part007

theorem surrogateDiagonalTailChunk000Sub001Block143Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part007] using hcert

def TailChunk000Sub001Block143Part008SupportExplicit : Finset ℕ :=
  ([14174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part008 : ℚ :=
  (2912184375925 : ℚ) / 5026765651412502528

def SurrogateDiagonalTailChunk000Sub001Block143Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14174
    = surrogateDiagTailX0RatChunk000Sub001Block143Part008

theorem surrogateDiagonalTailChunk000Sub001Block143Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part008] using hcert

def TailChunk000Sub001Block143Part009SupportExplicit : Finset ℕ :=
  ([14177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block143Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14177
    = surrogateDiagTailX0RatChunk000Sub001Block143Part009

theorem surrogateDiagonalTailChunk000Sub001Block143Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part009] using hcert

def TailChunk000Sub001Block143Part010SupportExplicit : Finset ℕ :=
  ([14178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part010 : ℚ :=
  (1613431776175 : ℚ) / 950918108380397568

def SurrogateDiagonalTailChunk000Sub001Block143Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14178
    = surrogateDiagTailX0RatChunk000Sub001Block143Part010

theorem surrogateDiagonalTailChunk000Sub001Block143Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part010] using hcert

def TailChunk000Sub001Block143Part011SupportExplicit : Finset ℕ :=
  ([14179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part011 : ℚ :=
  (5568191703 : ℚ) / 917548538058342400

def SurrogateDiagonalTailChunk000Sub001Block143Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14179
    = surrogateDiagTailX0RatChunk000Sub001Block143Part011

theorem surrogateDiagonalTailChunk000Sub001Block143Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part011] using hcert

def TailChunk000Sub001Block143Part012SupportExplicit : Finset ℕ :=
  ([14181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part012 : ℚ :=
  (1401752205475 : ℚ) / 16937098961948540928

def SurrogateDiagonalTailChunk000Sub001Block143Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14181
    = surrogateDiagTailX0RatChunk000Sub001Block143Part012

theorem surrogateDiagonalTailChunk000Sub001Block143Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part012] using hcert

def TailChunk000Sub001Block143Part013SupportExplicit : Finset ℕ :=
  ([14182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part013 : ℚ :=
  (2562692923375 : ℚ) / 3399021490429052928

def SurrogateDiagonalTailChunk000Sub001Block143Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14182
    = surrogateDiagTailX0RatChunk000Sub001Block143Part013

theorem surrogateDiagonalTailChunk000Sub001Block143Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part013] using hcert

def TailChunk000Sub001Block143Part014SupportExplicit : Finset ℕ :=
  ([14183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part014 : ℚ :=
  (2003999419 : ℚ) / 487940172936883200

def SurrogateDiagonalTailChunk000Sub001Block143Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14183
    = surrogateDiagTailX0RatChunk000Sub001Block143Part014

theorem surrogateDiagonalTailChunk000Sub001Block143Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part014] using hcert

def TailChunk000Sub001Block143Part015SupportExplicit : Finset ℕ :=
  ([14185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part015 : ℚ :=
  (1006411201525 : ℚ) / 41408712769298792448

def SurrogateDiagonalTailChunk000Sub001Block143Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14185
    = surrogateDiagTailX0RatChunk000Sub001Block143Part015

theorem surrogateDiagonalTailChunk000Sub001Block143Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part015] using hcert

def TailChunk000Sub001Block143Part016SupportExplicit : Finset ℕ :=
  ([14186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part016 : ℚ :=
  (2812210123 : ℚ) / 5211612866150400

def SurrogateDiagonalTailChunk000Sub001Block143Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14186
    = surrogateDiagTailX0RatChunk000Sub001Block143Part016

theorem surrogateDiagonalTailChunk000Sub001Block143Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part016] using hcert

def TailChunk000Sub001Block143Part017SupportExplicit : Finset ℕ :=
  ([14187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part017 : ℚ :=
  (349437267325 : ℚ) / 4998005407923904512

def SurrogateDiagonalTailChunk000Sub001Block143Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14187
    = surrogateDiagTailX0RatChunk000Sub001Block143Part017

theorem surrogateDiagonalTailChunk000Sub001Block143Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part017] using hcert

def TailChunk000Sub001Block143Part018SupportExplicit : Finset ℕ :=
  ([14189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part018 : ℚ :=
  (42844084675 : ℚ) / 3033312252838019136

def SurrogateDiagonalTailChunk000Sub001Block143Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14189
    = surrogateDiagTailX0RatChunk000Sub001Block143Part018

theorem surrogateDiagonalTailChunk000Sub001Block143Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part018] using hcert

def TailChunk000Sub001Block143Part019SupportExplicit : Finset ℕ :=
  ([14190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part019 : ℚ :=
  (51064007 : ℚ) / 14164506574848

def SurrogateDiagonalTailChunk000Sub001Block143Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14190
    = surrogateDiagTailX0RatChunk000Sub001Block143Part019

theorem surrogateDiagonalTailChunk000Sub001Block143Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part019] using hcert

def TailChunk000Sub001Block143Part020SupportExplicit : Finset ℕ :=
  ([14191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part020 : ℚ :=
  (16360562475 : ℚ) / 7028443933568425984

def SurrogateDiagonalTailChunk000Sub001Block143Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14191
    = surrogateDiagTailX0RatChunk000Sub001Block143Part020

theorem surrogateDiagonalTailChunk000Sub001Block143Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part020] using hcert

def TailChunk000Sub001Block143Part021SupportExplicit : Finset ℕ :=
  ([14194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part021 : ℚ :=
  (1498945817 : ℚ) / 2798969682000000

def SurrogateDiagonalTailChunk000Sub001Block143Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14194
    = surrogateDiagTailX0RatChunk000Sub001Block143Part021

theorem surrogateDiagonalTailChunk000Sub001Block143Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part021] using hcert

def TailChunk000Sub001Block143Part022SupportExplicit : Finset ℕ :=
  ([14195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part022 : ℚ :=
  (664158335875 : ℚ) / 31855109844592754688

def SurrogateDiagonalTailChunk000Sub001Block143Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14195
    = surrogateDiagTailX0RatChunk000Sub001Block143Part022

theorem surrogateDiagonalTailChunk000Sub001Block143Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part022] using hcert

def TailChunk000Sub001Block143Part023SupportExplicit : Finset ℕ :=
  ([14197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block143Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14197
    = surrogateDiagTailX0RatChunk000Sub001Block143Part023

theorem surrogateDiagonalTailChunk000Sub001Block143Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part023] using hcert

def TailChunk000Sub001Block143Part024SupportExplicit : Finset ℕ :=
  ([14198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block143Part024 : ℚ :=
  (120087076021 : ℚ) / 218933014583347200

def SurrogateDiagonalTailChunk000Sub001Block143Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14198
    = surrogateDiagTailX0RatChunk000Sub001Block143Part024

theorem surrogateDiagonalTailChunk000Sub001Block143Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block143Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block143Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block143Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block143Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block143Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block143Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block143HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block143Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block143Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block143Part000
    + surrogateDiagTailX0RatChunk000Sub001Block143Part001
    + surrogateDiagTailX0RatChunk000Sub001Block143Part002
    + surrogateDiagTailX0RatChunk000Sub001Block143Part003
    + surrogateDiagTailX0RatChunk000Sub001Block143Part004
    + surrogateDiagTailX0RatChunk000Sub001Block143Part005
    + surrogateDiagTailX0RatChunk000Sub001Block143Part006
    + surrogateDiagTailX0RatChunk000Sub001Block143Part007
    + surrogateDiagTailX0RatChunk000Sub001Block143Part008
    + surrogateDiagTailX0RatChunk000Sub001Block143Part009

def surrogateDiagonalTailChunk000Sub001Block143MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block143Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block143Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block143Part010
    + surrogateDiagTailX0RatChunk000Sub001Block143Part011
    + surrogateDiagTailX0RatChunk000Sub001Block143Part012
    + surrogateDiagTailX0RatChunk000Sub001Block143Part013
    + surrogateDiagTailX0RatChunk000Sub001Block143Part014
    + surrogateDiagTailX0RatChunk000Sub001Block143Part015
    + surrogateDiagTailX0RatChunk000Sub001Block143Part016
    + surrogateDiagTailX0RatChunk000Sub001Block143Part017
    + surrogateDiagTailX0RatChunk000Sub001Block143Part018
    + surrogateDiagTailX0RatChunk000Sub001Block143Part019

def surrogateDiagonalTailChunk000Sub001Block143TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block143Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block143Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block143Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block143Part020
    + surrogateDiagTailX0RatChunk000Sub001Block143Part021
    + surrogateDiagTailX0RatChunk000Sub001Block143Part022
    + surrogateDiagTailX0RatChunk000Sub001Block143Part023
    + surrogateDiagTailX0RatChunk000Sub001Block143Part024

def surrogateDiagonalTailChunk000Sub001Block143Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block143HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block143MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block143TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block143 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block143Part000
    + surrogateDiagTailX0RatChunk000Sub001Block143Part001
    + surrogateDiagTailX0RatChunk000Sub001Block143Part002
    + surrogateDiagTailX0RatChunk000Sub001Block143Part003
    + surrogateDiagTailX0RatChunk000Sub001Block143Part004
    + surrogateDiagTailX0RatChunk000Sub001Block143Part005
    + surrogateDiagTailX0RatChunk000Sub001Block143Part006
    + surrogateDiagTailX0RatChunk000Sub001Block143Part007
    + surrogateDiagTailX0RatChunk000Sub001Block143Part008
    + surrogateDiagTailX0RatChunk000Sub001Block143Part009
    + surrogateDiagTailX0RatChunk000Sub001Block143Part010
    + surrogateDiagTailX0RatChunk000Sub001Block143Part011
    + surrogateDiagTailX0RatChunk000Sub001Block143Part012
    + surrogateDiagTailX0RatChunk000Sub001Block143Part013
    + surrogateDiagTailX0RatChunk000Sub001Block143Part014
    + surrogateDiagTailX0RatChunk000Sub001Block143Part015
    + surrogateDiagTailX0RatChunk000Sub001Block143Part016
    + surrogateDiagTailX0RatChunk000Sub001Block143Part017
    + surrogateDiagTailX0RatChunk000Sub001Block143Part018
    + surrogateDiagTailX0RatChunk000Sub001Block143Part019
    + surrogateDiagTailX0RatChunk000Sub001Block143Part020
    + surrogateDiagTailX0RatChunk000Sub001Block143Part021
    + surrogateDiagTailX0RatChunk000Sub001Block143Part022
    + surrogateDiagTailX0RatChunk000Sub001Block143Part023
    + surrogateDiagTailX0RatChunk000Sub001Block143Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block143_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block143Head + surrogateDiagTailX0RatChunk000Sub001Block143Mid + surrogateDiagTailX0RatChunk000Sub001Block143Tail =
      surrogateDiagTailX0RatChunk000Sub001Block143 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block143Head surrogateDiagTailX0RatChunk000Sub001Block143Mid surrogateDiagTailX0RatChunk000Sub001Block143Tail surrogateDiagTailX0RatChunk000Sub001Block143
  ring

def SurrogateDiagonalTailChunk000Sub001Block143HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block143HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block143Head

def SurrogateDiagonalTailChunk000Sub001Block143MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block143MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block143Mid

def SurrogateDiagonalTailChunk000Sub001Block143TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block143TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block143Tail

theorem surrogateDiagonalTailChunk000Sub001Block143_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block143HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block143MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block143TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block143Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block143 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block143HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block143MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block143TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block143Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block143_eq_head_add_mid_add_tail

/-- Block 144 covers tail-support indices [8600,8625) and q from 14199 to 14239. -/

def TailChunk000Sub001Block144Part000SupportExplicit : Finset ℕ :=
  ([14199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part000 : ℚ :=
  (12501018475 : ℚ) / 179105021715494784

def SurrogateDiagonalTailChunk000Sub001Block144Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14199
    = surrogateDiagTailX0RatChunk000Sub001Block144Part000

theorem surrogateDiagonalTailChunk000Sub001Block144Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part000] using hcert

def TailChunk000Sub001Block144Part001SupportExplicit : Finset ℕ :=
  ([14201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part001 : ℚ :=
  (16756104109 : ℚ) / 2769782655762000000

def SurrogateDiagonalTailChunk000Sub001Block144Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14201
    = surrogateDiagTailX0RatChunk000Sub001Block144Part001

theorem surrogateDiagonalTailChunk000Sub001Block144Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part001] using hcert

def TailChunk000Sub001Block144Part002SupportExplicit : Finset ℕ :=
  ([14203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part002 : ℚ :=
  (257934984575 : ℚ) / 27407767871145452544

def SurrogateDiagonalTailChunk000Sub001Block144Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14203
    = surrogateDiagTailX0RatChunk000Sub001Block144Part002

theorem surrogateDiagonalTailChunk000Sub001Block144Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part002] using hcert

def TailChunk000Sub001Block144Part003SupportExplicit : Finset ℕ :=
  ([14205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part003 : ℚ :=
  (504230883675 : ℚ) / 2734198859043536896

def SurrogateDiagonalTailChunk000Sub001Block144Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14205
    = surrogateDiagTailX0RatChunk000Sub001Block144Part003

theorem surrogateDiagonalTailChunk000Sub001Block144Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part003] using hcert

def TailChunk000Sub001Block144Part004SupportExplicit : Finset ℕ :=
  ([14206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part004 : ℚ :=
  (788322015625 : ℚ) / 1590338377866768402

def SurrogateDiagonalTailChunk000Sub001Block144Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14206
    = surrogateDiagTailX0RatChunk000Sub001Block144Part004

theorem surrogateDiagonalTailChunk000Sub001Block144Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part004] using hcert

def TailChunk000Sub001Block144Part005SupportExplicit : Finset ℕ :=
  ([14207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block144Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14207
    = surrogateDiagTailX0RatChunk000Sub001Block144Part005

theorem surrogateDiagonalTailChunk000Sub001Block144Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part005] using hcert

def TailChunk000Sub001Block144Part006SupportExplicit : Finset ℕ :=
  ([14209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part006 : ℚ :=
  (41788843625 : ℚ) / 8192187563755732992

def SurrogateDiagonalTailChunk000Sub001Block144Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14209
    = surrogateDiagTailX0RatChunk000Sub001Block144Part006

theorem surrogateDiagonalTailChunk000Sub001Block144Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part006] using hcert

def TailChunk000Sub001Block144Part007SupportExplicit : Finset ℕ :=
  ([14213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part007 : ℚ :=
  (10626901 : ℚ) / 10791070934630400

def SurrogateDiagonalTailChunk000Sub001Block144Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14213
    = surrogateDiagTailX0RatChunk000Sub001Block144Part007

theorem surrogateDiagonalTailChunk000Sub001Block144Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part007] using hcert

def TailChunk000Sub001Block144Part008SupportExplicit : Finset ℕ :=
  ([14214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part008 : ℚ :=
  (1646574867625 : ℚ) / 1014467765274298368

def SurrogateDiagonalTailChunk000Sub001Block144Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14214
    = surrogateDiagTailX0RatChunk000Sub001Block144Part008

theorem surrogateDiagonalTailChunk000Sub001Block144Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part008] using hcert

def TailChunk000Sub001Block144Part009SupportExplicit : Finset ℕ :=
  ([14215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part009 : ℚ :=
  (1010668848025 : ℚ) / 41760252753143973888

def SurrogateDiagonalTailChunk000Sub001Block144Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14215
    = surrogateDiagTailX0RatChunk000Sub001Block144Part009

theorem surrogateDiagonalTailChunk000Sub001Block144Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part009] using hcert

def TailChunk000Sub001Block144Part010SupportExplicit : Finset ℕ :=
  ([14217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part010 : ℚ :=
  (3916645475 : ℚ) / 30848319506055168

def SurrogateDiagonalTailChunk000Sub001Block144Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14217
    = surrogateDiagTailX0RatChunk000Sub001Block144Part010

theorem surrogateDiagonalTailChunk000Sub001Block144Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part010] using hcert

def TailChunk000Sub001Block144Part011SupportExplicit : Finset ℕ :=
  ([14218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part011 : ℚ :=
  (789654390625 : ℚ) / 1595719470068558112

def SurrogateDiagonalTailChunk000Sub001Block144Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14218
    = surrogateDiagTailX0RatChunk000Sub001Block144Part011

theorem surrogateDiagonalTailChunk000Sub001Block144Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part011] using hcert

def TailChunk000Sub001Block144Part012SupportExplicit : Finset ℕ :=
  ([14219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part012 : ℚ :=
  (747791981 : ℚ) / 751058537050275840

def SurrogateDiagonalTailChunk000Sub001Block144Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14219
    = surrogateDiagTailX0RatChunk000Sub001Block144Part012

theorem surrogateDiagonalTailChunk000Sub001Block144Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part012] using hcert

def TailChunk000Sub001Block144Part013SupportExplicit : Finset ℕ :=
  ([14221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block144Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14221
    = surrogateDiagTailX0RatChunk000Sub001Block144Part013

theorem surrogateDiagonalTailChunk000Sub001Block144Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part013] using hcert

def TailChunk000Sub001Block144Part014SupportExplicit : Finset ℕ :=
  ([14222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part014 : ℚ :=
  (1515146125 : ℚ) / 2461594820840064

def SurrogateDiagonalTailChunk000Sub001Block144Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14222
    = surrogateDiagTailX0RatChunk000Sub001Block144Part014

theorem surrogateDiagonalTailChunk000Sub001Block144Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part014] using hcert

def TailChunk000Sub001Block144Part015SupportExplicit : Finset ℕ :=
  ([14223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part015 : ℚ :=
  (5664256969 : ℚ) / 54711756163200000

def SurrogateDiagonalTailChunk000Sub001Block144Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14223
    = surrogateDiagTailX0RatChunk000Sub001Block144Part015

theorem surrogateDiagonalTailChunk000Sub001Block144Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part015] using hcert

def TailChunk000Sub001Block144Part016SupportExplicit : Finset ℕ :=
  ([14226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part016 : ℚ :=
  (14051939309 : ℚ) / 25244700418497600

def SurrogateDiagonalTailChunk000Sub001Block144Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14226
    = surrogateDiagTailX0RatChunk000Sub001Block144Part016

theorem surrogateDiagonalTailChunk000Sub001Block144Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part016] using hcert

def TailChunk000Sub001Block144Part017SupportExplicit : Finset ℕ :=
  ([14227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part017 : ℚ :=
  (1244239171 : ℚ) / 917426370568396800

def SurrogateDiagonalTailChunk000Sub001Block144Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14227
    = surrogateDiagTailX0RatChunk000Sub001Block144Part017

theorem surrogateDiagonalTailChunk000Sub001Block144Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part017] using hcert

def TailChunk000Sub001Block144Part018SupportExplicit : Finset ℕ :=
  ([14230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part018 : ℚ :=
  (23764963075 : ℚ) / 163585658711864448

def SurrogateDiagonalTailChunk000Sub001Block144Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14230
    = surrogateDiagTailX0RatChunk000Sub001Block144Part018

theorem surrogateDiagonalTailChunk000Sub001Block144Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part018] using hcert

def TailChunk000Sub001Block144Part019SupportExplicit : Finset ℕ :=
  ([14231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part019 : ℚ :=
  (38270084875 : ℚ) / 1789509878674612992

def SurrogateDiagonalTailChunk000Sub001Block144Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14231
    = surrogateDiagTailX0RatChunk000Sub001Block144Part019

theorem surrogateDiagonalTailChunk000Sub001Block144Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part019] using hcert

def TailChunk000Sub001Block144Part020SupportExplicit : Finset ℕ :=
  ([14233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part020 : ℚ :=
  (85191479 : ℚ) / 68351179206340800

def SurrogateDiagonalTailChunk000Sub001Block144Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14233
    = surrogateDiagTailX0RatChunk000Sub001Block144Part020

theorem surrogateDiagonalTailChunk000Sub001Block144Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part020] using hcert

def TailChunk000Sub001Block144Part021SupportExplicit : Finset ℕ :=
  ([14234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part021 : ℚ :=
  (8459693083 : ℚ) / 174187474384771200

def SurrogateDiagonalTailChunk000Sub001Block144Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14234
    = surrogateDiagTailX0RatChunk000Sub001Block144Part021

theorem surrogateDiagonalTailChunk000Sub001Block144Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part021] using hcert

def TailChunk000Sub001Block144Part022SupportExplicit : Finset ℕ :=
  ([14235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part022 : ℚ :=
  (1464755243725 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk000Sub001Block144Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14235
    = surrogateDiagTailX0RatChunk000Sub001Block144Part022

theorem surrogateDiagonalTailChunk000Sub001Block144Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part022] using hcert

def TailChunk000Sub001Block144Part023SupportExplicit : Finset ℕ :=
  ([14237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part023 : ℚ :=
  (49389755725 : ℚ) / 21360503781931244832

def SurrogateDiagonalTailChunk000Sub001Block144Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14237
    = surrogateDiagTailX0RatChunk000Sub001Block144Part023

theorem surrogateDiagonalTailChunk000Sub001Block144Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part023] using hcert

def TailChunk000Sub001Block144Part024SupportExplicit : Finset ℕ :=
  ([14239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block144Part024 : ℚ :=
  (905849647 : ℚ) / 506296885337241600

def SurrogateDiagonalTailChunk000Sub001Block144Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14239
    = surrogateDiagTailX0RatChunk000Sub001Block144Part024

theorem surrogateDiagonalTailChunk000Sub001Block144Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block144Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block144Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block144Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block144Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block144Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block144Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block144HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block144Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block144Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block144Part000
    + surrogateDiagTailX0RatChunk000Sub001Block144Part001
    + surrogateDiagTailX0RatChunk000Sub001Block144Part002
    + surrogateDiagTailX0RatChunk000Sub001Block144Part003
    + surrogateDiagTailX0RatChunk000Sub001Block144Part004
    + surrogateDiagTailX0RatChunk000Sub001Block144Part005
    + surrogateDiagTailX0RatChunk000Sub001Block144Part006
    + surrogateDiagTailX0RatChunk000Sub001Block144Part007
    + surrogateDiagTailX0RatChunk000Sub001Block144Part008
    + surrogateDiagTailX0RatChunk000Sub001Block144Part009

def surrogateDiagonalTailChunk000Sub001Block144MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block144Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block144Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block144Part010
    + surrogateDiagTailX0RatChunk000Sub001Block144Part011
    + surrogateDiagTailX0RatChunk000Sub001Block144Part012
    + surrogateDiagTailX0RatChunk000Sub001Block144Part013
    + surrogateDiagTailX0RatChunk000Sub001Block144Part014
    + surrogateDiagTailX0RatChunk000Sub001Block144Part015
    + surrogateDiagTailX0RatChunk000Sub001Block144Part016
    + surrogateDiagTailX0RatChunk000Sub001Block144Part017
    + surrogateDiagTailX0RatChunk000Sub001Block144Part018
    + surrogateDiagTailX0RatChunk000Sub001Block144Part019

def surrogateDiagonalTailChunk000Sub001Block144TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block144Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block144Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block144Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block144Part020
    + surrogateDiagTailX0RatChunk000Sub001Block144Part021
    + surrogateDiagTailX0RatChunk000Sub001Block144Part022
    + surrogateDiagTailX0RatChunk000Sub001Block144Part023
    + surrogateDiagTailX0RatChunk000Sub001Block144Part024

def surrogateDiagonalTailChunk000Sub001Block144Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block144HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block144MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block144TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block144 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block144Part000
    + surrogateDiagTailX0RatChunk000Sub001Block144Part001
    + surrogateDiagTailX0RatChunk000Sub001Block144Part002
    + surrogateDiagTailX0RatChunk000Sub001Block144Part003
    + surrogateDiagTailX0RatChunk000Sub001Block144Part004
    + surrogateDiagTailX0RatChunk000Sub001Block144Part005
    + surrogateDiagTailX0RatChunk000Sub001Block144Part006
    + surrogateDiagTailX0RatChunk000Sub001Block144Part007
    + surrogateDiagTailX0RatChunk000Sub001Block144Part008
    + surrogateDiagTailX0RatChunk000Sub001Block144Part009
    + surrogateDiagTailX0RatChunk000Sub001Block144Part010
    + surrogateDiagTailX0RatChunk000Sub001Block144Part011
    + surrogateDiagTailX0RatChunk000Sub001Block144Part012
    + surrogateDiagTailX0RatChunk000Sub001Block144Part013
    + surrogateDiagTailX0RatChunk000Sub001Block144Part014
    + surrogateDiagTailX0RatChunk000Sub001Block144Part015
    + surrogateDiagTailX0RatChunk000Sub001Block144Part016
    + surrogateDiagTailX0RatChunk000Sub001Block144Part017
    + surrogateDiagTailX0RatChunk000Sub001Block144Part018
    + surrogateDiagTailX0RatChunk000Sub001Block144Part019
    + surrogateDiagTailX0RatChunk000Sub001Block144Part020
    + surrogateDiagTailX0RatChunk000Sub001Block144Part021
    + surrogateDiagTailX0RatChunk000Sub001Block144Part022
    + surrogateDiagTailX0RatChunk000Sub001Block144Part023
    + surrogateDiagTailX0RatChunk000Sub001Block144Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block144_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block144Head + surrogateDiagTailX0RatChunk000Sub001Block144Mid + surrogateDiagTailX0RatChunk000Sub001Block144Tail =
      surrogateDiagTailX0RatChunk000Sub001Block144 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block144Head surrogateDiagTailX0RatChunk000Sub001Block144Mid surrogateDiagTailX0RatChunk000Sub001Block144Tail surrogateDiagTailX0RatChunk000Sub001Block144
  ring

def SurrogateDiagonalTailChunk000Sub001Block144HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block144HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block144Head

def SurrogateDiagonalTailChunk000Sub001Block144MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block144MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block144Mid

def SurrogateDiagonalTailChunk000Sub001Block144TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block144TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block144Tail

theorem surrogateDiagonalTailChunk000Sub001Block144_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block144HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block144MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block144TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block144Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block144 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block144HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block144MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block144TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block144Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block144_eq_head_add_mid_add_tail

/-- Block 145 covers tail-support indices [8625,8650) and q from 14241 to 14282. -/

def TailChunk000Sub001Block145Part000SupportExplicit : Finset ℕ :=
  ([14241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part000 : ℚ :=
  (2258452441 : ℚ) / 28661449543680000

def SurrogateDiagonalTailChunk000Sub001Block145Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14241
    = surrogateDiagTailX0RatChunk000Sub001Block145Part000

theorem surrogateDiagonalTailChunk000Sub001Block145Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part000] using hcert

def TailChunk000Sub001Block145Part001SupportExplicit : Finset ℕ :=
  ([14242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block145Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14242
    = surrogateDiagTailX0RatChunk000Sub001Block145Part001

theorem surrogateDiagonalTailChunk000Sub001Block145Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part001] using hcert

def TailChunk000Sub001Block145Part002SupportExplicit : Finset ℕ :=
  ([14243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block145Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14243
    = surrogateDiagTailX0RatChunk000Sub001Block145Part002

theorem surrogateDiagonalTailChunk000Sub001Block145Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part002] using hcert

def TailChunk000Sub001Block145Part003SupportExplicit : Finset ℕ :=
  ([14245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part003 : ℚ :=
  (1097947801 : ℚ) / 11611827693158400

def SurrogateDiagonalTailChunk000Sub001Block145Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14245
    = surrogateDiagTailX0RatChunk000Sub001Block145Part003

theorem surrogateDiagonalTailChunk000Sub001Block145Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part003] using hcert

def TailChunk000Sub001Block145Part004SupportExplicit : Finset ℕ :=
  ([14246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part004 : ℚ :=
  (45250670925 : ℚ) / 1667595297927725056

def SurrogateDiagonalTailChunk000Sub001Block145Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14246
    = surrogateDiagTailX0RatChunk000Sub001Block145Part004

theorem surrogateDiagonalTailChunk000Sub001Block145Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part004] using hcert

def TailChunk000Sub001Block145Part005SupportExplicit : Finset ℕ :=
  ([14249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block145Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14249
    = surrogateDiagTailX0RatChunk000Sub001Block145Part005

theorem surrogateDiagonalTailChunk000Sub001Block145Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part005] using hcert

def TailChunk000Sub001Block145Part006SupportExplicit : Finset ℕ :=
  ([14251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block145Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14251
    = surrogateDiagTailX0RatChunk000Sub001Block145Part006

theorem surrogateDiagonalTailChunk000Sub001Block145Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part006] using hcert

def TailChunk000Sub001Block145Part007SupportExplicit : Finset ℕ :=
  ([14253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part007 : ℚ :=
  (225725011 : ℚ) / 3258676605000000

def SurrogateDiagonalTailChunk000Sub001Block145Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14253
    = surrogateDiagTailX0RatChunk000Sub001Block145Part007

theorem surrogateDiagonalTailChunk000Sub001Block145Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part007] using hcert

def TailChunk000Sub001Block145Part008SupportExplicit : Finset ℕ :=
  ([14254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block145Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14254
    = surrogateDiagTailX0RatChunk000Sub001Block145Part008

theorem surrogateDiagonalTailChunk000Sub001Block145Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part008] using hcert

def TailChunk000Sub001Block145Part009SupportExplicit : Finset ℕ :=
  ([14255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part009 : ℚ :=
  (13551462763 : ℚ) / 563099317344000000

def SurrogateDiagonalTailChunk000Sub001Block145Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14255
    = surrogateDiagTailX0RatChunk000Sub001Block145Part009

theorem surrogateDiagonalTailChunk000Sub001Block145Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part009] using hcert

def TailChunk000Sub001Block145Part010SupportExplicit : Finset ℕ :=
  ([14257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part010 : ℚ :=
  (33780293325 : ℚ) / 31438234916966465536

def SurrogateDiagonalTailChunk000Sub001Block145Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14257
    = surrogateDiagTailX0RatChunk000Sub001Block145Part010

theorem surrogateDiagonalTailChunk000Sub001Block145Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part010] using hcert

def TailChunk000Sub001Block145Part011SupportExplicit : Finset ℕ :=
  ([14258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block145Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14258
    = surrogateDiagTailX0RatChunk000Sub001Block145Part011

theorem surrogateDiagonalTailChunk000Sub001Block145Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part011] using hcert

def TailChunk000Sub001Block145Part012SupportExplicit : Finset ℕ :=
  ([14261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part012 : ℚ :=
  (378832400125 : ℚ) / 74815926702828945408

def SurrogateDiagonalTailChunk000Sub001Block145Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14261
    = surrogateDiagTailX0RatChunk000Sub001Block145Part012

theorem surrogateDiagonalTailChunk000Sub001Block145Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part012] using hcert

def TailChunk000Sub001Block145Part013SupportExplicit : Finset ℕ :=
  ([14262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part013 : ℚ :=
  (353077876475 : ℚ) / 637532884708245504

def SurrogateDiagonalTailChunk000Sub001Block145Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14262
    = surrogateDiagTailX0RatChunk000Sub001Block145Part013

theorem surrogateDiagonalTailChunk000Sub001Block145Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part013] using hcert

def TailChunk000Sub001Block145Part014SupportExplicit : Finset ℕ :=
  ([14263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part014 : ℚ :=
  (44679432225 : ℚ) / 13468884032528580608

def SurrogateDiagonalTailChunk000Sub001Block145Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14263
    = surrogateDiagTailX0RatChunk000Sub001Block145Part014

theorem surrogateDiagonalTailChunk000Sub001Block145Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part014] using hcert

def TailChunk000Sub001Block145Part015SupportExplicit : Finset ℕ :=
  ([14266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part015 : ℚ :=
  (325466414275 : ℚ) / 3480350413738808448

def SurrogateDiagonalTailChunk000Sub001Block145Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14266
    = surrogateDiagTailX0RatChunk000Sub001Block145Part015

theorem surrogateDiagonalTailChunk000Sub001Block145Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part015] using hcert

def TailChunk000Sub001Block145Part016SupportExplicit : Finset ℕ :=
  ([14267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part016 : ℚ :=
  (16911170821 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk000Sub001Block145Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14267
    = surrogateDiagTailX0RatChunk000Sub001Block145Part016

theorem surrogateDiagonalTailChunk000Sub001Block145Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part016] using hcert

def TailChunk000Sub001Block145Part017SupportExplicit : Finset ℕ :=
  ([14269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part017 : ℚ :=
  (372474971 : ℚ) / 123043353750000000

def SurrogateDiagonalTailChunk000Sub001Block145Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14269
    = surrogateDiagTailX0RatChunk000Sub001Block145Part017

theorem surrogateDiagonalTailChunk000Sub001Block145Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part017] using hcert

def TailChunk000Sub001Block145Part018SupportExplicit : Finset ℕ :=
  ([14270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part018 : ℚ :=
  (95593638175 : ℚ) / 661736263600722432

def SurrogateDiagonalTailChunk000Sub001Block145Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14270
    = surrogateDiagTailX0RatChunk000Sub001Block145Part018

theorem surrogateDiagonalTailChunk000Sub001Block145Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part018] using hcert

def TailChunk000Sub001Block145Part019SupportExplicit : Finset ℕ :=
  ([14271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part019 : ℚ :=
  (2099953903 : ℚ) / 27002934995097600

def SurrogateDiagonalTailChunk000Sub001Block145Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14271
    = surrogateDiagTailX0RatChunk000Sub001Block145Part019

theorem surrogateDiagonalTailChunk000Sub001Block145Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part019] using hcert

def TailChunk000Sub001Block145Part020SupportExplicit : Finset ℕ :=
  ([14273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part020 : ℚ :=
  (260475726575 : ℚ) / 27952366594488128064

def SurrogateDiagonalTailChunk000Sub001Block145Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14273
    = surrogateDiagTailX0RatChunk000Sub001Block145Part020

theorem surrogateDiagonalTailChunk000Sub001Block145Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part020] using hcert

def TailChunk000Sub001Block145Part021SupportExplicit : Finset ℕ :=
  ([14277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part021 : ℚ :=
  (707767659275 : ℚ) / 10252141617961848384

def SurrogateDiagonalTailChunk000Sub001Block145Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14277
    = surrogateDiagTailX0RatChunk000Sub001Block145Part021

theorem surrogateDiagonalTailChunk000Sub001Block145Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part021] using hcert

def TailChunk000Sub001Block145Part022SupportExplicit : Finset ℕ :=
  ([14279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part022 : ℚ :=
  (294728929 : ℚ) / 388646965715973120

def SurrogateDiagonalTailChunk000Sub001Block145Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14279
    = surrogateDiagTailX0RatChunk000Sub001Block145Part022

theorem surrogateDiagonalTailChunk000Sub001Block145Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part022] using hcert

def TailChunk000Sub001Block145Part023SupportExplicit : Finset ℕ :=
  ([14281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block145Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14281
    = surrogateDiagTailX0RatChunk000Sub001Block145Part023

theorem surrogateDiagonalTailChunk000Sub001Block145Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part023] using hcert

def TailChunk000Sub001Block145Part024SupportExplicit : Finset ℕ :=
  ([14282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block145Part024 : ℚ :=
  (17710431625 : ℚ) / 1426861386935304192

def SurrogateDiagonalTailChunk000Sub001Block145Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14282
    = surrogateDiagTailX0RatChunk000Sub001Block145Part024

theorem surrogateDiagonalTailChunk000Sub001Block145Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block145Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block145Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block145Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block145Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block145Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block145Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block145HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block145Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block145Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block145Part000
    + surrogateDiagTailX0RatChunk000Sub001Block145Part001
    + surrogateDiagTailX0RatChunk000Sub001Block145Part002
    + surrogateDiagTailX0RatChunk000Sub001Block145Part003
    + surrogateDiagTailX0RatChunk000Sub001Block145Part004
    + surrogateDiagTailX0RatChunk000Sub001Block145Part005
    + surrogateDiagTailX0RatChunk000Sub001Block145Part006
    + surrogateDiagTailX0RatChunk000Sub001Block145Part007
    + surrogateDiagTailX0RatChunk000Sub001Block145Part008
    + surrogateDiagTailX0RatChunk000Sub001Block145Part009

def surrogateDiagonalTailChunk000Sub001Block145MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block145Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block145Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block145Part010
    + surrogateDiagTailX0RatChunk000Sub001Block145Part011
    + surrogateDiagTailX0RatChunk000Sub001Block145Part012
    + surrogateDiagTailX0RatChunk000Sub001Block145Part013
    + surrogateDiagTailX0RatChunk000Sub001Block145Part014
    + surrogateDiagTailX0RatChunk000Sub001Block145Part015
    + surrogateDiagTailX0RatChunk000Sub001Block145Part016
    + surrogateDiagTailX0RatChunk000Sub001Block145Part017
    + surrogateDiagTailX0RatChunk000Sub001Block145Part018
    + surrogateDiagTailX0RatChunk000Sub001Block145Part019

def surrogateDiagonalTailChunk000Sub001Block145TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block145Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block145Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block145Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block145Part020
    + surrogateDiagTailX0RatChunk000Sub001Block145Part021
    + surrogateDiagTailX0RatChunk000Sub001Block145Part022
    + surrogateDiagTailX0RatChunk000Sub001Block145Part023
    + surrogateDiagTailX0RatChunk000Sub001Block145Part024

def surrogateDiagonalTailChunk000Sub001Block145Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block145HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block145MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block145TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block145 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block145Part000
    + surrogateDiagTailX0RatChunk000Sub001Block145Part001
    + surrogateDiagTailX0RatChunk000Sub001Block145Part002
    + surrogateDiagTailX0RatChunk000Sub001Block145Part003
    + surrogateDiagTailX0RatChunk000Sub001Block145Part004
    + surrogateDiagTailX0RatChunk000Sub001Block145Part005
    + surrogateDiagTailX0RatChunk000Sub001Block145Part006
    + surrogateDiagTailX0RatChunk000Sub001Block145Part007
    + surrogateDiagTailX0RatChunk000Sub001Block145Part008
    + surrogateDiagTailX0RatChunk000Sub001Block145Part009
    + surrogateDiagTailX0RatChunk000Sub001Block145Part010
    + surrogateDiagTailX0RatChunk000Sub001Block145Part011
    + surrogateDiagTailX0RatChunk000Sub001Block145Part012
    + surrogateDiagTailX0RatChunk000Sub001Block145Part013
    + surrogateDiagTailX0RatChunk000Sub001Block145Part014
    + surrogateDiagTailX0RatChunk000Sub001Block145Part015
    + surrogateDiagTailX0RatChunk000Sub001Block145Part016
    + surrogateDiagTailX0RatChunk000Sub001Block145Part017
    + surrogateDiagTailX0RatChunk000Sub001Block145Part018
    + surrogateDiagTailX0RatChunk000Sub001Block145Part019
    + surrogateDiagTailX0RatChunk000Sub001Block145Part020
    + surrogateDiagTailX0RatChunk000Sub001Block145Part021
    + surrogateDiagTailX0RatChunk000Sub001Block145Part022
    + surrogateDiagTailX0RatChunk000Sub001Block145Part023
    + surrogateDiagTailX0RatChunk000Sub001Block145Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block145_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block145Head + surrogateDiagTailX0RatChunk000Sub001Block145Mid + surrogateDiagTailX0RatChunk000Sub001Block145Tail =
      surrogateDiagTailX0RatChunk000Sub001Block145 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block145Head surrogateDiagTailX0RatChunk000Sub001Block145Mid surrogateDiagTailX0RatChunk000Sub001Block145Tail surrogateDiagTailX0RatChunk000Sub001Block145
  ring

def SurrogateDiagonalTailChunk000Sub001Block145HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block145HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block145Head

def SurrogateDiagonalTailChunk000Sub001Block145MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block145MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block145Mid

def SurrogateDiagonalTailChunk000Sub001Block145TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block145TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block145Tail

theorem surrogateDiagonalTailChunk000Sub001Block145_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block145HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block145MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block145TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block145Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block145 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block145HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block145MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block145TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block145Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block145_eq_head_add_mid_add_tail

/-- Block 146 covers tail-support indices [8650,8675) and q from 14285 to 14322. -/

def TailChunk000Sub001Block146Part000SupportExplicit : Finset ℕ :=
  ([14285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part000 : ℚ :=
  (511046830375 : ℚ) / 42589215130963673088

def SurrogateDiagonalTailChunk000Sub001Block146Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14285
    = surrogateDiagTailX0RatChunk000Sub001Block146Part000

theorem surrogateDiagonalTailChunk000Sub001Block146Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part000] using hcert

def TailChunk000Sub001Block146Part001SupportExplicit : Finset ℕ :=
  ([14286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part001 : ℚ :=
  (10203 : ℚ) / 6162867200

def SurrogateDiagonalTailChunk000Sub001Block146Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14286
    = surrogateDiagTailX0RatChunk000Sub001Block146Part001

theorem surrogateDiagonalTailChunk000Sub001Block146Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part001] using hcert

def TailChunk000Sub001Block146Part002SupportExplicit : Finset ℕ :=
  ([14287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part002 : ℚ :=
  (4301554862225 : ℚ) / 19898724644657823744

def SurrogateDiagonalTailChunk000Sub001Block146Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14287
    = surrogateDiagTailX0RatChunk000Sub001Block146Part002

theorem surrogateDiagonalTailChunk000Sub001Block146Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part002] using hcert

def TailChunk000Sub001Block146Part003SupportExplicit : Finset ℕ :=
  ([14289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part003 : ℚ :=
  (6734194667 : ℚ) / 15482436924211200

def SurrogateDiagonalTailChunk000Sub001Block146Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14289
    = surrogateDiagTailX0RatChunk000Sub001Block146Part003

theorem surrogateDiagonalTailChunk000Sub001Block146Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part003] using hcert

def TailChunk000Sub001Block146Part004SupportExplicit : Finset ℕ :=
  ([14290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part004 : ℚ :=
  (403873330975 : ℚ) / 443637657614204928

def SurrogateDiagonalTailChunk000Sub001Block146Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14290
    = surrogateDiagTailX0RatChunk000Sub001Block146Part004

theorem surrogateDiagonalTailChunk000Sub001Block146Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part004] using hcert

def TailChunk000Sub001Block146Part005SupportExplicit : Finset ℕ :=
  ([14291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part005 : ℚ :=
  (96363166193 : ℚ) / 725492941574400000

def SurrogateDiagonalTailChunk000Sub001Block146Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14291
    = surrogateDiagTailX0RatChunk000Sub001Block146Part005

theorem surrogateDiagonalTailChunk000Sub001Block146Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part005] using hcert

def TailChunk000Sub001Block146Part006SupportExplicit : Finset ℕ :=
  ([14293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part006 : ℚ :=
  (3192028890625 : ℚ) / 26081880314794919712

def SurrogateDiagonalTailChunk000Sub001Block146Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14293
    = surrogateDiagTailX0RatChunk000Sub001Block146Part006

theorem surrogateDiagonalTailChunk000Sub001Block146Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part006] using hcert

def TailChunk000Sub001Block146Part007SupportExplicit : Finset ℕ :=
  ([14294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part007 : ℚ :=
  (6125506439 : ℚ) / 8253603798681600

def SurrogateDiagonalTailChunk000Sub001Block146Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14294
    = surrogateDiagTailX0RatChunk000Sub001Block146Part007

theorem surrogateDiagonalTailChunk000Sub001Block146Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part007] using hcert

def TailChunk000Sub001Block146Part008SupportExplicit : Finset ℕ :=
  ([14295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part008 : ℚ :=
  (4024102824325 : ℚ) / 8412684470313811968

def SurrogateDiagonalTailChunk000Sub001Block146Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14295
    = surrogateDiagTailX0RatChunk000Sub001Block146Part008

theorem surrogateDiagonalTailChunk000Sub001Block146Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part008] using hcert

def TailChunk000Sub001Block146Part009SupportExplicit : Finset ℕ :=
  ([14298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part009 : ℚ :=
  (443502456025 : ℚ) / 321998522404875552

def SurrogateDiagonalTailChunk000Sub001Block146Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14298
    = surrogateDiagTailX0RatChunk000Sub001Block146Part009

theorem surrogateDiagonalTailChunk000Sub001Block146Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part009] using hcert

def TailChunk000Sub001Block146Part010SupportExplicit : Finset ℕ :=
  ([14299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part010 : ℚ :=
  (18370468861 : ℚ) / 143943320635545600

def SurrogateDiagonalTailChunk000Sub001Block146Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14299
    = surrogateDiagTailX0RatChunk000Sub001Block146Part010

theorem surrogateDiagonalTailChunk000Sub001Block146Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part010] using hcert

def TailChunk000Sub001Block146Part011SupportExplicit : Finset ℕ :=
  ([14302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part011 : ℚ :=
  (51136801 : ℚ) / 104561308330050

def SurrogateDiagonalTailChunk000Sub001Block146Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14302
    = surrogateDiagTailX0RatChunk000Sub001Block146Part011

theorem surrogateDiagonalTailChunk000Sub001Block146Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part011] using hcert

def TailChunk000Sub001Block146Part012SupportExplicit : Finset ℕ :=
  ([14303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part012 : ℚ :=
  (3196497015625 : ℚ) / 26154954109969037202

def SurrogateDiagonalTailChunk000Sub001Block146Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14303
    = surrogateDiagTailX0RatChunk000Sub001Block146Part012

theorem surrogateDiagonalTailChunk000Sub001Block146Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part012] using hcert

def TailChunk000Sub001Block146Part013SupportExplicit : Finset ℕ :=
  ([14305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part013 : ℚ :=
  (347715734479 : ℚ) / 1713132475679539200

def SurrogateDiagonalTailChunk000Sub001Block146Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14305
    = surrogateDiagTailX0RatChunk000Sub001Block146Part013

theorem surrogateDiagonalTailChunk000Sub001Block146Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part013] using hcert

def TailChunk000Sub001Block146Part014SupportExplicit : Finset ℕ :=
  ([14306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part014 : ℚ :=
  (20029945437 : ℚ) / 36063933907179200

def SurrogateDiagonalTailChunk000Sub001Block146Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14306
    = surrogateDiagTailX0RatChunk000Sub001Block146Part014

theorem surrogateDiagonalTailChunk000Sub001Block146Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part014] using hcert

def TailChunk000Sub001Block146Part015SupportExplicit : Finset ℕ :=
  ([14307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part015 : ℚ :=
  (208097379247 : ℚ) / 656231220000000000

def SurrogateDiagonalTailChunk000Sub001Block146Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14307
    = surrogateDiagTailX0RatChunk000Sub001Block146Part015

theorem surrogateDiagonalTailChunk000Sub001Block146Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part015] using hcert

def TailChunk000Sub001Block146Part016SupportExplicit : Finset ℕ :=
  ([14309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part016 : ℚ :=
  (488901427567 : ℚ) / 3755292685251379200

def SurrogateDiagonalTailChunk000Sub001Block146Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14309
    = surrogateDiagTailX0RatChunk000Sub001Block146Part016

theorem surrogateDiagonalTailChunk000Sub001Block146Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part016] using hcert

def TailChunk000Sub001Block146Part017SupportExplicit : Finset ℕ :=
  ([14311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part017 : ℚ :=
  (435345485167 : ℚ) / 2856671220000000000

def SurrogateDiagonalTailChunk000Sub001Block146Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14311
    = surrogateDiagTailX0RatChunk000Sub001Block146Part017

theorem surrogateDiagonalTailChunk000Sub001Block146Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part017] using hcert

def TailChunk000Sub001Block146Part018SupportExplicit : Finset ℕ :=
  ([14313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part018 : ℚ :=
  (5013745706725 : ℚ) / 14886622218413703168

def SurrogateDiagonalTailChunk000Sub001Block146Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14313
    = surrogateDiagTailX0RatChunk000Sub001Block146Part018

theorem surrogateDiagonalTailChunk000Sub001Block146Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part018] using hcert

def TailChunk000Sub001Block146Part019SupportExplicit : Finset ℕ :=
  ([14314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part019 : ℚ :=
  (5898381371 : ℚ) / 10198444733890560

def SurrogateDiagonalTailChunk000Sub001Block146Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14314
    = surrogateDiagTailX0RatChunk000Sub001Block146Part019

theorem surrogateDiagonalTailChunk000Sub001Block146Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part019] using hcert

def TailChunk000Sub001Block146Part020SupportExplicit : Finset ℕ :=
  ([14315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part020 : ℚ :=
  (3317517386225 : ℚ) / 11494298794195943424

def SurrogateDiagonalTailChunk000Sub001Block146Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14315
    = surrogateDiagTailX0RatChunk000Sub001Block146Part020

theorem surrogateDiagonalTailChunk000Sub001Block146Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part020] using hcert

def TailChunk000Sub001Block146Part021SupportExplicit : Finset ℕ :=
  ([14317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part021 : ℚ :=
  (12457282591525 : ℚ) / 98162111476641449088

def SurrogateDiagonalTailChunk000Sub001Block146Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14317
    = surrogateDiagTailX0RatChunk000Sub001Block146Part021

theorem surrogateDiagonalTailChunk000Sub001Block146Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part021] using hcert

def TailChunk000Sub001Block146Part022SupportExplicit : Finset ℕ :=
  ([14318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part022 : ℚ :=
  (800801265625 : ℚ) / 1641094703270802162

def SurrogateDiagonalTailChunk000Sub001Block146Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14318
    = surrogateDiagTailX0RatChunk000Sub001Block146Part022

theorem surrogateDiagonalTailChunk000Sub001Block146Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part022] using hcert

def TailChunk000Sub001Block146Part023SupportExplicit : Finset ℕ :=
  ([14321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part023 : ℚ :=
  (5127276025 : ℚ) / 42058998011338752

def SurrogateDiagonalTailChunk000Sub001Block146Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14321
    = surrogateDiagTailX0RatChunk000Sub001Block146Part023

theorem surrogateDiagonalTailChunk000Sub001Block146Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part023] using hcert

def TailChunk000Sub001Block146Part024SupportExplicit : Finset ℕ :=
  ([14322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block146Part024 : ℚ :=
  (1892409113 : ℚ) / 622204416000000

def SurrogateDiagonalTailChunk000Sub001Block146Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14322
    = surrogateDiagTailX0RatChunk000Sub001Block146Part024

theorem surrogateDiagonalTailChunk000Sub001Block146Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block146Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block146Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block146Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block146Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block146Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block146Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block146HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block146Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block146Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block146Part000
    + surrogateDiagTailX0RatChunk000Sub001Block146Part001
    + surrogateDiagTailX0RatChunk000Sub001Block146Part002
    + surrogateDiagTailX0RatChunk000Sub001Block146Part003
    + surrogateDiagTailX0RatChunk000Sub001Block146Part004
    + surrogateDiagTailX0RatChunk000Sub001Block146Part005
    + surrogateDiagTailX0RatChunk000Sub001Block146Part006
    + surrogateDiagTailX0RatChunk000Sub001Block146Part007
    + surrogateDiagTailX0RatChunk000Sub001Block146Part008
    + surrogateDiagTailX0RatChunk000Sub001Block146Part009

def surrogateDiagonalTailChunk000Sub001Block146MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block146Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block146Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block146Part010
    + surrogateDiagTailX0RatChunk000Sub001Block146Part011
    + surrogateDiagTailX0RatChunk000Sub001Block146Part012
    + surrogateDiagTailX0RatChunk000Sub001Block146Part013
    + surrogateDiagTailX0RatChunk000Sub001Block146Part014
    + surrogateDiagTailX0RatChunk000Sub001Block146Part015
    + surrogateDiagTailX0RatChunk000Sub001Block146Part016
    + surrogateDiagTailX0RatChunk000Sub001Block146Part017
    + surrogateDiagTailX0RatChunk000Sub001Block146Part018
    + surrogateDiagTailX0RatChunk000Sub001Block146Part019

def surrogateDiagonalTailChunk000Sub001Block146TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block146Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block146Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block146Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block146Part020
    + surrogateDiagTailX0RatChunk000Sub001Block146Part021
    + surrogateDiagTailX0RatChunk000Sub001Block146Part022
    + surrogateDiagTailX0RatChunk000Sub001Block146Part023
    + surrogateDiagTailX0RatChunk000Sub001Block146Part024

def surrogateDiagonalTailChunk000Sub001Block146Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block146HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block146MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block146TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block146 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block146Part000
    + surrogateDiagTailX0RatChunk000Sub001Block146Part001
    + surrogateDiagTailX0RatChunk000Sub001Block146Part002
    + surrogateDiagTailX0RatChunk000Sub001Block146Part003
    + surrogateDiagTailX0RatChunk000Sub001Block146Part004
    + surrogateDiagTailX0RatChunk000Sub001Block146Part005
    + surrogateDiagTailX0RatChunk000Sub001Block146Part006
    + surrogateDiagTailX0RatChunk000Sub001Block146Part007
    + surrogateDiagTailX0RatChunk000Sub001Block146Part008
    + surrogateDiagTailX0RatChunk000Sub001Block146Part009
    + surrogateDiagTailX0RatChunk000Sub001Block146Part010
    + surrogateDiagTailX0RatChunk000Sub001Block146Part011
    + surrogateDiagTailX0RatChunk000Sub001Block146Part012
    + surrogateDiagTailX0RatChunk000Sub001Block146Part013
    + surrogateDiagTailX0RatChunk000Sub001Block146Part014
    + surrogateDiagTailX0RatChunk000Sub001Block146Part015
    + surrogateDiagTailX0RatChunk000Sub001Block146Part016
    + surrogateDiagTailX0RatChunk000Sub001Block146Part017
    + surrogateDiagTailX0RatChunk000Sub001Block146Part018
    + surrogateDiagTailX0RatChunk000Sub001Block146Part019
    + surrogateDiagTailX0RatChunk000Sub001Block146Part020
    + surrogateDiagTailX0RatChunk000Sub001Block146Part021
    + surrogateDiagTailX0RatChunk000Sub001Block146Part022
    + surrogateDiagTailX0RatChunk000Sub001Block146Part023
    + surrogateDiagTailX0RatChunk000Sub001Block146Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block146_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block146Head + surrogateDiagTailX0RatChunk000Sub001Block146Mid + surrogateDiagTailX0RatChunk000Sub001Block146Tail =
      surrogateDiagTailX0RatChunk000Sub001Block146 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block146Head surrogateDiagTailX0RatChunk000Sub001Block146Mid surrogateDiagTailX0RatChunk000Sub001Block146Tail surrogateDiagTailX0RatChunk000Sub001Block146
  ring

def SurrogateDiagonalTailChunk000Sub001Block146HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block146HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block146Head

def SurrogateDiagonalTailChunk000Sub001Block146MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block146MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block146Mid

def SurrogateDiagonalTailChunk000Sub001Block146TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block146TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block146Tail

theorem surrogateDiagonalTailChunk000Sub001Block146_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block146HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block146MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block146TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block146Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block146 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block146HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block146MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block146TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block146Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block146_eq_head_add_mid_add_tail

/-- Block 147 covers tail-support indices [8675,8700) and q from 14323 to 14363. -/

def TailChunk000Sub001Block147Part000SupportExplicit : Finset ℕ :=
  ([14323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part000 : ℚ :=
  (3205442640625 : ℚ) / 26301562238257942482

def SurrogateDiagonalTailChunk000Sub001Block147Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14323
    = surrogateDiagTailX0RatChunk000Sub001Block147Part000

theorem surrogateDiagonalTailChunk000Sub001Block147Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part000] using hcert

def TailChunk000Sub001Block147Part001SupportExplicit : Finset ℕ :=
  ([14326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part001 : ℚ :=
  (856423747175 : ℚ) / 1115199931650932736

def SurrogateDiagonalTailChunk000Sub001Block147Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14326
    = surrogateDiagTailX0RatChunk000Sub001Block147Part001

theorem surrogateDiagonalTailChunk000Sub001Block147Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part001] using hcert

def TailChunk000Sub001Block147Part002SupportExplicit : Finset ℕ :=
  ([14327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part002 : ℚ :=
  (3207233265625 : ℚ) / 26330957666783265522

def SurrogateDiagonalTailChunk000Sub001Block147Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14327
    = surrogateDiagTailX0RatChunk000Sub001Block147Part002

theorem surrogateDiagonalTailChunk000Sub001Block147Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part002] using hcert

def TailChunk000Sub001Block147Part003SupportExplicit : Finset ℕ :=
  ([14329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part003 : ℚ :=
  (1106643945875 : ℚ) / 5690668474326122496

def SurrogateDiagonalTailChunk000Sub001Block147Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14329
    = surrogateDiagTailX0RatChunk000Sub001Block147Part003

theorem surrogateDiagonalTailChunk000Sub001Block147Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part003] using hcert

def TailChunk000Sub001Block147Part004SupportExplicit : Finset ℕ :=
  ([14330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part004 : ℚ :=
  (1218413780075 : ℚ) / 1345887936362840064

def SurrogateDiagonalTailChunk000Sub001Block147Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14330
    = surrogateDiagTailX0RatChunk000Sub001Block147Part004

theorem surrogateDiagonalTailChunk000Sub001Block147Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part004] using hcert

def TailChunk000Sub001Block147Part005SupportExplicit : Finset ℕ :=
  ([14331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part005 : ℚ :=
  (41473810037 : ℚ) / 128928486512394240

def SurrogateDiagonalTailChunk000Sub001Block147Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14331
    = surrogateDiagTailX0RatChunk000Sub001Block147Part005

theorem surrogateDiagonalTailChunk000Sub001Block147Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part005] using hcert

def TailChunk000Sub001Block147Part006SupportExplicit : Finset ℕ :=
  ([14333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part006 : ℚ :=
  (145561885211 : ℚ) / 958097114978774400

def SurrogateDiagonalTailChunk000Sub001Block147Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14333
    = surrogateDiagTailX0RatChunk000Sub001Block147Part006

theorem surrogateDiagonalTailChunk000Sub001Block147Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part006] using hcert

def TailChunk000Sub001Block147Part007SupportExplicit : Finset ℕ :=
  ([14334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part007 : ℚ :=
  (891477502475 : ℚ) / 650510237471007744

def SurrogateDiagonalTailChunk000Sub001Block147Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14334
    = surrogateDiagTailX0RatChunk000Sub001Block147Part007

theorem surrogateDiagonalTailChunk000Sub001Block147Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part007] using hcert

def TailChunk000Sub001Block147Part008SupportExplicit : Finset ℕ :=
  ([14335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part008 : ℚ :=
  (14291549093 : ℚ) / 64600414971494400

def SurrogateDiagonalTailChunk000Sub001Block147Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14335
    = surrogateDiagTailX0RatChunk000Sub001Block147Part008

theorem surrogateDiagonalTailChunk000Sub001Block147Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part008] using hcert

def TailChunk000Sub001Block147Part009SupportExplicit : Finset ℕ :=
  ([14338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part009 : ℚ :=
  (389040297875 : ℚ) / 748748689233968016

def SurrogateDiagonalTailChunk000Sub001Block147Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14338
    = surrogateDiagTailX0RatChunk000Sub001Block147Part009

theorem surrogateDiagonalTailChunk000Sub001Block147Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part009] using hcert

def TailChunk000Sub001Block147Part010SupportExplicit : Finset ℕ :=
  ([14339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part010 : ℚ :=
  (1395260306825 : ℚ) / 9558466758489159936

def SurrogateDiagonalTailChunk000Sub001Block147Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14339
    = surrogateDiagTailX0RatChunk000Sub001Block147Part010

theorem surrogateDiagonalTailChunk000Sub001Block147Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part010] using hcert

def TailChunk000Sub001Block147Part011SupportExplicit : Finset ℕ :=
  ([14341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part011 : ℚ :=
  (5141607025 : ℚ) / 42294457187357472

def SurrogateDiagonalTailChunk000Sub001Block147Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14341
    = surrogateDiagTailX0RatChunk000Sub001Block147Part011

theorem surrogateDiagonalTailChunk000Sub001Block147Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part011] using hcert

def TailChunk000Sub001Block147Part012SupportExplicit : Finset ℕ :=
  ([14342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part012 : ℚ :=
  (17800722277 : ℚ) / 34306860000000000

def SurrogateDiagonalTailChunk000Sub001Block147Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14342
    = surrogateDiagTailX0RatChunk000Sub001Block147Part012

theorem surrogateDiagonalTailChunk000Sub001Block147Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part012] using hcert

def TailChunk000Sub001Block147Part013SupportExplicit : Finset ℕ :=
  ([14343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part013 : ℚ :=
  (41213572775 : ℚ) / 103864129652676096

def SurrogateDiagonalTailChunk000Sub001Block147Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14343
    = surrogateDiagTailX0RatChunk000Sub001Block147Part013

theorem surrogateDiagonalTailChunk000Sub001Block147Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part013] using hcert

def TailChunk000Sub001Block147Part014SupportExplicit : Finset ℕ :=
  ([14345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part014 : ℚ :=
  (12667498573 : ℚ) / 54430442311680000

def SurrogateDiagonalTailChunk000Sub001Block147Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14345
    = surrogateDiagTailX0RatChunk000Sub001Block147Part014

theorem surrogateDiagonalTailChunk000Sub001Block147Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part014] using hcert

def TailChunk000Sub001Block147Part015SupportExplicit : Finset ℕ :=
  ([14347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part015 : ℚ :=
  (3216193890625 : ℚ) / 26478304580206052082

def SurrogateDiagonalTailChunk000Sub001Block147Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14347
    = surrogateDiagTailX0RatChunk000Sub001Block147Part015

theorem surrogateDiagonalTailChunk000Sub001Block147Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part015] using hcert

def TailChunk000Sub001Block147Part016SupportExplicit : Finset ℕ :=
  ([14349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part016 : ℚ :=
  (5717505521725 : ℚ) / 20921129544854164608

def SurrogateDiagonalTailChunk000Sub001Block147Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14349
    = surrogateDiagTailX0RatChunk000Sub001Block147Part016

theorem surrogateDiagonalTailChunk000Sub001Block147Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part016] using hcert

def TailChunk000Sub001Block147Part017SupportExplicit : Finset ℕ :=
  ([14351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part017 : ℚ :=
  (12520712351125 : ℚ) / 99170186514588499968

def SurrogateDiagonalTailChunk000Sub001Block147Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14351
    = surrogateDiagTailX0RatChunk000Sub001Block147Part017

theorem surrogateDiagonalTailChunk000Sub001Block147Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part017] using hcert

def TailChunk000Sub001Block147Part018SupportExplicit : Finset ℕ :=
  ([14353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part018 : ℚ :=
  (10800253333 : ℚ) / 82021415047608960

def SurrogateDiagonalTailChunk000Sub001Block147Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14353
    = surrogateDiagTailX0RatChunk000Sub001Block147Part018

theorem surrogateDiagonalTailChunk000Sub001Block147Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part018] using hcert

def TailChunk000Sub001Block147Part019SupportExplicit : Finset ℕ :=
  ([14354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part019 : ℚ :=
  (804833265625 : ℚ) / 1657664312344515072

def SurrogateDiagonalTailChunk000Sub001Block147Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14354
    = surrogateDiagTailX0RatChunk000Sub001Block147Part019

theorem surrogateDiagonalTailChunk000Sub001Block147Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part019] using hcert

def TailChunk000Sub001Block147Part020SupportExplicit : Finset ℕ :=
  ([14358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part020 : ℚ :=
  (214624875 : ℚ) / 130949755715584

def SurrogateDiagonalTailChunk000Sub001Block147Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14358
    = surrogateDiagTailX0RatChunk000Sub001Block147Part020

theorem surrogateDiagonalTailChunk000Sub001Block147Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part020] using hcert

def TailChunk000Sub001Block147Part021SupportExplicit : Finset ℕ :=
  ([14359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part021 : ℚ :=
  (2085159316725 : ℚ) / 16490916992797887488

def SurrogateDiagonalTailChunk000Sub001Block147Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14359
    = surrogateDiagTailX0RatChunk000Sub001Block147Part021

theorem surrogateDiagonalTailChunk000Sub001Block147Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part021] using hcert

def TailChunk000Sub001Block147Part022SupportExplicit : Finset ℕ :=
  ([14361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part022 : ℚ :=
  (5727073521325 : ℚ) / 20991217019667788928

def SurrogateDiagonalTailChunk000Sub001Block147Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14361
    = surrogateDiagTailX0RatChunk000Sub001Block147Part022

theorem surrogateDiagonalTailChunk000Sub001Block147Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part022] using hcert

def TailChunk000Sub001Block147Part023SupportExplicit : Finset ℕ :=
  ([14362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part023 : ℚ :=
  (774979446775 : ℚ) / 1477054027959404832

def SurrogateDiagonalTailChunk000Sub001Block147Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14362
    = surrogateDiagTailX0RatChunk000Sub001Block147Part023

theorem surrogateDiagonalTailChunk000Sub001Block147Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part023] using hcert

def TailChunk000Sub001Block147Part024SupportExplicit : Finset ℕ :=
  ([14363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block147Part024 : ℚ :=
  (248302280891 : ℚ) / 1943234828579865600

def SurrogateDiagonalTailChunk000Sub001Block147Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14363
    = surrogateDiagTailX0RatChunk000Sub001Block147Part024

theorem surrogateDiagonalTailChunk000Sub001Block147Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block147Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block147Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block147Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block147Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block147Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block147Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block147HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block147Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block147Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block147Part000
    + surrogateDiagTailX0RatChunk000Sub001Block147Part001
    + surrogateDiagTailX0RatChunk000Sub001Block147Part002
    + surrogateDiagTailX0RatChunk000Sub001Block147Part003
    + surrogateDiagTailX0RatChunk000Sub001Block147Part004
    + surrogateDiagTailX0RatChunk000Sub001Block147Part005
    + surrogateDiagTailX0RatChunk000Sub001Block147Part006
    + surrogateDiagTailX0RatChunk000Sub001Block147Part007
    + surrogateDiagTailX0RatChunk000Sub001Block147Part008
    + surrogateDiagTailX0RatChunk000Sub001Block147Part009

def surrogateDiagonalTailChunk000Sub001Block147MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block147Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block147Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block147Part010
    + surrogateDiagTailX0RatChunk000Sub001Block147Part011
    + surrogateDiagTailX0RatChunk000Sub001Block147Part012
    + surrogateDiagTailX0RatChunk000Sub001Block147Part013
    + surrogateDiagTailX0RatChunk000Sub001Block147Part014
    + surrogateDiagTailX0RatChunk000Sub001Block147Part015
    + surrogateDiagTailX0RatChunk000Sub001Block147Part016
    + surrogateDiagTailX0RatChunk000Sub001Block147Part017
    + surrogateDiagTailX0RatChunk000Sub001Block147Part018
    + surrogateDiagTailX0RatChunk000Sub001Block147Part019

def surrogateDiagonalTailChunk000Sub001Block147TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block147Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block147Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block147Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block147Part020
    + surrogateDiagTailX0RatChunk000Sub001Block147Part021
    + surrogateDiagTailX0RatChunk000Sub001Block147Part022
    + surrogateDiagTailX0RatChunk000Sub001Block147Part023
    + surrogateDiagTailX0RatChunk000Sub001Block147Part024

def surrogateDiagonalTailChunk000Sub001Block147Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block147HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block147MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block147TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block147 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block147Part000
    + surrogateDiagTailX0RatChunk000Sub001Block147Part001
    + surrogateDiagTailX0RatChunk000Sub001Block147Part002
    + surrogateDiagTailX0RatChunk000Sub001Block147Part003
    + surrogateDiagTailX0RatChunk000Sub001Block147Part004
    + surrogateDiagTailX0RatChunk000Sub001Block147Part005
    + surrogateDiagTailX0RatChunk000Sub001Block147Part006
    + surrogateDiagTailX0RatChunk000Sub001Block147Part007
    + surrogateDiagTailX0RatChunk000Sub001Block147Part008
    + surrogateDiagTailX0RatChunk000Sub001Block147Part009
    + surrogateDiagTailX0RatChunk000Sub001Block147Part010
    + surrogateDiagTailX0RatChunk000Sub001Block147Part011
    + surrogateDiagTailX0RatChunk000Sub001Block147Part012
    + surrogateDiagTailX0RatChunk000Sub001Block147Part013
    + surrogateDiagTailX0RatChunk000Sub001Block147Part014
    + surrogateDiagTailX0RatChunk000Sub001Block147Part015
    + surrogateDiagTailX0RatChunk000Sub001Block147Part016
    + surrogateDiagTailX0RatChunk000Sub001Block147Part017
    + surrogateDiagTailX0RatChunk000Sub001Block147Part018
    + surrogateDiagTailX0RatChunk000Sub001Block147Part019
    + surrogateDiagTailX0RatChunk000Sub001Block147Part020
    + surrogateDiagTailX0RatChunk000Sub001Block147Part021
    + surrogateDiagTailX0RatChunk000Sub001Block147Part022
    + surrogateDiagTailX0RatChunk000Sub001Block147Part023
    + surrogateDiagTailX0RatChunk000Sub001Block147Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block147_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block147Head + surrogateDiagTailX0RatChunk000Sub001Block147Mid + surrogateDiagTailX0RatChunk000Sub001Block147Tail =
      surrogateDiagTailX0RatChunk000Sub001Block147 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block147Head surrogateDiagTailX0RatChunk000Sub001Block147Mid surrogateDiagTailX0RatChunk000Sub001Block147Tail surrogateDiagTailX0RatChunk000Sub001Block147
  ring

def SurrogateDiagonalTailChunk000Sub001Block147HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block147HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block147Head

def SurrogateDiagonalTailChunk000Sub001Block147MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block147MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block147Mid

def SurrogateDiagonalTailChunk000Sub001Block147TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block147TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block147Tail

theorem surrogateDiagonalTailChunk000Sub001Block147_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block147HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block147MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block147TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block147Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block147 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block147HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block147MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block147TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block147Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block147_eq_head_add_mid_add_tail

/-- Block 148 covers tail-support indices [8700,8725) and q from 14366 to 14405. -/

def TailChunk000Sub001Block148Part000SupportExplicit : Finset ℕ :=
  ([14366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part000 : ℚ :=
  (113861024521 : ℚ) / 180749553498163200

def SurrogateDiagonalTailChunk000Sub001Block148Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14366
    = surrogateDiagTailX0RatChunk000Sub001Block148Part000

theorem surrogateDiagonalTailChunk000Sub001Block148Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part000] using hcert

def TailChunk000Sub001Block148Part001SupportExplicit : Finset ℕ :=
  ([14367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part001 : ℚ :=
  (5731860521125 : ℚ) / 21026326720584665088

def SurrogateDiagonalTailChunk000Sub001Block148Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14367
    = surrogateDiagTailX0RatChunk000Sub001Block148Part001

theorem surrogateDiagonalTailChunk000Sub001Block148Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part001] using hcert

def TailChunk000Sub001Block148Part002SupportExplicit : Finset ℕ :=
  ([14369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part002 : ℚ :=
  (3226065015625 : ℚ) / 26641099517880041472

def SurrogateDiagonalTailChunk000Sub001Block148Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14369
    = surrogateDiagTailX0RatChunk000Sub001Block148Part002

theorem surrogateDiagonalTailChunk000Sub001Block148Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part002] using hcert

def TailChunk000Sub001Block148Part003SupportExplicit : Finset ℕ :=
  ([14370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part003 : ℚ :=
  (233698753875 : ℚ) / 89114247242498048

def SurrogateDiagonalTailChunk000Sub001Block148Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14370
    = surrogateDiagTailX0RatChunk000Sub001Block148Part003

theorem surrogateDiagonalTailChunk000Sub001Block148Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part003] using hcert

def TailChunk000Sub001Block148Part004SupportExplicit : Finset ℕ :=
  ([14371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part004 : ℚ :=
  (9739755052225 : ℚ) / 57456780347253639168

def SurrogateDiagonalTailChunk000Sub001Block148Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14371
    = surrogateDiagTailX0RatChunk000Sub001Block148Part004

theorem surrogateDiagonalTailChunk000Sub001Block148Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part004] using hcert

def TailChunk000Sub001Block148Part005SupportExplicit : Finset ℕ :=
  ([14374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part005 : ℚ :=
  (807077640625 : ℚ) / 1666923691106616402

def SurrogateDiagonalTailChunk000Sub001Block148Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14374
    = surrogateDiagTailX0RatChunk000Sub001Block148Part005

theorem surrogateDiagonalTailChunk000Sub001Block148Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part005] using hcert

def TailChunk000Sub001Block148Part006SupportExplicit : Finset ℕ :=
  ([14377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part006 : ℚ :=
  (439372177213 : ℚ) / 2909776003328899200

def SurrogateDiagonalTailChunk000Sub001Block148Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14377
    = surrogateDiagTailX0RatChunk000Sub001Block148Part006

theorem surrogateDiagonalTailChunk000Sub001Block148Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part006] using hcert

def TailChunk000Sub001Block148Part007SupportExplicit : Finset ℕ :=
  ([14378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part007 : ℚ :=
  (2341319035675 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub001Block148Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14378
    = surrogateDiagTailX0RatChunk000Sub001Block148Part007

theorem surrogateDiagonalTailChunk000Sub001Block148Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part007] using hcert

def TailChunk000Sub001Block148Part008SupportExplicit : Finset ℕ :=
  ([14379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part008 : ℚ :=
  (5741440520725 : ℚ) / 21096678233296109568

def SurrogateDiagonalTailChunk000Sub001Block148Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14379
    = surrogateDiagTailX0RatChunk000Sub001Block148Part008

theorem surrogateDiagonalTailChunk000Sub001Block148Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part008] using hcert

def TailChunk000Sub001Block148Part009SupportExplicit : Finset ℕ :=
  ([14381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part009 : ℚ :=
  (6263900816975 : ℚ) / 49585093257294249984

def SurrogateDiagonalTailChunk000Sub001Block148Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14381
    = surrogateDiagTailX0RatChunk000Sub001Block148Part009

theorem surrogateDiagonalTailChunk000Sub001Block148Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part009] using hcert

def TailChunk000Sub001Block148Part010SupportExplicit : Finset ℕ :=
  ([14383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part010 : ℚ :=
  (842489825675 : ℚ) / 6124575963918892032

def SurrogateDiagonalTailChunk000Sub001Block148Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14383
    = surrogateDiagTailX0RatChunk000Sub001Block148Part010

theorem surrogateDiagonalTailChunk000Sub001Block148Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part010] using hcert

def TailChunk000Sub001Block148Part011SupportExplicit : Finset ℕ :=
  ([14385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part011 : ℚ :=
  (44640469975 : ℚ) / 63068854837837824

def SurrogateDiagonalTailChunk000Sub001Block148Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14385
    = surrogateDiagTailX0RatChunk000Sub001Block148Part011

theorem surrogateDiagonalTailChunk000Sub001Block148Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part011] using hcert

def TailChunk000Sub001Block148Part012SupportExplicit : Finset ℕ :=
  ([14386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part012 : ℚ :=
  (808425765625 : ℚ) / 1672497905081037312

def SurrogateDiagonalTailChunk000Sub001Block148Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14386
    = surrogateDiagTailX0RatChunk000Sub001Block148Part012

theorem surrogateDiagonalTailChunk000Sub001Block148Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part012] using hcert

def TailChunk000Sub001Block148Part013SupportExplicit : Finset ℕ :=
  ([14387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part013 : ℚ :=
  (3234152640625 : ℚ) / 26774852770614178002

def SurrogateDiagonalTailChunk000Sub001Block148Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14387
    = surrogateDiagTailX0RatChunk000Sub001Block148Part013

theorem surrogateDiagonalTailChunk000Sub001Block148Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part013] using hcert

def TailChunk000Sub001Block148Part014SupportExplicit : Finset ℕ :=
  ([14389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part014 : ℚ :=
  (3235051890625 : ℚ) / 26789745269883400992

def SurrogateDiagonalTailChunk000Sub001Block148Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14389
    = surrogateDiagTailX0RatChunk000Sub001Block148Part014

theorem surrogateDiagonalTailChunk000Sub001Block148Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part014] using hcert

def TailChunk000Sub001Block148Part015SupportExplicit : Finset ℕ :=
  ([14390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part015 : ℚ :=
  (775978880475 : ℚ) / 912391254207502336

def SurrogateDiagonalTailChunk000Sub001Block148Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14390
    = surrogateDiagTailX0RatChunk000Sub001Block148Part015

theorem surrogateDiagonalTailChunk000Sub001Block148Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part015] using hcert

def TailChunk000Sub001Block148Part016SupportExplicit : Finset ℕ :=
  ([14393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part016 : ℚ :=
  (1368833565425 : ℚ) / 10575995440032940032

def SurrogateDiagonalTailChunk000Sub001Block148Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14393
    = surrogateDiagTailX0RatChunk000Sub001Block148Part016

theorem surrogateDiagonalTailChunk000Sub001Block148Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part016] using hcert

def TailChunk000Sub001Block148Part017SupportExplicit : Finset ℕ :=
  ([14394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part017 : ℚ :=
  (449478411925 : ℚ) / 330737595924486432

def SurrogateDiagonalTailChunk000Sub001Block148Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14394
    = surrogateDiagTailX0RatChunk000Sub001Block148Part017

theorem surrogateDiagonalTailChunk000Sub001Block148Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part017] using hcert

def TailChunk000Sub001Block148Part018SupportExplicit : Finset ℕ :=
  ([14395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part018 : ℚ :=
  (8802642941725 : ℚ) / 43916728698193594368

def SurrogateDiagonalTailChunk000Sub001Block148Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14395
    = surrogateDiagTailX0RatChunk000Sub001Block148Part018

theorem surrogateDiagonalTailChunk000Sub001Block148Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part018] using hcert

def TailChunk000Sub001Block148Part019SupportExplicit : Finset ℕ :=
  ([14397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part019 : ℚ :=
  (5755825520125 : ℚ) / 21202536331591091328

def SurrogateDiagonalTailChunk000Sub001Block148Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14397
    = surrogateDiagTailX0RatChunk000Sub001Block148Part019

theorem surrogateDiagonalTailChunk000Sub001Block148Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part019] using hcert

def TailChunk000Sub001Block148Part020SupportExplicit : Finset ℕ :=
  ([14398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part020 : ℚ :=
  (58524924175 : ℚ) / 106741331176955904

def SurrogateDiagonalTailChunk000Sub001Block148Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14398
    = surrogateDiagTailX0RatChunk000Sub001Block148Part020

theorem surrogateDiagonalTailChunk000Sub001Block148Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part020] using hcert

def TailChunk000Sub001Block148Part021SupportExplicit : Finset ℕ :=
  ([14401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part021 : ℚ :=
  (207388801 : ℚ) / 1720270769356800

def SurrogateDiagonalTailChunk000Sub001Block148Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14401
    = surrogateDiagTailX0RatChunk000Sub001Block148Part021

theorem surrogateDiagonalTailChunk000Sub001Block148Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part021] using hcert

def TailChunk000Sub001Block148Part022SupportExplicit : Finset ℕ :=
  ([14402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part022 : ℚ :=
  (3006701241925 : ℚ) / 5359003968429030528

def SurrogateDiagonalTailChunk000Sub001Block148Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14402
    = surrogateDiagTailX0RatChunk000Sub001Block148Part022

theorem surrogateDiagonalTailChunk000Sub001Block148Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part022] using hcert

def TailChunk000Sub001Block148Part023SupportExplicit : Finset ℕ :=
  ([14403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part023 : ℚ :=
  (230424980797 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk000Sub001Block148Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14403
    = surrogateDiagTailX0RatChunk000Sub001Block148Part023

theorem surrogateDiagonalTailChunk000Sub001Block148Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part023] using hcert

def TailChunk000Sub001Block148Part024SupportExplicit : Finset ℕ :=
  ([14405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block148Part024 : ℚ :=
  (251280316075 : ℚ) / 1145317213755703296

def SurrogateDiagonalTailChunk000Sub001Block148Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14405
    = surrogateDiagTailX0RatChunk000Sub001Block148Part024

theorem surrogateDiagonalTailChunk000Sub001Block148Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block148Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block148Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block148Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block148Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block148Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block148Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block148HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block148Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block148Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block148Part000
    + surrogateDiagTailX0RatChunk000Sub001Block148Part001
    + surrogateDiagTailX0RatChunk000Sub001Block148Part002
    + surrogateDiagTailX0RatChunk000Sub001Block148Part003
    + surrogateDiagTailX0RatChunk000Sub001Block148Part004
    + surrogateDiagTailX0RatChunk000Sub001Block148Part005
    + surrogateDiagTailX0RatChunk000Sub001Block148Part006
    + surrogateDiagTailX0RatChunk000Sub001Block148Part007
    + surrogateDiagTailX0RatChunk000Sub001Block148Part008
    + surrogateDiagTailX0RatChunk000Sub001Block148Part009

def surrogateDiagonalTailChunk000Sub001Block148MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block148Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block148Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block148Part010
    + surrogateDiagTailX0RatChunk000Sub001Block148Part011
    + surrogateDiagTailX0RatChunk000Sub001Block148Part012
    + surrogateDiagTailX0RatChunk000Sub001Block148Part013
    + surrogateDiagTailX0RatChunk000Sub001Block148Part014
    + surrogateDiagTailX0RatChunk000Sub001Block148Part015
    + surrogateDiagTailX0RatChunk000Sub001Block148Part016
    + surrogateDiagTailX0RatChunk000Sub001Block148Part017
    + surrogateDiagTailX0RatChunk000Sub001Block148Part018
    + surrogateDiagTailX0RatChunk000Sub001Block148Part019

def surrogateDiagonalTailChunk000Sub001Block148TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block148Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block148Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block148Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block148Part020
    + surrogateDiagTailX0RatChunk000Sub001Block148Part021
    + surrogateDiagTailX0RatChunk000Sub001Block148Part022
    + surrogateDiagTailX0RatChunk000Sub001Block148Part023
    + surrogateDiagTailX0RatChunk000Sub001Block148Part024

def surrogateDiagonalTailChunk000Sub001Block148Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block148HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block148MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block148TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block148 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block148Part000
    + surrogateDiagTailX0RatChunk000Sub001Block148Part001
    + surrogateDiagTailX0RatChunk000Sub001Block148Part002
    + surrogateDiagTailX0RatChunk000Sub001Block148Part003
    + surrogateDiagTailX0RatChunk000Sub001Block148Part004
    + surrogateDiagTailX0RatChunk000Sub001Block148Part005
    + surrogateDiagTailX0RatChunk000Sub001Block148Part006
    + surrogateDiagTailX0RatChunk000Sub001Block148Part007
    + surrogateDiagTailX0RatChunk000Sub001Block148Part008
    + surrogateDiagTailX0RatChunk000Sub001Block148Part009
    + surrogateDiagTailX0RatChunk000Sub001Block148Part010
    + surrogateDiagTailX0RatChunk000Sub001Block148Part011
    + surrogateDiagTailX0RatChunk000Sub001Block148Part012
    + surrogateDiagTailX0RatChunk000Sub001Block148Part013
    + surrogateDiagTailX0RatChunk000Sub001Block148Part014
    + surrogateDiagTailX0RatChunk000Sub001Block148Part015
    + surrogateDiagTailX0RatChunk000Sub001Block148Part016
    + surrogateDiagTailX0RatChunk000Sub001Block148Part017
    + surrogateDiagTailX0RatChunk000Sub001Block148Part018
    + surrogateDiagTailX0RatChunk000Sub001Block148Part019
    + surrogateDiagTailX0RatChunk000Sub001Block148Part020
    + surrogateDiagTailX0RatChunk000Sub001Block148Part021
    + surrogateDiagTailX0RatChunk000Sub001Block148Part022
    + surrogateDiagTailX0RatChunk000Sub001Block148Part023
    + surrogateDiagTailX0RatChunk000Sub001Block148Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block148_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block148Head + surrogateDiagTailX0RatChunk000Sub001Block148Mid + surrogateDiagTailX0RatChunk000Sub001Block148Tail =
      surrogateDiagTailX0RatChunk000Sub001Block148 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block148Head surrogateDiagTailX0RatChunk000Sub001Block148Mid surrogateDiagTailX0RatChunk000Sub001Block148Tail surrogateDiagTailX0RatChunk000Sub001Block148
  ring

def SurrogateDiagonalTailChunk000Sub001Block148HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block148HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block148Head

def SurrogateDiagonalTailChunk000Sub001Block148MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block148MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block148Mid

def SurrogateDiagonalTailChunk000Sub001Block148TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block148TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block148Tail

theorem surrogateDiagonalTailChunk000Sub001Block148_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block148HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block148MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block148TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block148Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block148 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block148HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block148MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block148TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block148Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block148_eq_head_add_mid_add_tail

/-- Block 149 covers tail-support indices [8725,8750) and q from 14407 to 14447. -/

def TailChunk000Sub001Block149Part000SupportExplicit : Finset ℕ :=
  ([14407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part000 : ℚ :=
  (3243150765625 : ℚ) / 26924057496129085362

def SurrogateDiagonalTailChunk000Sub001Block149Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14407
    = surrogateDiagTailX0RatChunk000Sub001Block149Part000

theorem surrogateDiagonalTailChunk000Sub001Block149Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part000] using hcert

def TailChunk000Sub001Block149Part001SupportExplicit : Finset ℕ :=
  ([14410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part001 : ℚ :=
  (21506235691 : ℚ) / 18282695808000000

def SurrogateDiagonalTailChunk000Sub001Block149Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14410
    = surrogateDiagTailX0RatChunk000Sub001Block149Part001

theorem surrogateDiagonalTailChunk000Sub001Block149Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part001] using hcert

def TailChunk000Sub001Block149Part002SupportExplicit : Finset ℕ :=
  ([14411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part002 : ℚ :=
  (5191923025 : ℚ) / 43126356980296722

def SurrogateDiagonalTailChunk000Sub001Block149Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14411
    = surrogateDiagTailX0RatChunk000Sub001Block149Part002

theorem surrogateDiagonalTailChunk000Sub001Block149Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part002] using hcert

def TailChunk000Sub001Block149Part003SupportExplicit : Finset ℕ :=
  ([14413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part003 : ℚ :=
  (20647305667 : ℚ) / 106278063394406400

def SurrogateDiagonalTailChunk000Sub001Block149Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14413
    = surrogateDiagTailX0RatChunk000Sub001Block149Part003

theorem surrogateDiagonalTailChunk000Sub001Block149Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part003] using hcert

def TailChunk000Sub001Block149Part004SupportExplicit : Finset ℕ :=
  ([14414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part004 : ℚ :=
  (811575765625 : ℚ) / 1685558766633267762

def SurrogateDiagonalTailChunk000Sub001Block149Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14414
    = surrogateDiagTailX0RatChunk000Sub001Block149Part004

theorem surrogateDiagonalTailChunk000Sub001Block149Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part004] using hcert

def TailChunk000Sub001Block149Part005SupportExplicit : Finset ℕ :=
  ([14417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part005 : ℚ :=
  (1893487526575 : ℚ) / 13024457239755276288

def SurrogateDiagonalTailChunk000Sub001Block149Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14417
    = surrogateDiagTailX0RatChunk000Sub001Block149Part005

theorem surrogateDiagonalTailChunk000Sub001Block149Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part005] using hcert

def TailChunk000Sub001Block149Part006SupportExplicit : Finset ℕ :=
  ([14419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part006 : ℚ :=
  (3248555640625 : ℚ) / 27013879127904093522

def SurrogateDiagonalTailChunk000Sub001Block149Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14419
    = surrogateDiagTailX0RatChunk000Sub001Block149Part006

theorem surrogateDiagonalTailChunk000Sub001Block149Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part006] using hcert

def TailChunk000Sub001Block149Part007SupportExplicit : Finset ℕ :=
  ([14421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part007 : ℚ :=
  (57783859159 : ℚ) / 131179605907046400

def SurrogateDiagonalTailChunk000Sub001Block149Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14421
    = surrogateDiagTailX0RatChunk000Sub001Block149Part007

theorem surrogateDiagonalTailChunk000Sub001Block149Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part007] using hcert

def TailChunk000Sub001Block149Part008SupportExplicit : Finset ℕ :=
  ([14422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part008 : ℚ :=
  (1299963025 : ℚ) / 2702887122140562

def SurrogateDiagonalTailChunk000Sub001Block149Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14422
    = surrogateDiagTailX0RatChunk000Sub001Block149Part008

theorem surrogateDiagonalTailChunk000Sub001Block149Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part008] using hcert

def TailChunk000Sub001Block149Part009SupportExplicit : Finset ℕ :=
  ([14423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part009 : ℚ :=
  (3250358265625 : ℚ) / 27043869554246784882

def SurrogateDiagonalTailChunk000Sub001Block149Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14423
    = surrogateDiagTailX0RatChunk000Sub001Block149Part009

theorem surrogateDiagonalTailChunk000Sub001Block149Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part009] using hcert

def TailChunk000Sub001Block149Part010SupportExplicit : Finset ℕ :=
  ([14426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part010 : ℚ :=
  (812927640625 : ℚ) / 1691179633009903392

def SurrogateDiagonalTailChunk000Sub001Block149Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14426
    = surrogateDiagTailX0RatChunk000Sub001Block149Part010

theorem surrogateDiagonalTailChunk000Sub001Block149Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part010] using hcert

def TailChunk000Sub001Block149Part011SupportExplicit : Finset ℕ :=
  ([14429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part011 : ℚ :=
  (35893920425 : ℚ) / 32720703825547149696

def SurrogateDiagonalTailChunk000Sub001Block149Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14429
    = surrogateDiagTailX0RatChunk000Sub001Block149Part011

theorem surrogateDiagonalTailChunk000Sub001Block149Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part011] using hcert

def TailChunk000Sub001Block149Part012SupportExplicit : Finset ℕ :=
  ([14430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part012 : ℚ :=
  (684206167375 : ℚ) / 356715346733826048

def SurrogateDiagonalTailChunk000Sub001Block149Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14430
    = surrogateDiagTailX0RatChunk000Sub001Block149Part012

theorem surrogateDiagonalTailChunk000Sub001Block149Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part012] using hcert

def TailChunk000Sub001Block149Part013SupportExplicit : Finset ℕ :=
  ([14431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block149Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14431
    = surrogateDiagTailX0RatChunk000Sub001Block149Part013

theorem surrogateDiagonalTailChunk000Sub001Block149Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part013] using hcert

def TailChunk000Sub001Block149Part014SupportExplicit : Finset ℕ :=
  ([14433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part014 : ℚ :=
  (1456322880175 : ℚ) / 16581476717206437888

def SurrogateDiagonalTailChunk000Sub001Block149Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14433
    = surrogateDiagTailX0RatChunk000Sub001Block149Part014

theorem surrogateDiagonalTailChunk000Sub001Block149Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part014] using hcert

def TailChunk000Sub001Block149Part015SupportExplicit : Finset ℕ :=
  ([14434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part015 : ℚ :=
  (13325610691 : ℚ) / 145895114964355200

def SurrogateDiagonalTailChunk000Sub001Block149Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14434
    = surrogateDiagTailX0RatChunk000Sub001Block149Part015

theorem surrogateDiagonalTailChunk000Sub001Block149Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part015] using hcert

def TailChunk000Sub001Block149Part016SupportExplicit : Finset ℕ :=
  ([14435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part016 : ℚ :=
  (14103056125 : ℚ) / 1200191114428360704

def SurrogateDiagonalTailChunk000Sub001Block149Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14435
    = surrogateDiagTailX0RatChunk000Sub001Block149Part016

theorem surrogateDiagonalTailChunk000Sub001Block149Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part016] using hcert

def TailChunk000Sub001Block149Part017SupportExplicit : Finset ℕ :=
  ([14437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block149Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14437
    = surrogateDiagTailX0RatChunk000Sub001Block149Part017

theorem surrogateDiagonalTailChunk000Sub001Block149Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part017] using hcert

def TailChunk000Sub001Block149Part018SupportExplicit : Finset ℕ :=
  ([14438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block149Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14438
    = surrogateDiagTailX0RatChunk000Sub001Block149Part018

theorem surrogateDiagonalTailChunk000Sub001Block149Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part018] using hcert

def TailChunk000Sub001Block149Part019SupportExplicit : Finset ℕ :=
  ([14439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part019 : ℚ :=
  (5655601825 : ℚ) / 83793310898357448

def SurrogateDiagonalTailChunk000Sub001Block149Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14439
    = surrogateDiagTailX0RatChunk000Sub001Block149Part019

theorem surrogateDiagonalTailChunk000Sub001Block149Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part019] using hcert

def TailChunk000Sub001Block149Part020SupportExplicit : Finset ℕ :=
  ([14441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part020 : ℚ :=
  (266624497175 : ℚ) / 29292504718022028864

def SurrogateDiagonalTailChunk000Sub001Block149Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14441
    = surrogateDiagTailX0RatChunk000Sub001Block149Part020

theorem surrogateDiagonalTailChunk000Sub001Block149Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part020] using hcert

def TailChunk000Sub001Block149Part021SupportExplicit : Finset ℕ :=
  ([14442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part021 : ℚ :=
  (17278709025 : ℚ) / 26471898322386944

def SurrogateDiagonalTailChunk000Sub001Block149Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14442
    = surrogateDiagTailX0RatChunk000Sub001Block149Part021

theorem surrogateDiagonalTailChunk000Sub001Block149Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part021] using hcert

def TailChunk000Sub001Block149Part022SupportExplicit : Finset ℕ :=
  ([14443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part022 : ℚ :=
  (26943560707 : ℚ) / 2074014720000000000

def SurrogateDiagonalTailChunk000Sub001Block149Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14443
    = surrogateDiagTailX0RatChunk000Sub001Block149Part022

theorem surrogateDiagonalTailChunk000Sub001Block149Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part022] using hcert

def TailChunk000Sub001Block149Part023SupportExplicit : Finset ℕ :=
  ([14446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part023 : ℚ :=
  (22911691 : ℚ) / 1618660640194560

def SurrogateDiagonalTailChunk000Sub001Block149Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14446
    = surrogateDiagTailX0RatChunk000Sub001Block149Part023

theorem surrogateDiagonalTailChunk000Sub001Block149Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part023] using hcert

def TailChunk000Sub001Block149Part024SupportExplicit : Finset ℕ :=
  ([14447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block149Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block149Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14447
    = surrogateDiagTailX0RatChunk000Sub001Block149Part024

theorem surrogateDiagonalTailChunk000Sub001Block149Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block149Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block149Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block149Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block149Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block149Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block149Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block149HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block149Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block149Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block149Part000
    + surrogateDiagTailX0RatChunk000Sub001Block149Part001
    + surrogateDiagTailX0RatChunk000Sub001Block149Part002
    + surrogateDiagTailX0RatChunk000Sub001Block149Part003
    + surrogateDiagTailX0RatChunk000Sub001Block149Part004
    + surrogateDiagTailX0RatChunk000Sub001Block149Part005
    + surrogateDiagTailX0RatChunk000Sub001Block149Part006
    + surrogateDiagTailX0RatChunk000Sub001Block149Part007
    + surrogateDiagTailX0RatChunk000Sub001Block149Part008
    + surrogateDiagTailX0RatChunk000Sub001Block149Part009

def surrogateDiagonalTailChunk000Sub001Block149MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block149Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block149Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block149Part010
    + surrogateDiagTailX0RatChunk000Sub001Block149Part011
    + surrogateDiagTailX0RatChunk000Sub001Block149Part012
    + surrogateDiagTailX0RatChunk000Sub001Block149Part013
    + surrogateDiagTailX0RatChunk000Sub001Block149Part014
    + surrogateDiagTailX0RatChunk000Sub001Block149Part015
    + surrogateDiagTailX0RatChunk000Sub001Block149Part016
    + surrogateDiagTailX0RatChunk000Sub001Block149Part017
    + surrogateDiagTailX0RatChunk000Sub001Block149Part018
    + surrogateDiagTailX0RatChunk000Sub001Block149Part019

def surrogateDiagonalTailChunk000Sub001Block149TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block149Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block149Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block149Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block149Part020
    + surrogateDiagTailX0RatChunk000Sub001Block149Part021
    + surrogateDiagTailX0RatChunk000Sub001Block149Part022
    + surrogateDiagTailX0RatChunk000Sub001Block149Part023
    + surrogateDiagTailX0RatChunk000Sub001Block149Part024

def surrogateDiagonalTailChunk000Sub001Block149Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block149HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block149MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block149TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block149 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block149Part000
    + surrogateDiagTailX0RatChunk000Sub001Block149Part001
    + surrogateDiagTailX0RatChunk000Sub001Block149Part002
    + surrogateDiagTailX0RatChunk000Sub001Block149Part003
    + surrogateDiagTailX0RatChunk000Sub001Block149Part004
    + surrogateDiagTailX0RatChunk000Sub001Block149Part005
    + surrogateDiagTailX0RatChunk000Sub001Block149Part006
    + surrogateDiagTailX0RatChunk000Sub001Block149Part007
    + surrogateDiagTailX0RatChunk000Sub001Block149Part008
    + surrogateDiagTailX0RatChunk000Sub001Block149Part009
    + surrogateDiagTailX0RatChunk000Sub001Block149Part010
    + surrogateDiagTailX0RatChunk000Sub001Block149Part011
    + surrogateDiagTailX0RatChunk000Sub001Block149Part012
    + surrogateDiagTailX0RatChunk000Sub001Block149Part013
    + surrogateDiagTailX0RatChunk000Sub001Block149Part014
    + surrogateDiagTailX0RatChunk000Sub001Block149Part015
    + surrogateDiagTailX0RatChunk000Sub001Block149Part016
    + surrogateDiagTailX0RatChunk000Sub001Block149Part017
    + surrogateDiagTailX0RatChunk000Sub001Block149Part018
    + surrogateDiagTailX0RatChunk000Sub001Block149Part019
    + surrogateDiagTailX0RatChunk000Sub001Block149Part020
    + surrogateDiagTailX0RatChunk000Sub001Block149Part021
    + surrogateDiagTailX0RatChunk000Sub001Block149Part022
    + surrogateDiagTailX0RatChunk000Sub001Block149Part023
    + surrogateDiagTailX0RatChunk000Sub001Block149Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block149_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block149Head + surrogateDiagTailX0RatChunk000Sub001Block149Mid + surrogateDiagTailX0RatChunk000Sub001Block149Tail =
      surrogateDiagTailX0RatChunk000Sub001Block149 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block149Head surrogateDiagTailX0RatChunk000Sub001Block149Mid surrogateDiagTailX0RatChunk000Sub001Block149Tail surrogateDiagTailX0RatChunk000Sub001Block149
  ring

def SurrogateDiagonalTailChunk000Sub001Block149HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block149HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block149Head

def SurrogateDiagonalTailChunk000Sub001Block149MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block149MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block149Mid

def SurrogateDiagonalTailChunk000Sub001Block149TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block149TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block149Tail

theorem surrogateDiagonalTailChunk000Sub001Block149_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block149HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block149MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block149TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block149Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block149 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block149HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block149MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block149TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block149Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block149_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
