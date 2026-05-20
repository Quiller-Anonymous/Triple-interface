import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [71,72). -/

/- Block 071 covers tail-support indices [1775,1800) and q from 2971 to 3010. -/

def TailChunk000Sub000Block071Part000SupportExplicit : Finset ℕ :=
  ([2971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part000 : ℚ :=
  (220671025 : ℚ) / 77823838465362

def SurrogateDiagonalTailChunk000Sub000Block071Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2971
    = surrogateDiagTailX0RatChunk000Sub000Block071Part000

theorem surrogateDiagonalTailChunk000Sub000Block071Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part000] using hcert

def TailChunk000Sub000Block071Part001SupportExplicit : Finset ℕ :=
  ([2973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part001 : ℚ :=
  (3925789247 : ℚ) / 307452201344640

def SurrogateDiagonalTailChunk000Sub000Block071Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2973
    = surrogateDiagTailX0RatChunk000Sub000Block071Part001

theorem surrogateDiagonalTailChunk000Sub000Block071Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part001] using hcert

def TailChunk000Sub000Block071Part002SupportExplicit : Finset ℕ :=
  ([2974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part002 : ℚ :=
  (138142783275 : ℚ) / 4064254000275736

def SurrogateDiagonalTailChunk000Sub000Block071Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2974
    = surrogateDiagTailX0RatChunk000Sub000Block071Part002

theorem surrogateDiagonalTailChunk000Sub000Block071Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part002] using hcert

def TailChunk000Sub000Block071Part003SupportExplicit : Finset ℕ :=
  ([2977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part003 : ℚ :=
  (18604013675 : ℚ) / 2594761654321152

def SurrogateDiagonalTailChunk000Sub000Block071Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2977
    = surrogateDiagTailX0RatChunk000Sub000Block071Part003

theorem surrogateDiagonalTailChunk000Sub000Block071Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part003] using hcert

def TailChunk000Sub000Block071Part004SupportExplicit : Finset ℕ :=
  ([2978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part004 : ℚ :=
  (276973840925 : ℚ) / 6129267674333184

def SurrogateDiagonalTailChunk000Sub000Block071Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2978
    = surrogateDiagTailX0RatChunk000Sub000Block071Part004

theorem surrogateDiagonalTailChunk000Sub000Block071Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part004] using hcert

def TailChunk000Sub000Block071Part005SupportExplicit : Finset ℕ :=
  ([2981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part005 : ℚ :=
  (877730887 : ℚ) / 118121619600000

def SurrogateDiagonalTailChunk000Sub000Block071Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2981
    = surrogateDiagTailX0RatChunk000Sub000Block071Part005

theorem surrogateDiagonalTailChunk000Sub000Block071Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part005] using hcert

def TailChunk000Sub000Block071Part006SupportExplicit : Finset ℕ :=
  ([2982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part006 : ℚ :=
  (370327913 : ℚ) / 1844336793600

def SurrogateDiagonalTailChunk000Sub000Block071Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2982
    = surrogateDiagTailX0RatChunk000Sub000Block071Part006

theorem surrogateDiagonalTailChunk000Sub000Block071Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part006] using hcert

def TailChunk000Sub000Block071Part007SupportExplicit : Finset ℕ :=
  ([2983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part007 : ℚ :=
  (39885141425 : ℚ) / 5979184087938048

def SurrogateDiagonalTailChunk000Sub000Block071Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2983
    = surrogateDiagTailX0RatChunk000Sub000Block071Part007

theorem surrogateDiagonalTailChunk000Sub000Block071Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part007] using hcert

def TailChunk000Sub000Block071Part008SupportExplicit : Finset ℕ :=
  ([2985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part008 : ℚ :=
  (263463748925 : ℚ) / 7870776354422784

def SurrogateDiagonalTailChunk000Sub000Block071Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2985
    = surrogateDiagTailX0RatChunk000Sub000Block071Part008

theorem surrogateDiagonalTailChunk000Sub000Block071Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part008] using hcert

def TailChunk000Sub000Block071Part009SupportExplicit : Finset ℕ :=
  ([2986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part009 : ℚ :=
  (278463946325 : ℚ) / 6195440005353024

def SurrogateDiagonalTailChunk000Sub000Block071Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2986
    = surrogateDiagTailX0RatChunk000Sub000Block071Part009

theorem surrogateDiagonalTailChunk000Sub000Block071Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part009] using hcert

def TailChunk000Sub000Block071Part010SupportExplicit : Finset ℕ :=
  ([2987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part010 : ℚ :=
  (1058330465875 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk000Sub000Block071Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2987
    = surrogateDiagTailX0RatChunk000Sub000Block071Part010

theorem surrogateDiagonalTailChunk000Sub000Block071Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part010] using hcert

def TailChunk000Sub000Block071Part011SupportExplicit : Finset ℕ :=
  ([2990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part011 : ℚ :=
  (152437028375 : ℚ) / 1554721255194624

def SurrogateDiagonalTailChunk000Sub000Block071Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2990
    = surrogateDiagTailX0RatChunk000Sub000Block071Part011

theorem surrogateDiagonalTailChunk000Sub000Block071Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part011] using hcert

def TailChunk000Sub000Block071Part012SupportExplicit : Finset ℕ :=
  ([2991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part012 : ℚ :=
  (496682251075 : ℚ) / 39371702536194048

def SurrogateDiagonalTailChunk000Sub000Block071Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2991
    = surrogateDiagTailX0RatChunk000Sub000Block071Part012

theorem surrogateDiagonalTailChunk000Sub000Block071Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part012] using hcert

def TailChunk000Sub000Block071Part013SupportExplicit : Finset ℕ :=
  ([2993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part013 : ℚ :=
  (11051412839 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block071Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2993
    = surrogateDiagTailX0RatChunk000Sub000Block071Part013

theorem surrogateDiagonalTailChunk000Sub000Block071Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part013] using hcert

def TailChunk000Sub000Block071Part014SupportExplicit : Finset ℕ :=
  ([2994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part014 : ℚ :=
  (295184600725 : ℚ) / 2460731408512128

def SurrogateDiagonalTailChunk000Sub000Block071Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2994
    = surrogateDiagTailX0RatChunk000Sub000Block071Part014

theorem surrogateDiagonalTailChunk000Sub000Block071Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part014] using hcert

def TailChunk000Sub000Block071Part015SupportExplicit : Finset ℕ :=
  ([2995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part015 : ℚ :=
  (436539234425 : ℚ) / 40929983020852224

def SurrogateDiagonalTailChunk000Sub000Block071Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2995
    = surrogateDiagTailX0RatChunk000Sub000Block071Part015

theorem surrogateDiagonalTailChunk000Sub000Block071Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part015] using hcert

def TailChunk000Sub000Block071Part016SupportExplicit : Finset ℕ :=
  ([2998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part016 : ℚ :=
  (2864926275 : ℚ) / 85655800387864

def SurrogateDiagonalTailChunk000Sub000Block071Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2998
    = surrogateDiagTailX0RatChunk000Sub000Block071Part016

theorem surrogateDiagonalTailChunk000Sub000Block071Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part016] using hcert

def TailChunk000Sub000Block071Part017SupportExplicit : Finset ℕ :=
  ([2999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part017 : ℚ :=
  (1124025274975 : ℚ) / 202000931867992008

def SurrogateDiagonalTailChunk000Sub000Block071Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2999
    = surrogateDiagTailX0RatChunk000Sub000Block071Part017

theorem surrogateDiagonalTailChunk000Sub000Block071Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part017] using hcert

def TailChunk000Sub000Block071Part018SupportExplicit : Finset ℕ :=
  ([3001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part018 : ℚ :=
  (45020998999 : ℚ) / 8101620000000000

def SurrogateDiagonalTailChunk000Sub000Block071Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3001
    = surrogateDiagTailX0RatChunk000Sub000Block071Part018

theorem surrogateDiagonalTailChunk000Sub000Block071Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part018] using hcert

def TailChunk000Sub000Block071Part019SupportExplicit : Finset ℕ :=
  ([3002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part019 : ℚ :=
  (398052208825 : ℚ) / 9716174142899328

def SurrogateDiagonalTailChunk000Sub000Block071Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3002
    = surrogateDiagTailX0RatChunk000Sub000Block071Part019

theorem surrogateDiagonalTailChunk000Sub000Block071Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part019] using hcert

def TailChunk000Sub000Block071Part020SupportExplicit : Finset ℕ :=
  ([3003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part020 : ℚ :=
  (428698981 : ℚ) / 9557059829760

def SurrogateDiagonalTailChunk000Sub000Block071Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3003
    = surrogateDiagTailX0RatChunk000Sub000Block071Part020

theorem surrogateDiagonalTailChunk000Sub000Block071Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part020] using hcert

def TailChunk000Sub000Block071Part021SupportExplicit : Finset ℕ :=
  ([3005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part021 : ℚ :=
  (325525873 : ℚ) / 30726144000000

def SurrogateDiagonalTailChunk000Sub000Block071Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3005
    = surrogateDiagTailX0RatChunk000Sub000Block071Part021

theorem surrogateDiagonalTailChunk000Sub000Block071Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part021] using hcert

def TailChunk000Sub000Block071Part022SupportExplicit : Finset ℕ :=
  ([3007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part022 : ℚ :=
  (11142707369 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block071Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3007
    = surrogateDiagTailX0RatChunk000Sub000Block071Part022

theorem surrogateDiagonalTailChunk000Sub000Block071Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part022] using hcert

def TailChunk000Sub000Block071Part023SupportExplicit : Finset ℕ :=
  ([3009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part023 : ℚ :=
  (158323239675 : ℚ) / 9890482792431616

def SurrogateDiagonalTailChunk000Sub000Block071Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3009
    = surrogateDiagTailX0RatChunk000Sub000Block071Part023

theorem surrogateDiagonalTailChunk000Sub000Block071Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part023] using hcert

def TailChunk000Sub000Block071Part024SupportExplicit : Finset ℕ :=
  ([3010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block071Part024 : ℚ :=
  (146860069175 : ℚ) / 1290740661633024

def SurrogateDiagonalTailChunk000Sub000Block071Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3010
    = surrogateDiagTailX0RatChunk000Sub000Block071Part024

theorem surrogateDiagonalTailChunk000Sub000Block071Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block071Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block071Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block071Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block071Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block071Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block071Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block071HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block071Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block071Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block071Part000
    + surrogateDiagTailX0RatChunk000Sub000Block071Part001
    + surrogateDiagTailX0RatChunk000Sub000Block071Part002
    + surrogateDiagTailX0RatChunk000Sub000Block071Part003
    + surrogateDiagTailX0RatChunk000Sub000Block071Part004
    + surrogateDiagTailX0RatChunk000Sub000Block071Part005
    + surrogateDiagTailX0RatChunk000Sub000Block071Part006
    + surrogateDiagTailX0RatChunk000Sub000Block071Part007
    + surrogateDiagTailX0RatChunk000Sub000Block071Part008
    + surrogateDiagTailX0RatChunk000Sub000Block071Part009

def surrogateDiagonalTailChunk000Sub000Block071MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block071Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block071Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block071Part010
    + surrogateDiagTailX0RatChunk000Sub000Block071Part011
    + surrogateDiagTailX0RatChunk000Sub000Block071Part012
    + surrogateDiagTailX0RatChunk000Sub000Block071Part013
    + surrogateDiagTailX0RatChunk000Sub000Block071Part014
    + surrogateDiagTailX0RatChunk000Sub000Block071Part015
    + surrogateDiagTailX0RatChunk000Sub000Block071Part016
    + surrogateDiagTailX0RatChunk000Sub000Block071Part017
    + surrogateDiagTailX0RatChunk000Sub000Block071Part018
    + surrogateDiagTailX0RatChunk000Sub000Block071Part019

def surrogateDiagonalTailChunk000Sub000Block071TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block071Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block071Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block071Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block071Part020
    + surrogateDiagTailX0RatChunk000Sub000Block071Part021
    + surrogateDiagTailX0RatChunk000Sub000Block071Part022
    + surrogateDiagTailX0RatChunk000Sub000Block071Part023
    + surrogateDiagTailX0RatChunk000Sub000Block071Part024

def surrogateDiagonalTailChunk000Sub000Block071Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block071HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block071MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block071TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block071 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block071Part000
    + surrogateDiagTailX0RatChunk000Sub000Block071Part001
    + surrogateDiagTailX0RatChunk000Sub000Block071Part002
    + surrogateDiagTailX0RatChunk000Sub000Block071Part003
    + surrogateDiagTailX0RatChunk000Sub000Block071Part004
    + surrogateDiagTailX0RatChunk000Sub000Block071Part005
    + surrogateDiagTailX0RatChunk000Sub000Block071Part006
    + surrogateDiagTailX0RatChunk000Sub000Block071Part007
    + surrogateDiagTailX0RatChunk000Sub000Block071Part008
    + surrogateDiagTailX0RatChunk000Sub000Block071Part009
    + surrogateDiagTailX0RatChunk000Sub000Block071Part010
    + surrogateDiagTailX0RatChunk000Sub000Block071Part011
    + surrogateDiagTailX0RatChunk000Sub000Block071Part012
    + surrogateDiagTailX0RatChunk000Sub000Block071Part013
    + surrogateDiagTailX0RatChunk000Sub000Block071Part014
    + surrogateDiagTailX0RatChunk000Sub000Block071Part015
    + surrogateDiagTailX0RatChunk000Sub000Block071Part016
    + surrogateDiagTailX0RatChunk000Sub000Block071Part017
    + surrogateDiagTailX0RatChunk000Sub000Block071Part018
    + surrogateDiagTailX0RatChunk000Sub000Block071Part019
    + surrogateDiagTailX0RatChunk000Sub000Block071Part020
    + surrogateDiagTailX0RatChunk000Sub000Block071Part021
    + surrogateDiagTailX0RatChunk000Sub000Block071Part022
    + surrogateDiagTailX0RatChunk000Sub000Block071Part023
    + surrogateDiagTailX0RatChunk000Sub000Block071Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block071_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block071Head + surrogateDiagTailX0RatChunk000Sub000Block071Mid + surrogateDiagTailX0RatChunk000Sub000Block071Tail =
      surrogateDiagTailX0RatChunk000Sub000Block071 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block071Head surrogateDiagTailX0RatChunk000Sub000Block071Mid surrogateDiagTailX0RatChunk000Sub000Block071Tail surrogateDiagTailX0RatChunk000Sub000Block071
  ring

def SurrogateDiagonalTailChunk000Sub000Block071HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block071HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block071Head

def SurrogateDiagonalTailChunk000Sub000Block071MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block071MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block071Mid

def SurrogateDiagonalTailChunk000Sub000Block071TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block071TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block071Tail

theorem surrogateDiagonalTailChunk000Sub000Block071_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block071HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block071MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block071TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block071Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block071 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block071HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block071MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block071TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block071Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block071_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
