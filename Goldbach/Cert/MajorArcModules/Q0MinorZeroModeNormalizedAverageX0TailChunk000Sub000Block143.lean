import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [143,144). -/

/- Block 143 covers tail-support indices [3575,3600) and q from 5937 to 5974. -/

def TailChunk000Sub000Block143Part000SupportExplicit : Finset ℕ :=
  ([5937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part000 : ℚ :=
  (146780625 : ℚ) / 61230124201024

def SurrogateDiagonalTailChunk000Sub000Block143Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5937
    = surrogateDiagTailX0RatChunk000Sub000Block143Part000

theorem surrogateDiagonalTailChunk000Sub000Block143Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part000] using hcert

def TailChunk000Sub000Block143Part001SupportExplicit : Finset ℕ :=
  ([5938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part001 : ℚ :=
  (1101649750975 : ℚ) / 194036059033356288

def SurrogateDiagonalTailChunk000Sub000Block143Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5938
    = surrogateDiagTailX0RatChunk000Sub000Block143Part001

theorem surrogateDiagonalTailChunk000Sub000Block143Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part001] using hcert

def TailChunk000Sub000Block143Part002SupportExplicit : Finset ℕ :=
  ([5939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part002 : ℚ :=
  (551120640625 : ℚ) / 777190781390073042

def SurrogateDiagonalTailChunk000Sub000Block143Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5939
    = surrogateDiagTailX0RatChunk000Sub000Block143Part002

theorem surrogateDiagonalTailChunk000Sub000Block143Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part002] using hcert

def TailChunk000Sub000Block143Part003SupportExplicit : Finset ℕ :=
  ([5941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part003 : ℚ :=
  (2005518549325 : ℚ) / 2241874069333475328

def SurrogateDiagonalTailChunk000Sub000Block143Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5941
    = surrogateDiagTailX0RatChunk000Sub000Block143Part003

theorem surrogateDiagonalTailChunk000Sub000Block143Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part003] using hcert

def TailChunk000Sub000Block143Part004SupportExplicit : Finset ℕ :=
  ([5942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part004 : ℚ :=
  (220671025 : ℚ) / 77823838465362

def SurrogateDiagonalTailChunk000Sub000Block143Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5942
    = surrogateDiagTailX0RatChunk000Sub000Block143Part004

theorem surrogateDiagonalTailChunk000Sub000Block143Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part004] using hcert

def TailChunk000Sub000Block143Part005SupportExplicit : Finset ℕ :=
  ([5943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part005 : ℚ :=
  (132624662425 : ℚ) / 81976294805524992

def SurrogateDiagonalTailChunk000Sub000Block143Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5943
    = surrogateDiagTailX0RatChunk000Sub000Block143Part005

theorem surrogateDiagonalTailChunk000Sub000Block143Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part005] using hcert

def TailChunk000Sub000Block143Part006SupportExplicit : Finset ℕ :=
  ([5945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part006 : ℚ :=
  (3956137783 : ℚ) / 10072538008780800

def SurrogateDiagonalTailChunk000Sub000Block143Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5945
    = surrogateDiagTailX0RatChunk000Sub000Block143Part006

theorem surrogateDiagonalTailChunk000Sub000Block143Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part006] using hcert

def TailChunk000Sub000Block143Part007SupportExplicit : Finset ℕ :=
  ([5946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part007 : ℚ :=
  (3925789247 : ℚ) / 307452201344640

def SurrogateDiagonalTailChunk000Sub000Block143Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5946
    = surrogateDiagTailX0RatChunk000Sub000Block143Part007

theorem surrogateDiagonalTailChunk000Sub000Block143Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part007] using hcert

def TailChunk000Sub000Block143Part008SupportExplicit : Finset ℕ :=
  ([5947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part008 : ℚ :=
  (11408051975 : ℚ) / 276371175620247552

def SurrogateDiagonalTailChunk000Sub000Block143Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5947
    = surrogateDiagTailX0RatChunk000Sub000Block143Part008

theorem surrogateDiagonalTailChunk000Sub000Block143Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part008] using hcert

def TailChunk000Sub000Block143Part009SupportExplicit : Finset ℕ :=
  ([5951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part009 : ℚ :=
  (3337778327 : ℚ) / 42523783056000000

def SurrogateDiagonalTailChunk000Sub000Block143Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5951
    = surrogateDiagTailX0RatChunk000Sub000Block143Part009

theorem surrogateDiagonalTailChunk000Sub000Block143Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part009] using hcert

def TailChunk000Sub000Block143Part010SupportExplicit : Finset ℕ :=
  ([5953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part010 : ℚ :=
  (553722015625 : ℚ) / 784546262314647552

def SurrogateDiagonalTailChunk000Sub000Block143Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5953
    = surrogateDiagTailX0RatChunk000Sub000Block143Part010

theorem surrogateDiagonalTailChunk000Sub000Block143Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part010] using hcert

def TailChunk000Sub000Block143Part011SupportExplicit : Finset ℕ :=
  ([5954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part011 : ℚ :=
  (18604013675 : ℚ) / 2594761654321152

def SurrogateDiagonalTailChunk000Sub000Block143Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5954
    = surrogateDiagTailX0RatChunk000Sub000Block143Part011

theorem surrogateDiagonalTailChunk000Sub000Block143Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part011] using hcert

def TailChunk000Sub000Block143Part012SupportExplicit : Finset ℕ :=
  ([5955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part012 : ℚ :=
  (579617434475 : ℚ) / 125932421670764544

def SurrogateDiagonalTailChunk000Sub000Block143Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5955
    = surrogateDiagTailX0RatChunk000Sub000Block143Part012

theorem surrogateDiagonalTailChunk000Sub000Block143Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part012] using hcert

def TailChunk000Sub000Block143Part013SupportExplicit : Finset ℕ :=
  ([5957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part013 : ℚ :=
  (1709064995725 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk000Sub000Block143Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5957
    = surrogateDiagTailX0RatChunk000Sub000Block143Part013

theorem surrogateDiagonalTailChunk000Sub000Block143Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part013] using hcert

def TailChunk000Sub000Block143Part014SupportExplicit : Finset ℕ :=
  ([5959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part014 : ℚ :=
  (86060415709 : ℚ) / 113187592992000000

def SurrogateDiagonalTailChunk000Sub000Block143Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5959
    = surrogateDiagTailX0RatChunk000Sub000Block143Part014

theorem surrogateDiagonalTailChunk000Sub000Block143Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part014] using hcert

def TailChunk000Sub000Block143Part015SupportExplicit : Finset ℕ :=
  ([5961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part015 : ℚ :=
  (49323275 : ℚ) / 20742242781888

def SurrogateDiagonalTailChunk000Sub000Block143Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5961
    = surrogateDiagTailX0RatChunk000Sub000Block143Part015

theorem surrogateDiagonalTailChunk000Sub000Block143Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part015] using hcert

def TailChunk000Sub000Block143Part016SupportExplicit : Finset ℕ :=
  ([5962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part016 : ℚ :=
  (877730887 : ℚ) / 118121619600000

def SurrogateDiagonalTailChunk000Sub000Block143Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5962
    = surrogateDiagTailX0RatChunk000Sub000Block143Part016

theorem surrogateDiagonalTailChunk000Sub000Block143Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part016] using hcert

def TailChunk000Sub000Block143Part017SupportExplicit : Finset ℕ :=
  ([5963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part017 : ℚ :=
  (2156280672325 : ℚ) / 2845334237163061248

def SurrogateDiagonalTailChunk000Sub000Block143Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5963
    = surrogateDiagTailX0RatChunk000Sub000Block143Part017

theorem surrogateDiagonalTailChunk000Sub000Block143Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part017] using hcert

def TailChunk000Sub000Block143Part018SupportExplicit : Finset ℕ :=
  ([5965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part018 : ℚ :=
  (844422923075 : ℚ) / 646162648767135744

def SurrogateDiagonalTailChunk000Sub000Block143Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5965
    = surrogateDiagTailX0RatChunk000Sub000Block143Part018

theorem surrogateDiagonalTailChunk000Sub000Block143Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part018] using hcert

def TailChunk000Sub000Block143Part019SupportExplicit : Finset ℕ :=
  ([5966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part019 : ℚ :=
  (39885141425 : ℚ) / 5979184087938048

def SurrogateDiagonalTailChunk000Sub000Block143Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5966
    = surrogateDiagTailX0RatChunk000Sub000Block143Part019

theorem surrogateDiagonalTailChunk000Sub000Block143Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part019] using hcert

def TailChunk000Sub000Block143Part020SupportExplicit : Finset ℕ :=
  ([5969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part020 : ℚ :=
  (119550734525 : ℚ) / 156771769744812096

def SurrogateDiagonalTailChunk000Sub000Block143Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5969
    = surrogateDiagTailX0RatChunk000Sub000Block143Part020

theorem surrogateDiagonalTailChunk000Sub000Block143Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part020] using hcert

def TailChunk000Sub000Block143Part021SupportExplicit : Finset ℕ :=
  ([5970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part021 : ℚ :=
  (263463748925 : ℚ) / 7870776354422784

def SurrogateDiagonalTailChunk000Sub000Block143Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5970
    = surrogateDiagTailX0RatChunk000Sub000Block143Part021

theorem surrogateDiagonalTailChunk000Sub000Block143Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part021] using hcert

def TailChunk000Sub000Block143Part022SupportExplicit : Finset ℕ :=
  ([5971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part022 : ℚ :=
  (1862364115975 : ℚ) / 1707616094707795968

def SurrogateDiagonalTailChunk000Sub000Block143Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5971
    = surrogateDiagTailX0RatChunk000Sub000Block143Part022

theorem surrogateDiagonalTailChunk000Sub000Block143Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part022] using hcert

def TailChunk000Sub000Block143Part023SupportExplicit : Finset ℕ :=
  ([5973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part023 : ℚ :=
  (45049794457 : ℚ) / 16799519232000000

def SurrogateDiagonalTailChunk000Sub000Block143Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5973
    = surrogateDiagTailX0RatChunk000Sub000Block143Part023

theorem surrogateDiagonalTailChunk000Sub000Block143Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part023] using hcert

def TailChunk000Sub000Block143Part024SupportExplicit : Finset ℕ :=
  ([5974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block143Part024 : ℚ :=
  (1058330465875 : ℚ) / 166364121605326848

def SurrogateDiagonalTailChunk000Sub000Block143Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5974
    = surrogateDiagTailX0RatChunk000Sub000Block143Part024

theorem surrogateDiagonalTailChunk000Sub000Block143Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block143Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block143Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block143Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block143Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block143Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block143Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block143HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block143Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block143Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block143Part000
    + surrogateDiagTailX0RatChunk000Sub000Block143Part001
    + surrogateDiagTailX0RatChunk000Sub000Block143Part002
    + surrogateDiagTailX0RatChunk000Sub000Block143Part003
    + surrogateDiagTailX0RatChunk000Sub000Block143Part004
    + surrogateDiagTailX0RatChunk000Sub000Block143Part005
    + surrogateDiagTailX0RatChunk000Sub000Block143Part006
    + surrogateDiagTailX0RatChunk000Sub000Block143Part007
    + surrogateDiagTailX0RatChunk000Sub000Block143Part008
    + surrogateDiagTailX0RatChunk000Sub000Block143Part009

def surrogateDiagonalTailChunk000Sub000Block143MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block143Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block143Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block143Part010
    + surrogateDiagTailX0RatChunk000Sub000Block143Part011
    + surrogateDiagTailX0RatChunk000Sub000Block143Part012
    + surrogateDiagTailX0RatChunk000Sub000Block143Part013
    + surrogateDiagTailX0RatChunk000Sub000Block143Part014
    + surrogateDiagTailX0RatChunk000Sub000Block143Part015
    + surrogateDiagTailX0RatChunk000Sub000Block143Part016
    + surrogateDiagTailX0RatChunk000Sub000Block143Part017
    + surrogateDiagTailX0RatChunk000Sub000Block143Part018
    + surrogateDiagTailX0RatChunk000Sub000Block143Part019

def surrogateDiagonalTailChunk000Sub000Block143TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block143Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block143Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block143Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block143Part020
    + surrogateDiagTailX0RatChunk000Sub000Block143Part021
    + surrogateDiagTailX0RatChunk000Sub000Block143Part022
    + surrogateDiagTailX0RatChunk000Sub000Block143Part023
    + surrogateDiagTailX0RatChunk000Sub000Block143Part024

def surrogateDiagonalTailChunk000Sub000Block143Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block143HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block143MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block143TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block143 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block143Part000
    + surrogateDiagTailX0RatChunk000Sub000Block143Part001
    + surrogateDiagTailX0RatChunk000Sub000Block143Part002
    + surrogateDiagTailX0RatChunk000Sub000Block143Part003
    + surrogateDiagTailX0RatChunk000Sub000Block143Part004
    + surrogateDiagTailX0RatChunk000Sub000Block143Part005
    + surrogateDiagTailX0RatChunk000Sub000Block143Part006
    + surrogateDiagTailX0RatChunk000Sub000Block143Part007
    + surrogateDiagTailX0RatChunk000Sub000Block143Part008
    + surrogateDiagTailX0RatChunk000Sub000Block143Part009
    + surrogateDiagTailX0RatChunk000Sub000Block143Part010
    + surrogateDiagTailX0RatChunk000Sub000Block143Part011
    + surrogateDiagTailX0RatChunk000Sub000Block143Part012
    + surrogateDiagTailX0RatChunk000Sub000Block143Part013
    + surrogateDiagTailX0RatChunk000Sub000Block143Part014
    + surrogateDiagTailX0RatChunk000Sub000Block143Part015
    + surrogateDiagTailX0RatChunk000Sub000Block143Part016
    + surrogateDiagTailX0RatChunk000Sub000Block143Part017
    + surrogateDiagTailX0RatChunk000Sub000Block143Part018
    + surrogateDiagTailX0RatChunk000Sub000Block143Part019
    + surrogateDiagTailX0RatChunk000Sub000Block143Part020
    + surrogateDiagTailX0RatChunk000Sub000Block143Part021
    + surrogateDiagTailX0RatChunk000Sub000Block143Part022
    + surrogateDiagTailX0RatChunk000Sub000Block143Part023
    + surrogateDiagTailX0RatChunk000Sub000Block143Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block143_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block143Head + surrogateDiagTailX0RatChunk000Sub000Block143Mid + surrogateDiagTailX0RatChunk000Sub000Block143Tail =
      surrogateDiagTailX0RatChunk000Sub000Block143 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block143Head surrogateDiagTailX0RatChunk000Sub000Block143Mid surrogateDiagTailX0RatChunk000Sub000Block143Tail surrogateDiagTailX0RatChunk000Sub000Block143
  ring

def SurrogateDiagonalTailChunk000Sub000Block143HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block143HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block143Head

def SurrogateDiagonalTailChunk000Sub000Block143MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block143MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block143Mid

def SurrogateDiagonalTailChunk000Sub000Block143TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block143TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block143Tail

theorem surrogateDiagonalTailChunk000Sub000Block143_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block143HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block143MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block143TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block143Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block143 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block143HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block143MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block143TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block143Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block143_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
